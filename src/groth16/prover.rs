use rand_core::RngCore;
use std::ops::{AddAssign, MulAssign};
use std::sync::Arc;

use futures::Future;

use ff::{Field, PrimeField};
use group::{prime::PrimeCurveAffine, Curve};
use pairing::Engine;

use super::{ParameterSource, Proof};

use crate::{Circuit, ConstraintSystem, Index, LinearCombination, SynthesisError, Variable};

use crate::domain::{EvaluationDomain, Scalar};

use crate::multiexp::{multiexp, DensityTracker, FullDensity};

use crate::multicore::Worker;

fn eval<S: PrimeField>(
    lc: &LinearCombination<S>,
    mut input_density: Option<&mut DensityTracker>,
    mut aux_density: Option<&mut DensityTracker>,
    input_assignment: &[S],
    aux_assignment: &[S],
) -> S {
    let mut acc = S::zero();

    for &(index, coeff) in lc.0.iter() {
        let mut tmp;

        match index {
            Variable(Index::Input(i)) => {
                tmp = input_assignment[i];
                if let Some(ref mut v) = input_density {
                    v.inc(i);
                }
            }
            Variable(Index::Aux(i)) => {
                tmp = aux_assignment[i];
                if let Some(ref mut v) = aux_density {
                    v.inc(i);
                }
            }
        }

        if coeff == S::one() {
            acc.add_assign(&tmp);
        } else {
            tmp.mul_assign(&coeff);
            acc.add_assign(&tmp);
        }
    }

    acc
}

struct ProvingAssignment<S: PrimeField> {
    // Density of queries
    a_aux_density: DensityTracker,
    b_input_density: DensityTracker,
    b_aux_density: DensityTracker,

    // Evaluations of A, B, C polynomials
    a: Vec<Scalar<S>>,
    b: Vec<Scalar<S>>,
    c: Vec<Scalar<S>>,

    // Assignments of variables
    input_assignment: Vec<S>,
    aux_assignment: Vec<S>,
}

impl<S: PrimeField> ConstraintSystem<S> for ProvingAssignment<S> {
    type Root = Self;

    fn alloc<F, A, AR>(&mut self, _: A, f: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<S, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        self.aux_assignment.push(f()?);
        self.a_aux_density.add_element();
        self.b_aux_density.add_element();

        Ok(Variable(Index::Aux(self.aux_assignment.len() - 1)))
    }

    fn alloc_input<F, A, AR>(&mut self, _: A, f: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<S, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        self.input_assignment.push(f()?);
        self.b_input_density.add_element();

        Ok(Variable(Index::Input(self.input_assignment.len() - 1)))
    }

    fn enforce<A, AR, LA, LB, LC>(&mut self, _: A, a: LA, b: LB, c: LC)
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
        LA: FnOnce(LinearCombination<S>) -> LinearCombination<S>,
        LB: FnOnce(LinearCombination<S>) -> LinearCombination<S>,
        LC: FnOnce(LinearCombination<S>) -> LinearCombination<S>,
    {
        let a = a(LinearCombination::zero());
        let b = b(LinearCombination::zero());
        let c = c(LinearCombination::zero());

        self.a.push(Scalar(eval(
            &a,
            // Inputs have full density in the A query
            // because there are constraints of the
            // form x * 0 = 0 for each input.
            None,
            Some(&mut self.a_aux_density),
            &self.input_assignment,
            &self.aux_assignment,
        )));
        self.b.push(Scalar(eval(
            &b,
            Some(&mut self.b_input_density),
            Some(&mut self.b_aux_density),
            &self.input_assignment,
            &self.aux_assignment,
        )));
        self.c.push(Scalar(eval(
            &c,
            // There is no C polynomial query,
            // though there is an (beta)A + (alpha)B + C
            // query for all aux variables.
            // However, that query has full density.
            None,
            None,
            &self.input_assignment,
            &self.aux_assignment,
        )));
    }

    fn push_namespace<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        // Do nothing; we don't care about namespaces in this context.
    }

    fn pop_namespace(&mut self) {
        // Do nothing; we don't care about namespaces in this context.
    }

    fn get_root(&mut self) -> &mut Self::Root {
        self
    }
}

pub fn create_random_proof<E, C, R, P: ParameterSource<E>>(
    circuit: C,
    params: P,
    mut rng: &mut R,
) -> Result<Proof<E>, SynthesisError>
where
    E: Engine,
    C: Circuit<E::Fr>,
    R: RngCore,
{
    let r = E::Fr::random(&mut rng);
    let s = E::Fr::random(&mut rng);

    create_proof::<E, C, P>(circuit, params, r, s)
}

pub fn create_proof<E, C, P: ParameterSource<E>>(
    circuit: C,
    mut params: P,
    r: E::Fr,
    s: E::Fr,
) -> Result<Proof<E>, SynthesisError>
where
    E: Engine,
    C: Circuit<E::Fr>,
{
    let mut prover = ProvingAssignment {
        a_aux_density: DensityTracker::new(),
        b_input_density: DensityTracker::new(),
        b_aux_density: DensityTracker::new(),
        a: vec![],
        b: vec![],
        c: vec![],
        input_assignment: vec![],
        aux_assignment: vec![],
    };

    prover.alloc_input(|| "", || Ok(E::Fr::one()))?;

    circuit.synthesize(&mut prover)?;

    for i in 0..prover.input_assignment.len() {
        prover.enforce(|| "", |lc| lc + Variable(Index::Input(i)), |lc| lc, |lc| lc);
    }

    let worker = Worker::new();

    let vk = params.get_vk(prover.input_assignment.len())?;

    let h = {
        let mut a = EvaluationDomain::from_coeffs(prover.a)?;
        let mut b = EvaluationDomain::from_coeffs(prover.b)?;
        let mut c = EvaluationDomain::from_coeffs(prover.c)?;
        a.ifft(&worker);
        a.coset_fft(&worker);
        b.ifft(&worker);
        b.coset_fft(&worker);
        c.ifft(&worker);
        c.coset_fft(&worker);

        a.mul_assign(&worker, &b);
        drop(b);
        a.sub_assign(&worker, &c);
        drop(c);
        a.divide_by_z_on_coset(&worker);
        a.icoset_fft(&worker);
        let mut a = a.into_coeffs();
        let a_len = a.len() - 1;
        a.truncate(a_len);
        // TODO: parallelize if it's even helpful
        let a = Arc::new(a.into_iter().map(|s| s.0.to_le_bits()).collect::<Vec<_>>());

        multiexp(&worker, params.get_h(a.len())?, FullDensity, a)
    };

    // TODO: parallelize if it's even helpful
    let input_assignment = Arc::new(
        prover
            .input_assignment
            .into_iter()
            .map(|s| s.to_le_bits())
            .collect::<Vec<_>>(),
    );
    let aux_assignment = Arc::new(
        prover
            .aux_assignment
            .into_iter()
            .map(|s| s.to_le_bits())
            .collect::<Vec<_>>(),
    );

    let l = multiexp(
        &worker,
        params.get_l(aux_assignment.len())?,
        FullDensity,
        aux_assignment.clone(),
    );

    let a_aux_density_total = prover.a_aux_density.get_total_density();

    let (a_inputs_source, a_aux_source) =
        params.get_a(input_assignment.len(), a_aux_density_total)?;

    let a_inputs = multiexp(
        &worker,
        a_inputs_source,
        FullDensity,
        input_assignment.clone(),
    );
    let a_aux = multiexp(
        &worker,
        a_aux_source,
        Arc::new(prover.a_aux_density),
        aux_assignment.clone(),
    );

    let b_input_density = Arc::new(prover.b_input_density);
    let b_input_density_total = b_input_density.get_total_density();
    let b_aux_density = Arc::new(prover.b_aux_density);
    let b_aux_density_total = b_aux_density.get_total_density();

    let (b_g1_inputs_source, b_g1_aux_source) =
        params.get_b_g1(b_input_density_total, b_aux_density_total)?;

    let b_g1_inputs = multiexp(
        &worker,
        b_g1_inputs_source,
        b_input_density.clone(),
        input_assignment.clone(),
    );
    let b_g1_aux = multiexp(
        &worker,
        b_g1_aux_source,
        b_aux_density.clone(),
        aux_assignment.clone(),
    );

    let (b_g2_inputs_source, b_g2_aux_source) =
        params.get_b_g2(b_input_density_total, b_aux_density_total)?;

    let b_g2_inputs = multiexp(
        &worker,
        b_g2_inputs_source,
        b_input_density,
        input_assignment,
    );
    let b_g2_aux = multiexp(&worker, b_g2_aux_source, b_aux_density, aux_assignment);

    if bool::from(vk.delta_g1.is_identity() | vk.delta_g2.is_identity()) {
        // If this element is zero, someone is trying to perform a
        // subversion-CRS attack.
        return Err(SynthesisError::UnexpectedIdentity);
    }

    let mut g_a = vk.delta_g1 * &r;
    AddAssign::<&E::G1Affine>::add_assign(&mut g_a, &vk.alpha_g1);
    let mut g_b = vk.delta_g2 * &s;
    AddAssign::<&E::G2Affine>::add_assign(&mut g_b, &vk.beta_g2);
    let mut g_c;
    {
        let mut rs = r;
        rs.mul_assign(&s);

        g_c = vk.delta_g1 * &rs;
        AddAssign::<&E::G1>::add_assign(&mut g_c, &(vk.alpha_g1 * &s));
        AddAssign::<&E::G1>::add_assign(&mut g_c, &(vk.beta_g1 * &r));
    }
    let mut a_answer = a_inputs.wait()?;
    AddAssign::<&E::G1>::add_assign(&mut a_answer, &a_aux.wait()?);
    AddAssign::<&E::G1>::add_assign(&mut g_a, &a_answer);
    MulAssign::<E::Fr>::mul_assign(&mut a_answer, s);
    AddAssign::<&E::G1>::add_assign(&mut g_c, &a_answer);

    let mut b1_answer: E::G1 = b_g1_inputs.wait()?;
    AddAssign::<&E::G1>::add_assign(&mut b1_answer, &b_g1_aux.wait()?);
    let mut b2_answer = b_g2_inputs.wait()?;
    AddAssign::<&E::G2>::add_assign(&mut b2_answer, &b_g2_aux.wait()?);

    AddAssign::<&E::G2>::add_assign(&mut g_b, &b2_answer);
    MulAssign::<E::Fr>::mul_assign(&mut b1_answer, r);
    AddAssign::<&E::G1>::add_assign(&mut g_c, &b1_answer);
    AddAssign::<&E::G1>::add_assign(&mut g_c, &h.wait()?);
    AddAssign::<&E::G1>::add_assign(&mut g_c, &l.wait()?);

    Ok(Proof {
        a: g_a.to_affine(),
        b: g_b.to_affine(),
        c: g_c.to_affine(),
    })
}
