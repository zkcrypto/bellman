use rand::Rng;

use std::sync::Arc;

use crate::pairing::{
    Engine,
    Wnaf,
    CurveProjective,
    CurveAffine
};

use crate::pairing::ff::{    
    PrimeField,
    Field
};

use super::{
    Parameters,
    VerifyingKey
};

use crate::{
    SynthesisError,
    Circuit,
    ConstraintSystem,
    LinearCombination,
    Variable,
    Index
};

use crate::domain::{
    Scalar
};

use crate::multicore::{
    Worker
};

use std::marker::PhantomData;

use crate::sonic::cs::{Backend, SynthesisDriver};
use crate::sonic::srs::SRS;
use crate::sonic::cs::LinearCombination as SonicLinearCombination;
use crate::sonic::cs::Circuit as SonicCircuit;
use crate::sonic::cs::ConstraintSystem as SonicConstraintSystem;
use crate::sonic::cs::Variable as SonicVariable;
use crate::sonic::cs::Coeff;
use crate::sonic::sonic::{AdaptorCircuit};
use super::parameters::NUM_BLINDINGS;
use crate::sonic::sonic::NonassigningSynthesizer;
use crate::sonic::sonic::PermutationSynthesizer;
use crate::sonic::sonic::{Basic, Preprocess};

use crate::verbose_flag;

/// Generates a random common reference string for
/// a circuit.
pub fn generate_random_parameters<E, C, R>(
    circuit: C,
    rng: &mut R
) -> Result<Parameters<E>, SynthesisError>
    where E: Engine, C: Circuit<E>, R: Rng
{
    let alpha = rng.gen();
    let x = rng.gen();

    generate_parameters::<E, C>(
        circuit,
        alpha,
        x
    )
}

/// This is our assembly structure that we'll use to synthesize the
/// circuit into
#[derive(Clone, Debug)]
pub struct CircuitParameters<E: Engine> {
    pub num_inputs: usize,
    pub num_aux: usize,
    pub num_constraints: usize,
    pub k_map: Vec<usize>,
    pub n: usize,
    pub q: usize,
    _marker: PhantomData<E>
}

/// This is our assembly structure that we'll use to synthesize the
/// circuit into
struct GeneratorAssembly<'a, E: Engine, CS: SonicConstraintSystem<E> + 'a> {
    cs: &'a mut CS,
    num_inputs: usize,
    num_aux: usize,
    num_constraints: usize,
    _marker: PhantomData<E>
}

impl<'a, E: Engine, CS: SonicConstraintSystem<E> + 'a> crate::ConstraintSystem<E>
    for GeneratorAssembly<'a, E, CS>
{
    type Root = Self;

    // this is an important change
    fn one() -> crate::Variable {
        crate::Variable::new_unchecked(crate::Index::Input(1))
    }

    fn alloc<F, A, AR>(&mut self, _: A, f: F) -> Result<crate::Variable, crate::SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, crate::SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        self.num_aux += 1;

        let var = self.cs.alloc(|| {
            f().map_err(|_| crate::SynthesisError::AssignmentMissing)
        }).map_err(|_| crate::SynthesisError::AssignmentMissing)?;

        Ok(match var {
            SonicVariable::A(index) => crate::Variable::new_unchecked(crate::Index::Input(index)),
            SonicVariable::B(index) => crate::Variable::new_unchecked(crate::Index::Aux(index)),
            _ => unreachable!(),
        })
    }

    fn alloc_input<F, A, AR>(
        &mut self,
        _: A,
        f: F,
    ) -> Result<crate::Variable, crate::SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, crate::SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        self.num_inputs += 1;

        let var = self.cs.alloc_input(|| {
            f().map_err(|_| crate::SynthesisError::AssignmentMissing)
        }).map_err(|_| crate::SynthesisError::AssignmentMissing)?;

        Ok(match var {
            SonicVariable::A(index) => crate::Variable::new_unchecked(crate::Index::Input(index)),
            SonicVariable::B(index) => crate::Variable::new_unchecked(crate::Index::Aux(index)),
            _ => unreachable!(),
        })
    }

    fn enforce<A, AR, LA, LB, LC>(&mut self, _: A, a: LA, b: LB, c: LC)
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
        LA: FnOnce(crate::LinearCombination<E>) -> crate::LinearCombination<E>,
        LB: FnOnce(crate::LinearCombination<E>) -> crate::LinearCombination<E>,
        LC: FnOnce(crate::LinearCombination<E>) -> crate::LinearCombination<E>,
    {
        fn convert<E: Engine>(lc: crate::LinearCombination<E>) -> SonicLinearCombination<E> {
            let mut ret = SonicLinearCombination::zero();

            for &(v, coeff) in lc.as_ref().iter() {
                let var = match v.get_unchecked() {
                    crate::Index::Input(i) => SonicVariable::A(i),
                    crate::Index::Aux(i) => SonicVariable::B(i),
                };

                ret = ret + (Coeff::Full(coeff), var);
            }

            ret
        }

        fn eval<E: Engine, CS: SonicConstraintSystem<E>>(
            lc: &SonicLinearCombination<E>,
            cs: &CS,
        ) -> Option<E::Fr> {
            let mut ret = E::Fr::zero();

            for &(v, coeff) in lc.as_ref().iter() {
                let mut tmp = match cs.get_value(v) {
                    Ok(tmp) => tmp,
                    Err(_) => return None,
                };
                coeff.multiply(&mut tmp);
                ret.add_assign(&tmp);
            }

            Some(ret)
        }

        self.num_constraints += 1;

        let a_lc = convert(a(crate::LinearCombination::zero()));
        let a_value = eval(&a_lc, &*self.cs);
        let b_lc = convert(b(crate::LinearCombination::zero()));
        let b_value = eval(&b_lc, &*self.cs);
        let c_lc = convert(c(crate::LinearCombination::zero()));
        let c_value = eval(&c_lc, &*self.cs);

        let (a, b, c) = self
            .cs
            .multiply(|| Ok((a_value.unwrap(), b_value.unwrap(), c_value.unwrap())))
            .unwrap();

        self.cs.enforce_zero(a_lc - a);
        self.cs.enforce_zero(b_lc - b);
        self.cs.enforce_zero(c_lc - c);
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



/// Get circuit information such as number of input, variables, 
/// constraints, and the corresponding SONIC parameters
/// k_map, n, q
pub fn get_circuit_parameters<E, C>(
    circuit: C,
) -> Result<CircuitParameters<E>, SynthesisError>
    where E: Engine, C: Circuit<E>

{
    let mut preprocess = Preprocess::new();

    let (num_inputs, num_aux, num_constraints) = {

        let mut cs: NonassigningSynthesizer<E, &'_ mut Preprocess<E>> = NonassigningSynthesizer::new(&mut preprocess);

        let one = cs.alloc_input(|| Ok(E::Fr::one())).expect("should have no issues");

        match (one, <NonassigningSynthesizer<E, &'_ mut Preprocess<E>> as SonicConstraintSystem<E>>::ONE) {
            (SonicVariable::A(1), SonicVariable::A(1)) => {},
            _ => return Err(SynthesisError::UnconstrainedVariable)
        }

        let mut assembly = GeneratorAssembly::<'_, E, _> {
            cs: &mut cs,
            num_inputs: 0,
            num_aux: 0,
            num_constraints: 0,
            _marker: PhantomData
        };

        circuit.synthesize(&mut assembly)?;

        (assembly.num_inputs, assembly.num_aux, assembly.num_constraints)
    };

    Ok(CircuitParameters {
        num_inputs: num_inputs,
        num_aux: num_aux,
        num_constraints: num_constraints,
        k_map: preprocess.k_map,
        n: preprocess.n,
        q: preprocess.q,
        _marker: PhantomData
    })
}

/// Get circuit information such as number of input, variables, 
/// constraints, and the corresponding SONIC parameters
/// k_map, n, q
pub fn get_circuit_parameters_for_succinct_sonic<E, C>(
    circuit: C,
) -> Result<CircuitParameters<E>, SynthesisError>
    where E: Engine, C: Circuit<E>

{
    let mut preprocess = Preprocess::new();

    let (num_inputs, num_aux, num_constraints) = {

        let mut cs: PermutationSynthesizer<E, &'_ mut Preprocess<E>> = PermutationSynthesizer::new(&mut preprocess);

        let one = cs.alloc_input(|| Ok(E::Fr::one())).expect("should have no issues");

        match (one, <PermutationSynthesizer<E, &'_ mut Preprocess<E>> as SonicConstraintSystem<E>>::ONE) {
            (SonicVariable::A(1), SonicVariable::A(1)) => {},
            _ => return Err(SynthesisError::UnconstrainedVariable)
        }

        let mut assembly = GeneratorAssembly::<'_, E, _> {
            cs: &mut cs,
            num_inputs: 0,
            num_aux: 0,
            num_constraints: 0,
            _marker: PhantomData
        };

        circuit.synthesize(&mut assembly)?;

        (assembly.num_inputs, assembly.num_aux, assembly.num_constraints)
    };

    Ok(CircuitParameters {
        num_inputs: num_inputs,
        num_aux: num_aux,
        num_constraints: num_constraints,
        k_map: preprocess.k_map,
        n: preprocess.n,
        q: preprocess.q,
        _marker: PhantomData
    })
}

pub fn generate_parameters<E, C>(
    circuit: C,
    alpha: E::Fr,
    x: E::Fr
) -> Result<Parameters<E>, SynthesisError>
    where E: Engine, C: Circuit<E> 
{
    let circuit_parameters = get_circuit_parameters::<E, C>(circuit)?; 
    let min_d = circuit_parameters.n * 4 + 2*NUM_BLINDINGS;

    let srs = generate_srs(alpha, x, min_d)?;

    let parameters = generate_parameters_on_srs_and_information::<E>(&srs, circuit_parameters)?;

    Ok(parameters)
}

pub fn generate_parameters_on_srs<E, C>(
    circuit: C,
    srs: &SRS<E>,
) -> Result<Parameters<E>, SynthesisError>
    where E: Engine, C: Circuit<E> 
{
    let circuit_parameters = get_circuit_parameters::<E, C>(circuit)?;
    let parameters = generate_parameters_on_srs_and_information(&srs, circuit_parameters)?;

    Ok(parameters)
}

pub fn generate_parameters_on_srs_and_information<E: Engine>(
    srs: &SRS<E>,
    information: CircuitParameters<E>
) -> Result<Parameters<E>, SynthesisError>
{
    assert!(srs.d >= information.n * 4 + 2*NUM_BLINDINGS);
    let min_d = information.n * 4 + 2*NUM_BLINDINGS;

    let trimmed_srs: SRS<E> = SRS {
        d: min_d,
        g_negative_x: srs.g_negative_x[0..min_d+1].to_vec(),
        g_positive_x: srs.g_positive_x[0..min_d+1].to_vec().clone(),

        h_negative_x: srs.h_negative_x[0..min_d+1].to_vec(),
        h_positive_x: srs.h_positive_x[0..min_d+1].to_vec(),

        g_negative_x_alpha: srs.g_negative_x_alpha[0..min_d].to_vec(),
        g_positive_x_alpha: srs.g_positive_x_alpha[0..min_d].to_vec(),

        h_negative_x_alpha: srs.h_negative_x_alpha[0..min_d+1].to_vec(),
        h_positive_x_alpha: srs.h_positive_x_alpha[0..min_d+1].to_vec(),

    };

    let vk = VerifyingKey {
        alpha_x: trimmed_srs.h_positive_x_alpha[1],

        alpha: trimmed_srs.h_positive_x_alpha[0],

        neg_h: {
            let mut tmp = trimmed_srs.h_negative_x[0];
            tmp.negate();

            tmp
        },

        neg_x_n_minus_d: {
            let mut tmp = trimmed_srs.h_negative_x[trimmed_srs.d - information.n];
            tmp.negate();

            tmp
        },

        k_map: information.k_map,
        n: information.n,
        q: information.q
    };

    Ok(Parameters{
        vk: vk,
        srs: trimmed_srs
    })
}

pub fn generate_srs<E: Engine>(
    alpha: E::Fr,
    x: E::Fr,
    d: usize
) -> Result<SRS<E>, SynthesisError> {
    let verbose = verbose_flag();

    let g1 = E::G1Affine::one().into_projective();
    let g2 = E::G2Affine::one().into_projective();

    // Compute G1 window table
    let mut g1_wnaf = Wnaf::new();
    let g1_wnaf = g1_wnaf.base(g1, 4*d);

    // Compute G2 window table
    let mut g2_wnaf = Wnaf::new();
    let g2_wnaf = g2_wnaf.base(g2, 4*d);

    let x_inverse = x.inverse().ok_or(SynthesisError::UnexpectedIdentity)?;

    let worker = Worker::new();

    let mut x_powers_positive = vec![Scalar::<E>(E::Fr::zero()); d];
    let mut x_powers_negative = vec![Scalar::<E>(E::Fr::zero()); d];
    {
        // Compute powers of tau
        if verbose {eprintln!("computing powers of x...")};

        let start = std::time::Instant::now();

        {
            worker.scope(d, |scope, chunk| {
                for (i, x_powers) in x_powers_positive.chunks_mut(chunk).enumerate()
                {
                    scope.spawn(move |_| {
                        let mut current_power = x.pow(&[(i*chunk + 1) as u64]);

                        for p in x_powers {
                            p.0 = current_power;
                            current_power.mul_assign(&x);
                        }
                    });
                }
            });
        }
        {
            worker.scope(d, |scope, chunk| {
                for (i, x_powers) in x_powers_negative.chunks_mut(chunk).enumerate()
                {
                    scope.spawn(move |_| {
                        let mut current_power = x_inverse.pow(&[(i*chunk + 1) as u64]);

                        for p in x_powers {
                            p.0 = current_power;
                            current_power.mul_assign(&x_inverse);
                        }
                    });
                }
            });
        }
        if verbose {eprintln!("powers of x done in {} s", start.elapsed().as_millis() as f64 / 1000.0);};
    }

    // we will later add zero powers to g_x, h_x, h_x_alpha
    let mut g_negative_x = vec![E::G1::one(); d];
    let mut g_positive_x = vec![E::G1::one(); d];

    let mut h_negative_x = vec![E::G2::one(); d];
    let mut h_positive_x = vec![E::G2::one(); d];

    let mut g_negative_x_alpha = vec![E::G1::one(); d];
    let mut g_positive_x_alpha = vec![E::G1::one(); d];

    let mut h_negative_x_alpha = vec![E::G2::one(); d];
    let mut h_positive_x_alpha = vec![E::G2::one(); d];

    fn eval<E: Engine>(
        // wNAF window tables
        g1_wnaf: &Wnaf<usize, &[E::G1], &mut Vec<i64>>,
        g2_wnaf: &Wnaf<usize, &[E::G2], &mut Vec<i64>>,

        powers_of_x: &[Scalar<E>],

        g_x: &mut [E::G1],
        g_x_alpha: &mut [E::G1],
        h_x: &mut [E::G2],
        h_x_alpha: &mut [E::G2],

        // Trapdoors
        alpha: &E::Fr,

        // Worker
        worker: &Worker
    )

    {
        // Sanity check
        assert_eq!(g_x.len(), powers_of_x.len());
        assert_eq!(g_x.len(), g_x_alpha.len());
        assert_eq!(g_x.len(), h_x.len());
        assert_eq!(g_x.len(), h_x_alpha.len());

        // Evaluate polynomials in multiple threads
        worker.scope(g_x.len(), |scope, chunk| {
            for ((((x, g_x),  g_x_alpha), h_x), h_x_alpha) in powers_of_x.chunks(chunk)
                                                               .zip(g_x.chunks_mut(chunk))
                                                               .zip(g_x_alpha.chunks_mut(chunk))
                                                               .zip(h_x.chunks_mut(chunk))
                                                               .zip(h_x_alpha.chunks_mut(chunk))
            {
                let mut g1_wnaf = g1_wnaf.shared();
                let mut g2_wnaf = g2_wnaf.shared();

                scope.spawn(move |_| {
                    for ((((x, g_x),  g_x_alpha), h_x), h_x_alpha) in x.iter()
                                                                       .zip(g_x.iter_mut())
                                                                       .zip(g_x_alpha.iter_mut())
                                                                       .zip(h_x.iter_mut())
                                                                       .zip(h_x_alpha.iter_mut())
                    {
                        let mut x_alpha = x.0;
                        x_alpha.mul_assign(&alpha);

                        *g_x = g1_wnaf.scalar(x.0.into_repr());
                        *h_x = g2_wnaf.scalar(x.0.into_repr());

                        *g_x_alpha = g1_wnaf.scalar(x_alpha.into_repr());
                        *h_x_alpha = g2_wnaf.scalar(x_alpha.into_repr());
                    }

                    // Batch normalize
                    E::G1::batch_normalization(g_x);
                    E::G1::batch_normalization(g_x_alpha);
                    E::G2::batch_normalization(h_x);
                    E::G2::batch_normalization(h_x_alpha);
                });
            };
        });
    }

    let start = std::time::Instant::now();

    // Evaluate for positive powers.
    eval(
        &g1_wnaf,
        &g2_wnaf,
        &x_powers_positive,
        &mut g_positive_x[..],
        &mut g_positive_x_alpha[..],
        &mut h_positive_x[..],
        &mut h_positive_x_alpha[..],
        &alpha,
        &worker
    );

    // Evaluate for negative powers
    eval(
        &g1_wnaf,
        &g2_wnaf,
        &x_powers_negative,
        &mut g_negative_x[..],
        &mut g_negative_x_alpha[..],
        &mut h_negative_x[..],
        &mut h_negative_x_alpha[..],
        &alpha,
        &worker
    );

    if verbose {eprintln!("evaluating points done in {} s", start.elapsed().as_millis() as f64 / 1000.0);};

    let g1 = g1.into_affine();
    let g2 = g2.into_affine();

    let h_alpha = g2.mul(alpha.into_repr()).into_affine();

    let g_negative_x = {
        let mut tmp = vec![g1];
        tmp.extend(g_negative_x.into_iter().map(|e| e.into_affine()));

        tmp
    };
    let g_positive_x = {
        let mut tmp = vec![g1];
        tmp.extend(g_positive_x.into_iter().map(|e| e.into_affine()));

        tmp
    };

    let h_negative_x = {
        let mut tmp = vec![g2];
        tmp.extend(h_negative_x.into_iter().map(|e| e.into_affine()));

        tmp
    };
    let h_positive_x = {
        let mut tmp = vec![g2];
        tmp.extend(h_positive_x.into_iter().map(|e| e.into_affine()));

        tmp
    };

    let g_negative_x_alpha = g_negative_x_alpha.into_iter().map(|e| e.into_affine()).collect();
    let g_positive_x_alpha = g_positive_x_alpha.into_iter().map(|e| e.into_affine()).collect();

    let h_negative_x_alpha = {
        let mut tmp = vec![h_alpha];
        tmp.extend(h_negative_x_alpha.into_iter().map(|e| e.into_affine()));

        tmp
    };
    let h_positive_x_alpha = {
        let mut tmp = vec![h_alpha];
        tmp.extend(h_positive_x_alpha.into_iter().map(|e| e.into_affine()));

        tmp
    };

    Ok(SRS {
            d: d,
            g_negative_x: g_negative_x,
            g_positive_x: g_positive_x,

            h_negative_x: h_negative_x,
            h_positive_x: h_positive_x,

            g_negative_x_alpha: g_negative_x_alpha,
            g_positive_x_alpha: g_positive_x_alpha,

            h_negative_x_alpha: h_negative_x_alpha,
            h_positive_x_alpha: h_positive_x_alpha,
        }
    )
}