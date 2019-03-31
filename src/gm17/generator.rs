use super::super::verbose_flag;

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
    EvaluationDomain,
    Scalar
};

use crate::worker::{
    Worker
};

// /// Generates a random common reference string for
// /// a circuit.
// pub fn generate_random_parameters<E, C, R>(
//     circuit: C,
//     rng: &mut R
// ) -> Result<Parameters<E>, SynthesisError>
//     where E: Engine, C: Circuit<E>, R: Rng
// {
//     let g1 = rng.gen();
//     let g2 = rng.gen();
//     let alpha = rng.gen();
//     let beta = rng.gen();
//     let gamma = rng.gen();
//     let delta = rng.gen();
//     let tau = rng.gen();

//     generate_parameters::<E, C>(
//         circuit,
//         g1,
//         g2,
//         alpha,
//         beta,
//         gamma,
//         delta,
//         tau
//     )
// }

/// This is our assembly structure that we'll use to synthesize the
/// circuit into a SAP. Square arithmetic problem is different from QAP in a form:
/// it's A*A - C = 0 instead of A*B - C = 0
struct KeypairAssembly<E: Engine> {
    num_inputs: usize,
    num_aux: usize,
    num_constraints: usize,
    num_r1cs_aux: usize,
    num_r1cs_constraints: usize,
    at_inputs: Vec<Vec<(E::Fr, usize)>>,
    ct_inputs: Vec<Vec<(E::Fr, usize)>>,
    at_aux: Vec<Vec<(E::Fr, usize)>>,
    ct_aux: Vec<Vec<(E::Fr, usize)>>
}

impl<E: Engine> ConstraintSystem<E> for KeypairAssembly<E> {
    type Root = Self;

    fn alloc<F, A, AR>(
        &mut self,
        _: A,
        _: F
    ) -> Result<Variable, SynthesisError>
        where F: FnOnce() -> Result<E::Fr, SynthesisError>, A: FnOnce() -> AR, AR: Into<String>
    {
        // There is no assignment, so we don't even invoke the
        // function for obtaining one.

        let index = self.num_aux;
        self.num_aux += 1;

        self.num_r1cs_aux += 1;

        self.at_aux.push(vec![]);
        self.ct_aux.push(vec![]);

        Ok(Variable(Index::Aux(index)))
    }

    fn alloc_input<F, A, AR>(
        &mut self,
        _: A,
        _: F
    ) -> Result<Variable, SynthesisError>
        where F: FnOnce() -> Result<E::Fr, SynthesisError>, A: FnOnce() -> AR, AR: Into<String>
    {
        // There is no assignment, so we don't even invoke the
        // function for obtaining one.

        let index = self.num_inputs;
        self.num_inputs += 1;

        self.at_inputs.push(vec![]);
        self.ct_inputs.push(vec![]);

        Ok(Variable(Index::Input(index)))
    }

    fn enforce<A, AR, LA, LB, LC>(
        &mut self,
        _: A,
        a: LA,
        b: LB,
        c: LC
    )
        where A: FnOnce() -> AR, AR: Into<String>,
              LA: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
              LB: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
              LC: FnOnce(LinearCombination<E>) -> LinearCombination<E>
    {
        use std::ops::{Add, Sub};

        // this is where reduction happens. First we need to re-arrange initial constraints
        // from the form <a,x>*<b,x> = <c,x> to an artificial
        // <a - b,x> * <a - b,x> = y
        // <a + b,x> * <a + b,x> = 4*<c,x> + y

        fn quadruple<E: Engine>(
            coeff: E::Fr
        ) -> E::Fr {
            let mut tmp = coeff;
            tmp.double();
            tmp.double();

            tmp
        }

        fn eval<E: Engine>(
            l: LinearCombination<E>,
            inputs: &mut [Vec<(E::Fr, usize)>],
            aux: &mut [Vec<(E::Fr, usize)>],
            this_constraint: usize
        )
        {
            for (index, coeff) in l.0 {
                match index {
                    Variable(Index::Input(id)) => inputs[id].push((coeff, this_constraint)),
                    Variable(Index::Aux(id)) => aux[id].push((coeff, this_constraint))
                }
            }
        }

        // <a - b,x> * <a - b,x> = x_i
        let i = self.num_constraints;
        let y = self.alloc(
            || format!("SAP reduction y_{}", i),
            || Ok(E::Fr::one())
        ).expect("must allocate SAP reduction variable");
        self.num_r1cs_aux -= 1;

        let lc_a = a(LinearCombination::zero());
        let lc_b = b(LinearCombination::zero());
        let lc_c = c(LinearCombination::zero());

        let lc_a_minus_b = lc_a.clone().sub(&lc_b);

        let mut lc_y: LinearCombination<E> = LinearCombination::zero();
        lc_y = lc_y.add(y);

        eval(lc_a_minus_b, &mut self.at_inputs, &mut self.at_aux, self.num_constraints);
        eval(lc_y, &mut self.ct_inputs, &mut self.ct_aux, self.num_constraints);

        self.num_constraints += 1;

        // <a + b,x> * <a + b,x> = 4*<c,x> + y
        let lc_a_plus_b = lc_a.add(&lc_b);

        let mut lc_c_quadrupled: LinearCombination<E> = LinearCombination::zero();
        for s in &lc_c.0 {
            let tmp = quadruple::<E>(s.1);
            lc_c_quadrupled = lc_c_quadrupled + (tmp, s.0);
        }
        lc_c_quadrupled = lc_c_quadrupled.add(y);

        eval(lc_a_plus_b, &mut self.at_inputs, &mut self.at_aux, self.num_constraints);
        eval(lc_c_quadrupled, &mut self.ct_inputs, &mut self.ct_aux, self.num_constraints);

        self.num_constraints += 1;

        self.num_r1cs_constraints += 1;
    }

    fn push_namespace<NR, N>(&mut self, _: N)
        where NR: Into<String>, N: FnOnce() -> NR
    {
        // Do nothing; we don't care about namespaces in this context.
    }

    fn pop_namespace(&mut self)
    {
        // Do nothing; we don't care about namespaces in this context.
    }

    fn get_root(&mut self) -> &mut Self::Root {
        self
    }
}

/// Create parameters for a circuit, given some toxic waste.
pub fn generate_parameters<E, C>(
    circuit: C,
    g1: E::G1,
    g2: E::G2,
    alpha: E::Fr,
    beta: E::Fr,
    gamma: E::Fr,
    // delta: E::Fr,
    tau: E::Fr
) -> Result<(), SynthesisError>
// Result<Parameters<E>, SynthesisError>
    where E: Engine, C: Circuit<E>
{
    let verbose = verbose_flag();

    let mut assembly = KeypairAssembly {
        num_inputs: 0,
        num_aux: 0,
        num_constraints: 0,
        num_r1cs_aux: 0,
        num_r1cs_constraints: 0,
        at_inputs: vec![],
        ct_inputs: vec![],
        at_aux: vec![],
        ct_aux: vec![]
    };

    // Allocate the "one" input variable
    let input_0 = assembly.alloc_input(|| "", || Ok(E::Fr::one()))?;

    // Synthesize the circuit.
    circuit.synthesize(&mut assembly)?;

    let num_inputs_without_identity = assembly.num_inputs - 1;

    // inputs must be constrained manually in SAP style,
    // so input 0 (identity) is constrained as 1*1=1
    {
        use std::ops::{Add, Sub};

        fn eval_lc<E: Engine>(
            l: LinearCombination<E>,
            inputs: &mut [Vec<(E::Fr, usize)>],
            aux: &mut [Vec<(E::Fr, usize)>],
            this_constraint: usize
        )
        {
            for (index, coeff) in l.0 {
                match index {
                    Variable(Index::Input(id)) => inputs[id].push((coeff, this_constraint)),
                    Variable(Index::Aux(id)) => aux[id].push((coeff, this_constraint))
                }
            }
        }

        let mut lc_input_0_a: LinearCombination<E> = LinearCombination::zero();
        lc_input_0_a = lc_input_0_a.add(input_0.clone());
        eval_lc(lc_input_0_a, &mut assembly.at_inputs, &mut assembly.at_aux, assembly.num_constraints);
        
        assembly.num_constraints += 1;
    }

    let num_constraints_before_inputs_constraining = assembly.num_constraints;
    let num_aux_before_inputs_constraining = assembly.num_aux;

    // Other inputs are constrained as x_i * 1 = x_i where
    // 1 is actually input number 0 (identity)

    for i in 1..assembly.num_inputs {
        assembly.enforce(|| "",
            |lc| lc + Variable(Index::Input(i)),
            |lc| lc + Variable(Index::Input(0)),
            |lc| lc + Variable(Index::Input(i)),
        );
    }

    // check that each input generates 2 constraints
    assert_eq!(num_inputs_without_identity * 2 +
            num_constraints_before_inputs_constraining,
            assembly.num_constraints,
            "each input must produce two extra constraints");
    // and that it creates one extra variable
    assert_eq!(num_inputs_without_identity +
            num_aux_before_inputs_constraining, 
            assembly.num_aux,
            "each input must generate an extra variable");

    assert_eq!(assembly.num_inputs + assembly.num_r1cs_constraints + assembly.num_r1cs_aux,
            assembly.num_inputs + assembly.num_aux,
            "each constraint in principle adds one variable");

    if verbose {eprintln!("Constraint system size is {}", assembly.num_constraints)};
    // Create bases for blind evaluation of polynomials at tau
    let powers_of_tau = vec![Scalar::<E>(E::Fr::zero()); assembly.num_constraints];
    let mut domain = EvaluationDomain::from_coeffs(powers_of_tau)?;

    // Compute G1 window table
    let mut g1_wnaf = Wnaf::new();
    let g1_wnaf = g1_wnaf.base(g1, {
        2*(assembly.num_inputs + assembly.num_r1cs_constraints + assembly.num_r1cs_aux)
        + assembly.num_r1cs_constraints + assembly.num_r1cs_aux
        + 2*(assembly.num_inputs + assembly.num_r1cs_constraints)
    });

    // Compute gamma*G2 window table
    let mut g2_wnaf = Wnaf::new();
    // let gamma_g2 = g2.into_affine().mul(gamma.into_repr());
    let g2_wnaf = g2_wnaf.base(g2, {
        // B query
        assembly.num_inputs + assembly.num_aux
        // alternatively expressed as 
        // assembly.num_inputs + assembly.num_r1cs_constraints + assembly.num_r1cs_aux
    });

    let worker = Worker::new();

    // let z_at_tau = {
    //     // Compute powers of tau
    //     if verbose {eprintln!("computing powers of tau...")};

    //     let start = std::time::Instant::now();

    //     {
    //         let domain = domain.as_mut();
    //         worker.scope(domain.len(), |scope, chunk| {
    //             for (i, subdomain) in domain.chunks_mut(chunk).enumerate()
    //             {
    //                 scope.spawn(move || {
    //                     let mut current_power = tau.pow(&[(i*chunk) as u64]);

    //                     for p in subdomain {
    //                         p.0 = current_power;
    //                         current_power.mul_assign(&tau);
    //                     }
    //                 });
    //             }
    //         });
    //     }
    //     if verbose {eprintln!("powers of tau stage 1 done in {} s", start.elapsed().as_millis() as f64 / 1000.0);};

    //     // z_at_tau = t(x)
    //     let z_at_tau = domain.z(&tau);

    //     z_at_tau
    // };

    let domain_length = domain.as_ref().len();

    if verbose {eprintln!("Domain length is {} ", domain_length)};

    // G1^{gamma^2 * Z(t) * t^i} for 0 <= i < 2^m - 1 for 2^m domains
    let mut gamma2_z_t_g1 = vec![E::G1::zero(); domain.as_ref().len() - 1];
    let mut z_at_tau = E::Fr::zero();

    {
        // Compute powers of tau
        if verbose {eprintln!("computing powers of tau...")};

        let start = std::time::Instant::now();

        {
            let domain = domain.as_mut();
            worker.scope(domain.len(), |scope, chunk| {
                for (i, subdomain) in domain.chunks_mut(chunk).enumerate()
                {
                    scope.spawn(move |_| {
                        let mut current_power = tau.pow(&[(i*chunk) as u64]);

                        for p in subdomain {
                            p.0 = current_power;
                            current_power.mul_assign(&tau);
                        }
                    });
                }
            });
        }
        if verbose {eprintln!("powers of tau stage 1 done in {} s", start.elapsed().as_millis() as f64 / 1000.0);};

        // z_at_tau = t(x)
        z_at_tau = domain.z(&tau);
        
        let mut gamma2_z_t = z_at_tau;
        gamma2_z_t.mul_assign(&gamma);
        gamma2_z_t.mul_assign(&gamma);

        if verbose {eprintln!("computing the `G1^(gamma^2 * Z(t) * t^i)` query with multiple threads...")};

        let start = std::time::Instant::now();

        // Compute the H query with multiple threads
        worker.scope(gamma2_z_t_g1.len(), |scope, chunk| {
            for (gamma2_z_t_g1, p) in gamma2_z_t_g1.chunks_mut(chunk).zip(domain.as_ref().chunks(chunk))
            {
                let mut g1_wnaf = g1_wnaf.shared();
                scope.spawn(move |_| {
                    // Set values of the H query to g1^{(tau^i * t(tau)) / delta}
                    for (gamma2_z_t_g1, p) in gamma2_z_t_g1.iter_mut().zip(p.iter())
                    {
                        // Compute final exponent
                        let mut exp = p.0;
                        exp.mul_assign(&gamma2_z_t);

                        // Exponentiate
                        *gamma2_z_t_g1 = g1_wnaf.scalar(exp.into_repr());
                    }

                    // Batch normalize
                    E::G1::batch_normalization(gamma2_z_t_g1);
                });
            }
        });
        if verbose {eprintln!("computing the `G1^(gamma^2 * Z(t) * t^i)` query done in {} s", start.elapsed().as_millis() as f64 / 1000.0);};
    }

    // G1^{gamma * A_i(t)} for 0 <= i <= num_variables
    let mut a_g1 = vec![E::G1::zero(); assembly.num_inputs + assembly.num_aux];
    // G2^{gamma * A_i(t)} for 0 <= i <= num_variables
    let mut a_g2 = vec![E::G2::zero(); assembly.num_inputs + assembly.num_aux];

    // G1^{gamma^2 * C_i(t) + (alpha + beta) * gamma * A_i(t)}
    // for num_inputs + 1 < i <= num_variables
    let mut c_1_g1 = vec![E::G1::zero(); assembly.num_inputs + assembly.num_aux];
    // G1^{2 * gamma^2 * Z(t) * A_i(t)} for 0 <= i <= num_variables
    let mut c_2_g1 = vec![E::G1::zero(); assembly.num_inputs + assembly.num_aux];

    // G1^{gamma * Z(t)}
    let mut gamma_zt = gamma;
    gamma_zt.mul_assign(&z_at_tau);

    let gamma_z = g1.into_affine().mul(gamma.into_repr());
    // G2^{gamma * Z(t)}
    let gamma_z_g2 = g2.into_affine().mul(gamma.into_repr());

    let mut ab_gamma = alpha;
    ab_gamma.add_assign(&beta);
    ab_gamma.mul_assign(&gamma);
    // G1^{(alpha + beta) * gamma * Z(t)}
    let ab_gamma_z_g1 = g1.into_affine().mul(ab_gamma.into_repr());

    let mut gamma2_z2 = gamma;
    gamma2_z2.mul_assign(&z_at_tau);
    gamma2_z2.square();
    // G1^{gamma^2 * Z(t)^2}
    let gamma2_z2_g1 = g1.into_affine().mul(gamma2_z2.into_repr());

    // G^{gamma^2 * Z(t) * t^i} for 0 <= i < 2^m - 1 for 2^m domains
    let mut gamma2_z_t = vec![E::G1::zero(); domain.as_ref().len() - 1];

    if verbose {eprintln!("using inverse FFT to convert to intepolation coefficients...")};
    
    let start = std::time::Instant::now();

    // Use inverse FFT to convert to intepolation coefficients
    domain.ifft(&worker);
    let powers_of_tau = domain.into_coeffs();
    // domain is now a set of scalars

    if verbose {eprintln!("powers of tau evaluation in radix2 domain in {} s", start.elapsed().as_millis() as f64 / 1000.0)};

    if verbose {eprintln!("evaluating polynomials...")};
    let start = std::time::Instant::now();

    // overall strategy:
    // a_g1, a_g2, c_1_g1, c_2_g1 should be combined together by computing
    // ab = (alpha + beta)
    // g_2 = gamma^2
    // t0 = gamma*A_i(t)
    // t1 = g_2*C_t(t)
    // a_g1 = t0*G1
    // a_g2 = t0*G2
    // c_1_g1 = (t1 + ab*t0)*G1
    // c_2_g1 = (2*gamma*z_at_tau*t0)*G1

    fn eval_stage_1<E: Engine>(
        // wNAF window tables
        g1_wnaf: &Wnaf<usize, &[E::G1], &mut Vec<i64>>,
        g2_wnaf: &Wnaf<usize, &[E::G2], &mut Vec<i64>>,

        // powers of tau coefficients
        powers_of_tau: &[Scalar<E>],

        // SAP polynomials
        at: &[Vec<(E::Fr, usize)>],
        ct: &[Vec<(E::Fr, usize)>],

        // Resulting evaluated SAP polynomials
        a_g1: &mut [E::G1],
        a_g2: &mut [E::G2],
        c_1_g1: &mut [E::G1],
        c_2_g1: &mut [E::G1],

        // Trapdoors
        alpha: &E::Fr,
        beta: &E::Fr,
        gamma: &E::Fr,
        z_at_tau: &E::Fr,

        // Worker
        worker: &Worker
    )

    {
        // Sanity check
        assert_eq!(a_g1.len(), at.len());
        assert_eq!(a_g1.len(), ct.len());
        assert_eq!(a_g1.len(), a_g2.len());
        assert_eq!(a_g1.len(), c_1_g1.len());
        assert_eq!(a_g1.len(), c_2_g1.len());

        // compute once
        let mut ab = *alpha;
        ab.add_assign(&beta);

        let mut gamma2 = *gamma;
        gamma2.square();

        // Evaluate polynomials in multiple threads
        worker.scope(a_g1.len(), |scope, chunk| {
            for (((((a_g1, a_g2), c_1_g1), c_2_g1), at), ct) in a_g1.chunks_mut(chunk)
                                                               .zip(a_g2.chunks_mut(chunk))
                                                               .zip(c_1_g1.chunks_mut(chunk))
                                                               .zip(c_2_g1.chunks_mut(chunk))
                                                               .zip(at.chunks(chunk))
                                                               .zip(ct.chunks(chunk))
            {
                let mut g1_wnaf = g1_wnaf.shared();
                let mut g2_wnaf = g2_wnaf.shared();

                scope.spawn(move |_| {
                    for (((((a_g1, a_g2), c_1_g1), c_2_g1), at), ct) in a_g1.iter_mut()
                                                                       .zip(a_g2.iter_mut())
                                                                       .zip(c_1_g1.iter_mut())
                                                                       .zip(c_2_g1.iter_mut())
                                                                       .zip(at.iter())
                                                                       .zip(ct.iter())
                    {
                        fn eval_at_tau<E: Engine>(
                            powers_of_tau: &[Scalar<E>],
                            p: &[(E::Fr, usize)]
                        ) -> E::Fr
                        {
                            let mut acc = E::Fr::zero();

                            for &(ref coeff, index) in p {
                                let mut n = powers_of_tau[index].0;
                                n.mul_assign(coeff);
                                acc.add_assign(&n);
                            }

                            acc
                        }

                        // Evaluate SAP polynomials at tau
                        // t0 = gamma*A_i(t)
                        let mut t0 = eval_at_tau(powers_of_tau, at);
                        t0.mul_assign(&gamma);
                        // t1 = gamma^2*C_t(t)
                        let mut t1 = eval_at_tau(powers_of_tau, ct);
                        t1.mul_assign(&gamma2);

                        // a_g1 = t0*G1
                        // a_g2 = t0*G2
                        // c_1_g1 = (t1 + ab*t0)*G1
                        // c_2_g1 = (2*gamma*z_at_tau*t0)*G1

                        // Compute a_g1 and a_g2
                        if !t0.is_zero() {
                            *a_g1 = g1_wnaf.scalar(t0.into_repr());
                            *a_g2 = g2_wnaf.scalar(t0.into_repr());
                        }

                        let mut c_1_g1_factor = t0;
                        c_1_g1_factor.mul_assign(&ab);
                        c_1_g1_factor.add_assign(&t1);

                        // (2*gamma*z_at_tau*t0) inplace
                        t0.mul_assign(&z_at_tau);
                        t0.mul_assign(&gamma);
                        t0.double();

                        *c_1_g1 = g1_wnaf.scalar(c_1_g1_factor.into_repr());
                        *c_2_g1 = g1_wnaf.scalar(t0.into_repr());
                    }

                    // Batch normalize
                    E::G1::batch_normalization(a_g1);
                    E::G2::batch_normalization(a_g2);
                    E::G1::batch_normalization(c_1_g1);
                    E::G1::batch_normalization(c_2_g1);
                });
            };
        });
    }

    // Evaluate for inputs.
    eval_stage_1(
        &g1_wnaf,
        &g2_wnaf,
        &powers_of_tau,
        &assembly.at_inputs,
        &assembly.ct_inputs,
        &mut a_g1[0..assembly.num_inputs],
        &mut a_g2[0..assembly.num_inputs],
        &mut c_1_g1[0..assembly.num_inputs],
        &mut c_2_g1[0..assembly.num_inputs],
        &alpha,
        &beta,
        &gamma,
        &z_at_tau,
        &worker
    );

    // Evaluate for inputs.
    eval_stage_1(
        &g1_wnaf,
        &g2_wnaf,
        &powers_of_tau,
        &assembly.at_aux,
        &assembly.ct_aux,
        &mut a_g1[assembly.num_inputs..],
        &mut a_g2[assembly.num_inputs..],
        &mut c_1_g1[assembly.num_inputs..],
        &mut c_2_g1[assembly.num_inputs..],
        &alpha,
        &beta,
        &gamma,
        &z_at_tau,
        &worker
    );

    // for _ in 0..assembly.num_inputs {
    //     c_1_g1.remove(0);
    // }

    if verbose {eprintln!("evaluating polynomials done in {} s", start.elapsed().as_millis() as f64 / 1000.0);};

    // // Don't allow any elements be unconstrained, so that
    // // the L query is always fully dense.
    // for e in l.iter() {
    //     if e.is_zero() {
    //         return Err(SynthesisError::UnconstrainedVariable);
    //     }
    // }

    // let g1 = g1.into_affine();
    // let g2 = g2.into_affine();

    // let vk = VerifyingKey::<E> {
    //     alpha_g1: g1.mul(alpha).into_affine(),
    //     beta_g1: g1.mul(beta).into_affine(),
    //     beta_g2: g2.mul(beta).into_affine(),
    //     gamma_g2: g2.mul(gamma).into_affine(),
    //     delta_g1: g1.mul(delta).into_affine(),
    //     delta_g2: g2.mul(delta).into_affine(),
    //     ic: ic.into_iter().map(|e| e.into_affine()).collect()
    // };

    println!("Has generated {} points", a_g1.len());

    Ok(())

    // Ok(Parameters {
    //     vk: vk,
    //     h: Arc::new(h.into_iter().map(|e| e.into_affine()).collect()),
    //     l: Arc::new(l.into_iter().map(|e| e.into_affine()).collect()),

    //     // Filter points at infinity away from A/B queries
    //     a: Arc::new(a.into_iter().filter(|e| !e.is_zero()).map(|e| e.into_affine()).collect()),
    //     b_g1: Arc::new(b_g1.into_iter().filter(|e| !e.is_zero()).map(|e| e.into_affine()).collect()),
    //     b_g2: Arc::new(b_g2.into_iter().filter(|e| !e.is_zero()).map(|e| e.into_affine()).collect())
    // })
}
