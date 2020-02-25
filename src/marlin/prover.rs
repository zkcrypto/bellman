use crate::log::Stopwatch;

use rand::Rng;

use std::sync::Arc;

use futures::Future;

use crate::pairing::{
    Engine,
    CurveProjective,
    CurveAffine
};

use crate::pairing::ff::{
    PrimeField,
    Field
};

use super::{
    IndexedSetup
};

use crate::{
    SynthesisError,
    Circuit,
    ConstraintSystem,
    LinearCombination,
    Variable,
    Index
};

use crate::worker::{
    Worker
};

use crate::plonk::polynomials::*;
use crate::plonk::domains::*;

use super::generator::*;

use crate::kate_commitment::*;

fn eval<E: Engine>(
    lc: LinearCombination<E>,
    input_assignment: &[E::Fr],
    aux_assignment: &[E::Fr]
) -> E::Fr
{
    let mut acc = E::Fr::zero();

    for (index, coeff) in lc.0.into_iter() {
        let mut tmp;

        match index {
            Variable(Index::Input(i)) => {
                tmp = input_assignment[i];
            },
            Variable(Index::Aux(i)) => {
                tmp = aux_assignment[i];
            }
        }

        if coeff == E::Fr::one() {
           acc.add_assign(&tmp);
        } else {
           tmp.mul_assign(&coeff);
           acc.add_assign(&tmp);
        }
    }

    acc
}

// This is a proving assignment with densities precalculated
pub struct PreparedProver<E: Engine>{
    assignment: ProvingAssignment<E>,
}

#[derive(Clone)]
struct ProvingAssignment<E: Engine> {
    // Evaluations of A, B, C polynomials
    a: Vec<E::Fr>,
    b: Vec<E::Fr>,
    c: Vec<E::Fr>,

    // Assignments of variables
    input_assignment: Vec<E::Fr>,
    aux_assignment: Vec<E::Fr>
}

pub fn prepare_prover<E, C>(
    circuit: C,
) -> Result<PreparedProver<E>, SynthesisError>
    where E: Engine, C: Circuit<E> 
{
    let mut prover = ProvingAssignment {
        a: vec![],
        b: vec![],
        c: vec![],
        input_assignment: vec![],
        aux_assignment: vec![]
    };

    prover.alloc_input(|| "CS::ONE", || Ok(E::Fr::one()))?;

    circuit.synthesize(&mut prover)?;

    // for i in 0..prover.input_assignment.len() {
    //     prover.enforce(|| "",
    //         |lc| lc + Variable(Index::Input(i)),
    //         |lc| lc,
    //         |lc| lc,
    //     );
    // }

    let prepared = PreparedProver {
        assignment: prover
    };

    return Ok(prepared)
}


pub struct IndexPrecomputations<E: Engine> {
    // values on 2K size coset for the last check
    pub a_row_over_2k_coset: Polynomial<E::Fr, Values>,
    pub b_row_over_2k_coset: Polynomial<E::Fr, Values>,
    pub c_row_over_2k_coset: Polynomial<E::Fr, Values>,
    pub a_col_over_2k_coset: Polynomial<E::Fr, Values>,
    pub b_col_over_2k_coset: Polynomial<E::Fr, Values>,
    pub c_col_over_2k_coset: Polynomial<E::Fr, Values>,
    pub a_val_over_2k_coset: Polynomial<E::Fr, Values>,
    pub b_val_over_2k_coset: Polynomial<E::Fr, Values>,
    pub c_val_over_2k_coset: Polynomial<E::Fr, Values>,

    // values on K size for sumchecks
    pub a_row_over_k: Polynomial<E::Fr, Values>,
    pub b_row_over_k: Polynomial<E::Fr, Values>,
    pub c_row_over_k: Polynomial<E::Fr, Values>,
    pub a_col_over_k: Polynomial<E::Fr, Values>,
    pub b_col_over_k: Polynomial<E::Fr, Values>,
    pub c_col_over_k: Polynomial<E::Fr, Values>,
    pub a_val_over_k: Polynomial<E::Fr, Values>,
    pub b_val_over_k: Polynomial<E::Fr, Values>,
    pub c_val_over_k: Polynomial<E::Fr, Values>,

    // r(x, x) on H
    pub r_x_x_values_over_h: Polynomial<E::Fr, Values>,
}

impl<E: Engine> IndexPrecomputations<E> {
    pub fn new(params: &IndexedSetup<E>, worker: &Worker) -> Result<Self, SynthesisError> {
        let lde_factor_from_h_to_k = params.domain_k_size / params.domain_h_size;
        assert!(lde_factor_from_h_to_k.is_power_of_two());

        let domain_h = Domain::<E::Fr>::new_for_size(params.domain_h_size as u64)?;

        let r_x_x_values_over_h = eval_unnormalized_bivariate_lagrange_poly_over_diaginal(domain_h.size, &domain_h, &worker);
        let r_x_x_values_over_h = Polynomial::from_values(r_x_x_values_over_h)?;

        let a_row_over_2k_coset: Polynomial<E::Fr, Values> = params.a_row_poly.clone().coset_lde(&worker, 2)?;
        let b_row_over_2k_coset: Polynomial<E::Fr, Values> = params.b_row_poly.clone().coset_lde(&worker, 2)?;
        let c_row_over_2k_coset: Polynomial<E::Fr, Values> = params.c_row_poly.clone().coset_lde(&worker, 2)?;
        let a_col_over_2k_coset: Polynomial<E::Fr, Values> = params.a_col_poly.clone().coset_lde(&worker, 2)?;
        let b_col_over_2k_coset: Polynomial<E::Fr, Values> = params.b_col_poly.clone().coset_lde(&worker, 2)?;
        let c_col_over_2k_coset: Polynomial<E::Fr, Values> = params.c_col_poly.clone().coset_lde(&worker, 2)?;
        let a_val_over_2k_coset: Polynomial<E::Fr, Values> = params.a_matrix_poly.clone().coset_lde(&worker, 2)?;
        let b_val_over_2k_coset: Polynomial<E::Fr, Values> = params.b_matrix_poly.clone().coset_lde(&worker, 2)?;
        let c_val_over_2k_coset: Polynomial<E::Fr, Values> = params.c_matrix_poly.clone().coset_lde(&worker, 2)?;
        let a_row_over_k: Polynomial<E::Fr, Values> = params.a_row_poly.clone().fft(&worker);
        let b_row_over_k: Polynomial<E::Fr, Values> = params.b_row_poly.clone().fft(&worker);
        let c_row_over_k: Polynomial<E::Fr, Values> = params.c_row_poly.clone().fft(&worker);
        let a_col_over_k: Polynomial<E::Fr, Values> = params.a_col_poly.clone().fft(&worker);
        let b_col_over_k: Polynomial<E::Fr, Values> = params.b_col_poly.clone().fft(&worker);
        let c_col_over_k: Polynomial<E::Fr, Values> = params.c_col_poly.clone().fft(&worker);
        let a_val_over_k: Polynomial<E::Fr, Values> = params.a_matrix_poly.clone().fft(&worker);
        let b_val_over_k: Polynomial<E::Fr, Values> = params.b_matrix_poly.clone().fft(&worker);
        let c_val_over_k: Polynomial<E::Fr, Values> = params.c_matrix_poly.clone().fft(&worker);

        let new = IndexPrecomputations::<E> {
            a_row_over_2k_coset,
            b_row_over_2k_coset,
            c_row_over_2k_coset,
            a_col_over_2k_coset,
            b_col_over_2k_coset,
            c_col_over_2k_coset,
            a_val_over_2k_coset,
            b_val_over_2k_coset,
            c_val_over_2k_coset,
            a_row_over_k,
            b_row_over_k,
            c_row_over_k,
            a_col_over_k,
            b_col_over_k,
            c_col_over_k,
            a_val_over_k,
            b_val_over_k,
            c_val_over_k,
            r_x_x_values_over_h,
        };

        Ok(new)

    }
}
pub struct PrecomputedBases<E: Engine> {
    pub crs_values_on_h: Crs::<E, CrsForLagrangeForm>,
    pub crs_values_on_k: Crs::<E, CrsForLagrangeForm>,
    // pub crs_values_on_h_coset: Crs::<E, CrsForLagrangeFormOnCoset>
}

impl<E: Engine> PrecomputedBases<E> {
    pub fn new_42_for_index(params: &IndexedSetup<E>, worker: &Worker) -> Self {
        println!("Making CRS");

        let monomial = Crs::<E, CrsForMonomialForm>::crs_42(params.domain_k_size, &worker);

        println!("Done making power series");

        // TODO: use subslicing here
        let crs_values_on_h = Crs::<E, CrsForLagrangeForm>::from_powers(&monomial, params.domain_h_size, &worker);
        println!("Done making lagrange bases on H");

        let crs_values_on_k = Crs::<E, CrsForLagrangeForm>::from_powers(&monomial, params.domain_k_size, &worker);
        // let crs_values_on_h_coset = Crs::<E, CrsForLagrangeFormOnCoset>::from_powers(&monomial, params.domain_h_size, &worker);

        println!("Done making CRS");

        Self {
            crs_values_on_h,
            crs_values_on_k,
            // crs_values_on_h_coset,
        }
    }
}

impl<E:Engine> PreparedProver<E> {
    pub fn create_proof(
        self,
        params: &IndexedSetup<E>,
        crs: &PrecomputedBases<E>,
        precomputations: &IndexPrecomputations<E>,
    ) -> Result<(), SynthesisError>
    {
        // this prover performs the following:
        // - commit to the witness vector `w` and to the results of application of the A/B/C matrixes
        // to it as `z_a`, `z_b`, `z_c` (we may ommit commitment to `z_c` and just claim it's value)
        // - commit to the quotient (z_a * z_b - z_c)/vanishing_on_H
        // - perform a first sumcheck using random challenge `alpha` and linear combination challenges
        // `eta_a`, `eta_b`, `eta_c`. Those prove that over the domain H (matrix size):
        // sum of the r(alpha, x) * z_m(x) - r_m(alpha, x) * w(x) is equal to zero where M \in {A, B, C}
        // and r_m(alpha, x) = \sum_{k \in H} r(alpha, k) * M(k, x)
        // at this step we claim commit to eta_a * r_a(alpha, x) + eta_b * r_b(alpha, x) + eta_c * r_c(alpha, x)
        // without individual contributions r_a(alpha, x), r_b(alpha, x), r_c(alpha, x)
        // - perform the second sumcheck to prove that \sum_{k \in H} r(alpha, k) * M(k, x) is evaluated correctly
        // in a batched way: define q_2(x) = r(alpha, x) \sum_{m \in M}  * M(x, beta_1)
        // if we avaluate previous batched commitment to eta_a * r_a(alpha, x) + eta_b * r_b(alpha, x) + eta_c * r_c(alpha, x)
        // at the point beta_1 then it must be equal to \sum_{H} q_2(x)
        // - perform a third sumcheck to claim that q_2(x) was evaluated correctly:
        // we later check that q_2(beta_2) = r(alpha, beta_2) * \sum_{m \in M}  * M(beta_2, beta_1)
        // for this purpose we need to prove correctness of M(beta_2, beta_1) relatively to the initial indexing
        // for this we define individual polynomials over domain K f_m = M(x, beta_1, beta_2) = Func(indexing, beta_1, beta_2) such that 
        // after summing out over x we'll get the value M(beta_2, beta_1). To achieve this we perform a sumcheck

        let worker = Worker::new();

        let domain_h = Domain::<E::Fr>::new_for_size(params.domain_h_size as u64)?;
        let domain_k = Domain::<E::Fr>::new_for_size(params.domain_k_size as u64)?;

        let prover = self.assignment;

        println!("Start prover work");
        let stopwatch = Stopwatch::new();

        let a_values_on_h = Polynomial::from_values(prover.a)?;
        let b_values_on_h = Polynomial::from_values(prover.b)?;
        let c_values_on_h = Polynomial::from_values(prover.c)?;

        println!("Committing z_a, z_b, z_c");
        let a_commitment = commit_using_values(&a_values_on_h, &crs.crs_values_on_h, &worker)?;
        let b_commitment = commit_using_values(&b_values_on_h, &crs.crs_values_on_h, &worker)?;
        let c_commitment = commit_using_values(&c_values_on_h, &crs.crs_values_on_h, &worker)?;

        let h_poly_values_on_coset = {
            elog_verbose!("H size is {}", a_values_on_h.size());

            let a_poly = a_values_on_h.clone().ifft(&worker);
            let b_poly = b_values_on_h.clone().ifft(&worker);
            let c_poly = c_values_on_h.clone().ifft(&worker);

            let mut a = a_poly.coset_fft(&worker);
            let b = b_poly.coset_fft(&worker);
            let c = c_poly.coset_fft(&worker);

            a.mul_assign(&worker, &b);
            drop(b);
            a.sub_assign(&worker, &c);
            drop(c);

            let z_in_coset = evaluate_vanishing_for_size(&E::Fr::multiplicative_generator(), domain_h.size);
            let z_in_coset_inv = z_in_coset.inverse().ok_or(SynthesisError::DivisionByZero)?;

            a.scale(&worker, z_in_coset_inv); // divide

            let h = a.icoset_fft(&worker);

            let h_values = h.fft(&worker);

            h_values
        };

        println!("Committing h");
        let h_commitment = commit_using_values(&h_poly_values_on_coset, &crs.crs_values_on_h, &worker)?;

        // TODO: later split this up: use witness poly for proving, but commit to the one contatining
        // zeroes instead of inputs

        let mut witness_values_on_h = Vec::with_capacity(a_values_on_h.size());
        witness_values_on_h.extend(prover.input_assignment);
        witness_values_on_h.extend(prover.aux_assignment);
        witness_values_on_h.resize(a_values_on_h.size(), E::Fr::zero());

        let witness_values_on_h = Polynomial::from_values(witness_values_on_h)?;

        println!("Committing w");
        let witness_commitment = commit_using_values(&witness_values_on_h, &crs.crs_values_on_h, &worker)?;

        // now start the lincheck

        let alpha = E::Fr::from_str("5").unwrap();
        let eta_a = E::Fr::from_str("7").unwrap();
        let eta_b = E::Fr::from_str("11").unwrap();
        let eta_c = E::Fr::from_str("42").unwrap();

        // We have not committed to witness values and values of application of A/B/C matrixes on witness

        // also no masking for now

        let mut repr = <E::Fr as PrimeField>::Repr::default();
        repr.as_mut()[0] = domain_h.size;
        let size_h_as_fe = E::Fr::from_repr(repr).expect("must convert domain size into field element");

        let mut repr = <E::Fr as PrimeField>::Repr::default();
        repr.as_mut()[0] = domain_k.size;
        let size_k_as_fe = E::Fr::from_repr(repr).expect("must convert domain size into field element");

        // By this moment we should have oracles to all the witness polynomials, as well as Af, Bf, Cf

        // first sumcheck is for the polynomial 
        // Q_1(X) = r(alpha, X) * F_1(X) + r_m(alpha, X) * F_2(X)
        // where r_m(alpha, X) = \sum_{k \in K} r(X, k) M (k, Y)
        // F_1(X) is result of applying one of the matrixes (A/B/C) on the vector of witnesses
        // F_2(X) is a witness itself
        // this is reduced for the following sumcheck (neglecting the ZK)
        // \sum_{H} r(alpha, X) ( \sum_{M} eta_M * z_M(X) ) - witness(X) * \sum_{M} ( \eta_M r_M(alpha, X)) )
        // where z_M(X) = (M * witness)(X)

        let r_alpha_x_values = eval_unnormalized_bivariate_lagrange_poly_over_different_inputs(
            alpha, 
            domain_h.size, 
            &domain_h, 
            &worker
        );

        let r_alpha_x_values_over_h = Polynomial::from_values(r_alpha_x_values)?;

        // now do the same for A/B/C matrixes

        // R(X, X)
        // let r_x_x_over_h = eval_unnormalized_bivariate_lagrange_poly_over_diaginal(domain_h.size, &domain_h, &worker);
        // let r_x_x_values_over_h = Polynomial::from_values(r_x_x_over_h)?;

        // now compute r_M(alpha, X) = \sum_{H} r(alpha, X) M(X, Y) (sum is over X \in H)

        let lde_factor_from_h_to_k = domain_k.size / domain_h.size;
        assert!(lde_factor_from_h_to_k.is_power_of_two());

        // let a_matrix_at_k = params.a_matrix_poly.clone().fft(&worker);
        // let b_matrix_at_k = params.b_matrix_poly.clone().fft(&worker);
        // let c_matrix_at_k = params.c_matrix_poly.clone().fft(&worker);

        // let domain_h_elements = materialize_domain_elements(&domain_h, &worker);

        fn construct_r_m_from_matrix<F: PrimeField>(
            matrix_evals_at_k: &Polynomial<F, Values>,
            r_x_x_on_h: &Polynomial<F, Values>,
            r_alpha_x_on_h: &Polynomial<F, Values>,
            row_indexes: &Vec<usize>,
            col_indexes: &Vec<usize>,
            domain_h: &Domain<F>,
            worker: &Worker
        ) -> Result<Polynomial<F, Values>, SynthesisError> {
            let mut result = vec![F::zero(); domain_h.size as usize];

            let to_spawn = worker.get_num_spawned_threads(col_indexes.len());
            let mut subresults = vec![result.clone(); to_spawn];

            // M(X, Y) for X = omega^row_index and Y = omega^col_index is equal to the 
            // R1CS matrix M value at (row_index, col_index)

            // first |H| indexes will have non-trivial contributions from R(X, X) and R(alpha, X)

            worker.scope(col_indexes.len(), |scope, chunk_size| {
                for (chunk_id, ((subres, row_chunk), col_chunk)) in subresults.chunks_mut(1)
                                                    .zip(row_indexes.chunks(chunk_size))
                                                    .zip(col_indexes.chunks(chunk_size))
                                                    .enumerate() {
                    scope.spawn(move |_| {
                        let start = chunk_id * chunk_size;
                        let write_to_subres = &mut subres[0];
                        // first we go over non-degenerate indexes
                        for (i, (&row_index, &col_index)) in row_chunk.iter().zip(col_chunk.iter()).enumerate() {
                            let k_domain_index = start + i;

                            let r_x_x_at_h_row = &r_x_x_on_h.as_ref()[row_index];
                            let r_x_x_at_h_col = &r_x_x_on_h.as_ref()[col_index];
                            let r_alpha_x_at_h = &r_alpha_x_on_h.as_ref()[row_index];

                            let val = &matrix_evals_at_k.as_ref()[k_domain_index];

                            let mut result = *r_x_x_at_h_col;
                            result.mul_assign(val);
                            result.mul_assign(r_x_x_at_h_row);
                            // println!("Matrix element contribution into row {}, column {} = {}", row_index, col_index, result);
                            result.mul_assign(r_alpha_x_at_h);

                            write_to_subres[col_index].add_assign(&result);
                        }
                    });
                }
            });

            let subresults_ref = &subresults;
            worker.scope(result.len(), |scope, chunk_size| {
                for (chunk_id, chunk) in result.chunks_mut(chunk_size).enumerate() {
                    scope.spawn(move |_| {
                        let start = chunk_id * chunk_size;
                        for (j, el) in chunk.iter_mut().enumerate() {
                            let idx = start + j;
                            for s in subresults_ref.iter() {
                                if !s[idx].is_zero() {
                                    el.add_assign(&s[idx]);
                                }
                            }
                        }
                    });
                }
            });

            Polynomial::from_values(result)
        }

        let r_a_alpha_x = construct_r_m_from_matrix(
            &precomputations.a_val_over_k,
            &precomputations.r_x_x_values_over_h,
            &r_alpha_x_values_over_h,
            &params.a_row_indexes,
            &params.a_col_indexes,
            &domain_h,
            &worker
        )?;

        let r_b_alpha_x = construct_r_m_from_matrix(
            &precomputations.b_val_over_k,
            &precomputations.r_x_x_values_over_h,
            &r_alpha_x_values_over_h,
            &params.b_row_indexes,
            &params.b_col_indexes,
            &domain_h,
            &worker
        )?;

        let r_c_alpha_x = construct_r_m_from_matrix(
            &precomputations.c_val_over_k,
            &precomputations.r_x_x_values_over_h,
            &r_alpha_x_values_over_h,
            &params.c_row_indexes,
            &params.c_col_indexes,
            &domain_h,
            &worker
        )?;

        let mut r_m_sum = a_values_on_h.clone();
        r_m_sum.scale(&worker, eta_a);
        r_m_sum.add_assign_scaled(&worker, &b_values_on_h, &eta_b);
        r_m_sum.add_assign_scaled(&worker, &c_values_on_h, &eta_c);

        let mut r_m_alpha_x_sum = r_a_alpha_x.clone();
        r_m_alpha_x_sum.scale(&worker, eta_a);
        r_m_alpha_x_sum.add_assign_scaled(&worker, &r_b_alpha_x, &eta_b);
        r_m_alpha_x_sum.add_assign_scaled(&worker, &r_c_alpha_x, &eta_c);

        // r(alpha, X) * \sum (M*witness)(x) * eta_m

        let mut t_0 = r_m_sum;
        t_0.mul_assign(&worker, &r_alpha_x_values_over_h);

        // \sum r_m(alpha, X) * eta_m * witness(x)

        let mut t_1 = r_m_alpha_x_sum;
        t_1.mul_assign(&worker, &witness_values_on_h);

        // let r_m_sum_sum_over_h = t_0.calculate_sum(&worker)?;
        // let r_m_alpha_x_sum_over_h = t_1.calculate_sum(&worker)?;
        // assert!(r_m_sum_sum_over_h == r_m_alpha_x_sum_over_h);

        let mut q_1_poly_values_over_h = t_0;
        q_1_poly_values_over_h.sub_assign(&worker, &t_1);

        let (q_1_sum_over_h, q_1_grand_sum_poly_values_over_h) = q_1_poly_values_over_h.calculate_grand_sum(&worker)?;

        assert!(q_1_sum_over_h.is_zero());

        println!("Committing Q1 and it's sumcheck poly");

        let q_1_commitment = commit_using_values(&q_1_poly_values_over_h, &crs.crs_values_on_h, &worker)?;
        let q_1_sum_commitment = commit_using_values(&q_1_grand_sum_poly_values_over_h, &crs.crs_values_on_h, &worker)?;

        // Now we've completed the first part of the lincheck by incorporating alpha into M(X, Y)

        // {
        //     let z = E::Fr::from_str("10000").unwrap();

        //     let mut z_omega = z;
        //     z_omega.mul_assign(&domain_h.generator);
    
        //     let grand_sum_at_z = q_1_grand_sum_poly_coeffs.evaluate_at(&worker, z);
        //     let grand_sum_at_z_omega = q_1_grand_sum_poly_coeffs.evaluate_at(&worker, z_omega);
        //     let el_at_z = q_1_poly_coeffs.evaluate_at(&worker, z);
        //     let vanishing_at_z = evaluate_vanishing_for_size(&z, domain_h.size);
        //     let quotient_at_z = q_1_sumcheck_quotient_over_h_coeffs.evaluate_at(&worker, z);
    
        //     let mut lhs = grand_sum_at_z;
        //     lhs.sub_assign(&grand_sum_at_z_omega);
        //     lhs.add_assign(&el_at_z);
    
        //     let mut rhs = vanishing_at_z;
        //     rhs.mul_assign(&quotient_at_z);
    
        //     assert_eq!(lhs, rhs, "q_1 sumcheck must pass");
        // }

        // we would later need to evaluate q_1(z) and q_1_sum(z) and q_1_sum(z*omega)


        let beta_1 = E::Fr::from_str("137").unwrap();

        // claim values of z_a, z_b, z_c and h at beta_1

        let a_at_beta_1 = a_values_on_h.barycentric_evaluate_at(&worker, beta_1)?;
        let b_at_beta_1 = b_values_on_h.barycentric_evaluate_at(&worker, beta_1)?;
        let c_at_beta_1 = c_values_on_h.barycentric_evaluate_at(&worker, beta_1)?;
        let h_at_beta_1 = h_poly_values_on_coset.barycentric_evaluate_at(&worker, beta_1)?;

        let vanishing_at_beta_1 = evaluate_vanishing_for_size(&beta_1, domain_h.size);

        let mut lhs = a_at_beta_1;
        lhs.mul_assign(&b_at_beta_1);
        lhs.sub_assign(&c_at_beta_1);

        let mut rhs = h_at_beta_1;
        rhs.mul_assign(&vanishing_at_beta_1);

        assert!(lhs == rhs, "ab - c == h * z_H");

        // now we need to make q_2 = r(alpha, X) M(X, beta)

        let r_beta_1_x_values = eval_unnormalized_bivariate_lagrange_poly_over_different_inputs(
            beta_1, 
            domain_h.size, 
            &domain_h, 
            &worker
        );

        let r_beta_1_x_values_over_h = Polynomial::from_values(r_beta_1_x_values)?;

        fn materialize_m_x_beta<F: PrimeField>(
            matrix_evals_at_k: &Polynomial<F, Values>,
            r_x_x_on_h: &Polynomial<F, Values>,
            r_beta_x_on_h: &Polynomial<F, Values>,
            row_indexes: &Vec<usize>,
            col_indexes: &Vec<usize>,
            domain_h: &Domain<F>,
            worker: &Worker
        ) -> Result<Polynomial<F, Values>, SynthesisError> {
            let mut result = vec![F::zero(); domain_h.size as usize];

            let to_spawn = worker.get_num_spawned_threads(col_indexes.len());
            let mut subresults = vec![result.clone(); to_spawn];

            // M(X, Y) for X = omega^row_index and Y = omega^col_index is equal to the 
            // R1CS matrix M value at (row_index, col_index)

            // first |H| indexes will have non-trivial contributions from R(X, X) and R(alpha, X)

            worker.scope(col_indexes.len(), |scope, chunk_size| {
                for (chunk_id, ((subres, row_chunk), col_chunk)) in subresults.chunks_mut(1)
                                                    .zip(row_indexes.chunks(chunk_size))
                                                    .zip(col_indexes.chunks(chunk_size))
                                                    .enumerate() {
                    scope.spawn(move |_| {
                        let start = chunk_id * chunk_size;
                        let write_to_subres = &mut subres[0];
                        // first we go over non-degenerate indexes
                        for (i, (&row_index, &col_index)) in row_chunk.iter().zip(col_chunk.iter()).enumerate() {
                            let k_domain_index = start + i;

                            let r_x_x_at_h_row = &r_x_x_on_h.as_ref()[row_index];
                            let r_beta_x_at_h_col = &r_beta_x_on_h.as_ref()[col_index];

                            let val = &matrix_evals_at_k.as_ref()[k_domain_index];

                            let mut result = *r_x_x_at_h_row;
                            result.mul_assign(val);
                            // println!("Matrix element contribution into row {}, column {} = {}", row_index, col_index, result);
                            result.mul_assign(r_beta_x_at_h_col);

                            write_to_subres[col_index].add_assign(&result);
                        }
                    });
                }
            });

            let subresults_ref = &subresults;
            worker.scope(result.len(), |scope, chunk_size| {
                for (chunk_id, chunk) in result.chunks_mut(chunk_size).enumerate() {
                    scope.spawn(move |_| {
                        let start = chunk_id * chunk_size;
                        for (j, el) in chunk.iter_mut().enumerate() {
                            let idx = start + j;
                            for s in subresults_ref.iter() {
                                if !s[idx].is_zero() {
                                    el.add_assign(&s[idx]);
                                }
                            }
                        }
                    });
                }
            });

            Polynomial::from_values(result)
        }

        let r_a_x_beta_on_h = materialize_m_x_beta(
            &precomputations.a_val_over_k,
            &precomputations.r_x_x_values_over_h,
            &r_beta_1_x_values_over_h,
            &params.a_row_indexes,
            &params.a_col_indexes,
            &domain_h,
            &worker
        )?;

        let r_b_x_beta_on_h = materialize_m_x_beta(
            &precomputations.b_val_over_k,
            &precomputations.r_x_x_values_over_h,
            &r_beta_1_x_values_over_h,
            &params.a_row_indexes,
            &params.a_col_indexes,
            &domain_h,
            &worker
        )?;

        let r_c_x_beta_on_h = materialize_m_x_beta(
            &precomputations.c_val_over_k,
            &precomputations.r_x_x_values_over_h,
            &r_beta_1_x_values_over_h,
            &params.a_row_indexes,
            &params.a_col_indexes,
            &domain_h,
            &worker
        )?;

        let mut r_m_beta_sum = r_a_x_beta_on_h.clone();
        r_m_beta_sum.scale(&worker, eta_a);
        r_m_beta_sum.add_assign_scaled(&worker, &r_b_x_beta_on_h, &eta_b);
        r_m_beta_sum.add_assign_scaled(&worker, &r_c_x_beta_on_h, &eta_c);

        let mut q_2_poly_values_on_h = r_m_beta_sum;
        q_2_poly_values_on_h.mul_assign(&worker, &r_alpha_x_values_over_h);

        let q_2_sum_value = q_2_poly_values_on_h.calculate_sum(&worker)?;

        let sigma_2 = q_2_sum_value;

        let one_over_h_size = size_h_as_fe.inverse().ok_or(SynthesisError::DivisionByZero)?;

        let mut tmp = sigma_2;
        tmp.mul_assign(&one_over_h_size);

        q_2_poly_values_on_h.sub_constant(&worker, &tmp);

        let (tmp, q_2_grand_sum_over_h) = q_2_poly_values_on_h.calculate_grand_sum(&worker)?;

        assert!(tmp.is_zero());

        println!("Committing Q2 and it's sumcheck poly");
        let q_2_commitment = commit_using_values(&q_2_poly_values_on_h, &crs.crs_values_on_h, &worker)?;
        let q_2_sum_commitment = commit_using_values(&q_2_grand_sum_over_h, &crs.crs_values_on_h, &worker)?;

        // TODO: check if it's better to reduce it to the single poly of degree 6K then to 
        // three independent ones of degree 2k

        let beta_2 = E::Fr::from_str("456").unwrap();    
        
        // now calculate a polynomial f_3 over K using a definition

        fn evaluate_bivariate_lagrange_over_row_or_col_poly<F: PrimeField>(
            x: F,
            vanishing_poly_size: u64,
            row_or_col_evaluations_on_domain: &Polynomial<F, Values>, 
            evaluate_on_domain: &Domain<F>,
            worker: &Worker
        ) -> Result<Polynomial<F, Values>, SynthesisError> {
            assert!(evaluate_on_domain.size as usize == row_or_col_evaluations_on_domain.size());

            let vanishing_at_x = evaluate_vanishing_for_size(&x, vanishing_poly_size);
            let inv_vanishing_at_x = vanishing_at_x.inverse().ok_or(SynthesisError::DivisionByZero)?;
            let mut inverses = row_or_col_evaluations_on_domain.clone();
            inverses.map(&worker, |element| { // (x - col(k))/van(x)
                let mut tmp = x;
                tmp.sub_assign(&*element);
                tmp.mul_assign(&inv_vanishing_at_x);

                *element = tmp;
            });

            inverses.batch_inversion(&worker).expect("must inverse as there are no zeroes");

            Ok(inverses)
        }

        let a_row_poly = params.a_row_poly.clone();
        let b_row_poly = params.b_row_poly.clone();
        let c_row_poly = params.c_row_poly.clone();

        assert!(a_row_poly.size() == domain_k.size as usize);

        let a_col_poly = params.a_col_poly.clone();
        let b_col_poly = params.b_col_poly.clone();
        let c_col_poly = params.c_col_poly.clone();

        assert!(a_col_poly.size() == domain_k.size as usize);

        let a_row_values_at_k = a_row_poly.fft(&worker);
        let b_row_values_at_k = b_row_poly.fft(&worker);
        let c_row_values_at_k = c_row_poly.fft(&worker);

        let a_col_values_at_k = a_col_poly.fft(&worker);
        let b_col_values_at_k = b_col_poly.fft(&worker);
        let c_col_values_at_k = c_col_poly.fft(&worker);

        let r_beta_1_col_a_values_over_k = evaluate_bivariate_lagrange_over_row_or_col_poly(
            beta_1, 
            domain_h.size, 
            &a_col_values_at_k, 
            &domain_k, 
            &worker
        )?;

        let r_beta_1_col_b_values_over_k = evaluate_bivariate_lagrange_over_row_or_col_poly(
            beta_1, 
            domain_h.size, 
            &b_col_values_at_k, 
            &domain_k, 
            &worker
        )?;

        let r_beta_1_col_c_values_over_k = evaluate_bivariate_lagrange_over_row_or_col_poly(
            beta_1, 
            domain_h.size, 
            &c_col_values_at_k, 
            &domain_k, 
            &worker
        )?;

        let r_beta_2_row_a_values_over_k = evaluate_bivariate_lagrange_over_row_or_col_poly(
            beta_2, 
            domain_h.size, 
            &a_row_values_at_k, 
            &domain_k, 
            &worker
        )?;

        let r_beta_2_row_b_values_over_k = evaluate_bivariate_lagrange_over_row_or_col_poly(
            beta_2, 
            domain_h.size, 
            &b_row_values_at_k, 
            &domain_k, 
            &worker
        )?;

        let r_beta_2_row_c_values_over_k = evaluate_bivariate_lagrange_over_row_or_col_poly(
            beta_2, 
            domain_h.size, 
            &c_row_values_at_k, 
            &domain_k, 
            &worker
        )?;

        // do multiplication over K
        let mut f_3_a_values_over_k_by_eta_a = precomputations.a_val_over_k.clone();
        f_3_a_values_over_k_by_eta_a.scale(&worker, eta_a);
        f_3_a_values_over_k_by_eta_a.mul_assign(&worker, &r_beta_2_row_a_values_over_k);
        f_3_a_values_over_k_by_eta_a.mul_assign(&worker, &r_beta_1_col_a_values_over_k);

        let mut f_3_b_values_over_k_by_eta_b = precomputations.b_val_over_k.clone();
        f_3_b_values_over_k_by_eta_b.scale(&worker, eta_b);
        f_3_b_values_over_k_by_eta_b.mul_assign(&worker, &r_beta_2_row_b_values_over_k);
        f_3_b_values_over_k_by_eta_b.mul_assign(&worker, &r_beta_1_col_b_values_over_k);

        let mut f_3_c_values_over_k_by_eta_c = precomputations.c_val_over_k.clone();
        f_3_c_values_over_k_by_eta_c.scale(&worker, eta_c);
        f_3_c_values_over_k_by_eta_c.mul_assign(&worker, &r_beta_2_row_c_values_over_k);
        f_3_c_values_over_k_by_eta_c.mul_assign(&worker, &r_beta_1_col_c_values_over_k);

        // now we need to prove the following two statements
        // - f_3 sums to sigma_3 over K
        // - f_3 is calculated correctly

        // first is simple, we did it many times

        let q_3_a_by_eta_a_sum_value = f_3_a_values_over_k_by_eta_a.calculate_sum(&worker)?;
        let q_3_b_by_eta_b_sum_value = f_3_b_values_over_k_by_eta_b.calculate_sum(&worker)?;
        let q_3_c_by_eta_c_sum_value = f_3_c_values_over_k_by_eta_c.calculate_sum(&worker)?;

        let q_3_a_by_eta_a_poly_coeffs = f_3_a_values_over_k_by_eta_a.clone().ifft(&worker);
        let q_3_b_by_eta_b_poly_coeffs = f_3_b_values_over_k_by_eta_b.clone().ifft(&worker);
        let q_3_c_by_eta_c_poly_coeffs = f_3_c_values_over_k_by_eta_c.clone().ifft(&worker);

        let sigma_3_a = q_3_a_by_eta_a_sum_value;
        let sigma_3_b = q_3_b_by_eta_b_sum_value;
        let sigma_3_c = q_3_c_by_eta_c_sum_value;

        let one_over_k = size_k_as_fe.inverse().ok_or(SynthesisError::DivisionByZero)?;
        let mut tmp_a = one_over_k;
        tmp_a.mul_assign(&sigma_3_a);

        let mut tmp_b = one_over_k;
        tmp_b.mul_assign(&sigma_3_b);

        let mut tmp_c = one_over_k;
        tmp_c.mul_assign(&sigma_3_c);

        assert!(q_3_a_by_eta_a_poly_coeffs.as_ref()[0] == tmp_a);
        assert!(q_3_b_by_eta_b_poly_coeffs.as_ref()[0] == tmp_b);
        assert!(q_3_c_by_eta_c_poly_coeffs.as_ref()[0] == tmp_c);

        f_3_a_values_over_k_by_eta_a.sub_constant(&worker, &tmp_a);
        f_3_b_values_over_k_by_eta_b.sub_constant(&worker, &tmp_b);
        f_3_c_values_over_k_by_eta_c.sub_constant(&worker, &tmp_c);

        // these are sums of f_3_m(x) - sigma_3_m / |K|
        let (t_a, q_3_a_by_eta_a_grand_sum_over_k) = f_3_a_values_over_k_by_eta_a.calculate_grand_sum(&worker)?;
        let (t_b, q_3_b_by_eta_b_grand_sum_over_k) = f_3_b_values_over_k_by_eta_b.calculate_grand_sum(&worker)?;
        let (t_c, q_3_c_by_eta_c_grand_sum_over_k) = f_3_c_values_over_k_by_eta_c.calculate_grand_sum(&worker)?;

        assert!(t_a.is_zero());
        assert!(t_b.is_zero());
        assert!(t_c.is_zero());

        println!("Committing Q3_A and it's sumcheck poly");
        let q_3_a_by_eta_a_commitment = commit_using_values(&f_3_a_values_over_k_by_eta_a, &crs.crs_values_on_k, &worker)?;
        let q_3_a_by_eta_a_sum_commitment = commit_using_values(&q_3_a_by_eta_a_grand_sum_over_k, &crs.crs_values_on_k, &worker)?;

        println!("Committing Q3_B and it's sumcheck poly");
        let q_3_b_by_eta_b_commitment = commit_using_values(&f_3_b_values_over_k_by_eta_b, &crs.crs_values_on_k, &worker)?;
        let q_3_b_by_eta_b_sum_commitment = commit_using_values(&q_3_b_by_eta_b_grand_sum_over_k, &crs.crs_values_on_k, &worker)?;

        println!("Committing Q3_C and it's sumcheck poly");
        let q_3_c_by_eta_c_commitment = commit_using_values(&f_3_c_values_over_k_by_eta_c, &crs.crs_values_on_k, &worker)?;
        let q_3_c_by_eta_c_sum_commitment = commit_using_values(&q_3_c_by_eta_c_grand_sum_over_k, &crs.crs_values_on_k, &worker)?;

        // add the sum back to calculate for correspondance with vals

        let lde_factor_for_q_3_check_over_k: usize = 2;

        // this is f_3_a in the coset of size 2K
        let q_3_a_by_eta_a_values_over_2k_coset = q_3_a_by_eta_a_poly_coeffs.clone().coset_lde(&worker, lde_factor_for_q_3_check_over_k)?;
        let q_3_b_by_eta_b_values_over_2k_coset = q_3_b_by_eta_b_poly_coeffs.clone().coset_lde(&worker, lde_factor_for_q_3_check_over_k)?;
        let q_3_c_by_eta_c_values_over_2k_coset = q_3_c_by_eta_c_poly_coeffs.clone().coset_lde(&worker, lde_factor_for_q_3_check_over_k)?;

        let rational_check_linearization_challenge = E::Fr::from_str("1337").unwrap();

        // now proof that f_3 is a correct derivative of vals

        let vanishing_at_beta_2 = evaluate_vanishing_for_size(&beta_2, domain_h.size);

        let mut vanishing_on_beta_1_by_vanishing_on_beta_2 = vanishing_at_beta_1;
        vanishing_on_beta_1_by_vanishing_on_beta_2.mul_assign(&vanishing_at_beta_2);

        let lde_factor_vals = (params.domain_k_size as usize) * lde_factor_for_q_3_check_over_k / params.a_matrix_poly.size();
        assert!(lde_factor_vals.is_power_of_two());

        // let a_matrixes_values_over_2k_coset = params.a_matrix_poly.clone().coset_lde(&worker, lde_factor_vals)?;
        // let b_matrixes_values_over_2k_coset = params.b_matrix_poly.clone().coset_lde(&worker, lde_factor_vals)?;
        // let c_matrixes_values_over_2k_coset = params.c_matrix_poly.clone().coset_lde(&worker, lde_factor_vals)?;

        let lde_factor_row_col = (params.domain_k_size as usize) * lde_factor_for_q_3_check_over_k / params.a_row_poly.size();
        assert!(lde_factor_row_col.is_power_of_two());

        // let mut a_row_poly = params.a_row_poly.clone();
        // a_row_poly.as_mut()[0].sub_assign(&beta_2);
        // let mut b_row_poly = params.b_row_poly.clone();
        // b_row_poly.as_mut()[0].sub_assign(&beta_2);
        // let mut c_row_poly = params.c_row_poly.clone();
        // c_row_poly.as_mut()[0].sub_assign(&beta_2);

        // let a_row_minus_beta_2_over_2k_coset = a_row_poly.coset_lde(&worker, lde_factor_row_col)?;
        // let b_row_minus_beta_2_over_2k_coset = b_row_poly.coset_lde(&worker, lde_factor_row_col)?;
        // let c_row_minus_beta_2_over_2k_coset = c_row_poly.coset_lde(&worker, lde_factor_row_col)?;

        // let mut a_col_poly = params.a_col_poly.clone();
        // a_col_poly.as_mut()[0].sub_assign(&beta_1);
        // let mut b_col_poly = params.b_col_poly.clone();
        // b_col_poly.as_mut()[0].sub_assign(&beta_1);
        // let mut c_col_poly = params.c_col_poly.clone();
        // c_col_poly.as_mut()[0].sub_assign(&beta_1);

        // let a_col_minus_beta_1_over_2k_coset = a_col_poly.coset_lde(&worker, lde_factor_row_col)?;
        // let b_col_minus_beta_1_over_2k_coset = b_col_poly.coset_lde(&worker, lde_factor_row_col)?;
        // let c_col_minus_beta_1_over_2k_coset = c_col_poly.coset_lde(&worker, lde_factor_row_col)?;

        let mut a_row_minus_beta_2_over_2k_coset = precomputations.a_row_over_2k_coset.clone();
        a_row_minus_beta_2_over_2k_coset.sub_constant(&worker, &beta_2);

        let mut b_row_minus_beta_2_over_2k_coset = precomputations.b_row_over_2k_coset.clone();
        b_row_minus_beta_2_over_2k_coset.sub_constant(&worker, &beta_2);

        let mut c_row_minus_beta_2_over_2k_coset = precomputations.c_row_over_2k_coset.clone();
        c_row_minus_beta_2_over_2k_coset.sub_constant(&worker, &beta_2);

        let mut a_col_minus_beta_1_over_2k_coset = precomputations.a_col_over_2k_coset.clone();
        a_col_minus_beta_1_over_2k_coset.sub_constant(&worker, &beta_1);

        let mut b_col_minus_beta_1_over_2k_coset = precomputations.b_col_over_2k_coset.clone();
        b_col_minus_beta_1_over_2k_coset.sub_constant(&worker, &beta_1);

        let mut c_col_minus_beta_1_over_2k_coset = precomputations.c_col_over_2k_coset.clone();
        c_col_minus_beta_1_over_2k_coset.sub_constant(&worker, &beta_1);

        // for each of the metrixes A/B/C you need to make sure that
        // van(beta_1) * van(beta_2) * val(x) - (row(x) - beta_2)(col(x) - beta(1))*f_3_m(x) == 0 at K
        // we also aggregate it in a form
        // van(beta_1) * van(beta_2) * (eta_a * val_a(x) + eta_b * val_b(x) + eta_c * val_c(x)) -
        // -  eta_a * (row_a(x) - beta_2)(col_a(x) - beta(1))*f_3_a(x) - eta_b * ...

        // let f_3_values_over_2k_coset = q_3_poly_coeffs.clone().coset_lde(&worker, lde_factor_vals)?;

        let mut linearization_challenge = E::Fr::one();

        let mut val_a_total_coeffs = eta_a;
        val_a_total_coeffs.mul_assign(&vanishing_on_beta_1_by_vanishing_on_beta_2);
        // val_a_total_coeffs.mul_assign(&linearization_challenge);

        linearization_challenge.mul_assign(&rational_check_linearization_challenge);

        let mut val_b_total_coeffs = eta_b;
        val_b_total_coeffs.mul_assign(&vanishing_on_beta_1_by_vanishing_on_beta_2);
        val_b_total_coeffs.mul_assign(&linearization_challenge);

        linearization_challenge.mul_assign(&rational_check_linearization_challenge);

        let mut val_c_total_coeffs = eta_c;
        val_c_total_coeffs.mul_assign(&vanishing_on_beta_1_by_vanishing_on_beta_2);
        val_c_total_coeffs.mul_assign(&linearization_challenge);

        // eta_a * vanishing(beta_1) * vanishing(beta_2) * linearization_challenge prefactor over val_a(k)
        let mut f_3_well_formedness_poly_values_over_2k_coset = precomputations.a_val_over_2k_coset.clone();
        f_3_well_formedness_poly_values_over_2k_coset.scale(&worker, val_a_total_coeffs);
        f_3_well_formedness_poly_values_over_2k_coset.add_assign_scaled(&worker, &precomputations.b_val_over_2k_coset, &val_b_total_coeffs);
        f_3_well_formedness_poly_values_over_2k_coset.add_assign_scaled(&worker, &precomputations.c_val_over_2k_coset, &val_c_total_coeffs);

        let mut linearization_challenge = E::Fr::one();

        // now compute a RHS

        // this contains eta_M
        let mut tmp = q_3_a_by_eta_a_values_over_2k_coset; // into 2*K size
        // tmp.scale(&worker, linearization_challenge);
        tmp.mul_assign(&worker, &a_row_minus_beta_2_over_2k_coset);
        tmp.mul_assign(&worker, &a_col_minus_beta_1_over_2k_coset);

        f_3_well_formedness_poly_values_over_2k_coset.sub_assign(&worker, &tmp);

        drop(tmp);

        linearization_challenge.mul_assign(&rational_check_linearization_challenge);

        let mut tmp = q_3_b_by_eta_b_values_over_2k_coset; // into 2*K size
        tmp.scale(&worker, linearization_challenge);
        tmp.mul_assign(&worker, &b_row_minus_beta_2_over_2k_coset);
        tmp.mul_assign(&worker, &b_col_minus_beta_1_over_2k_coset);

        f_3_well_formedness_poly_values_over_2k_coset.sub_assign(&worker, &tmp);

        drop(tmp);

        linearization_challenge.mul_assign(&rational_check_linearization_challenge);

        let mut tmp = q_3_c_by_eta_c_values_over_2k_coset; // into 2*K size
        tmp.scale(&worker, linearization_challenge);
        tmp.mul_assign(&worker, &c_row_minus_beta_2_over_2k_coset);
        tmp.mul_assign(&worker, &c_col_minus_beta_1_over_2k_coset);

        f_3_well_formedness_poly_values_over_2k_coset.sub_assign(&worker, &tmp);

        drop(tmp);

        // let domain_2k = Domain::new_for_size(domain_k.size * (lde_factor_for_q_3_check_over_k as u64))?;

        fn evaluate_vanishing_polynomial_of_degree_on_domain<F: PrimeField>(
            vanishing_degree: u64,
            coset_factor: &F,
            domain: &Domain<F>,
            worker: &Worker
        ) -> Result<Polynomial<F, Values>, SynthesisError> {
            let domain_generator = domain.generator;

            let coset_factor = coset_factor.pow(&[vanishing_degree]);

            let domain_generator_in_vanishing_power = domain_generator.pow(&[vanishing_degree]);

            let mut minus_one = F::one();
            minus_one.negate();

            let mut result = vec![minus_one; domain.size as usize];

            worker.scope(result.len(), |scope, chunk_size| {
                for (chunk_id, chunk) in result.chunks_mut(chunk_size).enumerate() {
                    scope.spawn(move |_| {
                        let start = chunk_id * chunk_size;
                        let mut pow = domain_generator_in_vanishing_power.pow(&[start as u64]);
                        pow.mul_assign(&coset_factor);
                        for el in chunk.iter_mut() {
                            el.add_assign(&pow);
                            pow.mul_assign(&domain_generator_in_vanishing_power);
                        }
                    });
                }
            });

            Polynomial::from_values(result)
        }

        // let mut vanishing_of_degree_k_on_2k = evaluate_vanishing_polynomial_of_degree_on_domain(
        //     domain_k.size, 
        //     &E::Fr::multiplicative_generator(), 
        //     &domain_2k, 
        //     &worker
        // )?;

        // vanishing_of_degree_k_on_2k.batch_inversion(&worker)?;
        // f_3_well_formedness_poly_values_over_2k_coset.mul_assign(&worker, &vanishing_of_degree_k_on_2k);

        // drop(vanishing_of_degree_k_on_2k);
        
        // We can compute faster like this if domain is of size 2k

        // we divide by the polynomial that is vanishing on k, but not on 2k
        // on half of the element it's equal to the following (inversed):
        let vanishing_in_coset_over_k = evaluate_vanishing_for_size(&E::Fr::multiplicative_generator(), domain_k.size);
        let vanishing_in_coset_over_k = vanishing_in_coset_over_k.inverse().ok_or(SynthesisError::DivisionByZero)?;
        // for other elements x^n - 1 = (generator*omega)^n - 1 = - generator^n - 1 cause omega^2n == 1 on a large domain
        let mut vanishing_in_coset_over_k_shifted = E::Fr::multiplicative_generator().pow(&[domain_k.size]);
        vanishing_in_coset_over_k_shifted.negate();
        vanishing_in_coset_over_k_shifted.sub_assign(&E::Fr::one());
        let vanishing_in_coset_over_k_shifted = vanishing_in_coset_over_k_shifted.inverse().ok_or(SynthesisError::DivisionByZero)?;

        worker.scope(f_3_well_formedness_poly_values_over_2k_coset.size(), |scope, chunk_size| {
            for (chunk_id, chunk) in f_3_well_formedness_poly_values_over_2k_coset.as_mut().chunks_mut(chunk_size).enumerate() {
                scope.spawn(move |_| {
                    let start = chunk_id * chunk_size;
                    for (j, el) in chunk.iter_mut().enumerate() {
                        let idx = start + j;
                        if idx & 1 == 0 {
                            el.mul_assign(&vanishing_in_coset_over_k);
                        } else {
                            el.mul_assign(&vanishing_in_coset_over_k_shifted);
                        }
                    }
                });
            }
        });

        // let beta_3 = E::Fr::from_str("12345678890").unwrap();

        // let f_3_well_formedness_baryc_at_beta_3 = f_3_well_formedness_poly_values_over_2k_coset.barycentric_over_coset_evaluate_at(
        //     &worker,
        //     beta_3,
        //     &E::Fr::multiplicative_generator()
        // )?;

        let (f_3_even_values_on_k, f_3_odd_values_on_k) = f_3_well_formedness_poly_values_over_2k_coset.split_into_even_and_odd_assuming_natural_ordering(
            &worker,
            &E::Fr::multiplicative_generator()
        )?;

        // TODO: commit to the linear combination using some other linearization challenge

        let f_3_even_commitment = commit_using_values(&f_3_even_values_on_k, &crs.crs_values_on_k, &worker)?;
        let f_3_odd_commitment = commit_using_values(&f_3_odd_values_on_k, &crs.crs_values_on_k, &worker)?;

        elog_verbose!("{} seconds for all the commitments", stopwatch.elapsed());

        // println!("Committing matrix evaluation proof poly");
        // let f_3_well_formedness_poly_commitment = commit_using_values_on_coset(&f_3_well_formedness_poly_values_over_2k_coset, &crs_values_on_2k_coset, &worker)?;

        // elog_verbose!("{} seconds for all the commitments", stopwatch.elapsed());



        // let f_3_wellformedness_opening_proof = open_from_values_on_coset(
        //     &f_3_well_formedness_poly_values_over_2k_coset, 
        //     E::Fr::multiplicative_generator(), 
        //     beta_3, 
        //     f_3_well_formedness_baryc_at_beta_3, 
        //     &crs_values_on_2k_coset, 
        //     &worker
        // )?;

        // let valid = is_valid_opening::<E>(
        //     f_3_well_formedness_poly_commitment, 
        //     beta_3,
        //     f_3_well_formedness_baryc_at_beta_3, 
        //     f_3_wellformedness_opening_proof, 
        //     crs_values_on_2k_coset.g2_monomial_bases[1]
        // );

        // let (f_3_even_values_on_k_on_coset, f_3_odd_values_on_k) = f_3_well_formedness_poly_values_over_2k_coset.split_into_even_and_odd_assuming_natural_ordering(
        //     &worker,
        //     &E::Fr::multiplicative_generator()
        // )?;

        let beta_3 = E::Fr::from_str("12345678890").unwrap();

        let mut beta_3_squared = beta_3;
        beta_3_squared.square();

        let coset_offset_inv = E::Fr::multiplicative_generator().inverse().ok_or(SynthesisError::DivisionByZero)?;

        let mut beta_3_squared_by_coset_factor_squared = beta_3_squared;
        beta_3_squared_by_coset_factor_squared.mul_assign(&coset_offset_inv);
        beta_3_squared_by_coset_factor_squared.mul_assign(&coset_offset_inv);

        let f_3_even_eval = f_3_even_values_on_k.barycentric_evaluate_at(&worker, beta_3_squared_by_coset_factor_squared)?;
        let f_3_odd_eval = f_3_odd_values_on_k.barycentric_evaluate_at(&worker, beta_3_squared_by_coset_factor_squared)?;

        // let mut lhs = f_3_odd_eval;
        // lhs.mul_assign(&beta_3);
        // lhs.add_assign(&f_3_even_eval);

        // assert!(lhs == f_3_well_formedness_baryc_at_beta_3);

        // assert!(valid, "f_3 wellformedness");

        // now we need to perform all the openings

        // For domain K: 
        // - val_a_at_z, val_b_at_z, val_c_at_z
        // - row_a_at_z, row_b_at_z, row_c_at_z
        // - col_a_at_z, col_b_at_z, col_c_at_z
        // - q_3_a_by_eta_a_commitment at z,
        // - q_3_a_by_eta_a_sum_commitment at z and at z*omega
        // - q_3_b_by_eta_a_commitment at z,
        // - q_3_b_by_eta_a_sum_commitment at z and at z*omega
        // - q_3_c_by_eta_a_commitment at z,
        // - q_3_c_by_eta_a_sum_commitment at z and at z*omega

        // For domain 2K (and we can move it into two openings on K): 
        // - f_3_well_formedness_poly_at_z

        // for domain H:
        // - z_a_at_z, z_b_at_z, z_c_at_z, h_at_z
        // - q_1_at_z, q_1_sum_at_z, q_1_sum_at_z_omega
        // - q_2_at_z, q_2_sum_at_z, q_2_sum_at_z_omega



        // // -------------------------------------------

        // // sanity checks



        // let q_3_a_by_eta_a_at_z = q_3_a_by_eta_a_poly_coeffs.evaluate_at(&worker, z);
        // let q_3_b_by_eta_b_at_z = q_3_b_by_eta_b_poly_coeffs.evaluate_at(&worker, z);
        // let q_3_c_by_eta_c_at_z = q_3_c_by_eta_c_poly_coeffs.evaluate_at(&worker, z);
        // let val_a_at_z = params.a_matrix_poly.evaluate_at(&worker, z);
        // let val_b_at_z = params.b_matrix_poly.evaluate_at(&worker, z);
        // let val_c_at_z = params.c_matrix_poly.evaluate_at(&worker, z);
        // let row_a_at_z = params.a_row_poly.evaluate_at(&worker, z);
        // let row_b_at_z = params.b_row_poly.evaluate_at(&worker, z);
        // let row_c_at_z = params.c_row_poly.evaluate_at(&worker, z);
        // let col_a_at_z = params.a_col_poly.evaluate_at(&worker, z);
        // let col_b_at_z = params.b_col_poly.evaluate_at(&worker, z);
        // let col_c_at_z = params.c_col_poly.evaluate_at(&worker, z);
        // let vanishing_at_z = evaluate_vanishing_for_size(&z, domain_k.size);

        // // vanishing(beta_1) * vanishing(beta_2) * val_m(z) - (beta_2 - row_m(z))(beta_1 - col_m(z)) q_3_m(z) = wellformedness(z)*vanishing(z)

        // let mut lhs = E::Fr::zero();
        // let mut linearization_challenge = E::Fr::one();

        // let mut tmp = vanishing_on_beta_1_by_vanishing_on_beta_2;
        // tmp.mul_assign(&val_a_at_z);
        // tmp.mul_assign(&eta_a);
        
        // let mut t_row = beta_2;
        // t_row.sub_assign(&row_a_at_z);

        // let mut t_col = beta_1;
        // t_col.sub_assign(&col_a_at_z);

        // t_row.mul_assign(&t_col);
        // t_row.mul_assign(&q_3_a_by_eta_a_at_z);
        // tmp.sub_assign(&t_row);
        // tmp.mul_assign(&linearization_challenge);

        // lhs.add_assign(&tmp);

        // linearization_challenge.mul_assign(&rational_check_linearization_challenge);

        // let mut tmp = vanishing_on_beta_1_by_vanishing_on_beta_2;
        // tmp.mul_assign(&val_b_at_z);
        // tmp.mul_assign(&eta_b);
        
        // let mut t_row = beta_2;
        // t_row.sub_assign(&row_b_at_z);

        // let mut t_col = beta_1;
        // t_col.sub_assign(&col_b_at_z);

        // t_row.mul_assign(&t_col);
        // t_row.mul_assign(&q_3_b_by_eta_b_at_z);
        // tmp.sub_assign(&t_row);
        // tmp.mul_assign(&linearization_challenge);

        // lhs.add_assign(&tmp);

        // linearization_challenge.mul_assign(&rational_check_linearization_challenge);

        // let mut tmp = vanishing_on_beta_1_by_vanishing_on_beta_2;
        // tmp.mul_assign(&val_c_at_z);
        // tmp.mul_assign(&eta_c);
        
        // let mut t_row = beta_2;
        // t_row.sub_assign(&row_c_at_z);

        // let mut t_col = beta_1;
        // t_col.sub_assign(&col_c_at_z);

        // t_row.mul_assign(&t_col);
        // t_row.mul_assign(&q_3_c_by_eta_c_at_z);
        // tmp.sub_assign(&t_row);
        // tmp.mul_assign(&linearization_challenge);

        // lhs.add_assign(&tmp);

        // let mut rhs = vanishing_at_z;
        // rhs.mul_assign(&f_3_well_formedness_poly_at_z);

        // assert_eq!(lhs, rhs);

        // let mut z_by_omega_k = z;
        // z_by_omega_k.mul_assign(&domain_k.generator);

        // let q_3_a_by_eta_a_grand_sum_poly_at_z = q_3_a_grand_sum_poly_coeffs.evaluate_at(&worker, z);
        // let q_3_a_by_eta_a_grand_sum_poly_at_z_omega = q_3_a_grand_sum_poly_coeffs.evaluate_at(&worker, z_by_omega_k);
        // let q_3_a_by_eta_a_values_poly_at_z = q_3_a_by_eta_a_poly_coeffs.evaluate_at(&worker, z);
        // let q_3_a_sumcheck_poly_at_z = E::Fr::zero();

        // // sum(z*omega) = sum(z) + el(z) everywhere on k
        // // el(z) is actually el(z) - sigma_3/Domain_size

        // // sum(z*omega) - sum(z) - (el(z) - sum_over_k(el)) = vanishing(z) * quotient(z)

        // let mut sigma_3_a_over_size_of_k = one_over_k;
        // sigma_3_a_over_size_of_k.mul_assign(&sigma_3_a);

        // let mut lhs = q_3_a_by_eta_a_grand_sum_poly_at_z;
        // lhs.sub_assign(&q_3_a_by_eta_a_grand_sum_poly_at_z_omega);
        // lhs.add_assign(&q_3_a_by_eta_a_values_poly_at_z);
        // lhs.sub_assign(&sigma_3_a_over_size_of_k);

        // let mut rhs = vanishing_at_z;
        // rhs.mul_assign(&q_3_a_sumcheck_poly_at_z);

        // assert_eq!(lhs, rhs);

        Ok(())
    }
}


impl<E: Engine> ConstraintSystem<E> for ProvingAssignment<E> {
    type Root = Self;

    fn alloc<F, A, AR>(
        &mut self,
        _: A,
        f: F
    ) -> Result<Variable, SynthesisError>
        where F: FnOnce() -> Result<E::Fr, SynthesisError>, A: FnOnce() -> AR, AR: Into<String>
    {
        self.aux_assignment.push(f()?);

        Ok(Variable(Index::Aux(self.aux_assignment.len() - 1)))
    }

    fn alloc_input<F, A, AR>(
        &mut self,
        _: A,
        f: F
    ) -> Result<Variable, SynthesisError>
        where F: FnOnce() -> Result<E::Fr, SynthesisError>, A: FnOnce() -> AR, AR: Into<String>
    {
        self.input_assignment.push(f()?);

        Ok(Variable(Index::Input(self.input_assignment.len() - 1)))
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
        let a = a(LinearCombination::zero());
        let b = b(LinearCombination::zero());
        let c = c(LinearCombination::zero());

        self.a.push(eval(
            a,
            &self.input_assignment,
            &self.aux_assignment
        ));
        self.b.push(eval(
            b,
            &self.input_assignment,
            &self.aux_assignment
        ));
        self.c.push(eval(
            c,
            &self.input_assignment,
            &self.aux_assignment
        ));
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

// pub fn create_random_proof<E, C, R, P: ParameterSource<E>>(
//     circuit: C,
//     params: P,
//     rng: &mut R
// ) -> Result<Proof<E>, SynthesisError>
//     where E: Engine, C: Circuit<E>, R: Rng
// {
//     let r = rng.gen();
//     let s = rng.gen();

//     create_proof::<E, C, P>(circuit, params, r, s)
// }

pub fn create_proof<E, C>(
    circuit: C,
    params: &IndexedSetup<E>,
) -> Result<(), SynthesisError>
    where E: Engine, C: Circuit<E>
{
    let worker = Worker::new();
    let bases = PrecomputedBases::new_42_for_index(&params, &worker);
    let precomputations = IndexPrecomputations::new(&params, &worker).expect("must precompute");
    let prover = prepare_prover(circuit)?;

    prover.create_proof(params, &bases, &precomputations)
}

pub fn test_over_engine_and_circuit<E: Engine, C: Circuit<E> + Clone>(
    circuit: C
) {
    let params = generate_parameters(circuit.clone()).unwrap();

    println!("Params domain H size = {}", params.domain_h_size);
    println!("Params domain K size = {}", params.domain_k_size);

    let _ = create_proof(circuit, &params).unwrap();
}

#[cfg(test)]
mod test {
    use crate::tests::XORDemo;
    use crate::plonk::domains::*;
    use crate::worker::Worker;
    use super::*;
    use std::marker::PhantomData;
    use super::super::generator::*;

    #[test]
    fn test_proving_1() {
        use crate::pairing::bn256::{Bn256};

        let c = XORDemo::<Bn256> {
            a: Some(true),
            b: Some(true),
            _marker: PhantomData
        };

        test_over_engine_and_circuit(c);
    }

    #[test]
    fn test_proving_2() {
        use crate::pairing::bn256::{Bn256, Fr};

        let c = IndexerTester::<Bn256> {
            a: None,
            b: None,
        };

        test_over_engine_and_circuit(c);
    }
}