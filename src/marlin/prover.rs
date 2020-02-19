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

impl<E:Engine> PreparedProver<E> {
    pub fn create_proof(
        self,
        params: &IndexedSetup<E>,
    ) -> Result<(), SynthesisError>
    {
        let prover = self.assignment;
        let worker = Worker::new();

        let stopwatch = Stopwatch::new();

        let a_values_on_h = Polynomial::from_values(prover.a)?;
        let b_values_on_h = Polynomial::from_values(prover.b)?;
        let c_values_on_h = Polynomial::from_values(prover.c)?;

        // TODO: later split this up: use witness poly for proving, but commit to the one contatining
        // zeroes instead of inputs

        let mut witness_values_on_h = Vec::with_capacity(a_values_on_h.size());
        witness_values_on_h.extend(prover.input_assignment);
        witness_values_on_h.extend(prover.aux_assignment);
        witness_values_on_h.resize(a_values_on_h.size(), E::Fr::zero());

        let witness_values_on_h = Polynomial::from_values(witness_values_on_h)?;

        // let (a_poly, b_poly, c_poly, h_poly) = {
        //     let a = Polynomial::from_values(prover.a)?;
        //     let b = Polynomial::from_values(prover.b)?;
        //     let c = Polynomial::from_values(prover.c)?;
        //     elog_verbose!("H size is {}", a.as_ref().len());

        //     let a_poly = a.ifft(&worker);
        //     let b_poly = b.ifft(&worker);
        //     let c_poly = c.ifft(&worker);

        //     let mut a = a_poly.clone().coset_fft(&worker);
        //     let b = b_poly.clone().coset_fft(&worker);
        //     let c = c_poly.clone().coset_fft(&worker);

        //     a.mul_assign(&worker, &b);
        //     drop(b);
        //     a.sub_assign(&worker, &c);
        //     drop(c);

        //     let mut z_in_coset = E::Fr::multiplicative_generator().pow(&[a.size() as u64]);
        //     z_in_coset.sub_assign(&E::Fr::one());

        //     a.scale(&worker, z_in_coset);

        //     let h = a.icoset_fft(&worker);

        //     assert!(h.size() == params.domain_h_size);

        //     (a_poly, b_poly, c_poly, h)
        // };

        elog_verbose!("{} seconds for prover for H evaluation (FFT)", stopwatch.elapsed());

        let domain_h = Domain::<E::Fr>::new_for_size(params.domain_h_size as u64)?;
        let domain_k = Domain::<E::Fr>::new_for_size(params.domain_h_size as u64)?;
        // also no masking for now

        let mut repr = <E::Fr as PrimeField>::Repr::default();
        repr.as_mut()[0] = domain_h.size;
    
        let size_h_as_fe = E::Fr::from_repr(repr).expect("must convert domain size into field element");

        let mut repr = <E::Fr as PrimeField>::Repr::default();
        repr.as_mut()[0] = domain_k.size;
    
        let size_k_as_fe = E::Fr::from_repr(repr).expect("must convert domain size into field element");

        // By this moment we should have oracles to all the witness polynomials, as well as Af, Bf, Cf

        let alpha = E::Fr::from_str("5").unwrap();
        let eta_a = E::Fr::from_str("7").unwrap();
        let eta_b = E::Fr::from_str("11").unwrap();
        let eta_c = E::Fr::from_str("42").unwrap();

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

        // R(alpha, X)
        // let r_alpha_x_poly = r_alpha_x_values_over_h.clone().ifft(&worker);

        // now do the same for A/B/C matrixes

        // R(X, X)
        let r_x_x_over_h = eval_unnormalized_bivariate_lagrange_poly_over_diaginal(domain_h.size, &domain_h, &worker);
        let r_x_x_values_over_h = Polynomial::from_values(r_x_x_over_h)?;

        // now compute r_M(alpha, X) = \sum_{H} r(alpha, X) M(X, Y) (sum is over X \in H)

        let lde_factor_from_h_to_k = domain_k.size / domain_h.size;
        assert!(lde_factor_from_h_to_k.is_power_of_two());

        let a_matrix_at_k = params.a_matrix_poly.clone().fft(&worker);
        let b_matrix_at_k = params.b_matrix_poly.clone().fft(&worker);
        let c_matrix_at_k = params.c_matrix_poly.clone().fft(&worker);

        // let a_row_at_h = params.a_row_poly.clone().fft(&worker);
        // let a_col_at_h = params.a_col_poly.clone().fft(&worker);

        let domain_h_elements = materialize_domain_elements(&domain_h, &worker);

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
            &a_matrix_at_k,
            &r_x_x_values_over_h,
            &r_alpha_x_values_over_h,
            &params.a_row_indexes,
            &params.a_col_indexes,
            &domain_h,
            &worker
        )?;

        let r_b_alpha_x = construct_r_m_from_matrix(
            &b_matrix_at_k,
            &r_x_x_values_over_h,
            &r_alpha_x_values_over_h,
            &params.b_row_indexes,
            &params.b_col_indexes,
            &domain_h,
            &worker
        )?;

        let r_c_alpha_x = construct_r_m_from_matrix(
            &c_matrix_at_k,
            &r_x_x_values_over_h,
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

        let mut t_0 = r_alpha_x_values_over_h;
        t_0.mul_assign(&worker, &r_m_sum);

        // \sum r_m(alpha, X) * eta_m * witness(x)

        let mut t_1 = r_m_alpha_x_sum;
        t_1.mul_assign(&worker, &witness_values_on_h);

        // let r_m_sum_sum_over_h = t_0.calculate_sum(&worker)?;
        // let r_m_alpha_x_sum_over_h = t_1.calculate_sum(&worker)?;

        // assert!(r_m_sum_sum_over_h == r_m_alpha_x_sum_over_h);

        let mut q_1_poly_values_over_h = t_0;
        q_1_poly_values_over_h.sub_assign(&worker, &t_1);

        let (q_1_sum_over_h, q_1_grand_sum_poly_values_over_h) = q_1_poly_values_over_h.calculate_grand_sum(&worker)?;

        let q_1_poly_coeffs = q_1_grand_sum_poly_values_over_h.ifft(&worker);
        let q_1_grand_sum_poly_coeffs = q_1_grand_sum_poly_values_over_h.ifft(&worker);

        assert!(q_1_sum_over_h.is_zero());

        let q_1_grand_sum_poly_values_over_h_coset = q_1_grand_sum_poly_values_over_h.clone().coset_fft(&worker);
        let q_1_poly_values_over_h_coset = q_1_poly_coeffs.clone().coset_fft(&worker);

        let mut q_1_sumcheck_quotient_over_h_coset = vec![E::Fr::zero(); q_1_grand_sum_poly_values_over_h_coset.size()];

        let q_1_sum_ref = q_1_grand_sum_poly_values_over_h_coset.as_ref();
        let q_1_ref = q_1_poly_values_over_h_coset.as_ref();

        let work_size = q_1_sumcheck_quotient_over_h_coset.len() - 1;

        worker.scope(work_size, |scope, chunk_size| {
            for (chunk_id, q) in q_1_sumcheck_quotient_over_h_coset[0..work_size].chunks_mut(chunk_size).enumerate() {
                scope.spawn(move |_| {
                    // we need to place grand_sum(x) + value(x) - grand_sum(x*omega)
                    let start = chunk_id * chunk_size;
                    for (j, el) in q.iter_mut().enumerate() {
                        let idx = start + j;
                        *el = q_1_sum_ref[idx];
                        el.sub_assign(&q_1_sum_ref[idx+1]);
                        el.add_assign(&q_1_ref[idx]);
                    }
                });
            }
        });

        // do the last element
        let idx = q_1_sumcheck_quotient_over_h_coset.len() - 1;
        q_1_sumcheck_quotient_over_h_coset[idx] = q_1_sum_ref[idx];
        q_1_sumcheck_quotient_over_h_coset[idx].sub_assign(&q_1_sum_ref[0]);
        q_1_sumcheck_quotient_over_h_coset[idx].add_assign(&q_1_ref[idx]);

        drop(q_1_sum_ref);
        drop(q_1_ref);

        let mut q_1_sumcheck_quotient_over_h_coset = Polynomial::from_values(q_1_sumcheck_quotient_over_h_coset)?;
        let vanishing_on_h_over_the_coset = evaluate_vanishing_for_size(&E::Fr::multiplicative_generator(), q_1_sumcheck_quotient_over_h_coset.size() as u64);
        let vanishing_on_h_over_the_coset_inv = vanishing_on_h_over_the_coset.inverse().ok_or(SynthesisError::DivisionByZero)?;
        q_1_sumcheck_quotient_over_h_coset.scale(&worker, vanishing_on_h_over_the_coset_inv);

        let q_1_sumcheck_quotient_over_h_coeffs = q_1_sumcheck_quotient_over_h_coset.icoset_fft(&worker); // this proves sumcheck for q_1

        // we would later need to evaluate q_1(z) and q_1_sum(z) and q_1_sum(z*omega)

        let beta_1 = E::Fr::from_str("137").unwrap();

        // now we need to make q_2 = r(alpha, X) M(X, beta)

        let r_beta_1_x_values = eval_unnormalized_bivariate_lagrange_poly_over_different_inputs(
            beta_1, 
            domain_h.size, 
            &domain_h, 
            &worker
        );

        let r_alpha_x_values_over_h = Polynomial::from_values(r_alpha_x_values)?;

        fn materialize_m_x_beta<F: PrimeField>(
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
    let prover = prepare_prover(circuit)?;

    prover.create_proof(params)
}

#[cfg(test)]
mod test {
    use crate::tests::XORDemo;
    use crate::plonk::domains::*;
    use crate::worker::Worker;
    use super::*;
    use std::marker::PhantomData;
    use super::super::generator::*;

    fn test_over_engine_and_circuit<E: Engine, C: Circuit<E> + Clone>(
        circuit: C
    ) {
        let params = generate_parameters(circuit.clone()).unwrap();
        let worker = Worker::new();

        println!("Params domain H size = {}", params.domain_h_size);
        println!("Params domain K size = {}", params.domain_k_size);

        let _ = create_proof(circuit, &params).unwrap();

        // let domain_h = Domain::<E::Fr>::new_for_size(params.domain_h_size as u64).unwrap();
        // let domain_k = Domain::<E::Fr>::new_for_size(params.domain_k_size as u64).unwrap();
        // let generator_h = domain_h.generator;
        // let generator_k = domain_k.generator;

        // let mut a_matrix_values = vec![];

        // for i in 0..params.domain_h_size {
        //     let x = generator_h.pow(&[i as u64]);
        //     let mut row = vec![];
        //     for j in 0..params.domain_h_size {
        //         let y = generator_h.pow(&[j as u64]);

        //         let mut sum = E::Fr::zero();

        //         // sum
        //         for k in 0..params.domain_k_size {
        //             let k = generator_k.pow(&[k as u64]);
        //             let col_value = params.a_col_poly.evaluate_at(&worker, k);
        //             let row_value = params.a_row_poly.evaluate_at(&worker, k);

        //             let vanishing_at_col_value = evaluate_vanishing_for_size(&col_value, params.domain_h_size as u64);
        //             assert!(vanishing_at_col_value.is_zero());

        //             let vanishing_at_row_value = evaluate_vanishing_for_size(&row_value, params.domain_h_size as u64);
        //             assert!(vanishing_at_row_value.is_zero());

        //             let lag_x = evaluate_bivariate_lagrange_at_point_for_vanishing_y(x, row_value, params.domain_h_size as u64).unwrap();
        //             let lag_y = evaluate_bivariate_lagrange_at_point_for_vanishing_y(y, col_value, params.domain_h_size as u64).unwrap();
        //             let val = params.a_matrix_poly.evaluate_at(&worker, k);

        //             let mut result = lag_y;
        //             result.mul_assign(&lag_x);
        //             result.mul_assign(&val);

        //             sum.add_assign(&result);
        //         }

        //         row.push(sum);
        //     }

        //     a_matrix_values.push(row);
        // }

        // println!("Indexed A matrix values are {:?}", a_matrix_values);
    }

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