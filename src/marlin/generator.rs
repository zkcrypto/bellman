use crate::log::Stopwatch;

use rand::Rng;

use std::sync::Arc;
use std::collections::HashMap;

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
    IndexedSetup,
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

use crate::plonk::polynomials::*;

/// This is our assembly structure that we'll use to synthesize the
/// circuit into to perform indexing
struct KeypairAssembly<E: Engine> {
    num_inputs: usize,
    num_aux: usize,
    num_constraints: usize,
    num_non_zero_in_a: usize,
    num_non_zero_in_b: usize,
    num_non_zero_in_c: usize,
    // these are indexed by variable, and then by index in certain constraint
    a_rows: Vec<LinearCombination<E>>,
    b_rows: Vec<LinearCombination<E>>,
    c_rows: Vec<LinearCombination<E>>,
    deduplication_scratch: HashMap<Variable, E::Fr>,
}

impl<E: Engine> KeypairAssembly<E> {
    fn pad_to_square(&mut self) -> Result<(), SynthesisError> {
        let size = if self.num_inputs + self.num_aux >= self.num_constraints {
            self.num_inputs + self.num_aux
        } else {
            self.num_constraints
        };

        self.pad_square_to_size(size)
    }

    fn pad_square_to_size(&mut self, size: usize) -> Result<(), SynthesisError> {
        for _ in (self.num_inputs + self.num_aux)..size {
            self.alloc(|| "", || {
                Ok(E::Fr::one())
            })?;
        }

        self.a_rows.resize(size, LinearCombination::zero());
        self.b_rows.resize(size, LinearCombination::zero());
        self.c_rows.resize(size, LinearCombination::zero());

        self.num_constraints = size;

        Ok(())
    }

    fn into_indexer_input(self, _worker: &Worker) ->
        Result<(usize, usize, (Vec<Vec<(usize, E::Fr)>>, Vec<Vec<(usize, E::Fr)>> , Vec<Vec<(usize, E::Fr)>>)), SynthesisError> 
    {
        let domain_h_size = self.num_inputs + self.num_aux;
        let domain_h_size = domain_h_size.next_power_of_two();

        let domain_k_size = *[self.num_non_zero_in_a, self.num_non_zero_in_b, self.num_non_zero_in_c].iter().max().expect("must exist");
        let domain_k_size = domain_k_size.next_power_of_two();

        fn into_sparse_matrix<E: Engine>(
            constraints: Vec<LinearCombination<E>>, 
            num_inputs: usize) 
        -> Vec<Vec<(usize, E::Fr)>> {
            let mut result = Vec::with_capacity(constraints.len());
            for row in constraints.into_iter() {
                let mut new = Vec::with_capacity(row.0.len());
                for (var, coeff) in row.0.into_iter() {
                    match var {
                        Variable(Index::Input(i)) => {
                            new.push((i, coeff));
                        },
                        Variable(Index::Aux(i)) => {
                            new.push((i+num_inputs, coeff));
                        }
                    }
                }

                result.push(new);
            }

            result
        }

        let num_inputs = self.num_inputs;

        let a_matrix = into_sparse_matrix(self.a_rows, num_inputs);
        let b_matrix = into_sparse_matrix(self.b_rows, num_inputs);
        let c_matrix = into_sparse_matrix(self.c_rows, num_inputs);

        Ok((
            domain_h_size,
            domain_k_size,
            (a_matrix, b_matrix, c_matrix)
        ))
    }
}

use crate::plonk::domains::Domain;

pub(crate) fn materialize_domain_elements<F: PrimeField>(domain: &Domain<F>, worker: &Worker) -> Vec<F> {
    let mut values = vec![F::zero(); domain.size as usize];
    let generator = domain.generator;

    worker.scope(values.len(), |scope, chunk| {
        for (i, values) in values.chunks_mut(chunk).enumerate()
        {
            scope.spawn(move |_| {
                let mut current_power = generator.pow(&[(i*chunk) as u64]);

                for p in values {
                    *p = current_power;
                    current_power.mul_assign(&generator);
                }
            });
        }
    });

    values
}

pub(crate) fn eval_unnormalized_bivariate_lagrange_poly_over_diaginal<F: PrimeField>(
    vanishing_degree: u64,
    evaluate_on_domain: &Domain<F>, 
    worker: &Worker
) -> Vec<F> {
    let mut values = vec![F::zero(); evaluate_on_domain.size as usize];

    let mut repr = F::Repr::default();
    repr.as_mut()[0] = vanishing_degree;
    let size_as_fe = F::from_repr(repr).expect("must convert domain size into field element");

    // we need to calculate elements like X^{S - 1} where S is a domain size
    // so for omega^0 we have omega ^ 0 = 1
    // for omega^1 we have omega^{S-1}
    // for omega^2 we have (omega^2)^{S-1} = (omega^{S-1}) ^ 2
    // and continue to distribute powers this way
    let generator_in_size_minus_one = evaluate_on_domain.generator.pow(&[vanishing_degree - 1u64]);

    // each element is size * X ^ {size - 1}, so we just distribute powers of `generator_in_size_minus_one`
    worker.scope(values.len(), |scope, chunk| {
        for (i, values) in values.chunks_mut(chunk).enumerate()
        {
            scope.spawn(move |_| {
                let mut current_power = generator_in_size_minus_one.pow(&[(i*chunk) as u64]);
                current_power.mul_assign(&size_as_fe);

                for p in values {
                    *p = current_power;
                    current_power.mul_assign(&generator_in_size_minus_one);
                }
            });
        }
    });

    values
}

pub(crate) fn eval_unnormalized_bivariate_lagrange_poly_over_different_inputs<F: PrimeField>(
    x: F,
    vanishing_poly_size: u64,
    evaluate_on_domain: &Domain<F>, 
    worker: &Worker
) -> Vec<F> {
    let vanishing_at_x = evaluate_vanishing_for_size(&x, vanishing_poly_size);
    let inv_vanishing_at_x = vanishing_at_x.inverse().ok_or(SynthesisError::DivisionByZero).expect("should not vanish on random x");
    let inverses = materialize_domain_elements(evaluate_on_domain, &worker);
    let mut inverses = Polynomial::from_values(inverses).expect("must fit into the domain");
    inverses.map(&worker, |element| {
        let mut tmp = x;
        tmp.sub_assign(&*element);
        tmp.mul_assign(&inv_vanishing_at_x);

        *element = tmp;
    });

    inverses.batch_inversion(&worker).expect("must inverse as there are no zeroes");

    inverses.into_coeffs()
}

pub(crate) fn reindex_from_one_domain_to_another_assuming_natural_ordering<F: PrimeField>(
    domain_0: &Domain<F>,
    domain_1: &Domain<F>,
    index: usize
) -> usize {
    assert!(domain_0.size <= domain_1.size);

    let lde_factor = domain_1.size / domain_0.size;
    // in natural ordering element of index i will go into index i*lde_factor

    let new_index = index * (lde_factor as usize);

    new_index
}

fn reindex_from_one_domain_to_another_assuming_bitreversed_ordering<F: PrimeField>(
    domain_0: &Domain<F>,
    domain_1: &Domain<F>,
    index: usize
) -> usize {
    assert!(domain_0.size <= domain_1.size);

    // in bitreversed ordering element of index i will always be in the beginning and unchanged index

    index
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
        fn sort_vars(v_0: &Variable, v_1: &Variable) -> std::cmp::Ordering {
            match (v_0, v_1) {
                (Variable(Index::Input(v_0_value)), Variable(Index::Input(v_1_value))) => {
                    v_0_value.cmp(v_1_value)
                },
                (Variable(Index::Input(_)), Variable(Index::Aux(_))) => {
                    std::cmp::Ordering::Less
                },
                (Variable(Index::Aux(_)), Variable(Index::Input(_))) => {
                    std::cmp::Ordering::Greater
                },
                (Variable(Index::Aux(v_0_value)), Variable(Index::Aux(v_1_value))) => {
                    v_0_value.cmp(v_1_value)
                }
            }
        }


        fn deduplicate_with_sort<E: Engine>(
            lc: LinearCombination<E>,
            scratch: &mut HashMap<Variable, E::Fr>
        ) -> LinearCombination<E> {
            assert!(scratch.is_empty());

            if lc.as_ref().len() == 0 {
                return lc;
            }

            for (var, coeff) in lc.0.into_iter() {
                if let Some(existing_index) = scratch.get_mut(&var) {
                    existing_index.add_assign(&coeff);
                } else {
                    scratch.insert(var, coeff);
                }
            }

            let mut deduped_vec: Vec<(Variable, E::Fr)> = scratch.drain().filter(|(_var, coeff)| !coeff.is_zero()).collect();
            deduped_vec.sort_by(|(a, _), (b, _)| sort_vars(a, b));

            scratch.clear();

            LinearCombination(deduped_vec)
        }

        let a = deduplicate_with_sort(a(LinearCombination::zero()), &mut self.deduplication_scratch);
        let b = deduplicate_with_sort(b(LinearCombination::zero()), &mut self.deduplication_scratch);
        let c = deduplicate_with_sort(c(LinearCombination::zero()), &mut self.deduplication_scratch);

        // keep track on number of non-zero entries in a/b/c
        let num_non_zero_into_a = a.as_ref().len();
        let num_non_zero_into_b = b.as_ref().len();
        let num_non_zero_into_c = c.as_ref().len();

        let (a, b) = {
            self.num_non_zero_in_a += num_non_zero_into_a;
            self.num_non_zero_in_b += num_non_zero_into_b;

            (a, b)
        };

        // // keep track on A/B densities and swap if necessary

        // let (a, b) = if self.num_non_zero_in_a >= self.num_non_zero_in_b {
        //     // there are more in a than in b
        //     if num_non_zero_into_a >= num_non_zero_into_b {
        //         // swap a/b
        //         self.num_non_zero_in_a += num_non_zero_into_b;
        //         self.num_non_zero_in_b += num_non_zero_into_a;

        //         (b, a)
        //     } else {
        //         // don't swap
        //         self.num_non_zero_in_a += num_non_zero_into_a;
        //         self.num_non_zero_in_b += num_non_zero_into_b;

        //         (a, b)
        //     }
        // } else {
        //     if num_non_zero_into_b >= num_non_zero_into_a {
        //         // swap a/b
        //         self.num_non_zero_in_a += num_non_zero_into_b;
        //         self.num_non_zero_in_b += num_non_zero_into_a;

        //         (b, a)
        //     } else {
        //         // don't swap
        //         self.num_non_zero_in_a += num_non_zero_into_a;
        //         self.num_non_zero_in_b += num_non_zero_into_b;

        //         (a, b)
        //     }
        // };

        self.num_non_zero_in_c += num_non_zero_into_c;

        self.a_rows.push(a);
        self.b_rows.push(b);
        self.c_rows.push(c);

        self.num_constraints += 1;
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
) -> Result<IndexedSetup<E>, SynthesisError>
    where E: Engine, C: Circuit<E>
{
    let mut assembly = KeypairAssembly {
        num_inputs: 0,
        num_aux: 0,
        num_constraints: 0,
        num_non_zero_in_a: 0,
        num_non_zero_in_b: 0,
        num_non_zero_in_c: 0,
        a_rows: vec![],
        b_rows: vec![],
        c_rows: vec![],
        deduplication_scratch: HashMap::with_capacity((E::Fr::NUM_BITS * 2) as usize),
    };

    // Allocate the "one" input variable
    assembly.alloc_input(|| "CS::ONE", || Ok(E::Fr::one()))?;

    // Synthesize the circuit.
    circuit.synthesize(&mut assembly)?;

    // // Input constraints to ensure full density of IC query
    // // x * 0 = 0
    // for i in 0..assembly.num_inputs {
    //     assembly.enforce(|| "",
    //         |lc| lc + Variable(Index::Input(i)),
    //         |lc| lc,
    //         |lc| lc,
    //     );
    // }

    assembly.pad_to_square()?;

    let worker = Worker::new();

    let (domain_h_size, domain_k_size, (a_matrix, b_matrix, c_matrix)) = assembly.into_indexer_input(&worker)?;

    let domain_h = Domain::new_for_size(domain_h_size as u64)?;
    let domain_k = Domain::new_for_size(domain_k_size as u64)?;

    // todo: move materialized domain elements out
    fn interpolate_matrix<F: PrimeField>(
        matrix: Vec<Vec<(usize, F)>>,
        domain_h: &Domain<F>,
        domain_k: &Domain<F>,
        worker: &Worker
    ) -> Result<
        (
            usize,
            [Polynomial<F, Coefficients>; 3],
            [Vec<usize>; 2]
        ), SynthesisError> {
        let mut row_vec = Vec::with_capacity(domain_k.size as usize);
        let mut col_vec = Vec::with_capacity(domain_k.size as usize);
        let mut val_vec = Vec::with_capacity(domain_k.size as usize);

        let mut inverses_for_lagrange_polys = Vec::with_capacity(domain_k.size as usize);

        let domain_h_elements = materialize_domain_elements(domain_h, worker);
        let unnormalized_largrange_values_over_k = eval_unnormalized_bivariate_lagrange_poly_over_diaginal(
            domain_h.size,
            domain_k,
            &worker
        );

        let mut row_indexes = Vec::with_capacity(domain_k.size as usize);
        let mut col_indexes = Vec::with_capacity(domain_k.size as usize);

        for (row_index, row) in matrix.into_iter().enumerate() {
            for (col_index, coeff) in row {
                let row_val = domain_h_elements[row_index];
                row_indexes.push(row_index);
                let col_val = domain_h_elements[col_index];  // TODO: do something with inputs?
                col_indexes.push(col_index);

                row_vec.push(row_val);
                col_vec.push(col_val);
                val_vec.push(coeff);

                // row and column indexes are over H, but we can quickly pull their values from evaluations
                // over K
                let idx_row_into_larger_domain = reindex_from_one_domain_to_another_assuming_natural_ordering(
                    domain_h, 
                    domain_k, 
                    row_index);

                let idx_col_into_larger_domain = reindex_from_one_domain_to_another_assuming_natural_ordering(
                    domain_h, 
                    domain_k, 
                    col_index);

                let mut lagrange_eval_value = unnormalized_largrange_values_over_k[idx_row_into_larger_domain];
                lagrange_eval_value.mul_assign(&unnormalized_largrange_values_over_k[idx_col_into_larger_domain]);
                inverses_for_lagrange_polys.push(lagrange_eval_value);
            }
        }

        let num_non_zero = row_vec.len();

        let mut inverses_for_lagrange = Polynomial::from_values_unpadded(inverses_for_lagrange_polys)?;
        inverses_for_lagrange.batch_inversion(&worker)?;
        
        let mut val_values = Polynomial::from_values_unpadded(val_vec)?;

        val_values.mul_assign(&worker, &inverses_for_lagrange);

        // now pad to the domain size with zeroes
        val_values.pad_to_size(domain_k.size as usize)?;
        // val_values.pad_to_domain()?;

        assert!(val_values.size() == domain_k.size as usize);
        assert!(row_vec.len() <= domain_k.size as usize);
        assert!(col_vec.len() <= domain_k.size as usize);

        row_vec.resize(val_values.size(), F::one());
        col_vec.resize(val_values.size(), F::one());

        let row_values = Polynomial::from_values(row_vec)?;
        let col_values = Polynomial::from_values(col_vec)?;

        let val_poly = val_values.ifft(&worker);
        let row_poly = row_values.ifft(&worker);
        let col_poly = col_values.ifft(&worker);

        // row_indexes.resize(domain_k.size as usize, 0);

        Ok((num_non_zero, [row_poly, col_poly, val_poly], [row_indexes, col_indexes]))
    }

    let (a_num_non_zero, [row_a, col_a, val_a], [row_a_indexes, col_a_indexes]) = interpolate_matrix(a_matrix, &domain_h, &domain_k, &worker)?;
    let (b_num_non_zero, [row_b, col_b, val_b], [row_b_indexes, col_b_indexes]) = interpolate_matrix(b_matrix, &domain_h, &domain_k, &worker)?;
    let (c_num_non_zero, [row_c, col_c, val_c], [row_c_indexes, col_c_indexes]) = interpolate_matrix(c_matrix, &domain_h, &domain_k, &worker)?;

    Ok(IndexedSetup {
        a_num_non_zero,
        b_num_non_zero,
        c_num_non_zero,
        domain_h_size,
        domain_k_size,
        a_matrix_poly: val_a,
        b_matrix_poly: val_b,
        c_matrix_poly: val_c,
        a_row_poly: row_a,
        b_row_poly: row_b,
        c_row_poly: row_c,
        a_col_poly: col_a,
        b_col_poly: col_b,
        c_col_poly: col_c,
        a_row_indexes: row_a_indexes,
        b_row_indexes: row_b_indexes,
        c_row_indexes: row_c_indexes,
        a_col_indexes: col_a_indexes,
        b_col_indexes: col_b_indexes,
        c_col_indexes: col_c_indexes,
    })
}

fn evaluate_bivariate_lagrange_at_point<F: PrimeField>(x: F, y: F, vanishing_domain_size: u64) -> Result<F, SynthesisError> {
    if x == y {
        return evaluate_bivariate_lagrange_at_diagonal_point(x, vanishing_domain_size);
    }
    let x_vanishing = evaluate_vanishing_for_size(&x, vanishing_domain_size);
    let y_vanishing = evaluate_vanishing_for_size(&y, vanishing_domain_size);

    let mut num = x_vanishing;
    num.sub_assign(&y_vanishing);

    let mut den = x;
    den.sub_assign(&y);

    let den = den.inverse().ok_or(SynthesisError::DivisionByZero)?;

    num.mul_assign(&den);

    Ok(num)
} 

fn evaluate_bivariate_lagrange_at_diagonal_point<F: PrimeField>(x: F, vanishing_domain_size: u64) -> Result<F, SynthesisError> {
    let mut repr = F::Repr::default();
    repr.as_mut()[0] = vanishing_domain_size;
    let size_as_fe = F::from_repr(repr).expect("must convert domain size into field element");

    let mut result = x.pow(&[vanishing_domain_size - 1]);
    result.mul_assign(&size_as_fe);

    Ok(result)
} 

fn evaluate_bivariate_lagrange_at_point_for_vanishing_y<F: PrimeField>(x: F, y: F, vanishing_domain_size: u64) -> Result<F, SynthesisError> {
    if x == y {
        return evaluate_bivariate_lagrange_at_diagonal_point(x, vanishing_domain_size);
    }

    let mut x_vanishing = x.pow(&[vanishing_domain_size]);
    x_vanishing.sub_assign(&F::one());

    let mut num = x_vanishing;

    let mut den = x;
    den.sub_assign(&y);

    let den = den.inverse().ok_or(SynthesisError::DivisionByZero)?;

    num.mul_assign(&den);

    Ok(num)
} 

pub(crate) fn evaluate_vanishing_for_size<F: PrimeField>(point: &F, vanishing_domain_size: u64) -> F {
    let mut result = point.pow(&[vanishing_domain_size]);
    result.sub_assign(&F::one());

    result
}

#[derive(Clone)]
pub(crate) struct IndexerTester<E: Engine> {
    pub(crate) a: Option<E::Fr>,
    pub(crate) b: Option<E::Fr>,
}

impl<E: Engine> Circuit<E> for IndexerTester<E> {
    fn synthesize<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS
    ) -> Result<(), SynthesisError>
    {
        let a_var = cs.alloc(|| "a", || {
            if let Some(a_value) = self.a {
                Ok(a_value)
            } else {
                Err(SynthesisError::AssignmentMissing)
            }
        })?;

        cs.enforce(
            || "a is zero",
            |lc| lc + a_var,
            |lc| lc + CS::one(),
            |lc| lc
        );

        let b_var = cs.alloc(|| "b", || {
            if let Some(b_value) = self.b {
                Ok(b_value)
            } else {
                Err(SynthesisError::AssignmentMissing)
            }
        })?;

        cs.enforce(
            || "b is one",
            |lc| lc + b_var,
            |lc| lc + CS::one(),
            |lc| lc + CS::one()
        );

        let c_var = cs.alloc_input(|| "c", || {
            if let Some(a_value) = self.a {
                Ok(a_value)
            } else {
                Err(SynthesisError::AssignmentMissing)
            }
        })?;

        cs.enforce(
            || "a is equal to c",
            |lc| lc + a_var,
            |lc| lc + CS::one(),
            |lc| lc + c_var
        );

        cs.enforce(
            || "large linear combinations (valid)", 
            |lc| lc + a_var + b_var + c_var,
            |lc| lc + CS::one(),
            |lc| lc + a_var + b_var + c_var
        );

        cs.enforce(
            || "large linear combinations (invalid)", 
            |lc| lc + a_var + b_var + c_var,
            |lc| lc + a_var + b_var + c_var,
            |lc| lc
        );

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::tests::XORDemo;
    use crate::plonk::domains::*;
    use crate::worker::Worker;
    use super::*;
    use std::marker::PhantomData;

    fn test_over_engine_and_circuit<E: Engine, C: Circuit<E>>(
        circuit: C
    ) {
        let params = generate_parameters(circuit).unwrap();
        let worker = Worker::new();

        println!("Params domain H size = {}", params.domain_h_size);
        println!("Params domain K size = {}", params.domain_k_size);

        let domain_h = Domain::<E::Fr>::new_for_size(params.domain_h_size as u64).unwrap();
        let domain_k = Domain::<E::Fr>::new_for_size(params.domain_k_size as u64).unwrap();
        let generator_h = domain_h.generator;
        let generator_k = domain_k.generator;

        let mut a_matrix_values = vec![];

        for i in 0..params.domain_h_size {
            let x = generator_h.pow(&[i as u64]);
            let mut row = vec![];
            for j in 0..params.domain_h_size {
                let y = generator_h.pow(&[j as u64]);

                let mut sum = E::Fr::zero();

                // sum
                for k in 0..params.domain_k_size {
                    let k = generator_k.pow(&[k as u64]);
                    let col_value = params.a_col_poly.evaluate_at(&worker, k);
                    let row_value = params.a_row_poly.evaluate_at(&worker, k);

                    let vanishing_at_col_value = evaluate_vanishing_for_size(&col_value, params.domain_h_size as u64);
                    assert!(vanishing_at_col_value.is_zero());

                    let vanishing_at_row_value = evaluate_vanishing_for_size(&row_value, params.domain_h_size as u64);
                    assert!(vanishing_at_row_value.is_zero());

                    let lag_x = evaluate_bivariate_lagrange_at_point_for_vanishing_y(x, row_value, params.domain_h_size as u64).unwrap();
                    let lag_y = evaluate_bivariate_lagrange_at_point_for_vanishing_y(y, col_value, params.domain_h_size as u64).unwrap();
                    let val = params.a_matrix_poly.evaluate_at(&worker, k);

                    let mut result = lag_y;
                    result.mul_assign(&lag_x);
                    result.mul_assign(&val);

                    sum.add_assign(&result);
                }

                row.push(sum);
            }

            a_matrix_values.push(row);
        }

        println!("Indexed A matrix values are {:?}", a_matrix_values);
        println!("A row indexes are {:?}", params.a_row_indexes);
        println!("A column indexes are {:?}", params.a_col_indexes);
    }

    #[test]
    fn test_interpolation_poly_1() {
        use crate::pairing::bn256::{Bn256};

        let c = XORDemo::<Bn256> {
            a: None,
            b: None,
            _marker: PhantomData
        };

        test_over_engine_and_circuit(c);
    }

    #[test]
    fn test_interpolation_poly_2() {
        use crate::pairing::bn256::{Bn256, Fr};

        let c = IndexerTester::<Bn256> {
            a: None,
            b: None,
        };

        test_over_engine_and_circuit(c);
    }
}