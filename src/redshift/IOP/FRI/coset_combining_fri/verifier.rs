use crate::pairing::ff::PrimeField;
use crate::redshift::polynomials::*;
use crate::redshift::domains::*;
use crate::multicore::*;
use crate::SynthesisError;
use super::*;
use crate::redshift::fft::cooley_tukey_ntt::log2_floor;
use crate::redshift::IOP::oracle::*;
use super::coset_combiner::*;
use crate::redshift::fft::cooley_tukey_ntt::bitreverse;
use std::ops::Range;

//TODO: it is also very important to understand how do values are located inside coset

impl<F: PrimeField, O: Oracle<F>, C: Channel<F, Input = O::Commitment>> FriIop<F, O, C> {
    
    pub fn verify_proof_queries<Func: Fn(Vec<(Label, &F)>) -> Option<F>>(
        proof: &FriProof<F, O>,
        upper_layer_commitments: Vec<(Label, O::Commitment)>,
        natural_element_indexes: Vec<usize>,
        fri_challenges: &[F],
        params: &FriParams,
        oracle_params: &O::Params,
        upper_layer_combiner: Func,
    ) -> Result<bool, SynthesisError> {

        assert!(fri_challenges.len() == proof.commitments.len());
        assert!(proof.queries.len() == params.R);
        assert!(natural_element_indexes.len() == proof.queries.len());

        let mut two = F::one();
        two.double();

        let two_inv = two.inverse().ok_or(
            SynthesisError::DivisionByZero
        )?;

        let domain = Domain::<F>::new_for_size((params.initial_degree_plus_one * params.lde_factor) as u64)?;

        let omega = domain.generator;
        let omega_inv = omega.inverse().ok_or(
            SynthesisError::DivisionByZero
        )?;

        let collapsing_factor = params.collapsing_factor;
        let coset_size = 1 << collapsing_factor;
        let initial_domain_size = domain.size as usize;
        let log_initial_domain_size = log2_floor(initial_domain_size) as usize;

        if natural_element_indexes.len() != params.R || proof.final_coefficients.len() > params.final_degree_plus_one {
            return Ok(false);
        }

        let num_steps = 
            log2_floor(params.initial_degree_plus_one / params.final_degree_plus_one) / params.collapsing_factor as u32;
        
        for ((round, natural_first_element_index), upper_layer_query) in 
            proof.queries.iter().zip(natural_element_indexes.into_iter()).zip(proof.upper_layer_queries.iter()) {
            
            let valid = FriIop::<F, O, C>::verify_single_proof_round::<Func>(
                &upper_layer_query,
                &upper_layer_commitments,
                &upper_layer_combiner,
                round,
                &proof.commitments,
                &proof.final_coefficients,
                natural_first_element_index,
                fri_challenges,
                num_steps as usize,
                initial_domain_size,
                log_initial_domain_size,
                collapsing_factor,
                coset_size,
                &oracle_params,
                &omega,
                &omega_inv,
                &two_inv,
            )?;

            if !valid {
                return Ok(false);
            }
        }

        return Ok(true);
    }

    pub fn verify_single_proof_round<Func: Fn(Vec<(Label, &F)>) -> Option<F>>(
        upper_layer_queries: &Vec<(Label, O::Query)>,
        upper_layer_commitments: &Vec<(Label, O::Commitment)>, 
        upper_layer_combiner: &Func,
        queries: &Vec<O::Query>,
        commitments: &Vec<O::Commitment>,
        final_coefficients: &Vec<F>,
        natural_first_element_index: usize,
        fri_challenges: &[F],
        _num_steps: usize,
        initial_domain_size: usize,
        log_initial_domain_size: usize,
        collapsing_factor: usize,
        coset_size: usize,
        oracle_params: &O::Params,
        omega: &F,
        omega_inv: &F,
        two_inv: &F,
    ) -> Result<bool, SynthesisError>
    {
        let coset_idx_range = CosetCombiner::get_coset_idx_for_natural_index(
                natural_first_element_index, initial_domain_size, log_initial_domain_size, collapsing_factor);
        
        //check query cardinality here!
        if upper_layer_queries.iter().any(|x| x.1.card() != initial_domain_size || x.1.indexes() != coset_idx_range) {
            return Ok(false);
        }
        if !BatchedOracle::<F, O>::verify_query(upper_layer_commitments, upper_layer_queries, oracle_params) {
            return Ok(false);
        }

        let mut values = Vec::with_capacity(coset_size);
        for (i, coset_idx) in coset_idx_range.clone().enumerate() {
            let mut argument : Vec<(Label, &F)> = upper_layer_queries.iter().map(|x| (x.0, &x.1.values()[i])).collect();
            let natural_idx = CosetCombiner::get_natural_idx_for_coset_index(
                coset_idx, initial_domain_size, log_initial_domain_size, collapsing_factor);
            let evaluation_point = omega.pow([natural_idx as u64]);
            argument.push(("evaluation_point", &evaluation_point));
            let combined_value = upper_layer_combiner(argument).ok_or(SynthesisError::AssignmentMissing)?;
            values.push(combined_value);
        }

        let mut domain_size = initial_domain_size;
        let mut log_domain_size = log_initial_domain_size;
        let mut elem_index = (natural_first_element_index << collapsing_factor) % domain_size;
        let mut omega_inv = omega_inv.clone();
        let mut previous_layer_element = FriIop::<F, O, C>::coset_interpolant_value(
            &values[..],
            &fri_challenges[0],
            coset_idx_range,
            collapsing_factor,
            coset_size,
            &mut domain_size,
            &mut log_domain_size,
            &mut elem_index,
            & mut omega_inv,
            two_inv);

        for ((query, commitment), challenge) 
            in queries.into_iter().zip(commitments.iter()).zip(fri_challenges.iter().skip(1)) 
        {
            //check query cardinality here!
            if query.card() != domain_size {
                return Ok(false);
            }

            //we do also need to check that coset_indexes are consistent with query
            let (coset_idx_range, elem_tree_idx) = CosetCombiner::get_coset_idx_for_natural_index_extended(
                elem_index, domain_size, log_domain_size, collapsing_factor);
            
            assert_eq!(coset_idx_range.len(), coset_size);

            if query.indexes() != coset_idx_range {
                return Ok(false);
            }              
            <O as Oracle<F>>::verify_query(commitment, query, &oracle_params);
            
            //round consistency check
            let this_layer_element = FriIop::<F, O, C>::coset_interpolant_value(
                query.values(),
                &challenge,
                coset_idx_range,
                collapsing_factor,
                coset_size,
                &mut domain_size,
                &mut log_domain_size,
                &mut elem_index,
                & mut omega_inv,
                two_inv);
         
            if previous_layer_element != query.values()[elem_tree_idx] {
                return Ok(false);
            }
            previous_layer_element = this_layer_element;
        }

        // finally we need to get expected value from coefficients
        let mut expected_value_from_coefficients = F::zero();
        let mut power = F::one();
        let evaluation_point = omega.pow([elem_index as u64]);

        for c in final_coefficients.iter() {
            let mut tmp = power;
            tmp.mul_assign(c);
            expected_value_from_coefficients.add_assign(&tmp);
            power.mul_assign(&evaluation_point);
        }
        Ok(expected_value_from_coefficients == previous_layer_element)
    }

    pub fn coset_interpolant_value(
        values: &[F],
        challenge: &F,
        coset_idx_range: Range<usize>,
        collapsing_factor: usize,
        coset_size: usize,
        domain_size: &mut usize,
        log_domain_size: &mut usize,
        elem_index: &mut usize,
        omega_inv: &mut F,
        two_inv: &F,
    ) -> F
    {
        let mut challenge = challenge.clone();
        let mut this_level_values = Vec::with_capacity(coset_size/2);
        let mut next_level_values = vec![F::zero(); coset_size / 2];

        let base_omega_idx = bitreverse(coset_idx_range.start, *log_domain_size);

        for wrapping_step in 0..collapsing_factor {
            let inputs = if wrapping_step == 0 {
                                values
                            } else {
                                &this_level_values[..(coset_size >> wrapping_step)]
                            };
            for (pair_idx, (pair, o)) in inputs.chunks(2).zip(next_level_values.iter_mut()).enumerate() 
            {
                
                let idx = bitreverse(base_omega_idx + 2 * pair_idx, *log_domain_size);
                let divisor = omega_inv.pow([idx as u64]);
                let f_at_omega = pair[0];
                let f_at_minus_omega = pair[1];
                let mut v_even_coeffs = f_at_omega;
                v_even_coeffs.add_assign(&f_at_minus_omega);

                let mut v_odd_coeffs = f_at_omega;
                v_odd_coeffs.sub_assign(&f_at_minus_omega);
                v_odd_coeffs.mul_assign(&divisor);

                let mut tmp = v_odd_coeffs;
                tmp.mul_assign(&challenge);
                tmp.add_assign(&v_even_coeffs);
                tmp.mul_assign(&two_inv);

                *o = tmp;
            }

            if wrapping_step != collapsing_factor - 1 {
                this_level_values.clear();
                this_level_values.clone_from(&next_level_values);
                challenge.double();
            }
            
            omega_inv.square();
            *domain_size /= 2;
            *log_domain_size <<= 1;
            *elem_index = (*elem_index << collapsing_factor) % *domain_size;
        }

    next_level_values[0]
    }
}


