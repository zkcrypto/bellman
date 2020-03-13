use crate::pairing::ff::PrimeField;
use crate::redshift::polynomials::*;
use crate::redshift::domains::*;
use crate::multicore::*;
use crate::SynthesisError;
use super::*;
use crate::redshift::fft::cooley_tukey_ntt::log2_floor;
use crate::redshift::IOP::oracle::*;
use super::coset_combiner::*;

//TODO: it is also very important to understand how do values are located inside coset

impl<F: PrimeField, O: Oracle<F>, C: Channel<F, Input = O::Commitment>> FriIop<F, O, C> {
    
    pub fn verify_proof_queries(
        proof: &FriProof<F, O>,
        natural_element_indexes: Vec<usize>,
        fri_challenges: &[F],
        params: &FriParams,
    ) -> Result<bool, SynthesisError> {

        assert!(fri_challenges.len() == proof.commitments.len());
        assert!(proof.queries.len() == proof.commitments.len());
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
        let oracle_params = <O as Oracle<F>>::Params::from(coset_size);

        if natural_element_indexes.len() != params.R {
            return Ok(false);
        }

        // here round means a vector of queries - one for each intermediate oracle 
        // including the first, and excluding the last
        for (round, natural_first_element_index) in proof.queries.iter().zip(natural_element_indexes.into_iter()) {
            
            let mut domain_size = initial_domain_size;
            let mut log_domain_size = log_initial_domain_size;
            let mut elem_index = natural_first_element_index;
            let mut previous_layer_element;

            for ((query, commitment), challenge) 
                in round.into_iter().zip(proof.commitments.iter()).zip(fri_challenges.iter()) {

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
                let this_level_values = query.values();
                let mut next_level_values = Vec::with_capacity(wrapping_factor / 2);
                let mut challenge = challenge.clone();
                for (pair_idx, (pair, o)) in inputs.chunks(2).zip(next_level_values[..expected_next_level_values].iter_mut()).enumerate() {
                                    debug_assert!(base_omega_idx & pair_idx == 0);
                                    let omega_idx = base_omega_idx + pair_idx;
                                    let omega_inv = omegas_inv_bitreversed[omega_idx];
                                    let f_at_omega = pair[0];
                                    let f_at_minus_omega = pair[1];
                                    let mut v_even_coeffs = f_at_omega;
                                    v_even_coeffs.add_assign(&f_at_minus_omega);

                                    let mut v_odd_coeffs = f_at_omega;
                                    v_odd_coeffs.sub_assign(&f_at_minus_omega);
                                    v_odd_coeffs.mul_assign(&omega_inv);

                                    let mut tmp = v_odd_coeffs;
                                    tmp.mul_assign(&challenge);
                                    tmp.add_assign(&v_even_coeffs);
                                    tmp.mul_assign(&two_inv);

                                    *o = tmp;
                                }

                for wrapping_step in 0..params.collapsing_factor {
                    let f_at_omega = (&queries[0]).value();
                let f_at_minus_omega = (&queries[1]).value();
                let divisor = omega_inv.pow([coset_values[0] as u64]);

                let mut v_even_coeffs = f_at_omega;
                v_even_coeffs.add_assign(&f_at_minus_omega);

                let mut v_odd_coeffs = f_at_omega;
                v_odd_coeffs.sub_assign(&f_at_minus_omega);
                v_odd_coeffs.mul_assign(&divisor);
                               
                    if wrapping_step != params.collapsing_factor - 1
                                    challenge.double();
                                }
                }
                

                // those can be treated as (doubled) evaluations of polynomials that
                // are themselves made only from even or odd coefficients of original poly 
                // (with reduction of degree by 2) on a domain of the size twice smaller
                // with an extra factor of "omega" in odd coefficients

                // to do assemble FRI step we just need to add them with a random challenge

                let mut tmp = v_odd_coeffs;
                tmp.mul_assign(&iop_challenge);
                tmp.add_assign(&v_even_coeffs);
                tmp.mul_assign(&two_inv);

                expected_value = Some(tmp);

                domain_size >>= collapsing_factor;
                log_domain_size -= collapsing_factor;
                elem_index = (elem_index << collapsing_factor) % domain_size;

                 domain_idx = next_idx;
                domain_size = next_size;

                omega.square();
                omega_inv.square();

                 // finally we need to get expected value from coefficients

            let mut expected_value_from_coefficients = F::zero();
            let mut power = F::one();
            let evaluation_point = omega.pow([domain_idx as u64]);

            for c in proof.final_coefficients.iter() {
                let mut tmp = power;
                tmp.mul_assign(c);

                expected_value_from_coefficients.add_assign(&tmp);
                power.mul_assign(&evaluation_point);
            }
            
            let expected_value = expected_value.expect("is some");

            let valid = expected_value_from_coefficients == expected_value;

            if !valid {
                println!("Value from supplied coefficients {} is not equal to the value from queries {} for natural index {}", expected_value_from_coefficients, expected_value, natural_element_index);
                println!("Final coefficients = {:?}", proof.final_coefficients);
                return Ok(false);
            }

            }
        }
            
        Ok(true)    
    }

    //check consistency of all the oracles and challenges
}
