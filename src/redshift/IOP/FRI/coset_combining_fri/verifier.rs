use crate::pairing::ff::PrimeField;
use crate::redshift::polynomials::*;
use crate::redshift::domains::*;
use crate::multicore::*;
use crate::SynthesisError;
use super::*;
use crate::redshift::fft::cooley_tukey_ntt::log2_floor;

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

        let domain = Domain::<F>::new_for_size((proof.initial_degree_plus_one * proof.lde_factor) as u64)?;

        let omega = domain.generator;
        let omega_inv = omega.inverse().ok_or(
            SynthesisError::DivisionByZero
        )?;

        let collapsing_factor = proof.collapsing_factor;
        let coset_size = 1 << collapsing_factor;
        let initial_domain_size = domain.size as usize;
        let log_initial_domain_size = log2_floor(initial_domain_size) as usize;

        // here round means a vector of queries - one for each intermediate oracle 
        // including the first, and excluding the last
        for (round, natural_element_index) in proof.queries.iter().zip(natural_element_indexes.into_iter()) {

            
            for (round, ((root, queries), iop_challenge)) in proof.roots.iter()
                                    .zip(query.chunks_exact(degree)) 
                                    .zip(fri_challenges.iter())
                                    .enumerate()
            {
                let coset_values = <I::Combiner as CosetCombiner<F>>::get_coset_for_natural_index(domain_idx, domain_size);

                if coset_values.len() != <I::Combiner as CosetCombiner<F>>::COSET_SIZE {
                    return Err(SynthesisError::PolynomialDegreeTooLarge);
                }

                for q in queries.iter() {
                    if !coset_values.contains(&q.natural_index()) {
                        println!("Coset values do not contain query index {}", q.natural_index());
                        return Ok(false);
                    }
                }

                if round == 0 {
                    for q in queries.iter() {
                        if q.natural_index() == natural_element_index && q.value() != *expected_value_from_oracle {
                            println!("Expected {}, got {} from query", expected_value_from_oracle, q.value());
                            return Ok(false);
                        }
                    }
                }

                for (c, q) in coset_values.iter().zip(queries.iter()) {
                    let tree_index = <I::Combiner as CosetCombiner<F>>::natural_index_into_tree_index(*c);
                    if q.tree_index() != tree_index {
                        return Err(SynthesisError::PolynomialDegreeTooLarge);
                    }
                    assert!(q.natural_index() == *c, "coset values and produced queries are expected to be sorted!");
                }

                for q in queries.iter() {
                    if !I::verify_query(&q, &root) {
                        println!("Query is not in the root");
                        return Ok(false);
                    }
                }
                
                let f_at_omega = (&queries[0]).value();
                if let Some(value) = expected_value {
                    if !coset_values.contains(&domain_idx) {
                        println!("Coset values {:?} do not containt required index {}", coset_values, domain_idx);
                        return Ok(false);
                    }

                    let q: Vec<_> = queries.iter().filter(|el| el.natural_index() == domain_idx).collect();
                    if q.len() != 1 {
                        println!("Queries containt duplicate opening for required index {}", domain_idx);
                        return Ok(false)
                    }

                    let supplied_value = q[0].value();
                    // check in the next domain
                    if supplied_value != value {
                        println!("Query value {} is not equal to the expected value {} for round {}", supplied_value, value, round);
                        return Ok(false);
                    }
                }

                let f_at_minus_omega = (&queries[1]).value();
                let divisor = omega_inv.pow([coset_values[0] as u64]);

                let mut v_even_coeffs = f_at_omega;
                v_even_coeffs.add_assign(&f_at_minus_omega);

                let mut v_odd_coeffs = f_at_omega;
                v_odd_coeffs.sub_assign(&f_at_minus_omega);
                v_odd_coeffs.mul_assign(&divisor);

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

                // we have jumped in a coset and can keep it ordered using the smaller index out of two
                // domain_idx = coset_values[0];

                let (next_idx, next_size) = Domain::<F>::index_and_size_for_next_domain(domain_idx, domain_size);

                domain_idx = next_idx;
                domain_size = next_size;

                omega.square();
                omega_inv.square();
            }


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

        Ok(true)
    }
}
