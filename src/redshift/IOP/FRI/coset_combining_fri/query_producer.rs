use crate::pairing::ff::PrimeField;
use crate::redshift::polynomials::*;
use crate::redshift::domains::*;
use crate::multicore::*;
use crate::SynthesisError;
use super::fri::*;
use super::*;
use crate::redshift::IOP::oracle::*;
use super::coset_combiner::*;
use crate::redshift::fft::cooley_tukey_ntt::log2_floor;

impl<F: PrimeField, I: Oracle<F>> FriProofPrototype<F, I>
{
    pub fn produce_proof<'a>(
        self,
        natural_first_element_indexes: Vec<usize>,
        upper_layer_oracles: &'a BatchedOracle<F, I>,
        upper_layer_values: Vec<&[F]>,
        params: &FriParams,
        oracle_params: &I::Params,
    ) -> Result<FriProof<F, I>, SynthesisError> {

        let mut commitments = vec![];
        for iop in self.oracles.iter() {
            commitments.push(iop.get_commitment());
        }

        let mut rounds = vec![];
        let initial_domain_size = params.initial_degree_plus_one * params.lde_factor;
        let log_initial_domain_size = log2_floor(initial_domain_size) as usize;
        let collapsing_factor = params.collapsing_factor;
        let coset_size = 1 << collapsing_factor;
        let mut upper_layer_queries = vec![];

        for natural_first_element_index in natural_first_element_indexes.into_iter() {
            
            let coset_indexes = CosetCombiner::get_coset_idx_for_natural_index(
                natural_first_element_index, initial_domain_size, log_initial_domain_size, collapsing_factor);
            let upper_layer_query = upper_layer_oracles.produce_query(coset_indexes, &upper_layer_values, oracle_params);
            upper_layer_queries.push(upper_layer_query);

            let mut queries = vec![];
            let mut domain_size = initial_domain_size >> collapsing_factor;
            let mut log_domain_size = initial_domain_size - collapsing_factor;
            let mut elem_index = (natural_first_element_index << collapsing_factor) % domain_size;

            for (oracle, leaf_values) in self.oracles.iter().zip(&self.intermediate_values) {

                let coset_indexes = CosetCombiner::get_coset_idx_for_natural_index(
                    elem_index, domain_size, log_domain_size, collapsing_factor);
                
                assert_eq!(coset_indexes.len(), coset_size);
                let query = oracle.produce_query(coset_indexes, leaf_values.as_ref(), oracle_params);
                queries.push(query);

                domain_size >>= collapsing_factor;
                log_domain_size -= collapsing_factor;
                elem_index = (elem_index << collapsing_factor) % domain_size;
            }

            rounds.push(queries);
        }

        let proof = FriProof::<F, I> {
            upper_layer_queries,
            queries: rounds,
            commitments,
            final_coefficients: self.final_coefficients,
        };

        Ok(proof)
    }
}