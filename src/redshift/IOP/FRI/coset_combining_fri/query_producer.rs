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
    pub fn produce_proof(
        self,
        natural_first_element_indexes: Vec<usize>,
    ) -> Result<FriProof<F, I>, SynthesisError> {

        let domain_size = self.initial_degree_plus_one * self.lde_factor;
        let mut commitments = vec![];

        for iop in &self.oracles {
            commitments.push(iop.get_commitment());
        }

        let mut rounds = vec![];
        let collapsing_factor = self.collapsing_factor;
        let coset_size = 1 << collapsing_factor;

        for natural_first_element_index in natural_first_element_indexes.into_iter() {
            let mut queries = vec![];
            let mut domain_size = domain_size;
            let mut log_domain_size = log2_floor(domain_size) as usize;
            let mut elem_index = natural_first_element_index;

            for (oracle, leaf_values) in self.oracles.into_iter().zip(&self.intermediate_values) {

                let coset_indexes = CosetCombiner::get_coset_idx_for_natural_index(
                    elem_index, domain_size, log_domain_size, collapsing_factor);
                
                assert_eq!(coset_indexes.len(), coset_size);
                let query = oracle.produce_query(coset_indexes, leaf_values.as_ref());
                queries.push(query);

                domain_size >>= collapsing_factor;
                log_domain_size -= collapsing_factor;
                elem_index = (elem_index << collapsing_factor) % domain_size;
            }

            rounds.push(queries);
        }

        let proof = FriProof::<F, I> {
            queries: rounds,
            commitments,
            final_coefficients: self.final_coefficients,
            initial_degree_plus_one: self.initial_degree_plus_one,
            lde_factor: self.lde_factor,
            collapsing_factor: self.collapsing_factor,
        };

        Ok(proof)
    }
}