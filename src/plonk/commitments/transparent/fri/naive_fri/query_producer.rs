use crate::pairing::ff::PrimeField;
use crate::plonk::commitments::transparent::iop::*;
use crate::plonk::polynomials::*;
use crate::plonk::domains::*;
use crate::multicore::*;
use crate::SynthesisError;
use crate::plonk::commitments::transparent::iop::*;
use crate::plonk::commitments::transparent::utils::log2_floor;
use super::naive_fri::*;
use super::super::*;

impl<F: PrimeField, I: IOP<F>> FRIProofPrototype<F, I> {
    pub fn produce_proof(
        self,
        iop_values: &Polynomial<F, Values>,
        natural_first_element_indexes: Vec<usize>,
    ) -> Result<FRIProof<F, I>, SynthesisError> {
        let domain_size = self.initial_degree_plus_one * self.lde_factor;

        let mut roots = vec![];
        let l0_commitment = Some(self.l0_commitment);

        for iop in l0_commitment.iter().chain(&self.intermediate_commitments) {
            roots.push(iop.get_root());
        }

        let mut rounds = vec![];

        for natural_first_element_index in natural_first_element_indexes.into_iter() {
            let mut queries = vec![];
            let mut domain_idx = natural_first_element_index;
            let mut domain_size = domain_size;

            for (iop, leaf_values) in l0_commitment.iter().chain(&self.intermediate_commitments)
                                        .zip(Some(iop_values).into_iter().chain(&self.intermediate_values)) {
                
                let coset_values = <I::Combiner as CosetCombiner<F>>::get_coset_for_natural_index(domain_idx, domain_size);
                if coset_values.len() != <I::Combiner as CosetCombiner<F>>::COSET_SIZE {
                    return Err(SynthesisError::PolynomialDegreeTooLarge);
                }

                for idx in coset_values.into_iter() {
                    let query = iop.query(idx, leaf_values.as_ref());
                    queries.push(query);
                }

                let (next_idx, next_size) = Domain::<F>::index_and_size_for_next_domain(domain_idx, domain_size);

                domain_idx = next_idx;
                domain_size = next_size;
            }

            rounds.push(queries);
        }

        let proof = FRIProof::<F, I> {
            queries: rounds,
            roots,
            final_coefficients: self.final_coefficients,
            initial_degree_plus_one: self.initial_degree_plus_one,
            output_coeffs_at_degree_plus_one: self.output_coeffs_at_degree_plus_one,
            lde_factor: self.lde_factor,
        };

        Ok(proof)
    }
}