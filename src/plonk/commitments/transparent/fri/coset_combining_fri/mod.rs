pub mod fri;
pub mod query_producer;
pub mod verifier;
pub mod precomputation;

use crate::SynthesisError;
use crate::multicore::Worker;
use crate::ff::PrimeField;
use crate::plonk::commitments::transparent::iop_compiler::*;

use crate::plonk::polynomials::*;
use crate::plonk::commitments::transcript::Prng;

pub trait FriProofPrototype<F: PrimeField, I: IopInstance<F>> {
    fn get_roots(&self) -> Vec<I::Commitment>;
    fn get_final_root(&self) -> I::Commitment;
    fn get_final_coefficients(&self) -> Vec<F>;
}

pub trait FriProof<F: PrimeField, I: IopInstance<F>> {
    fn get_final_coefficients(&self) -> &[F];
    fn get_queries(&self) -> &Vec<Vec<I::Query>>;
}

pub trait FriPrecomputations<F: PrimeField> {
    fn new_for_domain_size(size: usize) -> Self;
    fn omegas_inv_bitreversed(&self) -> &[F];
    fn domain_size(&self) -> usize;
}

pub trait FriIop<F: PrimeField> {
    const DEGREE: usize;

    type IopType: IopInstance<F>;
    type ProofPrototype: FriProofPrototype<F, Self::IopType>;
    type Proof: FriProof<F, Self::IopType>;
    type Params: Clone + std::fmt::Debug;

    fn proof_from_lde<P: Prng<F, Input = <Self::IopType as IopInstance<F>>::Commitment>,
    C: FriPrecomputations<F>
    >(
        lde_values: &Polynomial<F, Values>, 
        lde_factor: usize,
        output_coeffs_at_degree_plus_one: usize,
        precomputations: &C,
        worker: &Worker,
        prng: &mut P,
        params: &Self::Params
    ) -> Result<Self::ProofPrototype, SynthesisError>;

    fn prototype_into_proof(
        prototype: Self::ProofPrototype,
        iop_values: &Polynomial<F, Values>,
        natural_first_element_indexes: Vec<usize>,
        params: &Self::Params
    ) -> Result<Self::Proof, SynthesisError>;

    fn get_fri_challenges<P: Prng<F, Input = <Self::IopType as IopInstance<F>>::Commitment>>(
        proof: &Self::Proof,
        prng: &mut P,
        params: &Self::Params
    ) -> Vec<F>;

    fn verify_proof_with_challenges(
        proof: &Self::Proof,
        natural_element_indexes: Vec<usize>,
        expected_value: &[F],
        fri_challenges: &[F],
        params: &Self::Params
    ) -> Result<bool, SynthesisError>;
}