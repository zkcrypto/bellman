use crate::pairing::ff::PrimeField;
use crate::plonk::commitments::transparent::iop::*;
use crate::plonk::polynomials::*;
use crate::multicore::*;
use crate::SynthesisError;
use crate::plonk::commitments::transparent::utils::log2_floor;
use crate::plonk::commitments::transcript::Prng;

pub mod naive_blake2s_fri;

pub trait FriProofPrototype<F: PrimeField, I: IOP<F>> {
    fn get_roots(&self) -> Vec< < <I::Tree as IopTree<F> >::TreeHasher as IopTreeHasher<F>>::HashOutput>;
    fn get_final_root(&self) -> < <I::Tree as IopTree<F> >::TreeHasher as IopTreeHasher<F>>::HashOutput;
    fn get_final_coefficients(&self) -> Vec<F>;
}

pub trait FriProof<F: PrimeField, I: IOP<F>> {
    fn get_final_coefficients(&self) -> &[F];
}

pub trait FriPrecomputations<F: PrimeField> {
    fn omegas_inv_ref(&self) -> &[F];
    fn domain_size(&self) -> usize;
}

pub trait FriIop<F: PrimeField> {
    const DEGREE: usize;

    type IopType: IOP<F>;
    type ProofPrototype: FriProofPrototype<F, Self::IopType>;
    type Proof: FriProof<F, Self::IopType>;
    type Prng: Prng<F, Input = < < <Self::IopType as IOP<F>>::Tree as IopTree<F> >::TreeHasher as IopTreeHasher<F>>::HashOutput >;
    type Precomputations: FriPrecomputations<F>;

    fn proof_from_lde(
        lde_values: &Polynomial<F, Values>, 
        lde_factor: usize,
        output_coeffs_at_degree_plus_one: usize,
        precomputations: &Self::Precomputations,
        worker: &Worker,
        prng: &mut Self::Prng
    ) -> Result<Self::ProofPrototype, SynthesisError>;

    fn prototype_into_proof(
        prototype: Self::ProofPrototype,
        iop_values: &Polynomial<F, Values>,
        natural_first_element_index: usize,
    ) -> Result<Self::Proof, SynthesisError>;

    fn verify_proof(
        proof: &Self::Proof,
        natural_element_index: usize,
        expected_value: F,
        prng: &mut Self::Prng
    ) -> Result<bool, SynthesisError>;
}