use crate::pairing::ff::PrimeField;
use crate::plonk::commitments::transparent::iop::*;
use crate::plonk::polynomials::*;
use crate::multicore::*;
use crate::SynthesisError;
use crate::plonk::commitments::transparent::utils::log2_floor;
use crate::plonk::commitments::transcript::Prng;

pub mod naive_fri;
pub mod coset_combining_fri;

pub trait FriProofPrototype<F: PrimeField, I: IOP<F>> {
    fn get_roots(&self) -> Vec< < <I::Tree as IopTree<F> >::TreeHasher as IopTreeHasher<F>>::HashOutput>;
    fn get_final_root(&self) -> < <I::Tree as IopTree<F> >::TreeHasher as IopTreeHasher<F>>::HashOutput;
    fn get_final_coefficients(&self) -> Vec<F>;
}

pub trait FriProof<F: PrimeField, I: IOP<F>> {
    fn get_final_coefficients(&self) -> &[F];
}

pub trait FriPrecomputations<F: PrimeField> {
    fn new_for_domain_size(size: usize) -> Self;
    fn omegas_inv_ref(&self) -> &[F];
    fn domain_size(&self) -> usize;
}

pub trait FriIop<F: PrimeField> {
    const DEGREE: usize;

    type IopType: IOP<F>;
    type ProofPrototype: FriProofPrototype<F, Self::IopType>;
    type Proof: FriProof<F, Self::IopType>;
    type Params: Clone + std::fmt::Debug;

    fn proof_from_lde<P: Prng<F, Input = < < <Self::IopType as IOP<F>>::Tree as IopTree<F> >::TreeHasher as IopTreeHasher<F>>::HashOutput >,
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

    // // will write roots to prng values
    // fn verify_proof_with_transcript<P: Prng<F, Input = < < <Self::IopType as IOP<F>>::Tree as IopTree<F> >::TreeHasher as IopTreeHasher<F>>::HashOutput > >(
    //     proof: &Self::Proof,
    //     natural_element_indexes: Vec<usize>,
    //     expected_values: &[F],
    //     prng: &mut P
    // ) -> Result<bool, SynthesisError>;

    fn get_fri_challenges<P: Prng<F, Input = < < <Self::IopType as IOP<F>>::Tree as IopTree<F> >::TreeHasher as IopTreeHasher<F>>::HashOutput > >(
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