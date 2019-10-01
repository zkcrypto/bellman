use crate::pairing::ff::PrimeField;

use crate::plonk::polynomials::*;
use crate::plonk::commitments::transcript::*;

pub mod transparent;

pub mod transcript;

pub trait CommitmentScheme<F: PrimeField> {
    type Commitment: std::fmt::Debug;
    type OpeningProof;
    type IntermediateData;
    type Meta: Clone;
    type Prng: Prng<F>;

    const REQUIRES_PRECOMPUTATION: bool;
    const IS_HOMOMORPHIC: bool;

    fn new_for_size(max_degree_plus_one: usize, meta: Self::Meta) -> Self;
    fn precompute(&self, poly: &Polynomial<F, Coefficients>) -> Option<Self::IntermediateData>;
    fn commit_single(&self, poly: &Polynomial<F, Coefficients>) -> (Self::Commitment, Option<Self::IntermediateData>);
    fn commit_multiple(&self, polynomials: Vec<&Polynomial<F, Coefficients>>, degrees: Vec<usize>, aggregation_coefficient: F) -> (Self::Commitment, Option<Vec<Self::IntermediateData>>);
    fn open_single(&self, poly: &Polynomial<F, Coefficients>, at_point: F, opening_value: F, data: &Option<&Self::IntermediateData>, prng: &mut Self::Prng) -> Self::OpeningProof;
    fn open_multiple(&self, polynomials: Vec<&Polynomial<F, Coefficients>>, degrees: Vec<usize>, aggregation_coefficient: F, at_points: Vec<F>, opening_values: Vec<F>, data: &Option<Vec<&Self::IntermediateData>>, prng: &mut Self::Prng) -> Self::OpeningProof;
    fn verify_single(&self, commitment: &Self::Commitment, at_point: F, claimed_value: F, proof: &Self::OpeningProof, prng: &mut Self::Prng) -> bool;
    fn verify_multiple_openings(&self, commitments: Vec<&Self::Commitment>, at_points: Vec<F>, claimed_values: &Vec<F>, aggregation_coefficient: F, proof: &Self::OpeningProof, prng: &mut Self::Prng) -> bool;
}