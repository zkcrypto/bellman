use crate::pairing::ff::PrimeField;

use crate::plonk::polynomials::*;
use crate::plonk::commitments::transcript::*;

pub mod transparent;

pub mod transcript;

pub trait CommitmentScheme<F: PrimeField> {
    type Commitment;
    type OpeningProof;
    type IntermediateData;
    type Meta;
    type Prng;

    fn new_for_size(max_degree_plus_one: usize, meta: Self::Meta) -> Self;
    fn commit_single(&self, poly: &Polynomial<F, Coefficients>) -> (Self::Commitment, Self::IntermediateData);
    fn commit_multiple(&self, polynomials: Vec<&Polynomial<F, Coefficients>>, degrees: Vec<usize>, aggregation_coefficient: F) -> (Self::Commitment, Vec<Self::IntermediateData>);
    fn open_single(&self, poly: &Polynomial<F, Coefficients>, at_point: F, data: Self::IntermediateData, prng: &mut Self::Prng) -> (F, Self::OpeningProof);
    fn open_multiple(&self, polynomials: Vec<&Polynomial<F, Coefficients>>, degrees: Vec<usize>, aggregation_coefficient: F, at_point: F, data: Vec<Self::IntermediateData>, prng: &mut Self::Prng) -> (Vec<F>, Self::OpeningProof);
}