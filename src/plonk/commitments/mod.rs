use crate::pairing::ff::PrimeField;

use crate::plonk::polynomials::*;

pub mod transparent;

pub mod transcript;

pub trait CommitmentScheme<F: PrimeField> {
    type Commitment;
    type OpeningValue;
    type OpeningProof;
    type IntermediateData;

    fn commit_single(poly: &Polynomial<F, Coefficients>) -> (Self::Commitment, Self::IntermediateData);
    fn commit_multiple(polynomials: Vec<&Polynomial<F, Coefficients>>, degrees: Vec<usize>, aggregation_coefficient: F) -> (Self::Commitment, Vec<Self::IntermediateData>);
    fn open_single(poly: Polynomial<F, Coefficients>, at_point: F, data: Self::IntermediateData) -> (Self::OpeningValue, Self::OpeningProof);
    fn open_multiple(polynomials: Vec<Polynomial<F, Coefficients>>, degrees: Vec<usize>, aggregation_coefficient: F, at_point: F, data: Vec<Self::IntermediateData>) -> (Vec<Self::OpeningValue>, Self::OpeningProof);
}