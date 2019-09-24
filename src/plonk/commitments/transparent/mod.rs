use crate::pairing::ff::PrimeField;

use crate::plonk::polynomials::*;

use super::CommitmentScheme;

pub mod precomputations;
pub mod iop;
pub mod fri;

pub mod utils;

use self::precomputations::PrecomputedOmegas;

pub struct TransparentCommitment<'a, F: PrimeField> {
    max_degree_plus_one: usize,
    lde_factor: usize,
    precomputed_values: &'a PrecomputedOmegas<F>
}