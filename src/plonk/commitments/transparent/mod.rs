use crate::pairing::ff::PrimeField;

use crate::plonk::polynomials::*;

use super::CommitmentScheme;

mod precomputations;
mod iop;
mod fri;

pub mod utils;

use self::precomputations::PrecomputedOmegas;

pub struct TransparentCommitment<'a, F: PrimeField> {
    max_degree_plus_one: usize,
    lde_factor: usize,
    precomputed_values: &'a PrecomputedOmegas<F>
}