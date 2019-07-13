/// Largeley this module is implementation of provable evaluation of s(z, y), that is represented in two parts
/// s2(X, Y) = \sum_{i=1}^{N} (Y^{-i} + Y^{i})X^{i}
/// s1(X, Y) = ...
/// s1 part requires grand product and permutation arguments, that are also implemented

mod s2_proof;
mod wellformed_argument;
pub mod grand_product_argument;
mod permutation_argument;
mod verifier;
pub mod permutation_structure;
mod aggregate;

pub use self::wellformed_argument::{WellformednessArgument, WellformednessProof};
pub use self::permutation_argument::{PermutationArgument, PermutationProof, PermutationArgumentProof};
pub use self::verifier::SuccinctMultiVerifier;
pub use self::aggregate::*;