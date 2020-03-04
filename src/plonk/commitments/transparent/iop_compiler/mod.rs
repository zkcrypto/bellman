use crate::ff::PrimeField;
use std::convert::From;

pub mod coset_combining_blake2s_tree;
pub mod rescue;
pub mod coset_combining_rescue_tree;

pub trait Commitment: Clone + Eq + PartialEq + std::fmt::Debug {}

pub trait IopInstance<F: PrimeField>: PartialEq + Eq {
    type Commitment: Clone + Eq + PartialEq + std::fmt::Debug;
    type Query: IopQuery<F>;
    type Params: Clone + Eq + PartialEq + std::fmt::Debug + From<usize>;

    fn create(values: &[F], params: &Self::Params) -> Self;
    fn size(&self) -> usize;
    fn get_commitment(&self) -> Self::Commitment;
    fn verify_query(commitment: &Self::Commitment, query: &Self::Query, params: &Self::Params) -> bool;
    fn produce_query(&self, indexes: Vec<usize>, values: &[F]) -> Self::Query;
}

pub trait IopQuery<F: PrimeField>: 'static + PartialEq + Eq + Clone + std::fmt::Debug {
    fn indexes(&self) -> Vec<usize>;
    fn values(&self) -> &[F];
}

pub trait CosetCombiner<F: PrimeField> {
    const EXPECTED_DEGREE: usize;
    const COSET_SIZE: usize;
    
    fn get_for_natural_index(leafs: &[F], natural_index: usize) -> &F;
    fn get_for_tree_index(leafs: &[F], tree_index: usize) -> &F;
    fn tree_index_into_natural_index(tree_index: usize) -> usize;
    fn natural_index_into_tree_index(natural_index: usize) -> usize;
    fn get_coset_for_natural_index(natural_index: usize, domain_size: usize) -> Vec<usize>;
    fn get_coset_for_tree_index(tree_index: usize, domain_size: usize) -> Vec<usize>;
}
