use crate::ff::PrimeField;

pub mod coset_combining_blake2s_tree;

pub trait Commitment: Clone + Eq + PartialEq + std::fmt::Debug {}

pub trait IopInstance<F: PrimeField>: PartialEq + Eq {
    type Commitment: Clone + Eq + PartialEq + std::fmt::Debug;
    type Query: IopQuery<F>;
    type Params: Clone + Eq + PartialEq + std::fmt::Debug;

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

// const fn byte_size<F: PrimeField>() -> usize {
//     (((F::NUM_BITS as usize) / 64) + 1) * 8
// }