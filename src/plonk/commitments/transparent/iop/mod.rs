use crate::pairing::ff::PrimeField;

pub mod trivial_coset_combiner;
pub mod blake2s_trivial_iop;
pub mod keccak_trivial_iop;

pub trait CosetInformation: Sized + Clone + Copy {
    const COSET_SIZE: usize;
}

pub trait CosetCombiner<F: PrimeField> {
    const EXPECTED_DEGREE: usize;
    const COSET_SIZE: usize;
    // type CosetData: CosetInformation;
    
    fn get_for_natural_index(leafs: &[F], natural_index: usize) -> &F;
    fn get_for_tree_index(leafs: &[F], tree_index: usize) -> &F;
    fn tree_index_into_natural_index(tree_index: usize) -> usize;
    fn natural_index_into_tree_index(natural_index: usize) -> usize;
    fn get_coset_for_natural_index(natural_index: usize, domain_size: usize) -> Vec<usize>;
    fn get_coset_for_tree_index(tree_index: usize, domain_size: usize) -> Vec<usize>;
}

pub trait HashFunctionOutput: Clone + Eq + PartialEq + std::fmt::Debug {}

pub trait LeafEncoder<F: PrimeField> {
    type Output;

    fn encode_leaf(value: &F) -> Self::Output;
}

pub trait FiatShamirHasher<F: PrimeField> {
    type Input;

    fn transform(value: &Self::Input) -> F;
}

pub trait IopTreeHasher<F: PrimeField> {
    type HashOutput: HashFunctionOutput;
    type LeafEncoder: LeafEncoder<F>;

    fn hash_leaf(value: &F) -> Self::HashOutput;
    fn hash_encoded_leaf(value: &<Self::LeafEncoder as LeafEncoder<F>>::Output) -> Self::HashOutput;
    fn hash_node(values: &[Self::HashOutput], level: usize) -> Self::HashOutput;
}


pub trait IopTree<F: PrimeField> {
    type Combiner: CosetCombiner<F>;
    type TreeHasher: IopTreeHasher<F>;
    type FiatShamirTransformer: FiatShamirHasher<F, Input = <Self::TreeHasher as IopTreeHasher<F>>::HashOutput>; 

    fn create(leafs: &[F]) -> Self;
    fn size(&self) -> usize;
    fn get_root(&self) -> <Self::TreeHasher as IopTreeHasher<F>>::HashOutput;
    fn encode_root_into_challenge(root: & <Self::TreeHasher as IopTreeHasher<F>>::HashOutput) -> F;
    fn get_challenge_scalar_from_root(&self) -> F;
    fn verify(root: &<Self::TreeHasher as IopTreeHasher<F>>::HashOutput, leaf_value: &F, path: &[<Self::TreeHasher as IopTreeHasher<F>>::HashOutput], index: usize) -> bool;
    fn get_path(&self, index: usize, leafs_values: &[F]) -> Vec< <Self::TreeHasher as IopTreeHasher<F>>::HashOutput >;
}

pub trait IopQuery<F: PrimeField>: 'static + PartialEq + Eq + Clone + std::fmt::Debug {
    type TreeHasher: IopTreeHasher<F>;

    fn tree_index(&self) -> usize;
    fn natural_index(&self) -> usize;
    fn natural_indexes(&self) -> Vec<usize>;
    fn value(&self) -> F;
    fn values(&self) -> &[F];
    fn path(&self) ->  &[<Self::TreeHasher as IopTreeHasher<F>>::HashOutput];
}

pub trait IOP<F: PrimeField> {
    type Combiner: CosetCombiner<F>;
    type Tree: IopTree<F, Combiner = Self::Combiner>;
    type Query: IopQuery<F, TreeHasher = <Self::Tree as IopTree<F> >::TreeHasher>;

    fn create(leafs: & [F]) -> Self;
    fn get_for_natural_index(leafs: &[F], natural_index: usize) -> &F;
    fn get_for_tree_index(leafs: &[F], tree_index: usize) -> &F;
    fn get_root(&self) -> < <Self::Tree as IopTree<F> >::TreeHasher as IopTreeHasher<F>>::HashOutput;
    fn verify_query(query: &Self::Query, root: &< <Self::Tree as IopTree<F> >::TreeHasher as IopTreeHasher<F>>::HashOutput) -> bool;
    fn query(&self, natural_index: usize, leafs: &[F]) -> Self::Query;
}