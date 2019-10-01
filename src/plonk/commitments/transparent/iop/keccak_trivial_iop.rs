use crate::pairing::ff::{PrimeField, PrimeFieldRepr};
use tiny_keccak::*;
use crate::multicore::Worker;
use super::super::utils::log2_floor;
use super::*;
use super::trivial_coset_combiner::*;

pub struct KeccakLeafEncoder<F: PrimeField> {
    _marker: std::marker::PhantomData<F>
}

impl<F: PrimeField> KeccakLeafEncoder<F>  {
    const SHAVE_BITS: u32 = 256 - F::CAPACITY;
    pub fn new() -> Self {
        assert!(F::NUM_BITS < 256);

        Self {
            _marker: std::marker::PhantomData
        }
    }
}

impl<F: PrimeField> LeafEncoder<F> for KeccakLeafEncoder<F>{
    type Output = [u8; 32];

    fn encode_leaf(value: &F) -> Self::Output {
        let raw_repr = value.into_raw_repr();
        let mut output = [0u8; 32];
        raw_repr.write_le(&mut output[..]).expect("will write");

        output
    }
}

impl<F: PrimeField> FiatShamirHasher<F> for KeccakLeafEncoder<F>{
    type Input = [u8; 32];

    fn transform(value: &Self::Input) -> F {
        let value = *value;
        let mut repr = F::Repr::default();
        let shaving_mask: u64 = 0xffffffffffffffff >> (Self::SHAVE_BITS % 64);
        repr.read_be(&value[..]).expect("will read");
        // repr.read_le(&value[..]).expect("will read");
        let last_limb_idx = repr.as_ref().len() - 1;
        repr.as_mut()[last_limb_idx] &= shaving_mask;
        let value = F::from_repr(repr).expect("in a field");

        value
    }
}

pub struct KeccakTreeHasher<F: PrimeField> {
    _marker: std::marker::PhantomData<F>
}

impl<F: PrimeField> KeccakTreeHasher<F> {
    pub fn new() -> Self {
        Self {
            _marker: std::marker::PhantomData
        }
    }
}

impl<F: PrimeField> IopTreeHasher<F> for KeccakTreeHasher<F> {
    type HashOutput = [u8; 32];
    type LeafEncoder = KeccakLeafEncoder<F>;

    fn hash_leaf(value: &F) -> Self::HashOutput {
        let value = <Self::LeafEncoder as LeafEncoder<F> >::encode_leaf(value);
        Self::hash_encoded_leaf(&value)
    }

    fn hash_encoded_leaf(value: &<Self::LeafEncoder as LeafEncoder<F>>::Output) -> Self::HashOutput {
        let output = keccak256(value);

        output
    }

    fn hash_node(values: &[Self::HashOutput], _level: usize) -> Self::HashOutput {
        debug_assert!(values.len() == 2);
        let mut state = Keccak::new_keccak256();
        for value in values.iter() {
            state.update(value);
        }

        let mut output: [u8; 32] = [0; 32];
        state.finalize(&mut output);

        output
    }
}

pub struct KeccakIopTree<F: PrimeField> {
    size: usize,
    nodes: Vec< < KeccakTreeHasher<F> as IopTreeHasher<F> >::HashOutput >,
}

impl<F: PrimeField> KeccakIopTree<F> {
    pub fn new() -> Self {
        Self {
            size: 0usize,
            nodes: vec![],
        }
    }
}

use std::time::Instant;

impl<'a, F: PrimeField> IopTree<F> for KeccakIopTree<F> {
    type Combiner = TrivialCombiner<F>;
    type TreeHasher = KeccakTreeHasher<F>;
    type FiatShamirTransformer = KeccakLeafEncoder<F>;

    fn size(&self) -> usize {
        self.size
    }

    fn create(leafs: &[F]) -> Self {
        println!("Creating a tree of size {}", leafs.len());
        let start = Instant::now();

        let num_leafs = leafs.len();
        assert!(num_leafs == num_leafs.next_power_of_two());
        let num_nodes = num_leafs;

        let size = num_leafs;

        let mut nodes = vec![[0u8; 32]; num_nodes];

        let worker = Worker::new();

        let mut leaf_hashes = vec![[0u8; 32]; num_leafs];

        {
            worker.scope(leafs.len(), |scope, chunk| {
                for (i, lh) in leaf_hashes.chunks_mut(chunk)
                                .enumerate() {
                    scope.spawn(move |_| {
                        let base_idx = i*chunk;
                        for (j, lh) in lh.iter_mut().enumerate() {
                            let idx = base_idx + j;
                            let leaf_ref = <Self::Combiner as CosetCombiner<F> >::get_for_tree_index(&leafs, idx);
                            *lh = < Self::TreeHasher as IopTreeHasher<F> >::hash_leaf(leaf_ref);
                        }
                    });
                }
            });
        }

        // leafs are now encoded and hashed, so let's make a tree

        let num_levels = log2_floor(num_leafs) as usize;
        let mut nodes_for_hashing = &mut nodes[..];

        // separately hash last level, which hashes leaf hashes into first nodes
        {
            let level = num_levels-1;
            let inputs = &mut leaf_hashes[..];
            let (_, outputs) = nodes_for_hashing.split_at_mut(nodes_for_hashing.len()/2);
            assert!(outputs.len() * 2 == inputs.len());
            assert!(outputs.len().is_power_of_two());

            worker.scope(outputs.len(), |scope, chunk| {
                for (o, i) in outputs.chunks_mut(chunk)
                                .zip(inputs.chunks(chunk*2)) {
                    scope.spawn(move |_| {
                        for (o, i) in o.iter_mut().zip(i.chunks(2)) {
                            *o = < Self::TreeHasher as IopTreeHasher<F> >::hash_node(i, level);
                        }
                    });
                }
            });
        }

        for level in (0..(num_levels-1)).rev() {
            // do the trick - split
            let (next_levels, inputs) = nodes_for_hashing.split_at_mut(nodes_for_hashing.len()/2);
            let (_, outputs) = next_levels.split_at_mut(next_levels.len() / 2);
            assert!(outputs.len() * 2 == inputs.len());
            assert!(outputs.len().is_power_of_two());

            worker.scope(outputs.len(), |scope, chunk| {
                for (o, i) in outputs.chunks_mut(chunk)
                                .zip(inputs.chunks(chunk*2)) {
                    scope.spawn(move |_| {
                        for (o, i) in o.iter_mut().zip(i.chunks(2)) {
                            *o = < Self::TreeHasher as IopTreeHasher<F> >::hash_node(i, level);
                        }
                    });
                }
            });

            nodes_for_hashing = next_levels;
        }

        println!("Done creating a tree of size {} in {:?}", leafs.len(), start.elapsed());

        Self {
            size: size,
            nodes: nodes,
        }
    }

    fn get_root(&self) -> <Self::TreeHasher as IopTreeHasher<F>>::HashOutput {
        // 1 here is ok, cause we have nodes as power of two, but not 2^n - 1
        self.nodes[1]
    }

    fn encode_root_into_challenge(root: & <Self::TreeHasher as IopTreeHasher<F>>::HashOutput) -> F {
        <Self::FiatShamirTransformer as FiatShamirHasher<F>>::transform(&root)
    }

    fn get_challenge_scalar_from_root(&self) -> F {
        let root = self.get_root();

        Self::encode_root_into_challenge(&root)
    }

    fn verify(root: &<Self::TreeHasher as IopTreeHasher<F>>::HashOutput, leaf_value: &F, path: &[<Self::TreeHasher as IopTreeHasher<F>>::HashOutput], tree_index: usize) -> bool {
        let mut hash = <Self::TreeHasher as IopTreeHasher<F>>::hash_leaf(&leaf_value);
        let mut idx = tree_index;
        for el in path.iter() {
            if idx & 1usize == 0 {
                hash = <Self::TreeHasher as IopTreeHasher<F>>::hash_node(&[hash, el.clone()], 0);
            } else {
                hash = <Self::TreeHasher as IopTreeHasher<F>>::hash_node(&[el.clone(), hash], 0);
            }
            idx >>= 1;
        }

        &hash == root
    }

    fn get_path(&self, tree_index: usize, leafs_values: &[F]) -> Vec< <Self::TreeHasher as IopTreeHasher<F>>::HashOutput >{
        assert!(self.size == self.nodes.len());
        let mut nodes = &self.nodes[..];

        let tree_pair_index = tree_index ^ 1usize;

        let mut path = vec![];

        let pair_natural_index = <Self::Combiner as CosetCombiner<F>>::tree_index_into_natural_index(tree_pair_index);

        let pair = &leafs_values[pair_natural_index as usize];
        let encoded_pair_hash = < Self::TreeHasher as IopTreeHasher<F> >::hash_leaf(pair);
        path.push(encoded_pair_hash);

        let mut idx = tree_index;
        idx >>= 1;

        for _ in 0..log2_floor(nodes.len() / 2) {
            let half_len = nodes.len() / 2;
            let (next_level, this_level) = nodes.split_at(half_len);
            let pair_idx = idx ^ 1usize;
            let value = this_level[pair_idx];
            path.push(value);
            idx >>= 1;
            nodes = next_level;
        }

        path
    }
}

pub struct TrivialKeccakIOP<F: PrimeField> {
    tree: KeccakIopTree<F>,
}


impl<F: PrimeField> IOP<F> for TrivialKeccakIOP<F> {
    type Combiner = TrivialCombiner<F>;
    type Tree = KeccakIopTree<F>;
    type Query = TrivialKeccakIopQuery<F>;

    fn create<'l> (leafs: &'l [F]) -> Self {
        let tree = Self::Tree::create(leafs);

        Self {
            tree
        }
    }

    fn get_for_natural_index(leafs: &[F], natural_index: usize) -> &F {
        <Self::Combiner as CosetCombiner<F>>::get_for_natural_index(leafs, natural_index)
    }

    fn get_for_tree_index(leafs: &[F], tree_index: usize) -> &F {
        <Self::Combiner as CosetCombiner<F>>::get_for_tree_index(leafs, tree_index)
    }

    fn get_root(&self) -> < <Self::Tree as IopTree<F> >::TreeHasher as IopTreeHasher<F>>::HashOutput {
        self.tree.get_root()
    }

    fn verify_query(query: &Self::Query, root: &< <Self::Tree as IopTree<F> >::TreeHasher as IopTreeHasher<F>>::HashOutput) -> bool {
        Self::Tree::verify(root, &query.value(), &query.path(), query.tree_index())
    }

    fn query(&self, natural_index: usize, leafs: &[F]) -> Self::Query {
        assert!(natural_index < self.tree.size() as usize);
        assert!(natural_index < leafs.len());
        let value = leafs[natural_index];

        let tree_index = <Self::Combiner as CosetCombiner<F>>::natural_index_into_tree_index(natural_index);

        let path = self.tree.get_path(tree_index, leafs);

        TrivialKeccakIopQuery::<F> {
            index: natural_index,
            value: value,
            path: path
        }
    }
}

impl<F: PrimeField> PartialEq for TrivialKeccakIOP<F> {
    fn eq(&self, other: &Self) -> bool {
        self.get_root() == other.get_root()
    }
}

impl<F: PrimeField> Eq for TrivialKeccakIOP<F> {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TrivialKeccakIopQuery<F: PrimeField> {
    index: usize,
    value: F,
    path: Vec<[u8; 32]>,
}

impl<F: PrimeField> IopQuery<F> for TrivialKeccakIopQuery<F> {
    type TreeHasher = KeccakTreeHasher<F>;

    fn natural_index(&self) -> usize {
        self.index
    }

    fn tree_index(&self) -> usize {
        self.index
    }

    fn value(&self) -> F {
        self.value
    }

    fn path(&self) ->  &[<Self::TreeHasher as IopTreeHasher<F>>::HashOutput] {
        &self.path
    }
}

// #[test]
// fn make_small_tree() {
//     use ff::Field;
//     use hex::encode;
//     use crate::experiments::Fr;
//     let inputs = vec![Fr::one(); 16];

//     let tree = Blake2sIopTree::create(&inputs);
//     let root = tree.get_root();
//     let challenge_scalar = tree.get_challenge_scalar_from_root();
//     println!("Root = {}, scalar = {}", encode(&root), challenge_scalar);
// }

// #[test]
// fn make_small_iop() {
//     use crate::iop::IOP;
//     use ff::Field;
//     const SIZE: usize = 64;
//     use crate::experiments::Fr;
//     let mut inputs = vec![];
//     let mut f = Fr::one();
//     for _ in 0..SIZE {
//         inputs.push(f);
//         f.double();
//     }

//     let iop = TrivialBlake2sIOP::create(&inputs);
//     let root = iop.get_root();
//     for i in 0..SIZE {
//         let query = iop.query(i, &inputs);
//         let valid = TrivialBlake2sIOP::verify_query(&query, &root);
//         assert!(valid, "invalid query for leaf {}", i);
//     }
// }