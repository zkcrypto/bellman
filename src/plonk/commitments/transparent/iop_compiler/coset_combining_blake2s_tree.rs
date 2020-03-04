use crate::pairing::ff::{PrimeField, PrimeFieldRepr};
use blake2s_const::blake2s_const;
use crate::multicore::Worker;
use super::super::utils::log2_floor;
use super::*;
use std::convert::From;

#[derive(Debug)]
pub struct FriSpecificBlake2sTree<F: PrimeField> {
    size: usize,
    nodes: Vec<[u8; 32]>,
    params: FriSpecificBlake2sTreeParams,
    _marker: std::marker::PhantomData<F>
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct FriSpecificBlake2sTreeParams {
    pub values_per_leaf: usize
}

impl From<usize> for FriSpecificBlake2sTreeParams {
    fn from(data: usize) -> Self {
        Self { values_per_leaf: data}
    }
}


use std::time::Instant;

impl<F: PrimeField> FriSpecificBlake2sTree<F> {
    const VALUE_BYTE_SIZE: usize = (((F::NUM_BITS as usize) / 64) + 1) * 8;

    fn encode_leaf_values(values: &[F], buffer: &mut [u8]) {
        debug_assert!(buffer.len() == values.len() * Self::VALUE_BYTE_SIZE);
        for (i, value) in values.iter().enumerate() {
            let start = Self::VALUE_BYTE_SIZE * i;
            let end = start + Self::VALUE_BYTE_SIZE;
            let raw_repr = value.into_raw_repr();
            raw_repr.write_le(&mut buffer[start..end]).expect("will write");
        }
    }

    fn decode_leaf_values(buffer: &[u8]) -> Vec<F> {
        debug_assert!(buffer.len() % Self::VALUE_BYTE_SIZE == 0);
        let num_elements = buffer.len() / Self::VALUE_BYTE_SIZE;
        let mut result = Vec::with_capacity(num_elements);
        let mut raw_repr = F::zero().into_raw_repr();
        for i in 0..num_elements {
            let start = Self::VALUE_BYTE_SIZE * i;
            let end = start + Self::VALUE_BYTE_SIZE;
            raw_repr.read_le(&buffer[start..end]).expect("will write");
            result.push(F::from_raw_repr(raw_repr).expect("must work"));
        }

        result
    }

    fn hash_into_leaf(values: &[F], scratch_space: &mut [u8]) -> [u8; 32] {
        Self::encode_leaf_values(values, scratch_space);
        *blake2s_const(scratch_space).as_array()
    }

    fn make_full_path(&self, leaf_index: usize, leaf_pair_hash: [u8; 32]) -> Vec<[u8; 32]> {
        let mut nodes = &self.nodes[..];

        let mut path = vec![];
        path.push(leaf_pair_hash);

        let mut idx = leaf_index;
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

impl<F: PrimeField> IopInstance<F> for FriSpecificBlake2sTree<F> {
    type Commitment = [u8; 32];
    type Params = FriSpecificBlake2sTreeParams;
    type Query = CosetCombinedQuery<F>;

    fn size(&self) -> usize {
        self.size
    }

    fn create(values: &[F], params: &Self::Params) -> Self {
        assert!(params.values_per_leaf.is_power_of_two());

        let values_per_leaf = params.values_per_leaf;
        let num_leafs = values.len() / values_per_leaf;
        assert!(num_leafs.is_power_of_two());

        let num_nodes = num_leafs;

        let size = values.len();

        let mut nodes = vec![[0u8; 32]; num_nodes];

        let worker = Worker::new();

        let mut leaf_hashes = vec![[0u8; 32]; num_leafs];

        {
            worker.scope(leaf_hashes.len(), |scope, chunk| {
                for (i, lh) in leaf_hashes.chunks_mut(chunk)
                                .enumerate() {
                    scope.spawn(move |_| {
                        let base_idx = i*chunk;
                        let mut scratch_space = vec![0u8; Self::VALUE_BYTE_SIZE * values_per_leaf];
                        for (j, lh) in lh.iter_mut().enumerate() {
                            let idx = base_idx + j;
                            let values_start = idx * values_per_leaf;
                            let values_end = values_start + values_per_leaf;
                            *lh = Self::hash_into_leaf(&values[values_start..values_end], &mut scratch_space);
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
            let _level = num_levels-1;
            let inputs = &mut leaf_hashes[..];
            let (_, outputs) = nodes_for_hashing.split_at_mut(nodes_for_hashing.len()/2);
            assert!(outputs.len() * 2 == inputs.len());
            assert!(outputs.len().is_power_of_two());

            worker.scope(outputs.len(), |scope, chunk| {
                for (o, i) in outputs.chunks_mut(chunk)
                                .zip(inputs.chunks(chunk*2)) {
                    scope.spawn(move |_| {
                        let mut hash_input = [0u8; 64];
                        for (o, i) in o.iter_mut().zip(i.chunks(2)) {
                            hash_input[0..32].copy_from_slice(&i[0]);
                            hash_input[32..64].copy_from_slice(&i[1]);
                            *o = *blake2s_const(&hash_input).as_array();
                        }
                    });
                }
            });
        }

        for _ in (0..(num_levels-1)).rev() {
            // do the trick - split
            let (next_levels, inputs) = nodes_for_hashing.split_at_mut(nodes_for_hashing.len()/2);
            let (_, outputs) = next_levels.split_at_mut(next_levels.len() / 2);
            assert!(outputs.len() * 2 == inputs.len());
            assert!(outputs.len().is_power_of_two());

            worker.scope(outputs.len(), |scope, chunk| {
                for (o, i) in outputs.chunks_mut(chunk)
                                .zip(inputs.chunks(chunk*2)) {
                    scope.spawn(move |_| {
                        let mut hash_input = [0u8; 64];
                        for (o, i) in o.iter_mut().zip(i.chunks(2)) {
                            hash_input[0..32].copy_from_slice(&i[0]);
                            hash_input[32..64].copy_from_slice(&i[1]);
                            *o = *blake2s_const(&hash_input).as_array();
                        }
                    });
                }
            });

            nodes_for_hashing = next_levels;
        }

        Self {
            size: size,
            nodes: nodes,
            params: params.clone(),
            _marker: std::marker::PhantomData
        }
    }

    fn get_commitment(&self) -> Self::Commitment {
        self.nodes[1]
    }

    fn produce_query(&self, indexes: Vec<usize>, values: &[F]) -> Self::Query {
        // we never expect that query is mis-alligned, so check it
        debug_assert!(indexes[0] % self.params.values_per_leaf == 0);
        debug_assert!(indexes.len() == self.params.values_per_leaf);
        debug_assert!(indexes == (indexes[0]..(indexes[0]+self.params.values_per_leaf)).collect::<Vec<_>>());
        debug_assert!(*indexes.last().expect("is some") < self.size());
        debug_assert!(*indexes.last().expect("is some") < values.len());

        let query_values = Vec::from(&values[indexes[0]..(indexes[0]+self.params.values_per_leaf)]);

        let leaf_index = indexes[0] / self.params.values_per_leaf;

        let pair_index = leaf_index ^ 1;

        let mut scratch_space = vec![0u8; Self::VALUE_BYTE_SIZE * self.params.values_per_leaf];
        let leaf_pair_hash = Self::hash_into_leaf(&values[(pair_index*self.params.values_per_leaf)..((pair_index+1)*self.params.values_per_leaf)], &mut scratch_space);

        let path = self.make_full_path(leaf_index, leaf_pair_hash);

        CosetCombinedQuery::<F> {
            indexes: indexes,
            values: query_values,
            path: path,
        }
    }

    fn verify_query(commitment: &Self::Commitment, query: &Self::Query, params: &Self::Params) -> bool {
        if query.values().len() != params.values_per_leaf {
            return false;
        }

        let mut scratch_space = vec![0u8; Self::VALUE_BYTE_SIZE * params.values_per_leaf];
        let mut hash = Self::hash_into_leaf(query.values(), &mut scratch_space);
        let mut idx = query.indexes()[0] / params.values_per_leaf;
        let mut hash_input = [0u8; 64];

        for el in query.path.iter() {
            {
                let (left, right) = hash_input.split_at_mut(32);
                if idx & 1usize == 0 {
                    left.copy_from_slice(&hash[..]);
                    right.copy_from_slice(&el[..]);
                } else {
                    right.copy_from_slice(&hash[..]);
                    left.copy_from_slice(&el[..]);
                }
            }
            hash = *blake2s_const(&hash_input).as_array();
            idx >>= 1;
        }

        &hash == commitment
    }
}

impl<F: PrimeField> PartialEq for FriSpecificBlake2sTree<F> {
    fn eq(&self, other: &Self) -> bool {
        self.get_commitment() == other.get_commitment()
    }
}

impl<F: PrimeField> Eq for FriSpecificBlake2sTree<F> {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CosetCombinedQuery<F: PrimeField> {
    indexes: Vec<usize>,
    values: Vec<F>,
    path: Vec<[u8; 32]>,
}

impl<F: PrimeField> IopQuery<F> for CosetCombinedQuery<F> {
    fn indexes(&self) -> Vec<usize> {
        self.indexes.clone()
    }

    fn values(&self) -> &[F] {
        &self.values
    }
}

#[test]
fn make_small_iop() {
    use crate::ff::Field;
    use crate::plonk::transparent_engine::Fr;

    const SIZE: usize = 16;
    const VALUES_PER_LEAF: usize = 4;

    let params = FriSpecificBlake2sTreeParams {
        values_per_leaf: VALUES_PER_LEAF
    };

    let mut inputs = vec![];
    let mut f = Fr::one();
    for _ in 0..SIZE {
        inputs.push(f);
        f.double();
    }

    let iop = FriSpecificBlake2sTree::create(&inputs, &params);
    let commitment = iop.get_commitment();
    let tree_size = iop.size();
    assert!(tree_size == SIZE);
    assert!(iop.nodes.len() == (SIZE / VALUES_PER_LEAF));
    for i in 0..(SIZE / VALUES_PER_LEAF) {
        let indexes: Vec<_> = ((i*VALUES_PER_LEAF)..(VALUES_PER_LEAF + i*VALUES_PER_LEAF)).collect();
        let query = iop.produce_query(indexes, &inputs);
        let valid = FriSpecificBlake2sTree::verify_query(&commitment, &query, &params);
        assert!(valid, "invalid query for leaf index {}", i);
    }
}


#[test]
fn test_bench_large_fri_specific_iop() {
    use crate::ff::Field;
    use crate::plonk::transparent_engine::Fr;

    const SIZE: usize = 1 << (20 + 4);
    const VALUES_PER_LEAF: usize = 8;

    let params = FriSpecificBlake2sTreeParams {
        values_per_leaf: VALUES_PER_LEAF
    };

    let mut inputs = vec![];
    let mut f = Fr::one();
    for _ in 0..SIZE {
        inputs.push(f);
        f.double();
    }

    let iop = FriSpecificBlake2sTree::create(&inputs, &params);
    let commitment = iop.get_commitment();
    let tree_size = iop.size();
    assert!(tree_size == SIZE);
    assert!(iop.nodes.len() == (SIZE / VALUES_PER_LEAF));
    for i in 0..128 {
        let indexes: Vec<_> = ((i*VALUES_PER_LEAF)..(VALUES_PER_LEAF + i*VALUES_PER_LEAF)).collect();
        let query = iop.produce_query(indexes, &inputs);
        let valid = FriSpecificBlake2sTree::verify_query(&commitment, &query, &params);
        assert!(valid, "invalid query for leaf index {}", i);
    }
}