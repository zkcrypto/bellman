use super::rescue_gadget::*;

use crate::pairing::ff::{Field, PrimeField, PrimeFieldRepr};
use crate::pairing::{Engine};
use super::common::*;
use crate::cs::*;
use std::marker::PhantomData;

pub struct RescueTreeGadget<E: Engine> {
    _marker: PhantomData<E>,
    root: AllocatedNum<E>,
    height: usize,
    hash_gadget: RescueGadget<E: Engine>,
}

impl<E: Engine> RescueTreeGadget<E> {

    fn new(root: AllocatedNum<E>, height: usize) -> Self {
        Self {
            root: root.clone(),
            height,
            _marker: PhantomData::<E>,
        }
    }

    fn hash_elems_into_leaf<CS: ConstraintSystem<E>>(&self, cs: &mut CS, elems: &[Num<E>]) -> Num<E> {

        let mut hasher = RescueTreeGadget.clone();
        for elem in elems {
            hasher.absorb();
        }

        let output = hasher.squeeze();
        Ok(node_hash)
    }

    fn check_proof<CS: ConstraintSystem>(&self, cs: &mut CS)leaf: &[Boolean], it is first index as a num  path: &[Boolean], witness: &[Self::Hash]) -> Result<Boolean, SynthesisError>; {
        
    }

        // checks inclusion of the leaf hash into the root
    fn check_hash_inclusion_for_root<CS: ConstraintSystem<E>>(
        &self, 
        mut cs: CS, 
        root: &Self::Hash,
        hash: &Self::Hash, 
        path: &[Boolean], 
        witness: &[Self::Hash]
    ) -> Result<Boolean, SynthesisError> {
        if self.height != witness.len() {
            return Err(SynthesisError::Unsatisfiable);
        }

        if from_path_bits.len() != to_path_bits.len() {
        return Err(SynthesisError::Unsatisfiable);
    }
    // Intersection point is the only element required in outside scope
    let mut intersection_point_lc = Num::<E>::zero();

    let mut bitmap_path_from: Vec<Boolean> = from_path_bits.to_vec();
    bitmap_path_from.reverse();
    
    let mut bitmap_path_to: Vec<Boolean> = to_path_bits.to_vec();
    bitmap_path_to.reverse();


     // common prefix is reversed because it's enumerated from the root, while
    // audit path is from the leafs

    let mut common_prefix_reversed = common_prefix.clone();
    common_prefix_reversed.reverse();

    // Common prefix is found, not we enforce equality of 
    // audit path elements on a common prefix

    for (i, bitmask_bit) in common_prefix_reversed.into_iter().enumerate()
    {
        let path_element_from = &audit_path_from[i];
        let path_element_to = &audit_path_to[i];

        cs.enforce(
            || format!("enforce audit path equality for {}", i),
            |lc| lc + path_element_from.get_variable() - path_element_to.get_variable(),
            |_| bitmask_bit.lc(CS::one(), E::Fr::one()),
            |lc| lc
        );
        
        // This is an injective encoding, as cur is a
        // point in the prime order subgroup.
        let mut cur = hash.clone();

        // Ascend the merkle tree authentication path
        for (i, direction_bit) in path.clone().into_iter()
                                        .enumerate() {
            let cs = &mut cs.namespace(|| format!("merkle tree hash {}", i));

            // "direction_bit" determines if the current subtree
            // is the "right" leaf at this depth of the tree.

            // Witness the authentication path element adjacent
            // at this depth.
            let path_element = &witness[i];

            // Swap the two if the current subtree is on the right
            let (xl, xr) = AllocatedNum::conditionally_reverse(
                cs.namespace(|| "conditional reversal of preimage"),
                &cur,
                path_element,
                &direction_bit
            )?;

            cur = self.hash_node(
                cs.namespace(|| "node hash computation"), 
                &[xl, xr], 
                i
            )?;
        }

        let included = AllocatedNum::equals(
            cs.namespace(|| "compare roots"), 
            &cur, 
            &root
        )?;

        Ok(included)
    }


}







    
    // checks inclusion of the leaf into the root
    fn check_inclusion_for_root<CS: ConstraintSystem<E>>(&self, mut cs: CS, root: &Self::Hash, leaf: &[Boolean], path: &[Boolean], witness: &[Self::Hash]) -> Result<Boolean, SynthesisError> {
        let leaf_hash = self.hash_leaf(
            cs.namespace(|| "leaf hash calculation"), 
            leaf
        )?;

        self.check_hash_inclusion_for_root(cs, root, &leaf_hash, path, witness)
    }
    

    // checks inclusion of the leaf hash into the root
    fn check_hash_inclusion<CS: ConstraintSystem<E>>(&self, cs: CS, hash: &Self::Hash, path: &[Boolean], witness: &[Self::Hash]) -> Result<Boolean, SynthesisError> {
        self.check_hash_inclusion_for_root(cs, &self.root, hash, path, witness)
    }
    
    // checks inclusion of the leaf hash into the root
    fn check_hash_inclusion_for_root<CS: ConstraintSystem<E>>(
        &self, 
        mut cs: CS, 
        root: &Self::Hash,
        hash: &Self::Hash, 
        path: &[Boolean], 
        witness: &[Self::Hash]
    ) -> Result<Boolean, SynthesisError> {
        // this tree is not-binary, so lookup procedure is more compicated
        let path_elements_chunks = self.branching_factor() - 1;
        // TODO: make generic later
        assert_eq!(path_elements_chunks, 3); // take by 3 elements from the witness
        assert!(witness.len() % path_elements_chunks == 0);
        assert!(witness.len() / path_elements_chunks == path.len() / self.path_bits_per_level());
        assert!(path.len() % self.path_bits_per_level() == 0);
        
        // This is an injective encoding, as cur is a
        // point in the prime order subgroup.
        let mut cur = hash.clone();

        for (chunk_number, (bits, path_elements)) in path.chunks_exact(self.path_bits_per_level())
                                                .zip(witness.chunks_exact(path_elements_chunks))
                                                .enumerate() {
            let cs = &mut cs.namespace(|| format!("merkle tree chunk {}", chunk_number));

            let mut path_to_shuffle = vec![cur];
            path_to_shuffle.extend_from_slice(&path_elements);

            assert_eq!(path_to_shuffle.len(), self.branching_factor());

            let swaps = self.calculate_swaps(
                cs.namespace(|| "calculate swaps"),
                bits
            )?;

            let (new_0, new_1) = AllocatedNum::conditionally_reverse(
                cs.namespace(|| "conditional reversal of 0 and 1"),
                &path_to_shuffle[0],
                &path_to_shuffle[1],
                &swaps[0]
            )?;

            path_to_shuffle[0] = new_0;
            path_to_shuffle[1] = new_1;

            let (new_1, new_2) = AllocatedNum::conditionally_reverse(
                cs.namespace(|| "conditional reversal of 1 and 2"),
                &path_to_shuffle[1],
                &path_to_shuffle[2],
                &swaps[1]
            )?;

            path_to_shuffle[1] = new_1;
            path_to_shuffle[2] = new_2;

            let (new_2, new_3) = AllocatedNum::conditionally_reverse(
                cs.namespace(|| "conditional reversal of 2 and 3"),
                &path_to_shuffle[2],
                &path_to_shuffle[3],
                &swaps[2]
            )?;

            path_to_shuffle[2] = new_2;
            path_to_shuffle[3] = new_3;

            cur = self.hash_node(
                cs.namespace(|| "hash round"), 
                &path_to_shuffle, 
                chunk_number
            )?;
        }

        let included = AllocatedNum::equals(
            cs.namespace(|| "compare roots"), 
            &cur, 
            &root
        )?;

        Ok(included)
    }


    fn update<CS: ConstraintSystem<E>>(&mut self, mut cs: CS, leaf: &[Boolean], path: &[Boolean], witness: &[Self::Hash]) -> Result<Self::Hash, SynthesisError> {
        let leaf_hash = self.hash_leaf(
            cs.namespace(|| "leaf hash calculation"), 
            leaf
        )?;

        self.update_from_hash(cs, &leaf_hash, path, witness)
    }

    fn update_from_hash<CS: ConstraintSystem<E>>(&mut self, mut cs: CS, hash: &Self::Hash, path: &[Boolean], witness: &[Self::Hash]) -> Result<Self::Hash, SynthesisError> {
        // this tree is not-binary, so lookup procedure is more compicated
        let path_elements_chunks = self.branching_factor() - 1;
        // TODO: make generic later
        assert_eq!(path_elements_chunks, 3);
        assert!(witness.len() % path_elements_chunks == 0);
        assert!(witness.len() / path_elements_chunks == path.len() / self.path_bits_per_level());
        assert!(path.len() % self.path_bits_per_level() == 0);
        
        // This is an injective encoding, as cur is a
        // point in the prime order subgroup.
        let mut cur = hash.clone();

        for (chunk_number, (bits, path_elements)) in path.chunks_exact(self.path_bits_per_level())
                                                .zip(witness.chunks_exact(path_elements_chunks))
                                                .enumerate() {
            let cs = &mut cs.namespace(|| format!("merkle tree chunk {}", chunk_number));

            let mut path_to_shuffle = vec![cur];
            path_to_shuffle.extend_from_slice(&path_elements);

            assert_eq!(path_to_shuffle.len(), self.branching_factor());

            let swaps = self.calculate_swaps(
                cs.namespace(|| "calculate swaps"),
                bits
            )?;

            let (new_0, new_1) = AllocatedNum::conditionally_reverse(
                cs.namespace(|| "conditional reversal of 0 and 1"),
                &path_to_shuffle[0],
                &path_to_shuffle[1],
                &swaps[0]
            )?;

            path_to_shuffle[0] = new_0;
            path_to_shuffle[1] = new_1;

            let (new_1, new_2) = AllocatedNum::conditionally_reverse(
                cs.namespace(|| "conditional reversal of 1 and 2"),
                &path_to_shuffle[1],
                &path_to_shuffle[2],
                &swaps[1]
            )?;

            path_to_shuffle[1] = new_1;
            path_to_shuffle[2] = new_2;

            let (new_2, new_3) = AllocatedNum::conditionally_reverse(
                cs.namespace(|| "conditional reversal of 2 and 3"),
                &path_to_shuffle[2],
                &path_to_shuffle[3],
                &swaps[2]
            )?;

            path_to_shuffle[2] = new_2;
            path_to_shuffle[3] = new_3;

            cur = self.hash_node(
                cs.namespace(|| "hash round"), 
                &path_to_shuffle, 
                chunk_number
            )?;
        }

        self.root = cur.clone();

        Ok(cur)
    }

    fn update_intersect<CS: ConstraintSystem<E>>(&mut self, cs: CS, leafs: (&[Boolean], &[Boolean]), paths: (&[Boolean], &[Boolean]), witnesses: (&[Self::Hash], &[Self::Hash])) -> Result<Self::Hash, SynthesisError> {
        unimplemented!();
    }

    fn update_from_hash_intersect<CS: ConstraintSystem<E>>(&mut self, cs: CS, leafs: (&Self::Hash, &Self::Hash), paths: (&[Boolean], &[Boolean]), witnesses: (&[Self::Hash], &[Self::Hash])) -> Result<Self::Hash, SynthesisError> {
        unimplemented!();
    }
}

#[test]
fn test_poseidon_quartic_tree() {
    use bellman::pairing::bn256::{Bn256, Fr};
    use bellman::pairing::ff::PrimeField;
    use crate::poseidon::{PoseidonEngine, PoseidonHashParams, self};
    use crate::poseidon::bn256::Bn256PoseidonParams;
    use crate::circuit::poseidon_hash;
    use crate::group_hash::BlakeHasher;
    use crate::circuit::test::*;
    use crate::circuit::num::AllocatedNum;
    use crate::circuit::merkle::{MerkleTree, PoseidonHashTree};

    let leaf_hashes = (0..16).map(|el| Fr::from_str(&el.to_string()).unwrap()).collect::<Vec<_>>();
    let params = Bn256PoseidonParams::new_for_quartic_tree::<BlakeHasher>();

    let mut node_hashes_1: Vec<Fr> = vec![];
    for chunk in leaf_hashes.chunks(4) {
        let hash = poseidon::poseidon_hash::<Bn256>(&params, &chunk[..]);
        node_hashes_1.push(hash[0]);
    }

    // println!("Node hashes = {:?}", node_hashes_1);

    let root_hash = poseidon::poseidon_hash::<Bn256>(&params, &node_hashes_1[..])[0];

    let element_to_proof = 15;
    let mut cs = TestConstraintSystem::<Bn256>::new();

    let input = AllocatedNum::alloc(cs.namespace(|| format!("input {}", element_to_proof)), 
    || {
        Ok(leaf_hashes[element_to_proof])
    }).unwrap();

    let root = AllocatedNum::alloc(cs.namespace(|| "expected root"), 
    || {
        Ok(root_hash)
    }).unwrap();

    let path_as_fr = AllocatedNum::alloc(cs.namespace(|| "path"), 
    || {
        Ok(Fr::from_str(&element_to_proof.to_string()).unwrap())
    }).unwrap();

    let mut path_bits = path_as_fr.into_bits_le(
        cs.namespace(|| "decompose path")
    ).unwrap();
    path_bits.truncate(4);

    let witness: Vec<AllocatedNum<Bn256>> = vec![
                        leaf_hashes[12].clone(),
                        leaf_hashes[13].clone(),
                        leaf_hashes[14].clone(),
                        node_hashes_1[0].clone(),
                        node_hashes_1[1].clone(),
                        node_hashes_1[2].clone()].into_iter().enumerate().map(|(i, el)| {
                            AllocatedNum::alloc(cs.namespace(|| format!("witness {}", i)), 
                                || {
                                    Ok(el)
                                }).unwrap()
                        }).collect();

    let zero = AllocatedNum::alloc(cs.namespace(|| "root"), 
    || {
        Ok(Fr::zero())
    }).unwrap();

    let tree = PoseidonHashTree::new(
        root.clone(), 
        2,
        2, 
        &params, 
        zero
    );

    let is_included = tree.check_hash_inclusion(
        cs.namespace(|| "check inclusion"),
        &input,
        &path_bits[..],
        &witness[..]
    ).unwrap();

    assert!(is_included.get_value().unwrap());

    println!("Tree for 16 elements and 2 levels requires {} constraints", cs.num_constraints());

    // let inputs: Vec<AllocatedNum<Bn256>> = leaf_hashes.iter().enumerate().map(|(i, b)| {
    //         AllocatedNum::alloc(cs.namespace(|| format!("input {}", i)), Some(*b)).unwrap()
    // }).collect();
}




fn pack_binary_decomposition<E, CS> (
    mut cs: CS,
    bits: &[Boolean],
) -> Result<AllocatedNum<E>, SynthesisError> 
    where E: Engine,
          CS: ConstraintSystem<E>
{
    assert!(bits.len() <= E::Fr::CAPACITY as usize);
    let mut num = Num::<E>::zero();
    let mut coeff = E::Fr::one();
    for bit in bits {
        num = num.add_bool_with_coeff(CS::one(), &bit, coeff);
        coeff.double();
    }

    let allocated = AllocatedNum::alloc(
        cs.namespace(|| "allocate packed value"),
        || Ok(*num.get_value().get()?)
    )?;

    cs.enforce(
        || "pack binary decomposition",
        |lc| lc + allocated.get_variable(),
        |lc| lc + CS::one(),
        |_| num.lc(E::Fr::one())
    );

    Ok(allocated)
}