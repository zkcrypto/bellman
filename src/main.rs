#![feature(clone_from_slice)]

extern crate tinysnark;
extern crate rand;

use tinysnark::{Proof, Keypair, FieldT, LinearTerm, ConstraintSystem};
use std::marker::PhantomData;

mod keccak;

fn main() {
    tinysnark::init();

    /*
    let mut cs = ConstraintSystem::new(2, 1);
    // xor
    // (2*b) * c = b+c - a
    cs.add_constraint(
        &[LinearTerm{coeff: FieldT::from(2), index: 2}],
        &[LinearTerm{coeff: FieldT::one(), index: 3}],
        &[LinearTerm{coeff: FieldT::one(), index: 2},
          LinearTerm{coeff: FieldT::one(), index: 3},
          LinearTerm{coeff: -FieldT::one(), index: 1}]
    );
    let prompt = [0.into(), 1.into()];
    let solution = [1.into()];
    assert!(cs.test(&prompt, &solution));
    let kp = Keypair::new(&cs);
    let proof = Proof::new(&kp, &prompt, &solution);
    assert!(proof.verify(&kp, &prompt));
    */
}
