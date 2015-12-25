extern crate tinysnark;
extern crate rand;

use tinysnark::{Proof, Keypair, FieldT, LinearTerm, ConstraintSystem};

fn main() {
    tinysnark::init();

    let mut cs = ConstraintSystem::new(1, 2);
    cs.add_constraint(
        &[LinearTerm{coeff: FieldT::one(), index: 2}],
        &[LinearTerm{coeff: FieldT::one(), index: 3}],
        &[LinearTerm{coeff: FieldT::one(), index: 1}]
    );
    assert!(cs.test(&[100.into()], &[10.into(), 10.into()]));
}
