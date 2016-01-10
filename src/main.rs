#![feature(iter_arith, btree_range, collections_bound)]

extern crate tinysnark;
extern crate rand;

use tinysnark::{Proof, Keypair, FieldT, LinearTerm, ConstraintSystem};
use variable::*;
use keccak::*;
use bit::*;

mod variable;
mod keccak;
mod bit;

fn main() {
    tinysnark::init();

    let inbytes = 64;
    //for inbits in 0..1024 {
        let inbits = inbytes * 8;
        let input: Vec<Bit> = (0..inbits).map(|i| Bit::new(&Var::new(i+1))).collect();
        let input: Vec<Byte> = input.chunks(8).map(|c| Byte::from(c.to_owned())).collect();

        let output = sha3_256(&input);

        let mut counter = 1 + (8*input.len());
        let mut constraints = vec![];
        let mut witness_map = WitnessMap::new();

        for o in output.iter().flat_map(|e| e.bits().into_iter()) {
            o.walk(&mut counter, &mut constraints, &mut witness_map);
        }

        let mut vars: Vec<FieldT> = (0..counter).map(|_| FieldT::zero()).collect();
        vars[0] = FieldT::one();

        witness_field_elements(&mut vars, &witness_map);

        for b in output.iter().flat_map(|e| e.bits()) {
            print!("{}", if b.val(&vars) { 1 } else { 0 });
        }
        println!("");

        println!("{}: {} constraints", inbits, constraints.len());
    //}
}
