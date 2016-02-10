#![feature(iter_arith, btree_range, collections_bound, box_syntax)]

extern crate tinysnark;
extern crate rand;

use tinysnark::{Proof, Keypair, FieldT, LinearTerm, ConstraintSystem};
use variable::*;
use circuit::*;
use keccak::*;
use bit::*;

mod variable;
mod keccak;
mod bit;
mod circuit;
mod chacha;
mod blake2;

fn main() {
    tinysnark::init();

    let (public, private, mut circuit) = CircuitBuilder::new(512, 256);

    let private: Vec<_> = private.iter().map(|b| Bit::Constant(false)).collect();
    let mut stream = chacha::ChaCha::new(&private);

    let block = stream.next().unwrap();

    let block = block.into_iter().map(|b| b.val(&[])).collect::<Vec<_>>();

    println!("{:?}", block);
}
