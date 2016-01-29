#![feature(iter_arith, btree_range, collections_bound)]

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

fn main() {

}