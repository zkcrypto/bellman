extern crate ff;
extern crate pairing;

use ff::{Field};
use pairing::{Engine, CurveProjective};
use std::marker::PhantomData;

mod verifier;
mod prover;
mod batch;
mod poly;
mod helper;

pub use self::batch::{Batch, VerifyingKey};
pub use self::helper::{Aggregate, create_aggregate};
pub use self::verifier::{MultiVerifier};
pub use self::prover::{create_proof, create_advice};

#[derive(Clone, Debug)]
pub struct SxyAdvice<E: Engine> {
    pub s: E::G1Affine,
    pub opening: E::G1Affine,
    pub szy: E::Fr,
}

#[derive(Clone, Debug)]
pub struct Proof<E: Engine> {
    pub r: E::G1Affine,
    pub t: E::G1Affine,
    pub rz: E::Fr,
    pub rzy: E::Fr,
    pub z_opening: E::G1Affine,
    pub zy_opening: E::G1Affine
}