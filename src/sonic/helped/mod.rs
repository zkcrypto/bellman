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

pub use self::batch::{Batch, VerificationKey};
pub use self::helper::{Aggregate, create_aggregate};
pub use self::verifier::{MultiVerifier};
pub use self::prover::{create_proof, create_advice};

#[derive(Clone)]
pub struct SxyAdvice<E: Engine> {
    s: E::G1Affine,
    opening: E::G1Affine,
    szy: E::Fr,
}

#[derive(Clone)]
pub struct Proof<E: Engine> {
    r: E::G1Affine,
    t: E::G1Affine,
    rz: E::Fr,
    rzy: E::Fr,
    z_opening: E::G1Affine,
    zy_opening: E::G1Affine
}