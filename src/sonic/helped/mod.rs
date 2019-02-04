extern crate ff;
extern crate pairing;
// extern crate merlin;

use ff::{Field};
use pairing::{Engine, CurveProjective};
use std::marker::PhantomData;
// use merlin::{Transcript};

mod verifier;
mod prover;
mod batch;
mod poly;

pub use self::verifier::{MultiVerifier, create_aggregate};
pub use self::prover::{Aggregate, create_proof, create_advice};

// use super::super::util::*;
// pub use super::batch::Batch;
// use crate::synthesis::{Backend, SynthesisDriver};
// use crate::{Circuit, SynthesisError, Variable, Coeff};
// use crate::srs::SRS;

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