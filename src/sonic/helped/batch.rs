//! Our protocol allows the verification of multiple proofs and even
//! of individual proofs to batch the pairing operations such that
//! only a smaller, fixed number of pairings must occur for an entire
//! batch of proofs. This is possible because G2 elements are fixed
//! in our protocol and never appear in proofs; everything can be
//! combined probabilistically.
//!
//! This submodule contains the `Batch` abstraction for creating a
//! context for batch verification.

use crate::pairing::ff::{Field};
use crate::pairing::{Engine, CurveAffine, CurveProjective};

use crate::SynthesisError;

use crate::sonic::cs::{Backend, SynthesisDriver};
use crate::sonic::cs::{Circuit};

use super::parameters::VerifyingKey;

use crate::sonic::srs::SRS;
use crate::sonic::util::multiexp;

use std::marker::PhantomData;

// One of the primary functions of the `Batch` abstraction is handling
// Kate commitment openings:
//
// e(P', [\alpha(x - z)] H) = e(P, H) e([-v] G, [\alpha] H)
// ==> e(P', [\alpha x] H) e([-z] P', [\alpha] H) = e(P, H) e([-v] G, [\alpha] H)
//
// Many of these can be opened simultaneously by sampling random `r` and
// accumulating...
//
// e([r] P', [\alpha x] H)
// e([-rz] P', [\alpha] H)
// e([r] P, -H)
// e([rv] G, [\alpha] H)
//
// ... and checking that the result is the identity in the target group.
pub struct Batch<E: Engine> {
    alpha_x: Vec<(E::G1Affine, E::Fr)>,
    alpha_x_precomp: <E::G2Affine as CurveAffine>::Prepared,

    alpha: Vec<(E::G1Affine, E::Fr)>,
    alpha_precomp: <E::G2Affine as CurveAffine>::Prepared,

    neg_h: Vec<(E::G1Affine, E::Fr)>,
    neg_h_precomp: <E::G2Affine as CurveAffine>::Prepared,

    neg_x_n_minus_d: Vec<(E::G1Affine, E::Fr)>,
    neg_x_n_minus_d_precomp: <E::G2Affine as CurveAffine>::Prepared,

    // The value paired with [\alpha] H, accumulated in the field
    // to save group operations.
    value: E::Fr,
    g: E::G1Affine,
}

impl<E: Engine> Batch<E> {
    pub fn new(srs: &SRS<E>, n: usize) -> Self {
        Batch {
            alpha_x: vec![],
            alpha_x_precomp: srs.h_positive_x_alpha[1].prepare(),

            alpha: vec![],
            alpha_precomp: srs.h_positive_x_alpha[0].prepare(),

            neg_h: vec![],
            neg_h_precomp: {
                let mut tmp = srs.h_negative_x[0];
                tmp.negate();
                tmp.prepare()
            },

            neg_x_n_minus_d: vec![],
            neg_x_n_minus_d_precomp: {
                let mut tmp = srs.h_negative_x[srs.d - n];
                tmp.negate();
                tmp.prepare()
            },

            value: E::Fr::zero(),
            g: srs.g_positive_x[0],
        }
    }

    pub fn new_from_key(vk: &VerifyingKey<E>) -> Self {
        Batch {
            alpha_x: vec![],
            alpha_x_precomp: vk.alpha_x.prepare(),

            alpha: vec![],
            alpha_precomp: vk.alpha.prepare(),

            neg_h: vec![],
            neg_h_precomp: vk.neg_h.prepare(),

            neg_x_n_minus_d: vec![],
            neg_x_n_minus_d_precomp: vk.neg_x_n_minus_d.prepare(),

            value: E::Fr::zero(),
            g: E::G1Affine::one(),
        }
    }

    /// add `(r*P) to the h^(alpha*x) terms, add -(r*point)*P to h^(alpha) terms 
    pub fn add_opening(&mut self, p: E::G1Affine, mut r: E::Fr, point: E::Fr) {
        self.alpha_x.push((p, r));
        r.mul_assign(&point);
        r.negate();
        self.alpha.push((p, r));
    }

    /// add (r*P) to -h^(x) terms
    pub fn add_commitment(&mut self, p: E::G1Affine, r: E::Fr) {
        self.neg_h.push((p, r));
    }

    /// add (r*P) to -h^(d-n) terms
    pub fn add_commitment_max_n(&mut self, p: E::G1Affine, r: E::Fr) {
        self.neg_x_n_minus_d.push((p, r));
    }

    /// add (r*point) to g terms for later pairing with h^(alpha)
    pub fn add_opening_value(&mut self, mut r: E::Fr, point: E::Fr) {
        r.mul_assign(&point);
        self.value.add_assign(&r);
    }

    pub fn check_all(mut self) -> bool {
        self.alpha.push((self.g, self.value));

        let alpha_x = multiexp(
            self.alpha_x.iter().map(|x| &x.0),
            self.alpha_x.iter().map(|x| &x.1),
        ).into_affine();

        let alpha_x = alpha_x.prepare();

        let alpha = multiexp(
            self.alpha.iter().map(|x| &x.0),
            self.alpha.iter().map(|x| &x.1),
        ).into_affine();

        let alpha = alpha.prepare();

        let neg_h = multiexp(
            self.neg_h.iter().map(|x| &x.0),
            self.neg_h.iter().map(|x| &x.1),
        ).into_affine();

        let neg_h = neg_h.prepare();

        let neg_x_n_minus_d = multiexp(
            self.neg_x_n_minus_d.iter().map(|x| &x.0),
            self.neg_x_n_minus_d.iter().map(|x| &x.1),
        ).into_affine();

        let neg_x_n_minus_d = neg_x_n_minus_d.prepare();

        E::final_exponentiation(&E::miller_loop(&[
            (&alpha_x, &self.alpha_x_precomp),
            (&alpha, &self.alpha_precomp),
            (&neg_h, &self.neg_h_precomp),
            (&neg_x_n_minus_d, &self.neg_x_n_minus_d_precomp),
        ])).unwrap() == E::Fqk::one()
    }
}