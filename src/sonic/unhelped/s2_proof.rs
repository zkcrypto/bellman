use ff::{Field};
use pairing::{Engine, CurveProjective, CurveAffine};
use std::marker::PhantomData;

use crate::sonic::srs::SRS;
use crate::sonic::util::*;

#[derive(Clone)]
pub struct S2Eval<E: Engine> {
    n: usize,
    _marker: PhantomData<E>
}

#[derive(Clone)]
pub struct S2Proof<E: Engine> {
    o: E::G1Affine,
    c_value: E::Fr,
    d_value: E::Fr,
    c_opening: E::G1Affine,
    d_opening: E::G1Affine
}

impl<E: Engine> S2Eval<E> {
    pub fn new(n: usize) -> Self {
        S2Eval {
            n: n,
            _marker: PhantomData
        }
    }

    pub fn evaluate(&self, x: E::Fr, y: E::Fr, srs: &SRS<E>) -> S2Proof<E> {
        // create a reference element first

        // TODO: parallelize
        let mut o = E::G1::zero();
        for i in 0..self.n {
            o.add_assign_mixed(&srs.g_positive_x_alpha[i]);
        }

        let mut poly = vec![E::Fr::one(); self.n+1];

        let (c, c_opening) = {
            let mut point = y;
            point.mul_assign(&x);
            let val = evaluate_at_consequitive_powers(&poly[1..], E::Fr::one(), point);
            poly[0] = val;
            poly[0].negate();
            let opening = polynomial_commitment_opening(0, self.n, poly.iter(), point, &srs);

            (val, opening)
        };

        let (d, d_opening) = {
            let mut point = y.inverse().unwrap();
            point.mul_assign(&x);
                        let val = evaluate_at_consequitive_powers(&poly[1..], E::Fr::one(), point);
            poly[0] = val;
            poly[0].negate();
            let opening = polynomial_commitment_opening(0, self.n, poly.iter(), point, &srs);

            (val, opening)
        };


        S2Proof {
            o: o.into_affine(),
            c_value: c,
            d_value: d,
            c_opening: c_opening,
            d_opening: d_opening
        }
    }

    pub fn verify(proof: &S2Proof<E>, srs: &SRS<E>) -> bool {
        true
    }

    
}