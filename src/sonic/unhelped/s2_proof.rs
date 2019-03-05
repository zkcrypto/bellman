use pairing::ff::{Field, PrimeField, PrimeFieldRepr};
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
    pub fn calculate_commitment_element(n: usize, srs: &SRS<E>) -> E::G1Affine {
        // TODO: parallelize
        let mut o = E::G1::zero();
        for i in 0..n {
            o.add_assign_mixed(&srs.g_positive_x_alpha[i]);
        }

        o.into_affine()
    }

    pub fn new(n: usize) -> Self {
        S2Eval {
            n: n,
            _marker: PhantomData
        }
    }

    pub fn evaluate(&self, x: E::Fr, y: E::Fr, srs: &SRS<E>) -> S2Proof<E> {
        // create a reference element first

        let o = Self::calculate_commitment_element(self.n, &srs);

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
            o: o,
            c_value: c,
            d_value: d,
            c_opening: c_opening,
            d_opening: d_opening
        }
    }

    pub fn verify(x: E::Fr, y: E::Fr, proof: &S2Proof<E>, srs: &SRS<E>) -> bool {

        // e(C,hαx)e(C−yz,hα) = e(O,h)e(g−c,hα)

        let alpha_x_precomp = srs.h_positive_x_alpha[1].prepare();
        let alpha_precomp = srs.h_positive_x_alpha[0].prepare();
        let mut h_prep = srs.h_positive_x[0];
        h_prep.negate();
        let h_prep = h_prep.prepare();

        let mut c_minus_xy = proof.c_value;
        let mut xy = x;
        xy.mul_assign(&y);

        c_minus_xy.sub_assign(&xy);

        let c_in_c_minus_xy = proof.c_opening.mul(c_minus_xy.into_repr()).into_affine();

        let valid = E::final_exponentiation(&E::miller_loop(&[
                (&proof.c_opening.prepare(), &alpha_x_precomp),
                (&c_in_c_minus_xy.prepare(), &alpha_precomp),
                (&proof.o.prepare(), &h_prep),
            ])).unwrap() == E::Fqk::one();

        if !valid {
            return false;
        } 

        // e(D,hαx)e(D−y−1z,hα) = e(O,h)e(g−d,hα)

        let mut d_minus_x_y_inv = proof.d_value;
        let mut x_y_inv = x;
        x_y_inv.mul_assign(&y.inverse().unwrap());

        d_minus_x_y_inv.sub_assign(&x_y_inv);

        let d_in_d_minus_x_y_inv = proof.d_opening.mul(d_minus_x_y_inv.into_repr()).into_affine();

        let valid = E::final_exponentiation(&E::miller_loop(&[
                (&proof.d_opening.prepare(), &alpha_x_precomp),
                (&d_in_d_minus_x_y_inv.prepare(), &alpha_precomp),
                (&proof.o.prepare(), &h_prep),
            ])).unwrap() == E::Fqk::one();

        if !valid {
            return false;
        } 

        true
    }
}