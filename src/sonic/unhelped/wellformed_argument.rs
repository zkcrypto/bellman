/// Wellformedness argument allows to verify that some committment was to multivariate polynomial of degree n, 
/// with no constant term and negative powers

use ff::{Field, PrimeField, PrimeFieldRepr};
use pairing::{Engine, CurveProjective, CurveAffine};
use std::marker::PhantomData;

use crate::sonic::srs::SRS;
use crate::sonic::util::*;

#[derive(Clone)]
pub struct WellformednessArgument<E: Engine> {
    polynomials: Vec<Vec<E::Fr>>
}

#[derive(Clone)]
pub struct WellformednessProof<E: Engine> {
    commitments: Vec<E::G1Affine>,
    challenges: Vec<E::Fr>,
    l: E::G1Affine,
    r: E::G1Affine
}

impl<E: Engine> WellformednessArgument<E> {
    pub fn new(polynomials: Vec<Vec<E::Fr>>) -> Self {
        assert!(polynomials.len() > 0);

        let length = polynomials[0].len();
        for p in polynomials.iter() {
            assert!(p.len() == length);
        }

        WellformednessArgument {
            polynomials: polynomials
        }
    }

    // Make a commitment to polynomial in a form \sum_{i=1}^{N} a_{i} X^{i} Y^{i}
    pub fn commit(&self, srs: &SRS<E>) -> Vec<E::G1Affine> {

        let mut results = vec![];

        let n = self.polynomials[0].len();

        for p in self.polynomials.iter() {
            let c = multiexp(
                srs.g_positive_x_alpha[0..n].iter(),
                p.iter()
            ).into_affine();
            
            results.push(c);
        }

        results
    }

    pub fn make_argument(self, challenges: Vec<E::Fr>, srs: &SRS<E>) -> WellformednessProof<E> {
        let commitments = self.commit(&srs);

        assert_eq!(commitments.len(), challenges.len());

        let mut polynomials = self.polynomials;
        let mut challenges = challenges;



        let mut p0 = polynomials.pop().unwrap();
        let r0 = challenges.pop().unwrap();
        let n = p0.len();
        mul_polynomial_by_scalar(&mut p0[..], r0);

        let m = polynomials.len();

        for _ in 0..m {
            let p = polynomials.pop().unwrap();
            let r = challenges.pop().unwrap();
            mul_add_polynomials(&mut p0[..], & p[..], r);
        }

        let d = srs.d;

        // here the multiplier is x^-d, so largest negative power is -d + 1
        let l = polynomial_commitment::<E, _>(
            n, 
            d - 1,
            0, 
            &srs,
            p0.iter());

        // here the multiplier is x^d-n, so largest positive power is d

        let r = polynomial_commitment::<E, _>(
            n, 
            0,
            d, 
            &srs,
            p0.iter());

        WellformednessProof {
            commitments: commitments,
            challenges: challenges,
            l: l,
            r: r
        }

    }


    // pub fn verify(challenges: Vec<E::Fr>, proof: &WellformednessProof<E>, srs: &SRS<E>) -> bool {

    //     // e(C,hαx)e(C−yz,hα) = e(O,h)e(g−c,hα)

    //     let alpha_x_precomp = srs.h_positive_x_alpha[1].prepare();
    //     let alpha_precomp = srs.h_positive_x_alpha[0].prepare();
    //     let mut h_prep = srs.h_positive_x[0];
    //     h_prep.negate();
    //     let h_prep = h_prep.prepare();

    //     let mut c_minus_xy = proof.c_value;
    //     let mut xy = x;
    //     xy.mul_assign(&y);

    //     c_minus_xy.sub_assign(&xy);

    //     let mut c_in_c_minus_xy = proof.c_opening.mul(c_minus_xy.into_repr()).into_affine();

    //     let valid = E::final_exponentiation(&E::miller_loop(&[
    //             (&proof.c_opening.prepare(), &alpha_x_precomp),
    //             (&c_in_c_minus_xy.prepare(), &alpha_precomp),
    //             (&proof.o.prepare(), &h_prep),
    //         ])).unwrap() == E::Fqk::one();

    //     if !valid {
    //         return false;
    //     } 

    //     // e(D,hαx)e(D−y−1z,hα) = e(O,h)e(g−d,hα)

    //     let mut d_minus_x_y_inv = proof.d_value;
    //     let mut x_y_inv = x;
    //     x_y_inv.mul_assign(&y.inverse().unwrap());

    //     d_minus_x_y_inv.sub_assign(&x_y_inv);

    //     let mut d_in_d_minus_x_y_inv = proof.d_opening.mul(d_minus_x_y_inv.into_repr()).into_affine();

    //     let valid = E::final_exponentiation(&E::miller_loop(&[
    //             (&proof.d_opening.prepare(), &alpha_x_precomp),
    //             (&d_in_d_minus_x_y_inv.prepare(), &alpha_precomp),
    //             (&proof.o.prepare(), &h_prep),
    //         ])).unwrap() == E::Fqk::one();

    //     if !valid {
    //         return false;
    //     } 

    //     true
    // }
}