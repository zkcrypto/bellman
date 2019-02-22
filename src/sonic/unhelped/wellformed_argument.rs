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

        assert!(n < d);

        // here the multiplier is x^-d, so largest negative power is -(d - 1), smallest negative power is -(d - n)
        let l = multiexp(
                srs.g_negative_x[(d - n)..(d - 1)].iter().rev(),
                p0.iter()
            ).into_affine();

        // here the multiplier is x^d-n, so largest positive power is d, smallest positive power is d - n + 1

        let r = multiexp(
                srs.g_positive_x[(d - n + 1)..].iter().rev(),
                p0.iter()
            ).into_affine();

        WellformednessProof {
            commitments: commitments,
            l: l,
            r: r
        }

    }

    pub fn verify(n: usize, challenges: Vec<E::Fr>, proof: &WellformednessProof<E>, srs: &SRS<E>) -> bool {
        let d = srs.d;

        let alpha_x_d_precomp = srs.h_positive_x_alpha[d].prepare();
        let alpha_x_n_minus_d_precomp = srs.h_negative_x_alpha[d - n].prepare();
        let mut h_prep = srs.h_positive_x[0];
        h_prep.negate();
        let h_prep = h_prep.prepare();

        let a = multiexp(
            proof.commitments.iter(),
            challenges.iter(),
        ).into_affine();

        let a = a.prepare();

        let valid = E::final_exponentiation(&E::miller_loop(&[
                (&a, &h_prep),
                (&proof.l.prepare(), &alpha_x_d_precomp)
            ])).unwrap() == E::Fqk::one();

        if !valid {
            return false;
        } 

        let valid = E::final_exponentiation(&E::miller_loop(&[
                (&a, &h_prep),
                (&proof.r.prepare(), &alpha_x_n_minus_d_precomp)
            ])).unwrap() == E::Fqk::one();

        if !valid {
            return false;
        } 

        true
    }
}