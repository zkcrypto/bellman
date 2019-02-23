/// One must prove that for commitments to two polynomials of degree n products of the coefficients 
/// in those two polynomials are equal (part of the permutation argument) with additional assumption that
/// those coefficients are never equal to zero

use ff::{Field, PrimeField, PrimeFieldRepr};
use pairing::{Engine, CurveProjective, CurveAffine};
use std::marker::PhantomData;

use crate::sonic::srs::SRS;
use crate::sonic::util::*;

#[derive(Clone)]
pub struct GrandProductArgument<E: Engine> {
    c_polynomials: Vec<Vec<E::Fr>>,
    v_elements: Vec<E::Fr>
}

#[derive(Clone)]
pub struct GrandProductProof<E: Engine> {
    l: E::G1Affine,
    r: E::G1Affine
}

impl<E: Engine> GrandProductArgument<E> {
    pub fn new(polynomials: Vec<(Vec<E::Fr>, Vec<E::Fr>)>) -> Self {
        assert!(polynomials.len() > 0);

        let length = polynomials[0].0.len();
        let mut c_polynomials = vec![];
        let mut v_elements = vec![];

        // a_{1..n} = first poly
        // a_{n+1..2n+1} = b_{1..n} = second poly

        // c_1 = a_1
        // c_2 = a_2 * c_1 = a_2 * a_1
        // c_3 = a_3 * c_2 = a_3 * a_2 * a_1
        // ...
        // c_n = a_n * c_{n-1} = \prod a_i
        // a_{n+1} = c_{n-1}^-1
        // c_{n+1} = 1
        // c_{n+1} = a_{n+2} * c_{n+1} = a_{n+2}
        // ...
        // c_{2n+1} = \prod a_{n+1+i} = \prod b_{i}
        // v = c_{n}^-1

        // calculate c, serially for now

        for p in polynomials.iter() {
            assert!(p.0.len() == p.1.len());
            assert!(p.0.len() == length);
            let mut c_poly: Vec<E::Fr> = Vec::with_capacity(2*length + 1);
            let mut c_coeff = E::Fr::one();
            // add a
            for a in p.0.iter() {
                c_coeff.mul_assign(a);
                c_poly.push(c_coeff);
            }
            let v = c_coeff.inverse().unwrap();
            // add c_{n+1}
            let mut c_coeff = E::Fr::one();
            c_poly.push(c_coeff);
            // add b
            for b in p.1.iter() {
                c_coeff.mul_assign(b);
                c_poly.push(c_coeff);
            }

            assert_eq!(c_poly.len(), 2*length + 1);
            c_polynomials.push(c_poly);
            v_elements.push(v);
        }

        GrandProductArgument {
            c_polynomials: c_polynomials,
            v_elements: v_elements
        }
    }

    // // Make a commitment to polynomial in a form \sum_{i=1}^{N} a_{i} X^{i} Y^{i}
    // pub fn commit(&self, srs: &SRS<E>) -> Vec<E::G1Affine> {

    //     let mut results = vec![];

    //     let n = self.polynomials[0].len();

    //     for p in self.polynomials.iter() {
    //         let c = multiexp(
    //             srs.g_positive_x_alpha[0..n].iter(),
    //             p.iter()
    //         ).into_affine();
            
    //         results.push(c);
    //     }

    //     results
    // }

    // pub fn make_argument(self, challenges: Vec<E::Fr>, srs: &SRS<E>) -> WellformednessProof<E> {
    //     let mut polynomials = self.polynomials;
    //     let mut challenges = challenges;

    //     let mut p0 = polynomials.pop().unwrap();
    //     let r0 = challenges.pop().unwrap();
    //     let n = p0.len();
    //     mul_polynomial_by_scalar(&mut p0[..], r0);

    //     let m = polynomials.len();

    //     for _ in 0..m {
    //         let p = polynomials.pop().unwrap();
    //         let r = challenges.pop().unwrap();
    //         mul_add_polynomials(&mut p0[..], & p[..], r);
    //     }

    //     let d = srs.d;

    //     assert!(n < d);

    //     // here the multiplier is x^-d, so largest negative power is -(d - 1), smallest negative power is -(d - n)
    //     let l = multiexp(
    //             srs.g_negative_x[(d - n)..d].iter().rev(),
    //             p0.iter()
    //         ).into_affine();

    //     // here the multiplier is x^d-n, so largest positive power is d, smallest positive power is d - n + 1

    //     let r = multiexp(
    //             srs.g_positive_x[(d - n + 1)..].iter().rev(),
    //             p0.iter()
    //         ).into_affine();

    //     WellformednessProof {
    //         l: l,
    //         r: r
    //     }
    // }

    // pub fn verify(n: usize, challenges: &Vec<E::Fr>, commitments: &Vec<E::G1Affine>, proof: &WellformednessProof<E>, srs: &SRS<E>) -> bool {
    //     let d = srs.d;

    //     let alpha_x_d_precomp = srs.h_positive_x_alpha[d].prepare();
    //     let alpha_x_n_minus_d_precomp = srs.h_negative_x_alpha[d - n].prepare();
    //     let mut h_prep = srs.h_positive_x[0];
    //     h_prep.negate();
    //     let h_prep = h_prep.prepare();

    //     let a = multiexp(
    //         commitments.iter(),
    //         challenges.iter(),
    //     ).into_affine();

    //     let a = a.prepare();

    //     let valid = E::final_exponentiation(&E::miller_loop(&[
    //             (&a, &h_prep),
    //             (&proof.l.prepare(), &alpha_x_d_precomp)
    //         ])).unwrap() == E::Fqk::one();

    //     if !valid {
    //         return false;
    //     } 

    //     let valid = E::final_exponentiation(&E::miller_loop(&[
    //             (&a, &h_prep),
    //             (&proof.r.prepare(), &alpha_x_n_minus_d_precomp)
    //         ])).unwrap() == E::Fqk::one();

    //     if !valid {
    //         return false;
    //     } 

    //     true
    // }
}

// #[test]
// fn test_argument() {
//     use pairing::bls12_381::{Fr, G1Affine, G1, Bls12};
//     use rand::{XorShiftRng, SeedableRng, Rand, Rng};
//     use crate::sonic::srs::SRS;

//     let srs_x = Fr::from_str("23923").unwrap();
//     let srs_alpha = Fr::from_str("23728792").unwrap();
//     let srs = SRS::<Bls12>::dummy(830564, srs_x, srs_alpha);

//     let n: usize = 1 << 16;
//     let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
//     let coeffs = (0..n).map(|_| Fr::rand(rng)).collect::<Vec<_>>();

//     let argument = WellformednessArgument::new(vec![coeffs]);
//     let challenges = (0..1).map(|_| Fr::rand(rng)).collect::<Vec<_>>();

//     let commitments = argument.commit(&srs);

//     let proof = argument.make_argument(challenges.clone(), &srs);

//     let valid = WellformednessArgument::verify(n, &challenges, &commitments,  &proof, &srs);

//     assert!(valid);
// }

// #[test]
// fn test_argument_soundness() {
//     use pairing::bls12_381::{Fr, G1Affine, G1, Bls12};
//     use rand::{XorShiftRng, SeedableRng, Rand, Rng};
//     use crate::sonic::srs::SRS;

//     let srs_x = Fr::from_str("23923").unwrap();
//     let srs_alpha = Fr::from_str("23728792").unwrap();
//     let srs = SRS::<Bls12>::dummy(830564, srs_x, srs_alpha);

//     let n: usize = 1 << 16;
//     let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
//     let coeffs = (0..n).map(|_| Fr::rand(rng)).collect::<Vec<_>>();

//     let argument = WellformednessArgument::new(vec![coeffs]);
//     let commitments = argument.commit(&srs);

//     let coeffs = (0..n).map(|_| Fr::rand(rng)).collect::<Vec<_>>();
//     let argument = WellformednessArgument::new(vec![coeffs]);
//     let challenges = (0..1).map(|_| Fr::rand(rng)).collect::<Vec<_>>();

//     let proof = argument.make_argument(challenges.clone(), &srs);

//     let valid = WellformednessArgument::verify(n, &challenges, &commitments,  &proof, &srs);

//     assert!(!valid);
// }

