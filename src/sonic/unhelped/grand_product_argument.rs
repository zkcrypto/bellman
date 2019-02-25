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
    a_polynomials: Vec<Vec<E::Fr>>,
    c_polynomials: Vec<Vec<E::Fr>>,
    v_elements: Vec<E::Fr>,
    n: usize
}

#[derive(Clone)]
pub struct GrandProductProof<E: Engine> {
    l: E::G1Affine,
    r: E::G1Affine
}

impl<E: Engine> GrandProductArgument<E> {
    pub fn new(polynomials: Vec<(Vec<E::Fr>, Vec<E::Fr>)>) -> Self {
        assert!(polynomials.len() > 0);

        let n = polynomials[0].0.len();
        let mut a_polynomials = vec![];
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

        for p in polynomials.into_iter() {
            let (p0, p1) = p;
            assert!(p0.len() == p1.len());
            assert!(p0.len() == n);
            let mut c_poly: Vec<E::Fr> = Vec::with_capacity(2*n + 1);
            let mut a_poly: Vec<E::Fr> = Vec::with_capacity(2*n + 1);
            let mut c_coeff = E::Fr::one();
            // add a
            for a in p0.iter() {
                c_coeff.mul_assign(a);
                c_poly.push(c_coeff);
            }
            assert_eq!(c_poly.len(), n);
            a_poly.extend(p0);
            a_poly.push(c_poly[n - 2].inverse().unwrap());
            // a_{n+1} = c_{n-1}^-1
            let v = c_coeff.inverse().unwrap();
            // add c_{n+1}
            let mut c_coeff = E::Fr::one();
            c_poly.push(c_coeff);
            // add b
            for b in p1.iter() {
                c_coeff.mul_assign(b);
                c_poly.push(c_coeff);
            }
            assert_eq!(c_poly.len(), 2*n + 1);
            a_poly.extend(p1);
            a_polynomials.push(a_poly);
            c_polynomials.push(c_poly);
            v_elements.push(v);
        }

        GrandProductArgument {
            a_polynomials: a_polynomials,
            c_polynomials: c_polynomials,
            v_elements: v_elements,
            n: n
        }
    }

    // Make a commitment for the begining of the protocol, returns commitment and `v` scalar
    pub fn commit(&self, srs: &SRS<E>) -> Vec<(E::G1Affine, E::Fr)> {

        let mut results = vec![];

        let n = self.c_polynomials[0].len();

        for (p, v) in self.c_polynomials.iter().zip(self.v_elements.iter()) {
            let c = multiexp(
                srs.g_positive_x_alpha[0..n].iter(),
                p.iter()
            ).into_affine();
            
            results.push((c, *v));
        }

        results
    }

    // Argument is based on an approach of main SONIC construction, but with a custom S(X,Y) polynomial of a simple form
    pub fn evaluate_t_polynomial(&self, challenges: Vec<E::Fr>, y: E::Fr, srs: &SRS<E>) -> E::G1Affine {
        assert_eq!(challenges.len(), self.a_polynomials.len());

        let n = self.n;

        let mut t_polynomial: Option<Vec<E::Fr>> = None;

        for (((a, c), v), challenge) in self.a_polynomials.iter()
                                        .zip(self.c_polynomials.iter())
                                        .zip(self.v_elements.iter())
                                        .zip(challenges.into_iter())
        {
            let mut a_xy = a.clone();
            let mut c_xy = c.clone();
            let v = *v;

            assert_eq!(a_xy.len(), 2*n + 1);

            // make a T polynomial

            let r: Vec<E::Fr> = {
                // p_a(X,Y)*Y
                let mut tmp = y;
                tmp.square();
                mut_distribute_consequitive_powers(&mut a_xy[..], tmp, y);

                // add extra terms 
                //v*(XY)^{n+1}*Y + X^{n+2} + X^{n+1}Y − X^{2n+2}*Y

                // n+1 term v*(XY)^{n+1}*Y + X^{n+1}Y 
                let tmp = y.pow(&[(n+2) as u64]);
                let mut x_n_plus_one_term = v;
                x_n_plus_one_term.mul_assign(&tmp);
                x_n_plus_one_term.add_assign(&y);
                a_xy[n].add_assign(&x_n_plus_one_term);

                // n+2 term 
                a_xy[n+1].add_assign(&E::Fr::one());

                // 2n+2 term 
                let mut tmp = y;
                tmp.negate();
                a_xy.push(tmp);

                assert_eq!(a_xy.len(), 2*n + 2);

                let mut r = vec![E::Fr::zero(); 2*n+3];
                r.extend(a_xy);

                r
            };

            // calculate product of the full term made of `a` poly with c(X^{-1}, 1) + X^-1
            let r_prime: Vec<E::Fr> = {
                let mut c_prime: Vec<E::Fr> = c_xy.iter().rev().map(|el| *el).collect();
                c_prime.push(E::Fr::one());
                c_prime.push(E::Fr::zero());

                c_prime
            };

            let mut t: Vec<E::Fr> = multiply_polynomials::<E>(r, r_prime);

            let mut val = {
                let mut tmp = y;
                tmp.square();
                evaluate_at_consequitive_powers(&c_xy, tmp, y)
            };

            val.add_assign(&E::Fr::one());

            t[2*n+2].sub_assign(&val);
            if t_polynomial.is_some() {
                if let Some(t_poly) = t_polynomial.as_mut() {
                    mul_add_polynomials(&mut t_poly[..], &t, challenge);
                } 
            } else {
                mul_polynomial_by_scalar(&mut t, challenge);
                t_polynomial = Some(t);
            }
        }

        let t_polynomial = t_polynomial.unwrap();

        polynomial_commitment(
            srs.d,
            2*n + 2, 
            2*n + 2, 
            srs, 
            t_polynomial.iter()
        )
    }

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

