/// Permutation argument allows to prove that a commitment to a vector A is 
/// actually a commitment to a vector of values that are equal to `(s^{perm})_i * y^{perm(i)}`
/// for some fixed permutation `perm`

use ff::{Field, PrimeField, PrimeFieldRepr, ScalarEngine};
use pairing::{Engine, CurveProjective, CurveAffine};
use std::marker::PhantomData;

use crate::sonic::srs::SRS;
use crate::sonic::util::*;

#[derive(Clone)]
pub struct SpecializedSRS<E: Engine> {
    p_1: E::G1Affine,
    p_2: Vec<E::G1Affine>,
    p_3: E::G1Affine,
    p_4: Vec<E::G1Affine>,
    n: usize
}

#[derive(Clone)]
pub struct PermutationArgument<E: Engine> {
    non_permuted_coefficients: Vec<Vec<E::Fr>>,
    permuted_coefficients: Vec<Vec<E::Fr>>,
    permutations: Vec<Vec<usize>>,
    n: usize
}

#[derive(Clone)]
pub struct PermutationProof<E: Engine> {
    v_zy: E::Fr,
    e_opening: E::G1Affine,
    f_opening: E::G1Affine,
}


fn permute<F: Field>(coeffs: &[F], permutation: & [usize]) -> Vec<F>{
    assert_eq!(coeffs.len(), permutation.len());
    let mut result: Vec<F> = vec![F::zero(); coeffs.len()];
    for (i, j) in permutation.iter().enumerate() {
        result[*j] = coeffs[i];
    }
    result
}

impl<E: Engine> PermutationArgument<E> {
    pub fn new(coefficients: Vec<Vec<E::Fr>>, permutations: Vec<Vec<usize>>) -> Self {
        assert!(coefficients.len() > 0);
        assert_eq!(coefficients.len(), permutations.len());

        let n = coefficients[0].len();

        for (c, p) in coefficients.iter().zip(permutations.iter()) {
            assert!(c.len() == p.len());
            assert!(c.len() == n);
        }

        PermutationArgument {
            non_permuted_coefficients: coefficients,
            permuted_coefficients: vec![vec![]],
            permutations: permutations,
            n: n
        }
    }

    pub fn make_specialized_srs(non_permuted_coefficients: &Vec<Vec<E::Fr>>, permutations: &Vec<Vec<usize>>, srs: &SRS<E>) -> SpecializedSRS<E> {
        assert!(non_permuted_coefficients.len() > 0);
        assert_eq!(non_permuted_coefficients.len(), permutations.len());

        let n = non_permuted_coefficients[0].len();

        // p1 is just a commitment to the powers of x
        let p_1 = multiexp(srs.g_positive_x_alpha[0..n].iter(), vec![E::Fr::one(); n].iter()).into_affine();

        let mut p_2 = vec![];

        let p_3 = {
            let values: Vec<E::Fr> = (1..=n).map(|el| {
                let mut repr = <<E as ScalarEngine>::Fr as PrimeField>::Repr::default();
                repr.as_mut()[0] = el as u64;
                let fe = E::Fr::from_repr(repr).unwrap();

                fe
            }).collect();

            multiexp(srs.g_positive_x_alpha[0..n].iter(), values.iter()).into_affine()
        };

        let mut p_4 = vec![];

        for (c, p) in non_permuted_coefficients.iter().zip(permutations.iter()) {
            assert!(c.len() == p.len());
            assert!(c.len() == n);

            // p2 is a commitment to the s^{perm}_i * x^i
            {
                // let permuted_coeffs = permute(&c[..], &p[..]);
                let p2 = multiexp(srs.g_positive_x_alpha[0..n].iter(), c.iter()).into_affine();
                p_2.push(p2);
            }

            {
                let values: Vec<E::Fr> = p.iter().map(|el| {
                    let mut repr = <<E as ScalarEngine>::Fr as PrimeField>::Repr::default();
                    repr.as_mut()[0] = *el as u64;
                    let fe = E::Fr::from_repr(repr).unwrap();

                    fe
                }).collect();
                let p4 = multiexp(srs.g_positive_x_alpha[0..n].iter(), values.iter()).into_affine();
                p_4.push(p4);
            }
        }

        SpecializedSRS {
            p_1: p_1,
            p_2: p_2,
            p_3: p_3,
            p_4: p_4,
            n: n
        }
    }

    // commit to s and s' at y. Mutates the state
    pub fn commit(&mut self, y: E::Fr, srs: &SRS<E>) -> Vec<(E::G1Affine, E::G1Affine)> {
        let mut result = vec![];

        let n = self.non_permuted_coefficients[0].len();

        let mut permuted_coefficients = vec![];

        for (c, p) in self.non_permuted_coefficients.iter().zip(self.permutations.iter()) {
            let mut non_permuted = c.clone();
            let permuted = permute(&non_permuted[..], &p[..]);

            mut_distribute_consequitive_powers(&mut non_permuted[..], y, y);
            let s_prime = multiexp(srs.g_positive_x_alpha[0..n].iter(), non_permuted.iter()).into_affine();

            let mut permuted_at_y = permute(&non_permuted[..], &p[..]);
            drop(non_permuted);

            let s = multiexp(srs.g_positive_x_alpha[0..n].iter(), permuted_at_y.iter()).into_affine();

            result.push((s, s_prime));

            permuted_coefficients.push(permuted);
        }

        self.permuted_coefficients = permuted_coefficients;

        result
    }

    pub fn open_commitments_to_s(&self, challenges: &Vec<E::Fr>, y: E::Fr, z_prime: E::Fr, srs: &SRS<E>) -> PermutationProof<E> {
        let n = self.non_permuted_coefficients[0].len();

        let mut yz = y;
        yz.mul_assign(&z_prime);

        let mut polynomial: Option<Vec<E::Fr>> = None;

        for (p, r) in self.non_permuted_coefficients.iter()
                    .zip(challenges.iter()) {
            if polynomial.is_some() {
                if let Some(poly) = polynomial.as_mut() {
                    mul_add_polynomials(&mut poly[..], &p[..], *r);
                }
            } else {
                let mut poly = p.clone();
                mul_polynomial_by_scalar(&mut poly[..], *r);

            }
        }

        let mut polynomial = polynomial.unwrap();
        let v = evaluate_at_consequitive_powers(&polynomial[..], yz, yz);

        let mut v_neg = v;
        v_neg.negate();

        let e = polynomial_commitment_opening(
            0, 
            n, 
            Some(v_neg).iter().chain_ext(polynomial.iter()), 
            yz, 
            &srs
        );

        mut_distribute_consequitive_powers(&mut polynomial[..], y, y);

        let f = polynomial_commitment_opening(
            0, 
            n, 
            Some(v_neg).iter().chain_ext(polynomial.iter()), 
            z_prime, 
            &srs
        );

        PermutationProof {
            v_zy: v,
            e_opening: e,
            f_opening: f
        }
    }  

    // // Make a commitment for the begining of the protocol, returns commitment and `v` scalar
    // pub fn commit_to_individual_c_polynomials(&self, srs: &SRS<E>) -> Vec<(E::G1Affine, E::Fr)> {

    //     let mut results = vec![];

    //     let n = self.c_polynomials[0].len();

    //     for (p, v) in self.c_polynomials.iter().zip(self.v_elements.iter()) {
    //         let c = multiexp(
    //             srs.g_positive_x_alpha[0..n].iter(),
    //             p.iter()
    //         ).into_affine();
            
    //         results.push((c, *v));
    //     }

    //     results
    // }

    // // Argument is based on an approach of main SONIC construction, but with a custom S(X,Y) polynomial of a simple form
    // pub fn commit_to_t_polynomial(&mut self, challenges: & Vec<E::Fr>, y: E::Fr, srs: &SRS<E>) -> E::G1Affine {
    //     assert_eq!(challenges.len(), self.a_polynomials.len());

    //     let n = self.n;

    //     let mut t_polynomial: Option<Vec<E::Fr>> = None;

    //     for (((a, c), v), challenge) in self.a_polynomials.iter()
    //                                     .zip(self.c_polynomials.iter())
    //                                     .zip(self.v_elements.iter())
    //                                     .zip(challenges.iter())
    //     {
    //         let mut a_xy = a.clone();
    //         let mut c_xy = c.clone();
    //         let v = *v;

    //         assert_eq!(a_xy.len(), 2*n + 1);
    //         assert_eq!(c_xy.len(), 2*n + 1);

    //         // make a T polynomial

    //         let r: Vec<E::Fr> = {
    //             // p_a(X,Y)*Y
    //             let mut tmp = y;
    //             tmp.square();
    //             mut_distribute_consequitive_powers(&mut a_xy[..], tmp, y);

    //             // add extra terms 
    //             //v*(XY)^{n+1}*Y + X^{n+2} + X^{n+1}Y − X^{2n+2}*Y

    //             // n+1 term v*(XY)^{n+1}*Y + X^{n+1}Y 
    //             let tmp = y.pow(&[(n+2) as u64]);
    //             let mut x_n_plus_one_term = v;
    //             x_n_plus_one_term.mul_assign(&tmp);
    //             x_n_plus_one_term.add_assign(&y);
    //             a_xy[n].add_assign(&x_n_plus_one_term);

    //             // n+2 term 
    //             a_xy[n+1].add_assign(&E::Fr::one());

    //             // 2n+2 term 
    //             let mut tmp = y;
    //             tmp.negate();

    //             a_xy.push(tmp);

    //             assert_eq!(a_xy.len(), 2*n + 2);

    //             let mut r = vec![E::Fr::zero(); 2*n + 3];
    //             r.extend(a_xy);

    //             r
    //         };

    //         let r_prime: Vec<E::Fr> = {
    //             let mut c_prime: Vec<E::Fr> = c_xy.iter().rev().map(|el| *el).collect();
    //             c_prime.push(E::Fr::one());
    //             c_prime.push(E::Fr::zero());

    //             assert_eq!(c_prime.len(), 2*n + 3);

    //             c_prime
    //         };

    //         // multiply polynomials with powers [-2n-2, -1] and [1, 2n+2],
    //         // expect result to be [-2n+1, 2n+1]
    //         let mut t: Vec<E::Fr> = multiply_polynomials::<E>(r, r_prime);

    //         assert_eq!(t.len(), 6*n + 7);

    //         // drain first powers due to the padding and last element due to requirement of being zero
    //         for (i, el) in t[0..(2*n+3)].iter().enumerate() {
    //             assert_eq!(*el, E::Fr::zero(), "{}", format!("Element {} is non-zero", i));
    //         }    

    //         t.drain(0..(2*n+3));
    //         let last = t.pop();
    //         assert_eq!(last.unwrap(), E::Fr::zero(), "last element should be zero");

    //         assert_eq!(t.len(), 4*n + 3);

    //         let mut val = {
    //             let mut tmp = y;
    //             tmp.square();
    //             evaluate_at_consequitive_powers(&c_xy, tmp, y)
    //         };

    //         val.add_assign(&E::Fr::one());

    //         // subtract at constant term
    //         assert_eq!(t[2*n+1], val);

    //         t[2*n+1].sub_assign(&val);

    //         if t_polynomial.is_some() {
    //             if let Some(t_poly) = t_polynomial.as_mut() {
    //                 mul_add_polynomials(&mut t_poly[..], &t, *challenge);
    //             } 
    //         } else {
    //             mul_polynomial_by_scalar(&mut t, *challenge);
    //             t_polynomial = Some(t);
    //         }
    //     }

    //     let t_polynomial = t_polynomial.unwrap();

    //     let c = multiexp(srs.g_negative_x_alpha[0..(2*n+1)].iter().rev()
    //                         .chain_ext(srs.g_positive_x_alpha[0..(2*n+1)].iter()), 
    //                         t_polynomial[0..(2*n+1)].iter()
    //                         .chain_ext(t_polynomial[(2*n+2)..].iter())).into_affine();

    //     self.t_polynomial = Some(t_polynomial);

    //     c
    // }


    // // Argument is based on an approach of main SONIC construction, but with a custom S(X,Y) polynomial of a simple form
    // pub fn make_argument(self, a_zy: & Vec<E::Fr>, challenges: & Vec<E::Fr>, y: E::Fr, z: E::Fr, srs: &SRS<E>) -> GrandProductProof<E> {
    //     assert_eq!(a_zy.len(), self.a_polynomials.len());
    //     assert_eq!(challenges.len(), self.a_polynomials.len());

    //     let n = self.n;

    //     let c_polynomials = self.c_polynomials;
    //     let mut e_polynomial: Option<Vec<E::Fr>> = None;
    //     let mut f_polynomial: Option<Vec<E::Fr>> = None;

    //     let mut yz = y;
    //     yz.mul_assign(&z);

    //     let z_inv = z.inverse().unwrap();

    //     for (((a, c), challenge), v) in a_zy.iter()
    //                                     .zip(c_polynomials.into_iter())
    //                                     .zip(challenges.iter())
    //                                     .zip(self.v_elements.iter())
    //     {
    //         // cj = ((aj + vj(yz)n+1)y + zn+2 + zn+1y − z2n+2y)z−1
    //         let mut c_zy = yz.pow([(n + 1) as u64]);
    //         c_zy.mul_assign(v);
    //         c_zy.add_assign(a);
    //         c_zy.mul_assign(&y);

    //         let mut z_n_plus_1 = z.pow([(n + 1) as u64]);

    //         let mut z_n_plus_2 = z_n_plus_1;
    //         z_n_plus_2.mul_assign(&z);

    //         let mut z_2n_plus_2 = z_n_plus_1;
    //         z_2n_plus_2.square();
    //         z_2n_plus_2.mul_assign(&y);

    //         z_n_plus_1.mul_assign(&y);

    //         c_zy.add_assign(&z_n_plus_1);
    //         c_zy.add_assign(&z_n_plus_2);
    //         c_zy.sub_assign(&z_2n_plus_2);

    //         c_zy.mul_assign(&z_inv);

    //         let mut rc = c_zy;
    //         rc.mul_assign(challenge);

    //         let mut ry = y;
    //         ry.mul_assign(challenge);

    //         if e_polynomial.is_some() && f_polynomial.is_some() {
    //             if let Some(e_poly) = e_polynomial.as_mut() {
    //                 if let Some(f_poly) = f_polynomial.as_mut() {
    //                     mul_add_polynomials(&mut e_poly[..], &c, rc);
    //                     mul_add_polynomials(&mut f_poly[..], &c, ry);
    //                 }
    //             } 
    //         } else {
    //             let mut e = c.clone();
    //             let mut f = c;
    //             mul_polynomial_by_scalar(&mut e, rc);
    //             mul_polynomial_by_scalar(&mut f, ry);
    //             e_polynomial = Some(e);
    //             f_polynomial = Some(f);
    //         }
    //     }

    //     let e_polynomial = e_polynomial.unwrap();
    //     let f_polynomial = f_polynomial.unwrap();

    //     // evaluate e at z^-1

    //     let mut e_val = evaluate_at_consequitive_powers(&e_polynomial, z_inv, z_inv);
    //     e_val.negate();

    //     // evaluate f at y

    //     let mut f_val = evaluate_at_consequitive_powers(&f_polynomial, y, y);
    //     f_val.negate();

    //     let e_opening = polynomial_commitment_opening(
    //         0, 
    //         2*n + 1, 
    //         Some(e_val).iter().chain_ext(e_polynomial.iter()), 
    //         z_inv, 
    //         srs);

    //     let f_opening = polynomial_commitment_opening(
    //         0, 
    //         2*n + 1, 
    //         Some(f_val).iter().chain_ext(f_polynomial.iter()), 
    //         y, 
    //         srs);

    //     e_val.negate();
    //     f_val.negate();

    //     let mut t_poly = self.t_polynomial.unwrap();
    //     assert_eq!(t_poly.len(), 4*n + 3);

    //     // largest negative power of t is -2n-1
    //     let t_zy = {
    //         let tmp = z_inv.pow([(2*n+1) as u64]);
    //         evaluate_at_consequitive_powers(&t_poly, tmp, z)
    //     };

    //     t_poly[2*n + 1].sub_assign(&t_zy);

    //     let t_opening = polynomial_commitment_opening(
    //         2*n + 1, 
    //         2*n + 1,
    //         t_poly.iter(), 
    //         z, 
    //         srs);

    //     GrandProductProof {
    //         t_opening: t_opening,
    //         e_zinv: e_val,
    //         e_opening: e_opening,
    //         f_y: f_val,
    //         f_opening: f_opening,
    //     }
    // }

    pub fn verify_s_prime_commitment(n: usize, 
        randomness: & Vec<E::Fr>, 
        challenges: & Vec<E::Fr>,
        commitments: &Vec<E::G1Affine>,
        proof: &PermutationProof<E>,
        y: E::Fr,
        z_prime: E::Fr,
        specialized_srs: &SpecializedSRS<E>,
        srs: &SRS<E>
    ) -> bool {
        assert_eq!(randomness.len(), 2);
        assert_eq!(challenges.len(), commitments.len());

        // e(E,hαx)e(E−z′,hα) = e(􏰗Mj=1Sj′rj,h)e(g−v,hα)
        // e(F,hαx)e(F−yz′,hα) = e(􏰗Mj=1P2jrj,h)e(g−v,hα)

        let g = srs.g_positive_x[0];

        let h_alpha_x_precomp = srs.h_positive_x_alpha[1].prepare();

        let h_alpha_precomp = srs.h_positive_x_alpha[0].prepare();

        let mut h_prep = srs.h_positive_x[0];
        h_prep.negate();
        let h_prep = h_prep.prepare();

        let mut value = E::Fr::zero();

        for r in randomness.iter() {
            value.add_assign(&r);
        }
        value.mul_assign(&proof.v_zy);

        let mut minus_yz = z_prime;
        minus_yz.mul_assign(&y);
        minus_yz.negate();

        let mut minus_z_prime = z_prime;
        minus_z_prime.negate();

        let f_yz = proof.f_opening.mul(minus_yz.into_repr());
        let e_z = proof.e_opening.mul(minus_z_prime.into_repr());

        let mut h_alpha_term = multiexp(
            vec![e_z.into_affine(), f_yz.into_affine()].iter(),
            randomness.iter(),
        );

        let g_v = g.mul(value.into_repr());

        h_alpha_term.add_assign(&g_v);

        let h_alpha_x_term = multiexp(
            Some(proof.e_opening).iter()
                .chain_ext(Some(proof.f_opening).iter()),
            randomness.iter(),
        ).into_affine();

        let s_r = multiexp(
                commitments.iter(), 
                challenges.iter()
            ).into_affine();

        let p2_r = multiexp(
                specialized_srs.p_2.iter(),
                challenges.iter()
            ).into_affine();

        let h_term = multiexp(
            Some(s_r).iter()
                .chain_ext(Some(p2_r).iter()),
            randomness.iter()
        ).into_affine();

        E::final_exponentiation(&E::miller_loop(&[
                (&h_alpha_x_term.prepare(), &h_alpha_x_precomp),
                (&h_alpha_term.into_affine().prepare(), &h_alpha_precomp),
                (&h_term.prepare(), &h_prep),
            ])).unwrap() == E::Fqk::one()
    }

    // pub fn verify(
    //     n: usize, 
    //     randomness: & Vec<E::Fr>, 
    //     a_zy: & Vec<E::Fr>,
    //     challenges: &Vec<E::Fr>, 
    //     t_commitment: E::G1Affine, 
    //     commitments: &Vec<(E::G1Affine, E::Fr)>, 
    //     proof: &GrandProductProof<E>, 
    //     y: E::Fr, 
    //     z: E::Fr,
    //     srs: &SRS<E>
    // ) -> bool {
    //     assert_eq!(randomness.len(), 3);
    //     assert_eq!(a_zy.len(), challenges.len());
    //     assert_eq!(commitments.len(), challenges.len());

    //     let d = srs.d;

    //     let g = srs.g_positive_x[0];

    //     let h_alpha_x_precomp = srs.h_positive_x_alpha[1].prepare();

    //     let h_alpha_precomp = srs.h_positive_x_alpha[0].prepare();

    //     let mut h_prep = srs.h_positive_x[0];
    //     h_prep.negate();
    //     let h_prep = h_prep.prepare();

    //     // first re-calculate cj and t(z,y)

    //     let mut yz = y;
    //     yz.mul_assign(&z);

    //     let z_inv = z.inverse().unwrap();

    //     let mut t_zy = E::Fr::zero();
    //     t_zy.add_assign(&proof.e_zinv);
    //     t_zy.sub_assign(&proof.f_y);

    //     let mut commitments_points = vec![];
    //     let mut rc_vec = vec![];
    //     let mut ry_vec = vec![];

    //     for ((r, commitment), a) in challenges.iter()
    //                                     .zip(commitments.iter())
    //                                     .zip(a_zy.iter()) {
    //         let (c, v) = commitment;
    //         commitments_points.push(c.clone());
            
    //         // cj = ((aj + vj(yz)n+1)y + zn+2 + zn+1y − z2n+2y)z−1
    //         let mut c_zy = yz.pow([(n + 1) as u64]);
    //         c_zy.mul_assign(v);
    //         c_zy.add_assign(a);
    //         c_zy.mul_assign(&y);

    //         let mut z_n_plus_1 = z.pow([(n + 1) as u64]);

    //         let mut z_n_plus_2 = z_n_plus_1;
    //         z_n_plus_2.mul_assign(&z);

    //         let mut z_2n_plus_2 = z_n_plus_1;
    //         z_2n_plus_2.square();
    //         z_2n_plus_2.mul_assign(&y);

    //         z_n_plus_1.mul_assign(&y);

    //         c_zy.add_assign(&z_n_plus_1);
    //         c_zy.add_assign(&z_n_plus_2);
    //         c_zy.sub_assign(&z_2n_plus_2);

    //         c_zy.mul_assign(&z_inv);

    //         let mut rc = c_zy;
    //         rc.mul_assign(&r);
    //         rc_vec.push(rc);

    //         let mut ry = y;
    //         ry.mul_assign(&r);
    //         ry_vec.push(ry);

    //         let mut val = rc;
    //         val.sub_assign(r);
    //         t_zy.add_assign(&val);
    //     }

    //     let c_rc = multiexp(
    //         commitments_points.iter(),
    //         rc_vec.iter(),
    //     ).into_affine();

    //     let c_ry = multiexp(
    //         commitments_points.iter(),
    //         ry_vec.iter(),
    //     ).into_affine();

    //     let mut minus_y = y;
    //     minus_y.negate();

    //     let mut f_y = proof.f_opening.mul(minus_y.into_repr());
    //     let g_f = g.mul(proof.f_y.into_repr());
    //     f_y.add_assign(&g_f);

    //     let mut minus_z = z;
    //     minus_z.negate();

    //     let mut t_z = proof.t_opening.mul(minus_z.into_repr());
    //     let g_tzy = g.mul(t_zy.into_repr());
    //     t_z.add_assign(&g_tzy);

    //     let mut minus_z_inv = z_inv;
    //     minus_z_inv.negate();

    //     let mut e_z_inv = proof.e_opening.mul(minus_z_inv.into_repr());
    //     let g_e = g.mul(proof.e_zinv.into_repr());
    //     e_z_inv.add_assign(&g_e);

    //     let h_alpha_term = multiexp(
    //         vec![e_z_inv.into_affine(), f_y.into_affine(), t_z.into_affine()].iter(),
    //         randomness.iter(),
    //     ).into_affine();

    //     let h_alpha_x_term = multiexp(
    //         Some(proof.e_opening).iter()
    //             .chain_ext(Some(proof.f_opening).iter())
    //             .chain_ext(Some(proof.t_opening).iter()),
    //         randomness.iter(),
    //     ).into_affine();


    //     let h_term = multiexp(
    //         Some(c_rc).iter()
    //             .chain_ext(Some(c_ry).iter())
    //             .chain_ext(Some(t_commitment).iter()),
    //         randomness.iter(),
    //     ).into_affine();

    //     E::final_exponentiation(&E::miller_loop(&[
    //             (&h_alpha_x_term.prepare(), &h_alpha_x_precomp),
    //             (&h_alpha_term.prepare(), &h_alpha_precomp),
    //             (&h_term.prepare(), &h_prep),
    //         ])).unwrap() == E::Fqk::one()

    // }
}

// #[test]
// fn test_grand_product_argument() {
//     use pairing::bls12_381::{Fr, G1Affine, G1, Bls12};
//     use rand::{XorShiftRng, SeedableRng, Rand, Rng};
//     use crate::sonic::srs::SRS;

//     let srs_x = Fr::from_str("23923").unwrap();
//     let srs_alpha = Fr::from_str("23728792").unwrap();
//     let srs = SRS::<Bls12>::dummy(830564, srs_x, srs_alpha);

//     let n: usize = 1 << 8;
//     let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
//     let coeffs = (0..n).map(|_| Fr::rand(rng)).collect::<Vec<_>>();
//     let mut permutation = coeffs.clone();
//     rng.shuffle(&mut permutation);

//     let a_commitment = multiexp(srs.g_positive_x_alpha[0..n].iter(), coeffs.iter()).into_affine();
//     let b_commitment = multiexp(srs.g_positive_x_alpha[0..n].iter(), permutation.iter()).into_affine();

//     let mut argument = GrandProductArgument::new(vec![(coeffs, permutation)]);

//     let commitments_and_v_values = argument.commit_to_individual_c_polynomials(&srs);

//     assert_eq!(commitments_and_v_values.len(), 1);

//     let y : Fr = rng.gen();

//     let challenges = (0..1).map(|_| Fr::rand(rng)).collect::<Vec<_>>();

//     let t_commitment = argument.commit_to_t_polynomial(&challenges, y, &srs);

//     let z : Fr = rng.gen();

//     let grand_product_openings = argument.open_commitments_for_grand_product(y, z, &srs);

//     let randomness = (0..1).map(|_| Fr::rand(rng)).collect::<Vec<_>>();

//     let valid = GrandProductArgument::verify_ab_commitment(n, 
//         &randomness, 
//         &vec![a_commitment], 
//         &vec![b_commitment], 
//         &grand_product_openings, 
//         y,
//         z,
//         &srs);

//     assert!(valid, "grand product commitments should be valid");

//     let a_zy: Vec<Fr> = grand_product_openings.iter().map(|el| el.0.clone()).collect();

//     let proof = argument.make_argument(&a_zy, &challenges, y, z, &srs);

//     let randomness = (0..3).map(|_| Fr::rand(rng)).collect::<Vec<_>>();

//     let valid = GrandProductArgument::verify(
//         n, 
//         &randomness, 
//         &a_zy, 
//         &challenges, 
//         t_commitment,
//         &commitments_and_v_values, 
//         &proof,
//         y,
//         z, 
//         &srs);

//     assert!(valid, "t commitment should be valid");
// }

