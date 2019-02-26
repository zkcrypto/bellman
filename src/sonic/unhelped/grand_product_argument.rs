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
    t_polynomial: Option<Vec<E::Fr>>,
    n: usize
}

#[derive(Clone)]
pub struct GrandProductProof<E: Engine> {
    t_opening: E::G1Affine,
    e_zinv: E::Fr,
    e_opening: E::G1Affine,
    f_y: E::Fr,
    f_opening: E::G1Affine,
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
            // v = a_{n+1} = c_{n}^-1
            let v = c_poly[n-1].inverse().unwrap();
            a_poly.push(E::Fr::zero());
            // a_poly.push(v);
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

            assert_eq!(c_poly[n-1], c_poly[2*n]);

            a_polynomials.push(a_poly);
            c_polynomials.push(c_poly);
            v_elements.push(v);
        }

        GrandProductArgument {
            a_polynomials: a_polynomials,
            c_polynomials: c_polynomials,
            v_elements: v_elements,
            t_polynomial: None,
            n: n
        }
    }

    // Make a commitment to a polynomial in a form A*B^{x+1} = [a_1...a_{n}, 0, b_1...b_{n}]
    pub fn commit_for_grand_product(a: &[E::Fr], b: &[E::Fr], srs: &SRS<E>) -> E::G1Affine {
        assert_eq!(a.len(), b.len());

        let n = a.len();

        multiexp(
                srs.g_positive_x_alpha[0..(2*n+1)].iter(),
                a.iter()
                    .chain_ext(Some(E::Fr::zero()).iter())
                    .chain_ext(b.iter())
        ).into_affine()
    }

    pub fn open_commitments_for_grand_product(&self, y: E::Fr, z: E::Fr, srs: &SRS<E>) -> Vec<(E::Fr, E::G1Affine)> {
        let n = self.n;

        let mut yz = y;
        yz.mul_assign(&z);

        let mut results = vec![];

        for a_poly in self.a_polynomials.iter() {
            let a = & a_poly[0..n];
            let b = & a_poly[(n+1)..];
            assert_eq!(a.len(), n);
            assert_eq!(b.len(), n);
            let mut val = evaluate_at_consequitive_powers(a, yz, yz);
            {
                let tmp = yz.pow([(n+2) as u64]);
                let v = evaluate_at_consequitive_powers(b, tmp, yz);
                val.add_assign(&v);
            }

            let mut constant_term = val;
            constant_term.negate();

            let opening = polynomial_commitment_opening(
                0,
                2*n + 1,
                Some(constant_term).iter()
                    .chain_ext(a.iter())
                    .chain_ext(Some(E::Fr::zero()).iter())
                    .chain_ext(b.iter()),
                yz, 
                &srs);

            results.push((val, opening));

        }

        results
    }  

    // Make a commitment for the begining of the protocol, returns commitment and `v` scalar
    pub fn commit_to_individual_c_polynomials(&self, srs: &SRS<E>) -> Vec<(E::G1Affine, E::Fr)> {

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
    pub fn commit_to_t_polynomial(&mut self, challenges: & Vec<E::Fr>, y: E::Fr, srs: &SRS<E>) -> E::G1Affine {
        assert_eq!(challenges.len(), self.a_polynomials.len());

        let n = self.n;

        let mut t_polynomial: Option<Vec<E::Fr>> = None;

        for (((a, c), v), challenge) in self.a_polynomials.iter()
                                        .zip(self.c_polynomials.iter())
                                        .zip(self.v_elements.iter())
                                        .zip(challenges.iter())
        {
            let mut a_xy = a.clone();
            let mut c_xy = c.clone();
            let v = *v;

            assert_eq!(a_xy.len(), 2*n + 1);
            assert_eq!(c_xy.len(), 2*n + 1);

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

                let mut r = vec![E::Fr::zero(); 2*n + 3];
                r.extend(a_xy);

                r
            };

            let r_prime: Vec<E::Fr> = {
                let mut c_prime: Vec<E::Fr> = c_xy.iter().rev().map(|el| *el).collect();
                c_prime.push(E::Fr::one());
                c_prime.push(E::Fr::zero());

                assert_eq!(c_prime.len(), 2*n + 3);

                c_prime
            };

            // multiply polynomials with powers [-2n-2, -1] and [1, 2n+2],
            // expect result to be [-2n+1, 2n+1]
            let mut t: Vec<E::Fr> = multiply_polynomials::<E>(r, r_prime);

            assert_eq!(t.len(), 6*n + 7);

            // drain first powers due to the padding and last element due to requirement of being zero
            for (i, el) in t[0..(2*n+3)].iter().enumerate() {
                assert_eq!(*el, E::Fr::zero(), "{}", format!("Element {} is non-zero", i));
            }    

            t.drain(0..(2*n+3));
            let last = t.pop();
            assert_eq!(last.unwrap(), E::Fr::zero(), "last element should be zero");

            assert_eq!(t.len(), 4*n + 3);

            let mut val = {
                let mut tmp = y;
                tmp.square();
                evaluate_at_consequitive_powers(&c_xy, tmp, y)
            };

            val.add_assign(&E::Fr::one());

            // subtract at constant term
            assert_eq!(t[2*n+1], val);

            t[2*n+1].sub_assign(&val);

            if t_polynomial.is_some() {
                if let Some(t_poly) = t_polynomial.as_mut() {
                    mul_add_polynomials(&mut t_poly[..], &t, *challenge);
                } 
            } else {
                mul_polynomial_by_scalar(&mut t, *challenge);
                t_polynomial = Some(t);
            }
        }

        let t_polynomial = t_polynomial.unwrap();

        let c = multiexp(srs.g_negative_x_alpha[0..(2*n+1)].iter().rev()
                            .chain_ext(srs.g_positive_x_alpha[0..(2*n+1)].iter()), 
                            t_polynomial[0..(2*n+1)].iter()
                            .chain_ext(t_polynomial[(2*n+2)..].iter())).into_affine();

        self.t_polynomial = Some(t_polynomial);

        c
    }


    // Argument is based on an approach of main SONIC construction, but with a custom S(X,Y) polynomial of a simple form
    pub fn make_argument(self, a_zy: & Vec<E::Fr>, challenges: & Vec<E::Fr>, y: E::Fr, z: E::Fr, srs: &SRS<E>) -> GrandProductProof<E> {
        assert_eq!(a_zy.len(), self.a_polynomials.len());
        assert_eq!(challenges.len(), self.a_polynomials.len());

        let n = self.n;

        let mut c_polynomials = self.c_polynomials;
        let mut e_polynomial: Option<Vec<E::Fr>> = None;
        let mut f_polynomial: Option<Vec<E::Fr>> = None;

        let mut yz = y;
        yz.mul_assign(&z);

        let z_inv = z.inverse().unwrap();

        for (((a, c), challenge), v) in a_zy.iter()
                                        .zip(c_polynomials.into_iter())
                                        .zip(challenges.iter())
                                        .zip(self.v_elements.iter())
        {
            // cj = ((aj + vj(yz)n+1)y + zn+2 + zn+1y − z2n+2y)z−1
            let mut c_zy = yz.pow([(n + 1) as u64]);
            c_zy.mul_assign(v);
            c_zy.add_assign(a);
            c_zy.mul_assign(&y);

            let mut z_n_plus_1 = z.pow([(n + 1) as u64]);

            let mut z_n_plus_2 = z_n_plus_1;
            z_n_plus_2.mul_assign(&z);

            let mut z_2n_plus_2 = z_n_plus_1;
            z_2n_plus_2.square();
            z_2n_plus_2.mul_assign(&y);

            z_n_plus_1.mul_assign(&y);

            c_zy.add_assign(&z_n_plus_1);
            c_zy.add_assign(&z_n_plus_2);
            c_zy.sub_assign(&z_2n_plus_2);

            c_zy.mul_assign(&z_inv);

            let mut rc = c_zy;
            rc.mul_assign(challenge);
            let mut ry = y;
            ry.mul_assign(challenge);

            if e_polynomial.is_some() && f_polynomial.is_some() {
                if let Some(e_poly) = e_polynomial.as_mut() {
                    if let Some(f_poly) = f_polynomial.as_mut() {
                        mul_add_polynomials(&mut e_poly[..], &c, rc);
                        mul_add_polynomials(&mut f_poly[..], &c, ry);
                    }
                } 
            } else {
                let mut e = c.clone();
                let mut f = c;
                mul_polynomial_by_scalar(&mut e, rc);
                mul_polynomial_by_scalar(&mut f, ry);
                e_polynomial = Some(e);
                f_polynomial = Some(f);
            }
        }

        let e_polynomial = e_polynomial.unwrap();
        let f_polynomial = f_polynomial.unwrap();

        // evaluate e at z^-1

        let mut e_val = evaluate_at_consequitive_powers(&e_polynomial, z_inv, z_inv);
        e_val.negate();

        // evaluate f at y

        let mut f_val = evaluate_at_consequitive_powers(&f_polynomial, y, y);
        f_val.negate();

        let e_opening = polynomial_commitment_opening(
            0, 
            2*n + 1, 
            Some(e_val).iter().chain_ext(e_polynomial.iter()), 
            z_inv, 
            srs);

        let f_opening = polynomial_commitment_opening(
            0, 
            2*n + 1, 
            Some(f_val).iter().chain_ext(f_polynomial.iter()), 
            y, 
            srs);

        e_val.negate();
        f_val.negate();

        let mut t_poly = self.t_polynomial.unwrap();

        let t_zy = {
            let tmp = z_inv.pow([(2*n+2) as u64]);
            evaluate_at_consequitive_powers(&t_poly, tmp, z)
        };

        t_poly[2*n + 2].sub_assign(&t_zy);

        let t_opening = polynomial_commitment_opening(
            2*n + 2, 
            2*n + 2,
            t_poly.iter(), 
            z, 
            srs);

        GrandProductProof {
            t_opening: t_opening,
            e_zinv: e_val,
            e_opening: e_opening,
            f_y: f_val,
            f_opening: f_opening,
        }
    }


    pub fn verify_ab_commitment(n: usize, 
        randomness: & Vec<E::Fr>, 
        a_commitments: &Vec<E::G1Affine>,
        b_commitments: &Vec<E::G1Affine>, 
        openings: &Vec<(E::Fr, E::G1Affine)>,
        y: E::Fr,
        z: E::Fr,
        srs: &SRS<E>
        ) -> bool {
        assert_eq!(randomness.len(), a_commitments.len());
        assert_eq!(openings.len(), a_commitments.len());
        assert_eq!(b_commitments.len(), a_commitments.len());
        let d = srs.d;

        // e(Dj,hαx)e(D−yz,hα) = e(Aj,h)e(Bj,hxn+1)e(g−aj ,hα)

        let g = srs.g_positive_x[0];

        let h_alpha_x_precomp = srs.h_positive_x_alpha[1].prepare();

        let h_alpha_precomp = srs.h_positive_x_alpha[0].prepare();

        let mut h_x_n_plus_one_precomp = srs.h_positive_x[n];
        h_x_n_plus_one_precomp.negate();
        let h_x_n_plus_one_precomp = h_x_n_plus_one_precomp.prepare();

        let mut h_prep = srs.h_positive_x[0];
        h_prep.negate();
        let h_prep = h_prep.prepare();

        let a = multiexp(
            a_commitments.iter(),
            randomness.iter(),
        ).into_affine();

        let a = a.prepare();

        let b = multiexp(
            b_commitments.iter(),
            randomness.iter(),
        ).into_affine();

        let b = b.prepare();

        let mut yz_neg = y;
        yz_neg.mul_assign(&z);
        yz_neg.negate();

        let mut ops = vec![];
        let mut value = E::Fr::zero();

        for (el, r) in openings.iter().zip(randomness.iter()) {
            let (v, o) = el;
            ops.push(o.clone());
            let mut val = *v;
            val.mul_assign(&r);
            value.add_assign(&val);
        }

        let value = g.mul(value.into_repr()).into_affine().prepare();

        let openings = multiexp(
            ops.iter(),
            randomness.iter(),
        ).into_affine();

        let openings_zy = openings.mul(yz_neg.into_repr()).into_affine().prepare();
        let openings = openings.prepare();


        // e(Dj,hαx)e(D−yz,hα) = e(Aj,h)e(Bj,hxn+1)e(g−aj ,hα)

        E::final_exponentiation(&E::miller_loop(&[
                (&openings, &h_alpha_x_precomp),
                (&openings_zy, &h_alpha_precomp),
                (&a, &h_prep),
                (&b, &h_x_n_plus_one_precomp),
                (&value, &h_alpha_precomp)
            ])).unwrap() == E::Fqk::one()
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

#[test]
fn test_grand_product_argument() {
    use pairing::bls12_381::{Fr, G1Affine, G1, Bls12};
    use rand::{XorShiftRng, SeedableRng, Rand, Rng};
    use crate::sonic::srs::SRS;

    let srs_x = Fr::from_str("23923").unwrap();
    let srs_alpha = Fr::from_str("23728792").unwrap();
    let srs = SRS::<Bls12>::dummy(830564, srs_x, srs_alpha);

    let n: usize = 1 << 1;
    let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
    // let coeffs = (0..n).map(|_| Fr::rand(rng)).collect::<Vec<_>>();
    let coeffs = vec![Fr::from_str("1").unwrap(), Fr::from_str("2").unwrap()];
    let mut permutation = coeffs.clone();
    rng.shuffle(&mut permutation);

    let a_commitment = multiexp(srs.g_positive_x_alpha[0..n].iter(), coeffs.iter()).into_affine();
    let b_commitment = multiexp(srs.g_positive_x_alpha[0..n].iter(), permutation.iter()).into_affine();

    let mut argument = GrandProductArgument::new(vec![(coeffs, permutation)]);

    let commitments_and_v_values = argument.commit_to_individual_c_polynomials(&srs);

    assert_eq!(commitments_and_v_values.len(), 1);

    // let y : Fr = rng.gen();

    let y = Fr::one();

    let challenges = (0..1).map(|_| Fr::rand(rng)).collect::<Vec<_>>();

    let t_commitment = argument.commit_to_t_polynomial(&challenges, y, &srs);

    let z : Fr = rng.gen();

    let grand_product_openings = argument.open_commitments_for_grand_product(y, z, &srs);

    let randomness = (0..1).map(|_| Fr::rand(rng)).collect::<Vec<_>>();

    let valid = GrandProductArgument::verify_ab_commitment(n, 
        &randomness, 
        &vec![a_commitment], 
        &vec![b_commitment], 
        &grand_product_openings, 
        y,
        z,
        &srs);

    assert!(valid);
}

