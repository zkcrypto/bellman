/// Permutation argument allows to prove that a commitment to a vector A is 
/// actually a commitment to a vector of values that are equal to `(s^{perm})_i * y^{perm(i)}`
/// for some fixed permutation `perm`

use pairing::ff::{Field, PrimeField, PrimeFieldRepr, ScalarEngine};
use pairing::{Engine, CurveProjective, CurveAffine};
use std::marker::PhantomData;

use crate::sonic::srs::SRS;
use crate::sonic::util::*;
use super::wellformed_argument::{WellformednessArgument, WellformednessProof};
use super::grand_product_argument::{GrandProductArgument, GrandProductProof};

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
    permuted_at_y_coefficients: Vec<Vec<E::Fr>>,
    permutations: Vec<Vec<usize>>,
    n: usize
}

#[derive(Clone)]
pub struct PermutationProof<E: Engine> {
    v_zy: E::Fr,
    e_opening: E::G1Affine,
    f_opening: E::G1Affine,
}

#[derive(Clone)]
pub struct Proof<E: Engine> {
    j: usize,
    s_opening: E::G1Affine,
    s_zy: E::Fr
}

fn permute<F: Field>(coeffs: &[F], permutation: & [usize]) -> Vec<F>{
    assert_eq!(coeffs.len(), permutation.len());
    let mut result: Vec<F> = vec![F::zero(); coeffs.len()];
    for (i, j) in permutation.iter().enumerate() {
        result[*j - 1] = coeffs[i];
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
            permuted_at_y_coefficients: vec![vec![]],
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
        let mut permuted_at_y_coefficients = vec![];

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
            permuted_at_y_coefficients.push(permuted_at_y);
        }

        self.permuted_coefficients = permuted_coefficients;
        self.permuted_at_y_coefficients = permuted_at_y_coefficients;

        result
    }

    pub fn open_commitments_to_s_prime(
        &self, 
        challenges: &Vec<E::Fr>, 
        y: E::Fr, 
        z_prime: E::Fr, 
        srs: &SRS<E>
    ) -> PermutationProof<E> {        
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
                polynomial = Some(poly);
            }
        }

        let mut polynomial = polynomial.unwrap();
        let v = evaluate_at_consequitive_powers(&polynomial[..], yz, yz);

        let mut v_neg = v;
        v_neg.negate();

        let f = polynomial_commitment_opening(
            0, 
            n, 
            Some(v_neg).iter().chain_ext(polynomial.iter()), 
            yz, 
            &srs
        );

        mut_distribute_consequitive_powers(&mut polynomial[..], y, y);

        let e = polynomial_commitment_opening(
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

    // Argument a permutation argument. Current implementation consumes, cause extra arguments are required
    pub fn make_argument(self, 
        beta: E::Fr, 
        gamma: E::Fr, 
        grand_product_challenges: & Vec<E::Fr>, 
        wellformed_challenges: & Vec<E::Fr>,
        y: E::Fr, 
        z: E::Fr, 
        specialized_srs: &SpecializedSRS<E>,
        srs: &SRS<E>
    ) -> Proof<E> {
        // Sj(P4j)β(P1j)γ is equal to the product of the coefficients of Sj′(P3j)β(P1j)γ
        // also open s = \sum self.permuted_coefficients(X, y) at z

        let n = self.n;
        let j = self.non_permuted_coefficients.len();
        assert_eq!(j, grand_product_challenges.len());
        assert_eq!(2*j, wellformed_challenges.len());

        let mut s_polynomial: Option<Vec<E::Fr>> = None;

        for c in self.permuted_at_y_coefficients.iter()
        {
            if s_polynomial.is_some()  {
                if let Some(poly) = s_polynomial.as_mut() {
                    add_polynomials(&mut poly[..], & c[..]);
                } 
            } else {
                s_polynomial = Some(c.clone());
            }
        }
        let mut s_polynomial = s_polynomial.unwrap();
        // evaluate at z
        let s_zy = evaluate_at_consequitive_powers(& s_polynomial[..], z, z);

        let mut s_zy_neg = s_zy;
        s_zy_neg.negate();

        let s_zy_opening = polynomial_commitment_opening(
            0, 
            n,
            Some(s_zy_neg).iter().chain_ext(s_polynomial.iter()),
            z, 
            &srs
        );

        // Sj(P4j)^β (P1j)^γ is equal to the product of the coefficients of Sj′(P3j)^β (P1j)^γ

        let p_1_values = vec![E::Fr::one(); n];
        let p_3_values: Vec<E::Fr> = (1..=n).map(|el| {
                        let mut repr = <<E as ScalarEngine>::Fr as PrimeField>::Repr::default();
                        repr.as_mut()[0] = el as u64;
                        let fe = E::Fr::from_repr(repr).unwrap();

                        fe
                    }).collect();

        let mut grand_products = vec![];

        for (i, ((non_permuted, permuted), permutation)) in self.non_permuted_coefficients.into_iter()
                                            .zip(self.permuted_coefficients.into_iter())
                                            .zip(self.permutations.into_iter()).enumerate()

        {
            // \prod si+βσi+γ = \prod s'i + β*i + γ
            let mut s_j_combination = non_permuted;
            {
                let p_4_values: Vec<E::Fr> = permutation.into_iter().map(|el| {
                        let mut repr = <<E as ScalarEngine>::Fr as PrimeField>::Repr::default();
                        repr.as_mut()[0] = el as u64;
                        let fe = E::Fr::from_repr(repr).unwrap();

                        fe
                    }).collect();
                mul_add_polynomials(&mut s_j_combination[..], & p_4_values[..], beta);
                mul_add_polynomials(&mut s_j_combination[..], & p_1_values[..], gamma);
            }

            let mut s_prime_j_combination = permuted;
            {
                mul_add_polynomials(&mut s_prime_j_combination[..], & p_3_values[..], beta);
                mul_add_polynomials(&mut s_prime_j_combination[..], & p_1_values[..], gamma);
            }

            grand_products.push((s_j_combination, s_prime_j_combination));
        }

        let mut a_commitments = vec![]; 
        let mut b_commitments = vec![]; 

        for (a, b) in grand_products.iter() {
            let (c_a, c_b) = GrandProductArgument::commit_for_individual_products(& a[..], & b[..], &srs);
            a_commitments.push(c_a);
            b_commitments.push(c_b);
        }

        {
            let mut all_polys = vec![];
            for p in grand_products.iter() {
                let (a, b) = p;
                all_polys.push(a.clone());
                all_polys.push(b.clone());
            }

            let wellformed_argument = WellformednessArgument::new(all_polys);
            let commitments = wellformed_argument.commit(&srs);
            let proof = wellformed_argument.make_argument(wellformed_challenges.clone(), &srs);
            let valid = WellformednessArgument::verify(n, &wellformed_challenges, &commitments, &proof, &srs);

            assert!(valid, "wellformedness argument must be valid");
        }

        let mut grand_product_argument = GrandProductArgument::new(grand_products);
        let c_commitments = grand_product_argument.commit_to_individual_c_polynomials(&srs);
        let t_commitment = grand_product_argument.commit_to_t_polynomial(&grand_product_challenges, y, &srs);
        let grand_product_openings = grand_product_argument.open_commitments_for_grand_product(y, z, &srs);
        let a_zy: Vec<E::Fr> = grand_product_openings.iter().map(|el| el.0.clone()).collect();
        let proof = grand_product_argument.make_argument(&a_zy, &grand_product_challenges, y, z, &srs);

        {
            use rand::{XorShiftRng, SeedableRng, Rand, Rng};
            let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
            let randomness = (0..j).map(|_| E::Fr::rand(rng)).collect::<Vec<_>>();

            let valid = GrandProductArgument::verify_ab_commitment(n, 
                &randomness, 
                &a_commitments, 
                & b_commitments,
                &grand_product_openings, 
                y, 
                z,
                &srs);
            assert!(valid, "ab part of grand product argument must be valid");

            let randomness = (0..3).map(|_| E::Fr::rand(rng)).collect::<Vec<_>>();
            let valid = GrandProductArgument::verify(n, 
                &randomness, 
                &a_zy, 
                &grand_product_challenges, 
                t_commitment, 
                &c_commitments, 
                &proof, 
                y,
                z,
                &srs);

            assert!(valid, "grand product argument must be valid");
        }
        
        Proof {
            j: j,
            s_opening: s_zy_opening,
            s_zy: s_zy
        }
    }

    pub fn verify_s_prime_commitment(
        n: usize, 
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

        // let g = srs.g_positive_x[0];

        // let h_alpha_x_precomp = srs.h_positive_x_alpha[1].prepare();

        // let h_alpha_precomp = srs.h_positive_x_alpha[0].prepare();

        // let mut h_prep = srs.h_positive_x[0];
        // h_prep.negate();
        // let h_prep = h_prep.prepare();

        // let value = proof.v_zy;
        // let g_v = g.mul(value.into_repr());

        // {

        //     let mut minus_z_prime = z_prime;
        //     minus_z_prime.negate();

        //     let e_z = proof.e_opening.mul(minus_z_prime.into_repr());

        //     let mut h_alpha_term = e_z;

        //     h_alpha_term.add_assign(&g_v);

        //     let h_alpha_x_term = proof.e_opening;
            
        //     let s_r = multiexp(
        //             commitments.iter(), 
        //             challenges.iter()
        //         ).into_affine();

        //     let h_term = s_r;

        //     let valid = E::final_exponentiation(&E::miller_loop(&[
        //             (&h_alpha_x_term.prepare(), &h_alpha_x_precomp),
        //             (&h_alpha_term.into_affine().prepare(), &h_alpha_precomp),
        //             (&h_term.prepare(), &h_prep),
        //         ])).unwrap() == E::Fqk::one();

        //     if !valid {
        //         return false;
        //     }
        // }
        // {
        //     let mut minus_yz = z_prime;
        //     minus_yz.mul_assign(&y);
        //     minus_yz.negate();

        //     let f_yz = proof.f_opening.mul(minus_yz.into_repr());

        //     let p2_r = multiexp(
        //         specialized_srs.p_2.iter(),
        //         challenges.iter()
        //     ).into_affine();

        //     let mut h_alpha_term = f_yz;

        //     h_alpha_term.add_assign(&g_v);

        //     let h_alpha_x_term = proof.f_opening;
            
        //     let h_term = p2_r;

        //     let valid = E::final_exponentiation(&E::miller_loop(&[
        //             (&h_alpha_x_term.prepare(), &h_alpha_x_precomp),
        //             (&h_alpha_term.into_affine().prepare(), &h_alpha_precomp),
        //             (&h_term.prepare(), &h_prep),
        //         ])).unwrap() == E::Fqk::one();

        //     if !valid {
        //         return false;
        //     }
        // }

        // true

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

    pub fn verify(
        s_commitments: &Vec<E::G1Affine>,
        proof: &Proof<E>,
        z: E::Fr,
        srs: &SRS<E>
    ) -> bool {

        let g = srs.g_positive_x[0];

        let h_alpha_x_precomp = srs.h_positive_x_alpha[1].prepare();

        let h_alpha_precomp = srs.h_positive_x_alpha[0].prepare();

        let mut h_prep = srs.h_positive_x[0];
        h_prep.negate();
        let h_prep = h_prep.prepare();    

        let mut minus_z = z;
        minus_z.negate();

        let opening_z = proof.s_opening.mul(minus_z.into_repr());

        let mut h_alpha_term = opening_z;
        let g_s = g.mul(proof.s_zy.into_repr());

        h_alpha_term.add_assign(&g_s);

        let h_alpha_x_term = proof.s_opening;

        let mut s = E::G1::zero();
        for p in s_commitments {
            s.add_assign_mixed(&p);
        }

        let h_term = s.into_affine();

        E::final_exponentiation(&E::miller_loop(&[
                (&h_alpha_x_term.prepare(), &h_alpha_x_precomp),
                (&h_alpha_term.into_affine().prepare(), &h_alpha_precomp),
                (&h_term.prepare(), &h_prep),
            ])).unwrap() == E::Fqk::one()
    }
}

#[test]
fn test_permutation_argument() {
    use pairing::bls12_381::{Fr, G1Affine, G1, Bls12};
    use rand::{XorShiftRng, SeedableRng, Rand, Rng};
    use crate::sonic::srs::SRS;

    let srs_x = Fr::from_str("23923").unwrap();
    let srs_alpha = Fr::from_str("23728792").unwrap();
    let srs = SRS::<Bls12>::dummy(830564, srs_x, srs_alpha);

    let n: usize = 1 << 1;
    let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
    // let coeffs = (0..n).map(|_| Fr::rand(rng)).collect::<Vec<_>>();
    // let mut permutation = (0..n).collect::<Vec<_>>();
    // rng.shuffle(&mut permutation);

    let coeffs = vec![Fr::from_str("3").unwrap(), Fr::from_str("4").unwrap()];
    let permutation = vec![2, 1];

    let coeffs = vec![coeffs];
    let permutations = vec![permutation];

    let specialized_srs = PermutationArgument::make_specialized_srs(&coeffs, &permutations, &srs);

    let mut argument = PermutationArgument::new(coeffs, permutations);

    let y : Fr = rng.gen();
    let y : Fr = Fr::one();
    let y : Fr = Fr::from_str("2").unwrap();

    // let challenges = (0..1).map(|_| Fr::rand(rng)).collect::<Vec<_>>();

    let challenges = vec![Fr::one()];

    let commitments = argument.commit(y, &srs);
    let mut s_commitments = vec![];
    let mut s_prime_commitments = vec![];
    for (s, s_prime) in commitments.into_iter() {
        s_commitments.push(s);
        s_prime_commitments.push(s_prime);
    }

    let z_prime : Fr = rng.gen();
    let z_prime : Fr = Fr::one();

    let opening = argument.open_commitments_to_s_prime(&challenges, y, z_prime, &srs);

    let randomness = (0..2).map(|_| Fr::rand(rng)).collect::<Vec<_>>();

    let valid = PermutationArgument::verify_s_prime_commitment(n, 
        &randomness, 
        &challenges, 
        &s_prime_commitments, 
        &opening, 
        y, 
        z_prime, 
        &specialized_srs, 
        &srs);

    assert!(valid, "s' commitment must be valid");

    let beta : Fr = rng.gen();
    let gamma : Fr = rng.gen();

    let grand_product_challenges = (0..1).map(|_| Fr::rand(rng)).collect::<Vec<_>>();
    let wellformed_challenges = (0..2).map(|_| Fr::rand(rng)).collect::<Vec<_>>();

    let z : Fr = rng.gen();

    let proof = argument.make_argument(
        beta, 
        gamma, 
        & grand_product_challenges, 
        & wellformed_challenges, 
        y, z, 
        &specialized_srs, &srs);

    let valid = PermutationArgument::verify(&s_commitments, &proof, z, &srs);

    assert!(valid, "permutation argument must be valid");
}

