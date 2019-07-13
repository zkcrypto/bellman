/// Wellformedness argument allows to verify that some committment was to multivariate polynomial of degree n, 
/// with no constant term and negative powers

use crate::pairing::ff::{Field, PrimeField, PrimeFieldRepr};
use crate::pairing::{Engine, CurveProjective, CurveAffine};
use std::marker::PhantomData;

use crate::sonic::srs::SRS;
use crate::sonic::util::*;
use crate::sonic::transcript::{Transcript, TranscriptProtocol};

#[derive(Clone)]
pub struct WellformednessArgument<E: Engine> {
    polynomials: Vec<Vec<E::Fr>>
}

#[derive(Clone)]
pub struct WellformednessProof<E: Engine> {
    pub l: E::G1Affine,
    pub r: E::G1Affine
}

#[derive(Clone)]
pub struct WellformednessSignature<E: Engine> {
    pub proof: WellformednessProof<E>
}

impl<E: Engine> WellformednessArgument<E> {

    pub fn create_signature(
        all_polys: Vec<Vec<E::Fr>>,
        wellformed_challenges: Vec<E::Fr>,
        srs: &SRS<E>
    ) -> WellformednessSignature<E> {
        let wellformed_argument = WellformednessArgument::new(all_polys);
    
        let proof = wellformed_argument.make_argument(wellformed_challenges, &srs);

        WellformednessSignature {
            proof
        }
    }

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
        assert_eq!(challenges.len(), self.polynomials.len());
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

        // TODO: it's not necessary to have n < d, fix later

        assert!(n < d);

        // here the multiplier is x^-d, so largest negative power is -(d - 1), smallest negative power is - (d - n)
        // H^{x^k} are labeled from 0 power, so we need to use proper indexes
        let l = multiexp(
                srs.g_negative_x[(d - n)..=(d - 1)].iter().rev(),
                p0.iter()
            ).into_affine();

        // here the multiplier is x^d-n, so largest positive power is d, smallest positive power is d - n + 1

        let r = multiexp(
                srs.g_positive_x[(d - n + 1)..=d].iter(),
                p0.iter()
            ).into_affine();

        WellformednessProof {
            l: l,
            r: r
        }
    }

    pub fn verify(n: usize, challenges: &Vec<E::Fr>, commitments: &Vec<E::G1Affine>, proof: &WellformednessProof<E>, srs: &SRS<E>) -> bool {
        let d = srs.d;

        let alpha_x_d_precomp = srs.h_positive_x_alpha[d].prepare();
        // TODO: not strictly required
        assert!(n < d);
        let d_minus_n = d - n;
        let alpha_x_n_minus_d_precomp = srs.h_negative_x_alpha[d_minus_n].prepare();
        let mut h_prep = srs.h_positive_x[0];
        h_prep.negate();
        let h_prep = h_prep.prepare();

        let a = multiexp(
            commitments.iter(),
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

#[test]
fn test_argument() {
    use crate::pairing::bls12_381::{Fr, G1Affine, G1, Bls12};
    use rand::{XorShiftRng, SeedableRng, Rand, Rng};
    use crate::sonic::srs::SRS;

    let srs_x = Fr::from_str("23923").unwrap();
    let srs_alpha = Fr::from_str("23728792").unwrap();
    // let srs = SRS::<Bls12>::dummy(830564, srs_x, srs_alpha);
    let srs = SRS::<Bls12>::new(128, srs_x, srs_alpha);

    let n: usize = 1 << 5;
    let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
    let coeffs = (1..=n).map(|_| Fr::rand(rng)).collect::<Vec<_>>();

    let argument = WellformednessArgument::new(vec![coeffs]);
    let challenges = (0..1).map(|_| Fr::rand(rng)).collect::<Vec<_>>();

    let commitments = argument.commit(&srs);

    let proof = argument.make_argument(challenges.clone(), &srs);

    let valid = WellformednessArgument::verify(n, &challenges, &commitments,  &proof, &srs);

    assert!(valid);
}

#[test]
fn test_argument_soundness() {
    use crate::pairing::bls12_381::{Fr, G1Affine, G1, Bls12};
    use rand::{XorShiftRng, SeedableRng, Rand, Rng};
    use crate::sonic::srs::SRS;

    let srs_x = Fr::from_str("23923").unwrap();
    let srs_alpha = Fr::from_str("23728792").unwrap();
    let srs = SRS::<Bls12>::dummy(830564, srs_x, srs_alpha);

    let n: usize = 1 << 8;
    let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
    let coeffs = (1..=n).map(|_| Fr::rand(rng)).collect::<Vec<_>>();

    let argument = WellformednessArgument::new(vec![coeffs]);
    let commitments = argument.commit(&srs);

    let coeffs = (1..=n).map(|_| Fr::rand(rng)).collect::<Vec<_>>();
    let argument = WellformednessArgument::new(vec![coeffs]);
    let challenges = (0..1).map(|_| Fr::rand(rng)).collect::<Vec<_>>();

    let proof = argument.make_argument(challenges.clone(), &srs);

    let valid = WellformednessArgument::verify(n, &challenges, &commitments,  &proof, &srs);

    assert!(!valid);
}