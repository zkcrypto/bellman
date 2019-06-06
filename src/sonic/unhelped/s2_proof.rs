use crate::pairing::ff::{Field, PrimeField, PrimeFieldRepr};
use crate::pairing::{Engine, CurveProjective, CurveAffine};
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
    pub c_value: E::Fr,
    pub d_value: E::Fr,
    pub c_opening: E::G1Affine,
    pub d_opening: E::G1Affine
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
            let val = evaluate_at_consequitive_powers(&poly[1..], point, point);
            poly[0] = val;
            poly[0].negate();
            let opening = polynomial_commitment_opening(0, self.n, poly.iter(), point, &srs);

            (val, opening)
        };

        let (d, d_opening) = {
            let mut point = y.inverse().unwrap();
            point.mul_assign(&x);
            let val = evaluate_at_consequitive_powers(&poly[1..], point, point);
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

        let mut minus_xy = x;
        minus_xy.mul_assign(&y);
        minus_xy.negate();

        let mut h_alpha_term = proof.c_opening.mul(minus_xy.into_repr());
        let g_in_c = E::G1Affine::one().mul(proof.c_value);
        h_alpha_term.add_assign(&g_in_c);

        let h_alpha_term = h_alpha_term.into_affine();

        let valid = E::final_exponentiation(&E::miller_loop(&[
                (&proof.c_opening.prepare(), &alpha_x_precomp),
                (&h_alpha_term.prepare(), &alpha_precomp),
                (&proof.o.prepare(), &h_prep),
            ])).unwrap() == E::Fqk::one();

        if !valid {
            return false;
        } 

        // e(D,hαx)e(D−y−1z,hα) = e(O,h)e(g−d,hα)

        let mut minus_x_y_inv = x;
        minus_x_y_inv.mul_assign(&y.inverse().unwrap());
        minus_x_y_inv.negate();

        let mut h_alpha_term = proof.d_opening.mul(minus_x_y_inv.into_repr());
        let g_in_d = E::G1Affine::one().mul(proof.d_value);
        h_alpha_term.add_assign(&g_in_d);

        let h_alpha_term = h_alpha_term.into_affine();

        let valid = E::final_exponentiation(&E::miller_loop(&[
                (&proof.d_opening.prepare(), &alpha_x_precomp),
                (&h_alpha_term.prepare(), &alpha_precomp),
                (&proof.o.prepare(), &h_prep),
            ])).unwrap() == E::Fqk::one();

        if !valid {
            return false;
        } 

        true
    }
}


#[test]
fn test_s2_proof() {
    use crate::pairing::ff::{Field, PrimeField};
    use crate::pairing::{Engine, CurveAffine, CurveProjective};
    use crate::pairing::bls12_381::{Bls12, Fr};
    use std::time::{Instant};
    use crate::sonic::srs::SRS;
    use crate::sonic::cs::{Circuit, ConstraintSystem, LinearCombination};

    let srs_x = Fr::from_str("23923").unwrap();
    let srs_alpha = Fr::from_str("23728792").unwrap();
    println!("making srs");
    let start = Instant::now();
    let srs = SRS::<Bls12>::dummy(830564, srs_x, srs_alpha);
    println!("done in {:?}", start.elapsed());

    {
        use rand::{XorShiftRng, SeedableRng, Rand, Rng};
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let x: Fr = rng.gen();
        let y: Fr = rng.gen();

        let proof = S2Eval::new(1024);
        let proof = proof.evaluate(x, y, &srs);

        let valid = S2Eval::verify(x, y, &proof, &srs);

        assert!(valid);
    }
}