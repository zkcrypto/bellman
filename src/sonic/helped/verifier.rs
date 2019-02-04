use ff::{Field};
use pairing::{Engine, CurveProjective};
use std::marker::PhantomData;

use super::{Proof, SxyAdvice};
use super::batch::Batch;
use super::poly::{SxEval, SyEval};

use crate::SynthesisError;

use crate::sonic::transcript::{Transcript, TranscriptProtocol};
use crate::sonic::util::*;
use crate::sonic::cs::{Backend, SynthesisDriver};
use crate::sonic::cs::{Circuit, Variable, Coeff};
use crate::sonic::srs::SRS;

pub struct MultiVerifier<E: Engine, C: Circuit<E>, S: SynthesisDriver> {
    circuit: C,
    batch: Batch<E>,
    k_map: Vec<usize>,
    n: usize,
    q: usize,
    _marker: PhantomData<(E, S)>
}

impl<E: Engine, C: Circuit<E>, S: SynthesisDriver> MultiVerifier<E, C, S> {
    pub fn new(circuit: C, srs: &SRS<E>) -> Result<Self, SynthesisError> {
        struct Preprocess<E: Engine> {
            k_map: Vec<usize>,
            n: usize,
            q: usize,
            _marker: PhantomData<E>
        }

        impl<'a, E: Engine> Backend<E> for &'a mut Preprocess<E> {
            fn new_k_power(&mut self, index: usize) {
                self.k_map.push(index);
            }

            fn new_multiplication_gate(&mut self) {
                self.n += 1;
            }

            fn new_linear_constraint(&mut self) {
                self.q += 1;
            }
        }

        let mut preprocess = Preprocess { k_map: vec![], n: 0, q: 0, _marker: PhantomData };

        S::synthesize(&mut preprocess, &circuit)?;

        Ok(MultiVerifier {
            circuit,
            batch: Batch::new(srs, preprocess.n),
            k_map: preprocess.k_map,
            n: preprocess.n,
            q: preprocess.q,
            _marker: PhantomData
        })
    }

    pub fn add_aggregate(
        &mut self,
        proofs: &[(Proof<E>, SxyAdvice<E>)],
        aggregate: &Aggregate<E>,
    )
    {
        let mut transcript = Transcript::new(&[]);
        let mut y_values: Vec<E::Fr> = Vec::with_capacity(proofs.len());
        for &(ref proof, ref sxyadvice) in proofs {
            {
                let mut transcript = Transcript::new(&[]);
                transcript.commit_point(&proof.r);
                y_values.push(transcript.get_challenge_scalar());
            }

            transcript.commit_point(&sxyadvice.s);
        }

        let z: E::Fr = transcript.get_challenge_scalar();

        transcript.commit_point(&aggregate.c);

        let w: E::Fr = transcript.get_challenge_scalar();

        let szw = {
            let mut tmp = SxEval::new(w, self.n);
            S::synthesize(&mut tmp, &self.circuit).unwrap(); // TODO

            tmp.finalize(z)
        };

        {
            // TODO: like everything else doing this, this isn't really random
            let random: E::Fr;
            let mut transcript = transcript.clone();
            random = transcript.get_challenge_scalar();

            self.batch.add_opening(aggregate.opening, random, w);
            self.batch.add_commitment(aggregate.c, random);
            self.batch.add_opening_value(szw, random);
        }

        for ((opening, value), &y) in aggregate.c_openings.iter().zip(y_values.iter()) {
            let random: E::Fr;
            let mut transcript = transcript.clone();
            random = transcript.get_challenge_scalar();

            self.batch.add_opening(*opening, random, y);
            self.batch.add_commitment(aggregate.c, random);
            self.batch.add_opening_value(*value, random);
        }

        let random: E::Fr;
        {
            let mut transcript = transcript.clone();
            random = transcript.get_challenge_scalar();
        }

        let mut expected_value = E::Fr::zero();
        for ((_, advice), c_opening) in proofs.iter().zip(aggregate.c_openings.iter()) {
            let mut r: E::Fr = transcript.get_challenge_scalar();

            // expected value of the later opening
            {
                let mut tmp = c_opening.1;
                tmp.mul_assign(&r);
                expected_value.add_assign(&tmp);
            }

            r.mul_assign(&random);

            self.batch.add_commitment(advice.s, r);
        }

        self.batch.add_opening_value(expected_value, random);
        self.batch.add_opening(aggregate.s_opening, random, z);
    }

    pub fn add_proof_with_advice(
        &mut self,
        proof: &Proof<E>,
        inputs: &[E::Fr],
        advice: &SxyAdvice<E>,
    )
    {
        let mut z = None;

        self.add_proof(proof, inputs, |_z, _y| {
            z = Some(_z);
            Some(advice.szy)
        });

        let z = z.unwrap();

        // We need to open up SxyAdvice.s at z using SxyAdvice.opening
        let mut transcript = Transcript::new(&[]);
        transcript.commit_point(&advice.opening);
        transcript.commit_point(&advice.s);
        transcript.commit_scalar(&advice.szy);
        let random: E::Fr = transcript.get_challenge_scalar();

        self.batch.add_opening(advice.opening, random, z);
        self.batch.add_commitment(advice.s, random);
        self.batch.add_opening_value(advice.szy, random);
    }

    pub fn add_proof<F>(
        &mut self,
        proof: &Proof<E>,
        inputs: &[E::Fr],
        sxy: F
    )
        where F: FnOnce(E::Fr, E::Fr) -> Option<E::Fr>
    {
        let mut transcript = Transcript::new(&[]);

        transcript.commit_point(&proof.r);

        let y: E::Fr = transcript.get_challenge_scalar();

        transcript.commit_point(&proof.t);

        let z: E::Fr = transcript.get_challenge_scalar();

        transcript.commit_scalar(&proof.rz);
        transcript.commit_scalar(&proof.rzy);

        let r1: E::Fr = transcript.get_challenge_scalar();

        transcript.commit_point(&proof.z_opening);
        transcript.commit_point(&proof.zy_opening);

        // First, the easy one. Let's open up proof.r at zy, using proof.zy_opening
        // as the evidence and proof.rzy as the opening.
        {
            let random = transcript.get_challenge_scalar();
            let mut zy = z;
            zy.mul_assign(&y);
            self.batch.add_opening(proof.zy_opening, random, zy);
            self.batch.add_commitment_max_n(proof.r, random);
            self.batch.add_opening_value(proof.rzy, random);
        }

        // Now we need to compute t(z, y) with what we have. Let's compute k(y).
        let mut ky = E::Fr::zero();
        for (exp, input) in self.k_map.iter().zip(Some(E::Fr::one()).iter().chain(inputs.iter())) {
            let mut term = y.pow(&[(*exp + self.n) as u64]);
            term.mul_assign(input);
            ky.add_assign(&term);
        }

        // Compute s(z, y)
        let szy = sxy(z, y).unwrap_or_else(|| {
            let mut tmp = SxEval::new(y, self.n);
            S::synthesize(&mut tmp, &self.circuit).unwrap(); // TODO

            tmp.finalize(z)

            // let mut tmp = SyEval::new(z, self.n, self.q);
            // S::synthesize(&mut tmp, &self.circuit).unwrap(); // TODO

            // tmp.finalize(y)
        });

        // Finally, compute t(z, y)
        let mut tzy = proof.rzy;
        tzy.add_assign(&szy);
        tzy.mul_assign(&proof.rz);
        tzy.sub_assign(&ky);

        // We open these both at the same time by keeping their commitments
        // linearly independent (using r1).
        {
            let mut random = transcript.get_challenge_scalar();

            self.batch.add_opening(proof.z_opening, random, z);
            self.batch.add_opening_value(tzy, random);
            self.batch.add_commitment(proof.t, random);

            random.mul_assign(&r1);

            self.batch.add_opening_value(proof.rz, random);
            self.batch.add_commitment_max_n(proof.r, random);
        }
    }

    pub fn check_all(self) -> bool {
        self.batch.check_all()
    }
}

#[derive(Clone)]
pub struct Aggregate<E: Engine> {
    // Commitment to s(z, Y)
    c: E::G1Affine,
    // We have to open each of the S commitments to a random point `z`
    s_opening: E::G1Affine,
    // We have to open C to each constituent `y`
    c_openings: Vec<(E::G1Affine, E::Fr)>,
    // Then we have to finally open C
    opening: E::G1Affine,
}

pub fn create_aggregate<E: Engine, C: Circuit<E>, S: SynthesisDriver>(
    circuit: &C,
    inputs: &[(Proof<E>, SxyAdvice<E>)],
    srs: &SRS<E>,
) -> Aggregate<E>
{
    // TODO: precompute this?
    let (n, q) = {
        struct CountN {
            n: usize,
            q: usize
        }

        impl<'a, E: Engine> Backend<E> for &'a mut CountN {
            fn new_multiplication_gate(&mut self) {
                self.n += 1;
            }

            fn new_linear_constraint(&mut self) {
                self.q += 1;
            }
        }

        let mut tmp = CountN{n:0,q:0};
        S::synthesize(&mut tmp, circuit).unwrap(); // TODO

        (tmp.n, tmp.q)
    };

    let mut transcript = Transcript::new(&[]);
    let mut y_values: Vec<E::Fr> = Vec::with_capacity(inputs.len());
    for &(ref proof, ref sxyadvice) in inputs {
        {
            let mut transcript = Transcript::new(&[]);
            transcript.commit_point(&proof.r);
            y_values.push(transcript.get_challenge_scalar());
        }

        transcript.commit_point(&sxyadvice.s);
    }

    let z: E::Fr = transcript.get_challenge_scalar();

    // Compute s(z, Y)
    let (s_poly_negative, s_poly_positive) = {
        let mut tmp = SyEval::new(z, n, q);
        S::synthesize(&mut tmp, circuit).unwrap(); // TODO

        tmp.poly()
    };

    // Compute C = g^{s(z, x)}
    let c = multiexp(
        srs.g_positive_x_alpha[0..(n + q)]
            .iter()
            .chain_ext(srs.g_negative_x_alpha[0..n].iter()),
        s_poly_positive.iter().chain_ext(s_poly_negative.iter())
    ).into_affine();

    transcript.commit_point(&c);

    // Open C at w
    let w: E::Fr = transcript.get_challenge_scalar();

    let value = compute_value::<E>(&w, &s_poly_positive, &s_poly_negative);

    let opening = {
        let mut value = value;
        value.negate();

        let poly = kate_divison(
            s_poly_negative.iter().rev().chain_ext(Some(value).iter()).chain_ext(s_poly_positive.iter()),
            w,
        );

        let negative_poly = poly[0..n].iter().rev();
        let positive_poly = poly[n..].iter();
        multiexp(
            srs.g_negative_x[1..(negative_poly.len() + 1)].iter().chain_ext(
                srs.g_positive_x[0..positive_poly.len()].iter()
            ),
            negative_poly.chain_ext(positive_poly)
        ).into_affine()
    };

    // Let's open up C to every y.
    fn compute_value<E: Engine>(y: &E::Fr, poly_positive: &[E::Fr], poly_negative: &[E::Fr]) -> E::Fr {
        let mut value = E::Fr::zero();

        let yinv = y.inverse().unwrap(); // TODO
        let mut tmp = yinv;
        for &coeff in poly_negative {
            let mut coeff = coeff;
            coeff.mul_assign(&tmp);
            value.add_assign(&coeff);
            tmp.mul_assign(&yinv);
        }

        let mut tmp = *y;
        for &coeff in poly_positive {
            let mut coeff = coeff;
            coeff.mul_assign(&tmp);
            value.add_assign(&coeff);
            tmp.mul_assign(&y);
        }

        value
    }

    let mut c_openings = vec![];
    for y in &y_values {
        let value = compute_value::<E>(y, &s_poly_positive, &s_poly_negative);

        let opening = {
            let mut value = value;
            value.negate();

            let poly = kate_divison(
                s_poly_negative.iter().rev().chain_ext(Some(value).iter()).chain_ext(s_poly_positive.iter()),
                *y,
            );

            let negative_poly = poly[0..n].iter().rev();
            let positive_poly = poly[n..].iter();
            multiexp(
                srs.g_negative_x[1..(negative_poly.len() + 1)].iter().chain_ext(
                    srs.g_positive_x[0..positive_poly.len()].iter()
                ),
                negative_poly.chain_ext(positive_poly)
            ).into_affine()
        };

        c_openings.push((opening, value));
    }

    // Okay, great. Now we need to open up each S at the same point z to the same value.
    // Since we're opening up all the S's at the same point, we create a bunch of random
    // challenges instead and open up a random linear combination.

    let mut poly_negative = vec![E::Fr::zero(); n];
    let mut poly_positive = vec![E::Fr::zero(); 2*n];
    let mut expected_value = E::Fr::zero();

    for (y, c_opening) in y_values.iter().zip(c_openings.iter()) {
        // Compute s(X, y_i)
        let (s_poly_negative, s_poly_positive) = {
            let mut tmp = SxEval::new(*y, n);
            S::synthesize(&mut tmp, circuit).unwrap(); // TODO

            tmp.poly()
        };

        let mut value = c_opening.1;
        let r: E::Fr = transcript.get_challenge_scalar();
        value.mul_assign(&r);
        expected_value.add_assign(&value);

        for (mut coeff, target) in s_poly_negative.into_iter().zip(poly_negative.iter_mut()) {
            coeff.mul_assign(&r);
            target.add_assign(&coeff);
        }

        for (mut coeff, target) in s_poly_positive.into_iter().zip(poly_positive.iter_mut()) {
            coeff.mul_assign(&r);
            target.add_assign(&coeff);
        }
    }

    let s_opening = {
        let mut value = expected_value;
        value.negate();

        let poly = kate_divison(
            poly_negative.iter().rev().chain_ext(Some(value).iter()).chain_ext(poly_positive.iter()),
            z,
        );

        let negative_poly = poly[0..n].iter().rev();
        let positive_poly = poly[n..].iter();
        multiexp(
            srs.g_negative_x[1..(negative_poly.len() + 1)].iter().chain_ext(
                srs.g_positive_x[0..positive_poly.len()].iter()
            ),
            negative_poly.chain_ext(positive_poly)
        ).into_affine()
    };

    Aggregate {
        // Commitment to s(z, Y)
        c,
        // We have to open each of the S commitments to a random point `z`
        s_opening,
        // We have to open C to each constituent `y`
        c_openings,
        // Then we have to finally open C
        opening,
    }
}