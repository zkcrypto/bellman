use crate::pairing::ff::{Field};
use crate::pairing::{Engine, CurveProjective};
use std::marker::PhantomData;

use super::{Proof, SxyAdvice};
use super::batch::Batch;
use super::poly::{SxEval, SyEval};
use super::Parameters;

use crate::SynthesisError;

use crate::sonic::transcript::{Transcript, TranscriptProtocol};
use crate::sonic::util::*;
use crate::sonic::cs::{Backend, SynthesisDriver};
use crate::sonic::cs::{Circuit, Variable, Coeff};
use crate::sonic::srs::SRS;
use crate::sonic::sonic::CountNandQ;

#[derive(Clone)]
pub struct Aggregate<E: Engine> {
    // Commitment to s(z, Y)
    pub c: E::G1Affine,
    // We have to open each of the S commitments to a random point `z`
    pub s_opening: E::G1Affine,
    // We have to open C to each constituent `y`
    pub c_openings: Vec<(E::G1Affine, E::Fr)>,
    // Then we have to finally open C
    pub opening: E::G1Affine,

    pub z: E::Fr,
    pub w: E::Fr,
}

pub fn create_aggregate<E: Engine, C: Circuit<E>, S: SynthesisDriver>(
    circuit: &C,
    inputs: &[(Proof<E>, SxyAdvice<E>)],
    params: &Parameters<E>,
) -> Aggregate<E>
{
    let n = params.vk.n;
    let q = params.vk.q;

    create_aggregate_on_srs_using_information::<E, C, S>(circuit, inputs, &params.srs, n, q)
}

pub fn create_aggregate_on_srs<E: Engine, C: Circuit<E>, S: SynthesisDriver>(
    circuit: &C,
    inputs: &[(Proof<E>, SxyAdvice<E>)],
    srs: &SRS<E>,
) -> Aggregate<E>
{
    // TODO: precompute this?
    let (n, q) = {
        let mut tmp = CountNandQ::<S>::new();

        S::synthesize(&mut tmp, circuit).unwrap(); // TODO

        (tmp.n, tmp.q)
    };

    create_aggregate_on_srs_using_information::<E, C, S>(circuit, inputs, srs, n, q)
}

pub fn create_aggregate_on_srs_using_information<E: Engine, C: Circuit<E>, S: SynthesisDriver>(
    circuit: &C,
    inputs: &[(Proof<E>, SxyAdvice<E>)],
    srs: &SRS<E>,
    n: usize,
    q: usize,
) -> Aggregate<E>
{
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

        polynomial_commitment_opening(
            n,
            0,
            s_poly_negative.iter().rev().chain_ext(Some(value).iter()).chain_ext(s_poly_positive.iter()),
            w,
            &srs
        )
    };

    // Let's open up C to every y.
    fn compute_value<E: Engine>(y: &E::Fr, poly_positive: &[E::Fr], poly_negative: &[E::Fr]) -> E::Fr {
        let mut value = E::Fr::zero();
        let yinv = y.inverse().unwrap(); // TODO

        let positive_powers_contrib = evaluate_at_consequitive_powers(poly_positive, *y, *y);
        let negative_powers_contrib = evaluate_at_consequitive_powers(poly_negative, yinv, yinv);
        value.add_assign(&positive_powers_contrib);
        value.add_assign(&negative_powers_contrib);

        value
    }

    use std::time::Instant;
    let start = Instant::now();

    let mut c_openings = vec![];
    for y in &y_values {
        let value = compute_value::<E>(y, &s_poly_positive, &s_poly_negative);

        let opening = {
            let mut value = value;
            value.negate();

            polynomial_commitment_opening(
                n,
                0,
                s_poly_negative.iter().rev().chain_ext(Some(value).iter()).chain_ext(s_poly_positive.iter()),
                *y,
                &srs
            )
        };

        c_openings.push((opening, value));
    }

    println!("Evaluation of s(z, Y) taken {:?}", start.elapsed());

    // Okay, great. Now we need to open up each S at the same point z to the same value.
    // Since we're opening up all the S's at the same point, we create a bunch of random
    // challenges instead and open up a random linear combination.

    let mut poly_negative = vec![E::Fr::zero(); n];
    let mut poly_positive = vec![E::Fr::zero(); 2*n];
    let mut expected_value = E::Fr::zero();

    // TODO: this part can be further parallelized due to synthesis of S(X, y) being singlethreaded
    let start = Instant::now();

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

        mul_add_polynomials(& mut poly_negative[..], &s_poly_negative[..], r);
        mul_add_polynomials(& mut poly_positive[..], &s_poly_positive[..], r);

    }

    println!("Re-evaluation of {} S polynomials taken {:?}", y_values.len(), start.elapsed());

    let s_opening = {
        let mut value = expected_value;
        value.negate();

        polynomial_commitment_opening(
            n,
            0,
            poly_negative.iter().rev().chain_ext(Some(value).iter()).chain_ext(poly_positive.iter()),
            z,
            &srs
        )

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

        z: z,

        w: w
    }
}