use crate::pairing::ff::{Field};
use crate::pairing::{Engine, CurveProjective};
use std::marker::PhantomData;

use super::{Proof, SxyAdvice};
use super::batch::Batch;
use super::poly::{SxEval, SyEval};
use super::parameters::{Parameters, NUM_BLINDINGS};

use crate::SynthesisError;

use crate::sonic::transcript::{Transcript, TranscriptProtocol};
use crate::sonic::util::*;
use crate::sonic::cs::{Backend, SynthesisDriver};
use crate::sonic::cs::{Circuit, Variable, Coeff};
use crate::sonic::srs::SRS;
use crate::sonic::sonic::{CountN, Basic};

pub fn create_advice_on_information_and_srs<E: Engine, C: Circuit<E>, S: SynthesisDriver>(
    circuit: &C,
    proof: &Proof<E>,
    srs: &SRS<E>,
    n: usize
) -> Result<SxyAdvice<E>, SynthesisError>
{
    let z: E::Fr;
    let y: E::Fr;
    {
        let mut transcript = Transcript::new(&[]);
        transcript.commit_point(&proof.r);
        y = transcript.get_challenge_scalar();
        transcript.commit_point(&proof.t);
        z = transcript.get_challenge_scalar();
    }
    let z_inv = z.inverse().ok_or(SynthesisError::DivisionByZero)?;

    let (s_poly_negative, s_poly_positive) = {
        let mut tmp = SxEval::new(y, n);
        S::synthesize(&mut tmp, circuit)?;

        tmp.poly()
    };

    // Compute S commitment
    let s = multiexp(
        srs.g_positive_x_alpha[0..(2 * n)]
            .iter()
            .chain_ext(srs.g_negative_x_alpha[0..(n)].iter()),
        s_poly_positive.iter().chain_ext(s_poly_negative.iter())
    ).into_affine();

    // Compute s(z, y)
    let mut szy = E::Fr::zero();
    {
        szy.add_assign(& evaluate_at_consequitive_powers(& s_poly_positive[..], z, z));
        szy.add_assign(& evaluate_at_consequitive_powers(& s_poly_negative[..], z_inv, z_inv));
    }

    // Compute kate opening
    let opening = {
        let mut open = szy;
        open.negate();

        let poly = kate_divison(
            s_poly_negative.iter().rev().chain_ext(Some(open).iter()).chain_ext(s_poly_positive.iter()),
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

    Ok(SxyAdvice {
        s,
        szy,
        opening
    })
}

pub fn create_advice<E: Engine, C: Circuit<E>, S: SynthesisDriver>(
    circuit: &C,
    proof: &Proof<E>,
    parameters: &Parameters<E>,
) -> Result<SxyAdvice<E>, SynthesisError>
{
    let n = parameters.vk.n;
    create_advice_on_information_and_srs::<E, C, S>(circuit, proof, &parameters.srs, n)   
}

pub fn create_advice_on_srs<E: Engine, C: Circuit<E>, S: SynthesisDriver>(
    circuit: &C,
    proof: &Proof<E>,
    srs: &SRS<E>
) -> Result<SxyAdvice<E>, SynthesisError>
{
    // annoying, but we need n to compute s(z, y), and this isn't
    // precomputed anywhere yet
    let n = {
        let mut tmp = CountN::<S>::new();
        S::synthesize(&mut tmp, circuit)?;

        tmp.n
    };

    create_advice_on_information_and_srs::<E, C, S>(circuit, proof, srs, n)   
}

pub fn create_proof<E: Engine, C: Circuit<E>, S: SynthesisDriver>(
    circuit: &C,
    parameters: &Parameters<E>
) -> Result<Proof<E>, SynthesisError> {
    create_proof_on_srs::<E, C, S>(circuit, &parameters.srs)
}

extern crate rand;
use self::rand::{Rand, Rng, thread_rng};
use crate::sonic::sonic::Wires;

pub fn create_proof_on_srs<E: Engine, C: Circuit<E>, S: SynthesisDriver>(
    circuit: &C,
    srs: &SRS<E>
) -> Result<Proof<E>, SynthesisError>
{
    let mut wires = Wires::new();

    S::synthesize(&mut wires, circuit)?;

    let n = wires.a.len();

    let mut transcript = Transcript::new(&[]);

    let rng = &mut thread_rng();

    // c_{n+1}, c_{n+2}, c_{n+3}, c_{n+4}
    let blindings: Vec<E::Fr> = (0..NUM_BLINDINGS).into_iter().map(|_| E::Fr::rand(rng)).collect();

    // r is a commitment to r(X, 1)
    let r = polynomial_commitment::<E, _>(
        n, 
        2*n + NUM_BLINDINGS, 
        n, 
        &srs,
        blindings.iter().rev()
            .chain_ext(wires.c.iter().rev())
            .chain_ext(wires.b.iter().rev())
            .chain_ext(Some(E::Fr::zero()).iter())
            .chain_ext(wires.a.iter()),
    );

    transcript.commit_point(&r);

    let y: E::Fr = transcript.get_challenge_scalar();

    // create r(X, 1) by observation that it's just a series of coefficients.
    // Used representation is for powers X^{-2n}...X^{-n-1}, X^{-n}...X^{-1}, X^{1}...X^{n}
    // Same representation is ok for r(X, Y) too cause powers always match
    let mut rx1 = wires.b;
    rx1.extend(wires.c);
    rx1.extend(blindings.clone()); 
    rx1.reverse();
    rx1.push(E::Fr::zero());
    rx1.extend(wires.a);

    let mut rxy = rx1.clone();

    let y_inv = y.inverse().ok_or(SynthesisError::DivisionByZero)?;

    // y^(-2n - num blindings)
    let tmp = y_inv.pow(&[(2*n + NUM_BLINDINGS) as u64]);
    mut_distribute_consequitive_powers(
        &mut rxy,
        tmp,
        y,
    );
    
    // negative powers [-1, -2n], positive [1, n]
    let (mut s_poly_negative, s_poly_positive) = {
        let mut tmp = SxEval::new(y, n);
        S::synthesize(&mut tmp, circuit)?;

        tmp.poly()
    };

    // r'(X, y) = r(X, y) + s(X, y). Note `y` - those are evaluated at the point already
    let mut rxy_prime = rxy.clone();
    {
        // extend to have powers [n+1, 2n]
        rxy_prime.resize(4 * n + 1 + NUM_BLINDINGS, E::Fr::zero());
        s_poly_negative.reverse();

        let neg_poly_len = s_poly_negative.len();
        add_polynomials(&mut rxy_prime[(NUM_BLINDINGS+neg_poly_len)..(2 * n + NUM_BLINDINGS)], &s_poly_negative[..]);
        s_poly_negative.reverse();

        add_polynomials(&mut rxy_prime[(2 * n + 1 + NUM_BLINDINGS)..], &s_poly_positive[..])
        
        // // add coefficients in front of X^{-2n}...X^{-n-1}, X^{-n}...X^{-1}
        // for (r, s) in rxy_prime[NUM_BLINDINGS..(2 * n + NUM_BLINDINGS)]
        //     .iter_mut()
        //     .rev()
        //     .zip(s_poly_negative)
        // {
        //     r.add_assign(&s);
        // }
        // // add coefficients in front of X^{1}...X^{n}, X^{n+1}...X^{2*n}
        // for (r, s) in rxy_prime[(2 * n + 1 + NUM_BLINDINGS)..].iter_mut().zip(s_poly_positive) {
        //     r.add_assign(&s);
        // }
    }

    // by this point all R related polynomials are blinded and evaluated for Y variable

    // t(X, y) = r'(X, y)*r(X, 1) and will be later evaluated at z
    // contained degree in respect to X are from -4*n to 3*n including X^0
    let mut txy = multiply_polynomials::<E>(rx1.clone(), rxy_prime);
    txy[4 * n + 2 * NUM_BLINDINGS] = E::Fr::zero(); // -k(y)

    // commit to t(X, y) to later open at z
    let t = polynomial_commitment(
        srs.d, 
        (4 * n) + 2*NUM_BLINDINGS,
        3 * n,
        srs,
        // skip what would be zero power
        txy[0..(4 * n) + 2*NUM_BLINDINGS].iter()
            .chain_ext(txy[(4 * n + 2*NUM_BLINDINGS + 1)..].iter()),
    );

    transcript.commit_point(&t);

    let z: E::Fr = transcript.get_challenge_scalar();
    let z_inv = z.inverse().ok_or(SynthesisError::DivisionByZero)?;

    let rz = {
        let tmp = z_inv.pow(&[(2*n + NUM_BLINDINGS) as u64]);

        evaluate_at_consequitive_powers(&rx1, tmp, z)
    };

    // rzy is evaluation of r(X, Y) at z, y
    let rzy = {
        let tmp = z_inv.pow(&[(2*n + NUM_BLINDINGS) as u64]);

        evaluate_at_consequitive_powers(&rxy, tmp, z)
    };
    
    transcript.commit_scalar(&rz);
    transcript.commit_scalar(&rzy);

    let r1: E::Fr = transcript.get_challenge_scalar();

    let zy_opening = {
        // r(X, 1) - r(z, y)
        // subtract constant term from R(X, 1)
        rx1[(2 * n + NUM_BLINDINGS)].sub_assign(&rzy);

        let mut point = y;
        point.mul_assign(&z);

        polynomial_commitment_opening(
            2 * n + NUM_BLINDINGS,
            n, 
            &rx1,
            point,
            srs
        )
    };

    assert_eq!(rx1.len(), 3*n + NUM_BLINDINGS + 1);

    // it's an opening of t(X, y) at z
    let z_opening = {
        rx1[(2 * n + NUM_BLINDINGS)].add_assign(&rzy); // restore

        let rx1_len = rx1.len();
        mul_add_polynomials(&mut txy[(2 * n + NUM_BLINDINGS)..(2 * n + NUM_BLINDINGS + rx1_len)], &rx1[..], r1);

        // // skip powers from until reach -2n - NUM_BLINDINGS
        // for (t, &r) in txy[(2 * n + NUM_BLINDINGS)..].iter_mut().zip(rx1.iter()) {
        //     let mut r = r;
        //     r.mul_assign(&r1);
        //     t.add_assign(&r);
        // }

        let val = {
            let tmp = z_inv.pow(&[(4*n + 2*NUM_BLINDINGS) as u64]);

            evaluate_at_consequitive_powers(&txy, tmp, z)
        };

        txy[(4 * n + 2*NUM_BLINDINGS)].sub_assign(&val);

        polynomial_commitment_opening(
            4*n + 2*NUM_BLINDINGS,
            3*n, 
            &txy,
            z, 
            srs)
    };

    Ok(Proof {
        r, rz, rzy, t, z_opening, zy_opening
    })
}
