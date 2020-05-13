use ff::{Field, PrimeField};
use futures::Future;
use groupy::{CurveAffine, CurveProjective};
use paired::{Engine, PairingCurveAffine};
use rayon::prelude::*;
use std::sync::Arc;

use super::{BatchPreparedVerifyingKey, PreparedVerifyingKey, Proof, VerifyingKey};
use crate::gpu::LockedMultiexpKernel;
use crate::multicore::Worker;
use crate::multiexp::{multiexp, FullDensity};
use crate::SynthesisError;

pub fn prepare_verifying_key<E: Engine>(vk: &VerifyingKey<E>) -> PreparedVerifyingKey<E> {
    let mut gamma = vk.gamma_g2;
    gamma.negate();
    let mut delta = vk.delta_g2;
    delta.negate();

    PreparedVerifyingKey {
        alpha_g1_beta_g2: E::pairing(vk.alpha_g1, vk.beta_g2),
        neg_gamma_g2: gamma.prepare(),
        neg_delta_g2: delta.prepare(),
        ic: vk.ic.clone(),
    }
}

pub fn prepare_batch_verifying_key<E: Engine>(
    vk: &VerifyingKey<E>,
) -> BatchPreparedVerifyingKey<E> {
    BatchPreparedVerifyingKey {
        alpha_g1_beta_g2: E::pairing(vk.alpha_g1, vk.beta_g2),
        gamma_g2: vk.gamma_g2.prepare(),
        delta_g2: vk.delta_g2.prepare(),
        ic: vk.ic.clone(),
    }
}

pub fn verify_proof<'a, E: Engine>(
    pvk: &'a PreparedVerifyingKey<E>,
    proof: &Proof<E>,
    public_inputs: &[E::Fr],
) -> Result<bool, SynthesisError> {
    if (public_inputs.len() + 1) != pvk.ic.len() {
        return Err(SynthesisError::MalformedVerifyingKey);
    }

    let mut acc = pvk.ic[0].into_projective();

    for (i, b) in public_inputs.iter().zip(pvk.ic.iter().skip(1)) {
        acc.add_assign(&b.mul(i.into_repr()));
    }

    // The original verification equation is:
    // A * B = alpha * beta + inputs * gamma + C * delta
    // ... however, we rearrange it so that it is:
    // A * B - inputs * gamma - C * delta = alpha * beta
    // or equivalently:
    // A * B + inputs * (-gamma) + C * (-delta) = alpha * beta
    // which allows us to do a single final exponentiation.

    Ok(E::final_exponentiation(&E::miller_loop(
        [
            (&proof.a.prepare(), &proof.b.prepare()),
            (&acc.into_affine().prepare(), &pvk.neg_gamma_g2),
            (&proof.c.prepare(), &pvk.neg_delta_g2),
        ]
        .iter(),
    ))
    .unwrap()
        == pvk.alpha_g1_beta_g2)
}

/// Randomized batch verification - see Appendix B.2 in Zcash spec
pub fn verify_proofs_batch<'a, E: Engine, R: rand::RngCore>(
    pvk: &'a BatchPreparedVerifyingKey<E>,
    rng: &mut R,
    proofs: &[&Proof<E>],
    public_inputs: &[Vec<E::Fr>],
) -> Result<bool, SynthesisError>
where
    <<E as ff::ScalarEngine>::Fr as ff::PrimeField>::Repr: From<<E as ff::ScalarEngine>::Fr>,
{
    for pub_input in public_inputs {
        if (pub_input.len() + 1) != pvk.ic.len() {
            return Err(SynthesisError::MalformedVerifyingKey);
        }
    }

    let worker = Worker::new();
    let pi_num = pvk.ic.len() - 1;
    let proof_num = proofs.len();

    // choose random coefficients for combining the proofs
    let mut r: Vec<E::Fr> = Vec::with_capacity(proof_num);
    for _ in 0..proof_num {
        use rand::Rng;

        let t: u128 = rng.gen();
        let mut el = E::Fr::zero().into_repr();
        let el_ref: &mut [u64] = el.as_mut();
        assert!(el_ref.len() > 1);
        el_ref[0] = (t & (-1i64 as u128) >> 64) as u64;
        el_ref[1] = (t >> 64) as u64;

        r.push(E::Fr::from_repr(el).unwrap());
    }

    let mut sum_r = E::Fr::zero();
    for i in r.iter() {
        sum_r.add_assign(i);
    }

    // create corresponding scalars for public input vk elements
    let pi_scalars: Vec<_> = (0..pi_num)
        .into_par_iter()
        .map(|i| {
            let mut pi = E::Fr::zero();
            for j in 0..proof_num {
                // z_j * a_j,i
                let mut tmp = r[j];
                tmp.mul_assign(&public_inputs[j][i]);
                pi.add_assign(&tmp);
            }
            pi.into_repr()
        })
        .collect();

    let mut multiexp_kern = get_verifier_kernel(pi_num);

    // create group element corresponding to public input combination
    // This roughly corresponds to Accum_Gamma in spec
    let mut acc_pi = pvk.ic[0].mul(sum_r.into_repr());
    acc_pi.add_assign(
        &multiexp(
            &worker,
            (Arc::new(pvk.ic[1..].to_vec()), 0),
            FullDensity,
            Arc::new(pi_scalars),
            &mut multiexp_kern,
        )
        .wait()
        .unwrap(),
    );

    // This corresponds to Accum_Y
    // -Accum_Y
    sum_r.negate();
    // This corresponds to Y^-Accum_Y
    let acc_y = pvk.alpha_g1_beta_g2.pow(&sum_r.into_repr());

    // This corresponds to Accum_Delta
    let mut acc_c = E::G1::zero();
    for (rand_coeff, proof) in r.iter().zip(proofs.iter()) {
        let mut tmp: E::G1 = proof.c.into();
        tmp.mul_assign(*rand_coeff);
        acc_c.add_assign(&tmp);
    }

    // This corresponds to Accum_AB
    let ml = r
        .par_iter()
        .zip(proofs.par_iter())
        .map(|(rand_coeff, proof)| {
            // [z_j] pi_j,A
            let mut tmp: E::G1 = proof.a.into();
            tmp.mul_assign(*rand_coeff);
            let g1 = tmp.into_affine().prepare();

            // -pi_j,B
            let mut tmp: E::G2 = proof.b.into();
            tmp.negate();
            let g2 = tmp.into_affine().prepare();

            (g1, g2)
        })
        .collect::<Vec<_>>();
    let mut parts = ml.iter().map(|(a, b)| (a, b)).collect::<Vec<_>>();

    // MillerLoop(Accum_Delta)
    let acc_c_prepared = acc_c.into_affine().prepare();
    parts.push((&acc_c_prepared, &pvk.delta_g2));

    // MillerLoop(\sum Accum_Gamma)
    let acc_pi_prepared = acc_pi.into_affine().prepare();
    parts.push((&acc_pi_prepared, &pvk.gamma_g2));

    let res = E::miller_loop(&parts);
    Ok(E::final_exponentiation(&res).unwrap() == acc_y)
}

fn get_verifier_kernel<E: Engine>(pi_num: usize) -> Option<LockedMultiexpKernel<E>> {
    match &std::env::var("BELLMAN_VERIFIER")
        .unwrap_or("auto".to_string())
        .to_lowercase()[..]
    {
        "gpu" => {
            let log_d = (pi_num as f32).log2().ceil() as usize;
            Some(LockedMultiexpKernel::<E>::new(log_d, false))
        }
        "cpu" => None,
        "auto" => None,
        s => panic!("Invalid verifier device selected: {}", s),
    }
}
