use ff::PrimeField;
use group::{CurveAffine, CurveProjective};
use pairing::{Engine, PairingCurveAffine};
use std::ops::{AddAssign, Neg};

use super::{PreparedVerifyingKey, Proof, VerifyingKey};

use crate::SynthesisError;

pub fn prepare_verifying_key<E: Engine>(vk: &VerifyingKey<E>) -> PreparedVerifyingKey<E> {
    let gamma = vk.gamma_g2.neg();
    let delta = vk.delta_g2.neg();

    PreparedVerifyingKey {
        alpha_g1_beta_g2: E::pairing(vk.alpha_g1, vk.beta_g2),
        neg_gamma_g2: gamma.prepare(),
        neg_delta_g2: delta.prepare(),
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
        AddAssign::<&E::G1>::add_assign(&mut acc, &b.mul(i.to_repr()));
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
