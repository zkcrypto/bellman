use group::{Curve, CurveAffine};
use pairing::{MillerLoopResult, MultiMillerLoop};
use std::ops::Neg;

use super::{PreparedVerifyingKey, Proof, VerifyingKey, multiexp::multiexp_vartime};

use bellman::VerificationError;

pub mod batch;

pub fn prepare_verifying_key<E: MultiMillerLoop>(vk: &VerifyingKey<E>) -> PreparedVerifyingKey<E> {
    let gamma = vk.gamma_g2.neg();
    let delta = vk.delta_g2.neg();

    PreparedVerifyingKey {
        alpha_g1_beta_g2: E::pairing(&vk.alpha_g1, &vk.beta_g2),
        neg_gamma_g2: E::prepare_reusable_g2(gamma),
        neg_delta_g2: E::prepare_reusable_g2(delta),
        ic: vk.ic.clone(),
    }
}

pub fn verify_proof<E: MultiMillerLoop>(
    pvk: &PreparedVerifyingKey<E>,
    proof: &Proof<E>,
    public_inputs: &[E::Fr],
) -> Result<(), VerificationError> {
    if (public_inputs.len() + 1) != pvk.ic.len() {
        return Err(VerificationError::InvalidVerifyingKey);
    }

    let bases = pvk.ic[1..]
        .iter()
        .map(|base| base.to_curve())
        .collect::<Vec<_>>();
    let mut acc = pvk.ic[0].to_curve();
    acc += &multiexp_vartime(&bases, public_inputs);

    // The original verification equation is:
    // A * B = alpha * beta + inputs * gamma + C * delta
    // ... however, we rearrange it so that it is:
    // A * B - inputs * gamma - C * delta = alpha * beta
    // or equivalently:
    // A * B + inputs * (-gamma) + C * (-delta) = alpha * beta
    // which allows us to do a single final exponentiation.

    if pvk.alpha_g1_beta_g2
        == E::multi_miller_loop(&[
            (&proof.a, &proof.b.into()),
            (&acc.to_affine(), &pvk.neg_gamma_g2),
            (&proof.c, &pvk.neg_delta_g2),
        ])
        .final_exponentiation()
    {
        Ok(())
    } else {
        Err(VerificationError::InvalidProof)
    }
}
