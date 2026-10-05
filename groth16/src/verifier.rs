use group::{Curve, CurveAffine, WnafBase, WnafScalar};
use pairing::{MillerLoopResult, MultiMillerLoop};
use std::ops::{AddAssign, Neg};

use super::{PUBLIC_INPUT_WINDOW, PreparedVerifyingKey, Proof, VerifyingKey};

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
        ic_wnaf: vk
            .ic
            .iter()
            .skip(1)
            .map(|base| WnafBase::new(base.to_curve()))
            .collect(),
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

    let mut acc = pvk.ic[0].to_curve();

    for (input, base) in public_inputs.iter().zip(pvk.ic_wnaf.iter()) {
        // Public inputs may be multiplied with a variable-time window method.
        let term = base * &WnafScalar::<E::Fr, PUBLIC_INPUT_WINDOW>::new(input);
        AddAssign::<&E::G1>::add_assign(&mut acc, &term);
    }

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
