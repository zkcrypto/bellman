use std::ops::AddAssign;

use ff::Field;
use group::{Curve, Group};
use pairing::{MillerLoopResult, MultiMillerLoop};
use rand_core::{CryptoRng, RngCore};

use crate::{
    groth16::{PreparedVerifyingKey, Proof, VerifyingKey},
    VerificationError,
};

#[derive(Clone, Debug)]
pub struct Item<E: MultiMillerLoop> {
    proof: Proof<E>,
    inputs: Vec<E::Fr>,
}

impl<E: MultiMillerLoop> From<(&Proof<E>, &[E::Fr])> for Item<E> {
    fn from((proof, inputs): (&Proof<E>, &[E::Fr])) -> Self {
        (proof.clone(), inputs.to_owned()).into()
    }
}

impl<E: MultiMillerLoop> From<(Proof<E>, Vec<E::Fr>)> for Item<E> {
    fn from((proof, inputs): (Proof<E>, Vec<E::Fr>)) -> Self {
        Self { proof, inputs }
    }
}

#[derive(Debug)]
pub struct Verifier<E: MultiMillerLoop> {
    items: Vec<Item<E>>,
}

// Need to impl Default by hand to avoid a derived E: Default bound
impl<E: MultiMillerLoop> Default for Verifier<E> {
    fn default() -> Self {
        Self { items: Vec::new() }
    }
}

impl<E: MultiMillerLoop> Verifier<E>
where
    E::G1: AddAssign<E::G1>,
{
    pub fn new() -> Self {
        Self::default()
    }

    pub fn queue<I: Into<Item<E>>>(&mut self, item: I) {
        self.items.push(item.into())
    }

    /// Verify a batch of (proof, inputs) items with a particular
    /// [`PreparedVerifyingKey`].
    ///
    /// In practice, you would create a Spend batch verifier and an Output batch
    /// verifier, add all the (Spend, inputs)'s and (Output, inputs)'s from a
    /// block, and invoke this method on each, with the appropriate
    /// [`PreparedVerifyingKey`].
    #[allow(non_snake_case)]
    pub fn verify<R: RngCore + CryptoRng>(
        self,
        mut rng: R,
        vk: &VerifyingKey<E>,
    ) -> Result<(), VerificationError> {
        let mut ml_terms = Vec::<(E::G1Affine, E::G2Prepared)>::new();
        let mut acc_Gammas = vec![E::Fr::zero(); vk.ic.len()];
        let mut acc_Delta = E::G1::identity();
        let mut acc_Y = E::Fr::zero();

        for Item { proof, inputs } in self.items.into_iter() {
            let z = E::Fr::random(&mut rng);

            if inputs.len() + 1 != vk.ic.len() {
                return Err(VerificationError::InvalidVerifyingKey);
            }

            ml_terms.push(((proof.a * z).into(), (-proof.b).into()));

            acc_Gammas[0] += &z; // a_0 is implicitly set to 1 (??)
            for (a_i, acc_Gamma_i) in Iterator::zip(inputs.iter(), acc_Gammas.iter_mut().skip(1)) {
                *acc_Gamma_i += &(z * a_i);
            }
            acc_Delta += proof.c * z;
            acc_Y += &z;
        }

        ml_terms.push((acc_Delta.to_affine(), E::G2Prepared::from(vk.delta_g2)));

        let Psi = vk
            .ic
            .iter()
            .zip(acc_Gammas.iter())
            .map(|(&Psi_i, acc_Gamma_i)| Psi_i * acc_Gamma_i)
            .sum();

        ml_terms.push((E::G1Affine::from(Psi), E::G2Prepared::from(vk.gamma_g2)));

        // Y = PreparedVerifyingKey.alpha_g1_beta_g2
        //
        // Y^acc_Y in multiplicative notation is [acc_Y]Y (scalar mul) in
        // additive notation, which is the code convention here.
        let Y = E::pairing(&vk.alpha_g1, &vk.beta_g2) * acc_Y;

        let mut terms = vec![];
        ml_terms.iter().for_each(|(a, b)| terms.push((a, b)));

        if E::multi_miller_loop(terms.as_slice()).final_exponentiation() + Y == E::Gt::identity() {
            Ok(())
        } else {
            Err(VerificationError::InvalidProof)
        }
    }
}

impl<E: MultiMillerLoop> Item<E> {
    pub fn verify_single(self, pvk: &PreparedVerifyingKey<E>) -> Result<(), VerificationError> {
        super::verify_proof(pvk, &self.proof, &self.inputs)
    }
}