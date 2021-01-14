use std::{
    iter,
    ops::{AddAssign, Neg},
};

use ff::Field;
use group::{cofactor::CofactorCurveAffine, Curve, Group};
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

    #[allow(non_snake_case)]
    pub fn verify<R: RngCore + CryptoRng>(
        self,
        mut rng: R,
        pvk: &PreparedVerifyingKey<E>,
    ) -> Result<(), VerificationError> {
        let mut ml_terms = Vec::<(E::G1Affine, E::G2Prepared)>::new();
        let mut acc_Gammas = vec![E::Fr::zero(); pvk.ic.len()];
        let mut acc_Delta = E::G1::identity();
        let mut acc_Y = E::Fr::zero();

        for Item { proof, inputs } in self.items.into_iter() {
            let z = E::Fr::random(&mut rng);
            if inputs.len() + 1 != pvk.ic.len() {
                return Err(VerificationError::InvalidVerifyingKey);
            }
            acc_Gammas[0] += &z; // a_0 is implicitly set to 1 (??)
            for (a_i, acc_Gamma_i) in Iterator::zip(inputs.iter(), acc_Gammas.iter_mut().skip(1)) {
                *acc_Gamma_i += &(z * a_i);
            }
            acc_Delta += proof.c * &z;
            acc_Y += &z;
            ml_terms.push(((proof.a * &z).into(), (-proof.b).into()));
        }

        /*
        let Psi = pvk
            .ic
            .iter()
            .zip(acc_Gammas.iter())
            .map(|(&Psi_i, acc_Gamma_i)| Psi_i * acc_Gamma_i)
            .sum();
            */

        unimplemented!();
    }
}

impl<E: MultiMillerLoop> Item<E> {
    pub fn verify_single(self, pvk: &PreparedVerifyingKey<E>) -> Result<(), VerificationError> {
        super::verify_proof(pvk, &self.proof, &self.inputs)
    }
}
