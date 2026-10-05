//! Performs batch Groth16 proof verification.
//!
//! Batch verification asks whether *all* proofs in some set are valid,
//! rather than asking whether *each* of them is valid. This allows sharing
//! computations among all proof verifications, performing less work overall
//! at the cost of higher latency (the entire batch must complete), complexity of
//! caller code (which must assemble a batch of proofs across work-items),
//! and loss of the ability to easily pinpoint failing proofs.
//!
//! This batch verification implementation is non-adaptive, in the sense that it
//! assumes that all the proofs in the batch are verifiable by the same
//! `VerifyingKey`. The reason is that if you have different proof statements,
//! you need to specify which statement you are proving, which means that you
//! need to refer to or lookup a particular `VerifyingKey`. In practice, with
//! large enough batches, it's manageable and not much worse performance-wise to
//! keep batches of each statement type, vs one large adaptive batch.

use std::ops::AddAssign;

use bellman::VerificationError;
use ff::Field;
use group::{Curve, Group};
use pairing::{MillerLoopResult, MultiMillerLoop};
use rand_core::{CryptoRng, Rng};

#[cfg(feature = "multicore")]
use rand::rngs::SysRng;
#[cfg(feature = "multicore")]
use rand_core::UnwrapErr;

#[cfg(feature = "multicore")]
use rayon::{iter::ParallelIterator, prelude::ParallelSlice};

use crate::{PreparedVerifyingKey, Proof, VerifyingKey};

/// A batch verification item.
///
/// This struct exists to allow batch processing to be decoupled from the
/// lifetime of the message. This is useful when using the batch verification
/// API in an async context.
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

impl<E: MultiMillerLoop> Item<E> {
    /// Perform non-batched verification of this `Item`.
    ///
    /// This is useful (in combination with `Item::clone`) for implementing
    /// fallback logic when batch verification fails.
    pub fn verify_single(self, pvk: &PreparedVerifyingKey<E>) -> Result<(), VerificationError> {
        super::verify_proof(pvk, &self.proof, &self.inputs)
    }
}

/// A batch verification context.
///
/// In practice, you would create a batch verifier for each proof statement
/// requiring the same `VerifyingKey`.
#[derive(Debug)]
pub struct Verifier<E: MultiMillerLoop> {
    items: Vec<Item<E>>,
}

/// Fixed G2 pairing terms for repeated batches under one verifying key.
///
/// Creating this once prepares beta, gamma, and delta for repeated batches.
/// Engines can spend more time preparing these terms to speed up verification.
pub struct PreparedBatchVerifyingKey<'a, E: MultiMillerLoop> {
    vk: &'a VerifyingKey<E>,
    beta_g2: E::G2Prepared,
    gamma_g2: E::G2Prepared,
    delta_g2: E::G2Prepared,
}

struct PreparedBatchTerms<E: MultiMillerLoop> {
    variable: Vec<(E::G1Affine, E::G2Prepared)>,
    delta: E::G1Affine,
    gamma: E::G1Affine,
    beta: E::G1Affine,
}

impl<E: MultiMillerLoop> PreparedBatchTerms<E> {
    fn with_key<'a>(
        &'a self,
        key: &'a PreparedBatchVerifyingKey<'_, E>,
    ) -> Vec<(&'a E::G1Affine, &'a E::G2Prepared)> {
        let mut terms = self
            .variable
            .iter()
            .map(|(a, b)| (a, b))
            .collect::<Vec<_>>();
        terms.extend([
            (&self.delta, &key.delta_g2),
            (&self.gamma, &key.gamma_g2),
            (&self.beta, &key.beta_g2),
        ]);
        terms
    }
}

impl<E: MultiMillerLoop> std::fmt::Debug for PreparedBatchVerifyingKey<'_, E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PreparedBatchVerifyingKey")
            .finish_non_exhaustive()
    }
}

impl<'a, E: MultiMillerLoop> From<&'a VerifyingKey<E>> for PreparedBatchVerifyingKey<'a, E> {
    fn from(vk: &'a VerifyingKey<E>) -> Self {
        Self {
            vk,
            beta_g2: E::prepare_reusable_g2(vk.beta_g2),
            gamma_g2: E::prepare_reusable_g2(vk.gamma_g2),
            delta_g2: E::prepare_reusable_g2(vk.delta_g2),
        }
    }
}

impl<'a, E: MultiMillerLoop> PreparedBatchVerifyingKey<'a, E> {
    // The raw verifier uses each G2 term once, so extra reusable preparation
    // would cost more than it saves.
    fn for_one_batch(vk: &'a VerifyingKey<E>) -> Self {
        Self {
            vk,
            beta_g2: vk.beta_g2.into(),
            gamma_g2: vk.gamma_g2.into(),
            delta_g2: vk.delta_g2.into(),
        }
    }
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
    /// Construct a new batch verifier.
    pub fn new() -> Self {
        Self::default()
    }

    /// Queue a (proof, inputs) tuple for verification.
    pub fn queue<I: Into<Item<E>>>(&mut self, item: I) {
        self.items.push(item.into())
    }

    /// Perform batch verification with a particular [`VerifyingKey`].
    ///
    /// For repeated batches, prepare the key once and use
    /// [`Verifier::verify_prepared`].
    pub fn verify<R: Rng + CryptoRng>(
        self,
        rng: R,
        vk: &VerifyingKey<E>,
    ) -> Result<(), VerificationError> {
        if self
            .items
            .iter()
            .any(|Item { inputs, .. }| inputs.len() + 1 != vk.ic.len())
        {
            return Err(VerificationError::InvalidVerifyingKey);
        }
        if self.items.is_empty() {
            return Ok(());
        }
        self.verify_prepared_unchecked(rng, &PreparedBatchVerifyingKey::for_one_batch(vk))
    }

    /// Verify a batch using fixed G2 terms prepared for its verifying key.
    pub fn verify_prepared<R: Rng + CryptoRng>(
        self,
        rng: R,
        pvk: &PreparedBatchVerifyingKey<'_, E>,
    ) -> Result<(), VerificationError> {
        let vk = pvk.vk;
        if self
            .items
            .iter()
            .any(|Item { inputs, .. }| inputs.len() + 1 != vk.ic.len())
        {
            return Err(VerificationError::InvalidVerifyingKey);
        }
        if self.items.is_empty() {
            return Ok(());
        }
        self.verify_prepared_unchecked(rng, pvk)
    }

    /// Verify two batches using different [`PreparedBatchVerifyingKey`] values
    /// in one Miller loop.
    ///
    /// Independent nonzero randomizers are sampled for every proof in both
    /// batches. This shares the Miller-loop squares and final exponentiation.
    pub fn verify_joint_prepared<R: Rng + CryptoRng>(
        self,
        other: Self,
        mut rng: R,
        key: &PreparedBatchVerifyingKey<'_, E>,
        other_key: &PreparedBatchVerifyingKey<'_, E>,
    ) -> Result<(), VerificationError> {
        if self
            .items
            .iter()
            .any(|item| item.inputs.len() + 1 != key.vk.ic.len())
            || other
                .items
                .iter()
                .any(|item| item.inputs.len() + 1 != other_key.vk.ic.len())
        {
            return Err(VerificationError::InvalidVerifyingKey);
        }
        if self.items.is_empty() {
            return other.verify_prepared(rng, other_key);
        }
        if other.items.is_empty() {
            return self.verify_prepared(rng, key);
        }

        let first = self.randomize_terms(&mut rng, key);
        let second = other.randomize_terms(&mut rng, other_key);
        let mut terms = first.with_key(key);
        terms.extend(second.with_key(other_key));

        if E::multi_miller_loop(&terms).final_exponentiation() == E::Gt::identity() {
            Ok(())
        } else {
            Err(VerificationError::InvalidProof)
        }
    }

    #[allow(non_snake_case)]
    fn verify_prepared_unchecked<R: Rng + CryptoRng>(
        self,
        rng: R,
        pvk: &PreparedBatchVerifyingKey<'_, E>,
    ) -> Result<(), VerificationError> {
        let terms = self.randomize_terms(rng, pvk);
        if E::multi_miller_loop(&terms.with_key(pvk)).final_exponentiation() == E::Gt::identity() {
            Ok(())
        } else {
            Err(VerificationError::InvalidProof)
        }
    }

    #[allow(non_snake_case)]
    fn randomize_terms<R: Rng + CryptoRng>(
        self,
        mut rng: R,
        pvk: &PreparedBatchVerifyingKey<'_, E>,
    ) -> PreparedBatchTerms<E> {
        let vk = pvk.vk;
        let mut ml_terms = Vec::<(E::G1Affine, E::G2Prepared)>::with_capacity(self.items.len());
        let mut acc_Gammas = vec![E::Fr::ZERO; vk.ic.len()];
        let mut acc_Delta = E::G1::identity();
        let mut acc_Y = E::Fr::ZERO;

        for Item { proof, inputs } in self.items.into_iter() {
            // The spec is explicit that z != 0.  Field::random is defined to
            // return a uniformly-random field element (which may be 0), so we
            // loop until it's not, avoiding needing an assert or throwing an
            // error through no fault of the batch items. This will likely never
            // actually loop, but handles the edge case.
            let z = loop {
                let z = E::Fr::random(&mut rng);
                if !z.is_zero_vartime() {
                    break z;
                }
            };

            ml_terms.push(((proof.a * z).into(), (-proof.b).into()));

            acc_Gammas[0] += &z; // a_0 is implicitly set to 1
            for (a_i, acc_Gamma_i) in Iterator::zip(inputs.iter(), acc_Gammas.iter_mut().skip(1)) {
                *acc_Gamma_i += &(z * a_i);
            }
            acc_Delta += proof.c * z;
            acc_Y += &z;
        }

        let delta = acc_Delta.to_affine();

        let Psi = vk
            .ic
            .iter()
            .zip(acc_Gammas.iter())
            .map(|(&Psi_i, acc_Gamma_i)| Psi_i * acc_Gamma_i)
            .sum();

        let gamma = E::G1Affine::from(Psi);

        // Covers the [acc_Y]⋅e(alpha_g1, beta_g2) component
        //
        // The multiplication by acc_Y is expensive -- it involves
        // exponentiating by acc_Y because the result of the pairing is an
        // element of a multiplicative subgroup of a large extension field.
        // Instead, we add
        //     ([acc_Y]⋅alpha_g1, beta_g2)
        // to our Miller loop terms because
        //     [acc_Y]⋅e(alpha_g1, beta_g2) = e([acc_Y]⋅alpha_g1, beta_g2)
        let beta = E::G1Affine::from(vk.alpha_g1 * acc_Y);

        PreparedBatchTerms {
            variable: ml_terms,
            delta,
            gamma,
            beta,
        }
    }

    /// Perform batch verification using the global Rayon thread pool.
    ///
    /// For repeated batches, prepare the key once and use
    /// [`Verifier::verify_multicore_prepared`].
    #[cfg(feature = "multicore")]
    pub fn verify_multicore(self, vk: &VerifyingKey<E>) -> Result<(), VerificationError> {
        if self
            .items
            .iter()
            .any(|Item { inputs, .. }| inputs.len() + 1 != vk.ic.len())
        {
            return Err(VerificationError::InvalidVerifyingKey);
        }
        if self.items.is_empty() {
            return Ok(());
        }
        self.verify_multicore_prepared_unchecked(&PreparedBatchVerifyingKey::for_one_batch(vk))
    }

    /// Verify a batch with prepared fixed G2 terms using the global Rayon
    /// thread pool.
    #[cfg(feature = "multicore")]
    pub fn verify_multicore_prepared(
        self,
        pvk: &PreparedBatchVerifyingKey<'_, E>,
    ) -> Result<(), VerificationError> {
        let vk = pvk.vk;
        if self
            .items
            .iter()
            .any(|Item { inputs, .. }| inputs.len() + 1 != vk.ic.len())
        {
            return Err(VerificationError::InvalidVerifyingKey);
        }
        if self.items.is_empty() {
            return Ok(());
        }
        self.verify_multicore_prepared_unchecked(pvk)
    }

    #[cfg(feature = "multicore")]
    #[allow(non_snake_case)]
    fn verify_multicore_prepared_unchecked(
        self,
        pvk: &PreparedBatchVerifyingKey<'_, E>,
    ) -> Result<(), VerificationError> {
        let vk = pvk.vk;
        struct Accumulator<E: MultiMillerLoop> {
            gammas: Vec<E::Fr>,
            delta: E::G1,
            y: E::Fr,
            ml_result: Option<E::Result>,
        }

        impl<E: MultiMillerLoop> Accumulator<E> {
            fn new(ic_len: usize) -> Self {
                Accumulator {
                    gammas: vec![E::Fr::ZERO; ic_len],
                    delta: E::G1::identity(),
                    y: E::Fr::ZERO,
                    ml_result: None,
                }
            }
        }

        let ic_len = vk.ic.len();

        // Give each Rayon thread a Miller-loop work item while retaining
        // batching within each loop when parallelism is scarce.
        const MAX_CHUNK_SIZE: usize = 8;
        let threads = rayon::current_num_threads();
        let chunk_size = self.items.len().div_ceil(threads).clamp(1, MAX_CHUNK_SIZE);

        let acc = self
            .items
            .par_chunks(chunk_size)
            .map(|items| {
                let mut acc = Accumulator::<E>::new(ic_len);
                let mut ml_terms: Vec<(E::G1Affine, E::G2Prepared)> = vec![];
                let z = loop {
                    let z = E::Fr::random(&mut UnwrapErr(SysRng));
                    if !z.is_zero_vartime() {
                        break z;
                    }
                };
                let mut cur_z = z;
                for Item { proof, inputs } in items {
                    acc.gammas[0] += &cur_z;
                    for (a_i, acc_gamma_i) in
                        Iterator::zip(inputs.iter(), acc.gammas.iter_mut().skip(1))
                    {
                        *acc_gamma_i += &(cur_z * a_i);
                    }
                    acc.delta += proof.c * cur_z;
                    acc.y += &cur_z;
                    ml_terms.push(((proof.a * cur_z).into(), (-proof.b).into()));

                    cur_z *= z;
                }
                let ml_terms = ml_terms.iter().map(|(a, b)| (a, b)).collect::<Vec<_>>();
                acc.ml_result = Some(E::multi_miller_loop(&ml_terms[..]));
                acc
            })
            .reduce(
                || Accumulator::<E>::new(ic_len),
                |mut a, b| {
                    for (a, b) in a.gammas.iter_mut().zip(b.gammas.into_iter()) {
                        *a += b;
                    }
                    a.delta += b.delta;
                    a.y += b.y;
                    a.ml_result = match (a.ml_result, b.ml_result) {
                        (Some(a), Some(b)) => Some(a + b),
                        (Some(a), None) | (None, Some(a)) => Some(a),
                        (None, None) => None,
                    };
                    a
                },
            );

        match acc.ml_result {
            None => Ok(()),
            Some(mut ml_result) => {
                // TODO: could use a multiexp (Bos-Coster maybe?)
                let psi = vk
                    .ic
                    .iter()
                    .zip(acc.gammas)
                    .map(|(&psi_i, acc_gamma_i)| psi_i * acc_gamma_i)
                    .sum();

                ml_result += E::multi_miller_loop(&[
                    (&acc.delta.to_affine(), &pvk.delta_g2),
                    (&E::G1Affine::from(psi), &pvk.gamma_g2),
                    (&E::G1Affine::from(vk.alpha_g1 * acc.y), &pvk.beta_g2),
                ]);

                if ml_result.final_exponentiation() == E::Gt::identity() {
                    Ok(())
                } else {
                    Err(VerificationError::InvalidProof)
                }
            }
        }
    }
}
