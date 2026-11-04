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
//!
//! Proofs, public inputs and verifying keys are public, and the weights only need to
//! be unpredictable until the proofs are fixed, so this module uses variable-time
//! arithmetic.

use std::{borrow::Cow, ops::AddAssign};

use bellman::VerificationError;
use ff::{Field, PrimeField};
use group::{Curve, CurveAffine, Group};
use pairing::{MillerLoopResult, MultiMillerLoop};
use rand_core::{CryptoRng, Rng};

#[cfg(feature = "multicore")]
use rand::rngs::SysRng;
#[cfg(feature = "multicore")]
use rand_core::UnwrapErr;

#[cfg(feature = "multicore")]
use rayon::{iter::ParallelIterator, prelude::ParallelSlice};

use crate::{PreparedVerifyingKey, Proof, VerifyingKey, multiexp::multiexp_vartime};

/// Samples a uniformly random nonzero scalar for batch verification.
fn random_weight<F: PrimeField>(rng: &mut impl Rng) -> F {
    // The spec is explicit that `z != 0`; a zero weight would remove
    // its proof from the batch equation. `Field::random` is defined to
    // return a uniformly-random field element (which may be 0), so we
    // loop until it's not, avoiding needing an assert or throwing an
    // error through no fault of the batch items. This will likely never
    // actually loop, but handles the edge case.
    loop {
        let weight = F::random(&mut *rng);
        if !weight.is_zero_vartime() {
            return weight;
        }
    }
}

/// Weighs batch items, returning their Miller loop terms, the weighted sums of their public
/// inputs, and the weighted sum of their `C` points.
///
/// The first public input is implicitly one, so its weighted sum is the sum of the weights.
#[allow(clippy::type_complexity)]
fn weigh<E: MultiMillerLoop>(
    items: &[Item<E>],
    weights: &[E::Fr],
    ic_len: usize,
) -> (Vec<E::G1>, Vec<E::G2Prepared>, Vec<E::Fr>, E::G1) {
    let mut a = Vec::with_capacity(items.len());
    let mut neg_b = Vec::with_capacity(items.len());
    let mut c = Vec::with_capacity(items.len());
    let mut ic_scalars = vec![E::Fr::ZERO; ic_len];
    for (Item { proof, inputs }, weight) in items.iter().zip(weights) {
        a.push(multiexp_vartime(
            &[proof.a.to_curve()],
            std::slice::from_ref(weight),
        ));
        neg_b.push((-proof.b).into());
        c.push(proof.c.to_curve());
        ic_scalars[0] += weight; // a_0 is implicitly set to 1
        for (input, ic_scalar) in inputs.iter().zip(&mut ic_scalars[1..]) {
            *ic_scalar += *weight * input;
        }
    }
    (a, neg_b, ic_scalars, multiexp_vartime(&c, weights))
}

/// Returns the G1 terms that pair the batch sums with the verifying key.
///
/// `ic_scalars[i]` multiplies `vk.ic[i]`, and `c_sum` is the weighted sum of the
/// proofs' `C` points.
fn shared_terms<E: MultiMillerLoop>(
    vk: &VerifyingKey<E>,
    ic_scalars: &[E::Fr],
    c_sum: E::G1,
) -> [E::G1; 3] {
    let ic = vk.ic.iter().map(|ic| ic.to_curve()).collect::<Vec<_>>();
    let psi = multiexp_vartime(&ic, ic_scalars);
    // The first public input is implicitly one, so its scalar is the sum of the weights.
    let weight_sum = ic_scalars[0];
    // Covers the [weight_sum] e(alpha_g1, beta_g2) component.
    //
    // The multiplication by weight_sum is expensive -- it involves
    // exponentiating by weight_sum because the result of the pairing is an
    // element of a multiplicative subgroup of a large extension field.
    // Instead, we add
    //     ([weight_sum] alpha_g1, beta_g2)
    // to our Miller loop terms because
    //     [weight_sum] e(alpha_g1, beta_g2) = e([weight_sum] alpha_g1, beta_g2)
    let alpha = multiexp_vartime(&[vk.alpha_g1.to_curve()], &[weight_sum]);
    [c_sum, psi, alpha]
}

/// Runs a Miller loop, normalizing all G1 points with one shared inversion.
fn miller_loop<E: MultiMillerLoop>(g1: &[E::G1], g2: &[&E::G2Prepared]) -> E::Result {
    let mut affine = vec![E::G1Affine::identity(); g1.len()];
    E::G1::batch_normalize(g1, &mut affine);
    let terms = affine.iter().zip(g2.iter().copied()).collect::<Vec<_>>();
    E::multi_miller_loop(&terms)
}

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

/// Reusable fixed G2 pairing terms from a Groth16 verifying key.
#[derive(Clone)]
pub struct PreparedBatchG2<E: MultiMillerLoop> {
    source_beta_g2: E::G2Affine,
    source_gamma_g2: E::G2Affine,
    source_delta_g2: E::G2Affine,
    beta_g2: E::G2Prepared,
    gamma_g2: E::G2Prepared,
    delta_g2: E::G2Prepared,
}

impl<E: MultiMillerLoop> std::fmt::Debug for PreparedBatchG2<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PreparedBatchG2").finish_non_exhaustive()
    }
}

impl<E: MultiMillerLoop> From<&VerifyingKey<E>> for PreparedBatchG2<E> {
    fn from(vk: &VerifyingKey<E>) -> Self {
        Self {
            source_beta_g2: vk.beta_g2,
            source_gamma_g2: vk.gamma_g2,
            source_delta_g2: vk.delta_g2,
            beta_g2: E::prepare_reusable_g2(vk.beta_g2),
            gamma_g2: E::prepare_reusable_g2(vk.gamma_g2),
            delta_g2: E::prepare_reusable_g2(vk.delta_g2),
        }
    }
}

impl<E: MultiMillerLoop> PreparedBatchG2<E> {
    // The raw verifier uses each G2 term once, so extra reusable preparation
    // would cost more than it saves.
    fn for_one_batch(vk: &VerifyingKey<E>) -> Self {
        Self {
            source_beta_g2: vk.beta_g2,
            source_gamma_g2: vk.gamma_g2,
            source_delta_g2: vk.delta_g2,
            beta_g2: vk.beta_g2.into(),
            gamma_g2: vk.gamma_g2.into(),
            delta_g2: vk.delta_g2.into(),
        }
    }
}

/// Fixed G2 pairing terms for repeated batches under one verifying key.
///
/// Creating this once prepares beta, gamma, and delta for repeated batches.
/// Engines can spend more time preparing these terms to speed up verification.
pub struct PreparedBatchVerifyingKey<'a, E: MultiMillerLoop> {
    vk: &'a VerifyingKey<E>,
    g2: Cow<'a, PreparedBatchG2<E>>,
}

struct PreparedBatchTerms<E: MultiMillerLoop> {
    g1: Vec<E::G1>,
    neg_b: Vec<E::G2Prepared>,
}

impl<E: MultiMillerLoop> PreparedBatchTerms<E> {
    fn with_key<'a>(&'a self, key: &'a PreparedBatchVerifyingKey<'_, E>) -> Vec<&'a E::G2Prepared> {
        let mut terms = self.neg_b.iter().collect::<Vec<_>>();
        terms.extend([&key.g2.delta_g2, &key.g2.gamma_g2, &key.g2.beta_g2]);
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
            g2: Cow::Owned(PreparedBatchG2::from(vk)),
        }
    }
}

impl<'a, E: MultiMillerLoop> PreparedBatchVerifyingKey<'a, E> {
    /// Borrows fixed G2 terms from [`PreparedBatchG2`].
    ///
    /// Returns an error if the key has different beta, gamma, or delta G2 terms.
    pub fn from_cached(
        vk: &'a VerifyingKey<E>,
        g2: &'a PreparedBatchG2<E>,
    ) -> Result<Self, VerificationError> {
        if g2.source_beta_g2 != vk.beta_g2
            || g2.source_gamma_g2 != vk.gamma_g2
            || g2.source_delta_g2 != vk.delta_g2
        {
            return Err(VerificationError::InvalidVerifyingKey);
        }
        Ok(Self {
            vk,
            g2: Cow::Borrowed(g2),
        })
    }

    // The raw verifier uses each G2 term once, so extra reusable preparation
    // would cost more than it saves.
    fn for_one_batch(vk: &'a VerifyingKey<E>) -> Self {
        Self {
            vk,
            g2: Cow::Owned(PreparedBatchG2::for_one_batch(vk)),
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

        let mut first = self.randomize_terms(&mut rng, key);
        let second = other.randomize_terms(&mut rng, other_key);
        first.g1.extend_from_slice(&second.g1);
        let mut g2 = first.with_key(key);
        g2.extend(second.with_key(other_key));

        if miller_loop::<E>(&first.g1, &g2).final_exponentiation() == E::Gt::identity() {
            Ok(())
        } else {
            Err(VerificationError::InvalidProof)
        }
    }

    fn verify_prepared_unchecked<R: Rng + CryptoRng>(
        self,
        rng: R,
        pvk: &PreparedBatchVerifyingKey<'_, E>,
    ) -> Result<(), VerificationError> {
        let terms = self.randomize_terms(rng, pvk);
        if miller_loop::<E>(&terms.g1, &terms.with_key(pvk)).final_exponentiation()
            == E::Gt::identity()
        {
            Ok(())
        } else {
            Err(VerificationError::InvalidProof)
        }
    }

    fn randomize_terms<R: Rng + CryptoRng>(
        self,
        mut rng: R,
        pvk: &PreparedBatchVerifyingKey<'_, E>,
    ) -> PreparedBatchTerms<E> {
        let weights = (0..self.items.len())
            .map(|_| random_weight(&mut rng))
            .collect::<Vec<_>>();
        let (mut g1, neg_b, ic_scalars, c_sum) = weigh(&self.items, &weights, pvk.vk.ic.len());
        g1.extend(shared_terms(pvk.vk, &ic_scalars, c_sum));

        PreparedBatchTerms { g1, neg_b }
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
    fn verify_multicore_prepared_unchecked(
        self,
        pvk: &PreparedBatchVerifyingKey<'_, E>,
    ) -> Result<(), VerificationError> {
        let vk = pvk.vk;
        struct Accumulator<E: MultiMillerLoop> {
            ic_scalars: Vec<E::Fr>,
            c_sum: E::G1,
            ml_result: Option<E::Result>,
        }

        impl<E: MultiMillerLoop> Accumulator<E> {
            fn new(ic_len: usize) -> Self {
                Accumulator {
                    ic_scalars: vec![E::Fr::ZERO; ic_len],
                    c_sum: E::G1::identity(),
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
                let z = random_weight::<E::Fr>(&mut UnwrapErr(SysRng));
                let mut cur_z = z;
                let weights = (0..items.len())
                    .map(|_| {
                        let weight = cur_z;
                        cur_z *= z;
                        weight
                    })
                    .collect::<Vec<_>>();
                let (g1, neg_b, ic_scalars, c_sum) = weigh(items, &weights, ic_len);
                let g2 = neg_b.iter().collect::<Vec<_>>();
                Accumulator {
                    ic_scalars,
                    c_sum,
                    ml_result: Some(miller_loop::<E>(&g1, &g2)),
                }
            })
            .reduce(
                || Accumulator::<E>::new(ic_len),
                |mut a, b| {
                    for (a, b) in a.ic_scalars.iter_mut().zip(b.ic_scalars.into_iter()) {
                        *a += b;
                    }
                    a.c_sum += b.c_sum;
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
                let g1 = shared_terms(vk, &acc.ic_scalars, acc.c_sum);
                let g2 = [&pvk.g2.delta_g2, &pvk.g2.gamma_g2, &pvk.g2.beta_g2];
                ml_result += miller_loop::<E>(&g1, &g2);

                if ml_result.final_exponentiation() == E::Gt::identity() {
                    Ok(())
                } else {
                    Err(VerificationError::InvalidProof)
                }
            }
        }
    }
}
