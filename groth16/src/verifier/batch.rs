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
//! Each verification gives one proof the weight one, and every other proof an independent
//! weight drawn uniformly from `1..=2^128 - 1` (or uniformly from the nonzero
//! scalars, if the scalar field has at most 128 bits). A batch containing any
//! invalid proof is accepted with probability at most `1 / (2^128 - 1)` (or
//! `1 / (r - 1)` for a scalar field of order `r < 2^128`), however many of its proofs
//! are invalid: the batch equation holds in a group of prime order `r`, so once every
//! other weight is fixed, at most one weight of an invalid, randomly weighted proof
//! satisfies it. A batch whose only invalid proof has the unit weight is always
//! rejected.
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
use rayon::{
    iter::{IndexedParallelIterator, ParallelIterator},
    prelude::ParallelSlice,
};

use crate::{PreparedVerifyingKey, Proof, VerifyingKey, multiexp::multiexp_vartime};

/// Bit length of the random batch weights, for scalar fields wider than this.
///
/// It bounds the probability of accepting a batch containing an invalid proof by
/// `1 / (2^WEIGHT_BITS - 1)`, as described in the module documentation.
const WEIGHT_BITS: u32 = 128;

// Random weights are sampled as `u128` integers.
const _: () = assert!(WEIGHT_BITS == u128::BITS);

/// Samples a random batch weight, as described in the module documentation.
fn random_weight<F: PrimeField>(rng: &mut impl Rng) -> F {
    // The spec is explicit that `z != 0`; a zero weight would remove
    // its proof from the batch equation. `Field::random` is defined to
    // return a uniformly-random field element (which may be 0), and
    // `rng.fill_bytes()` can return the all-zeros byte array. So we
    // loop until it's not, avoiding needing an assert or throwing an
    // error through no fault of the batch items. This will likely never
    // actually loop, but handles the edge case.
    loop {
        let weight = if F::NUM_BITS > WEIGHT_BITS {
            // The field order exceeds 2^WEIGHT_BITS, so these integers are distinct scalars.
            let mut bytes = [0; size_of::<u128>()];
            rng.fill_bytes(&mut bytes);
            F::from_u128(u128::from_le_bytes(bytes))
        } else {
            F::random(&mut *rng)
        };
        if !weight.is_zero_vartime() {
            return weight;
        }
    }
}

/// Weighted sums of a batch, which are paired with the verifying key.
struct WeightedSums<E: MultiMillerLoop> {
    /// `ic_scalars[i]` multiplies `vk.ic[i]`.
    ///
    /// The first public input is implicitly one, so `ic_scalars[0]` is the sum of the
    /// weights.
    ic_scalars: Vec<E::Fr>,
    /// Weighted sum of the proofs' `C` points.
    c_sum: E::G1,
}

impl<E: MultiMillerLoop> WeightedSums<E> {
    fn new(ic_len: usize) -> Self {
        WeightedSums {
            ic_scalars: vec![E::Fr::ZERO; ic_len],
            c_sum: E::G1::identity(),
        }
    }

    fn weight_sum(&self) -> E::Fr {
        self.ic_scalars[0]
    }
}

impl<E: MultiMillerLoop> AddAssign for WeightedSums<E> {
    fn add_assign(&mut self, other: Self) {
        debug_assert_eq!(self.ic_scalars.len(), other.ic_scalars.len());
        for (a, b) in self.ic_scalars.iter_mut().zip(other.ic_scalars) {
            *a += b;
        }
        self.c_sum += other.c_sum;
    }
}

/// A weighted batch: the per-proof Miller loop inputs, and the sums paired with the
/// verifying key.
struct WeightedBatch<E: MultiMillerLoop> {
    /// `([weight] A, -B)` for each proof.
    proofs: Vec<(E::G1, E::G2Prepared)>,
    sums: WeightedSums<E>,
}

impl<E: MultiMillerLoop> WeightedBatch<E> {
    /// Returns the per-proof Miller loop terms.
    fn proof_terms(&self) -> impl Iterator<Item = (E::G1, &E::G2Prepared)> {
        self.proofs.iter().map(|(a, neg_b)| (*a, neg_b))
    }

    /// Returns all Miller loop terms of this batch under `key`.
    fn terms<'a>(
        &'a self,
        key: &'a PreparedBatchVerifyingKey<'_, E>,
    ) -> Vec<(E::G1, &'a E::G2Prepared)> {
        let mut terms = self.proof_terms().collect::<Vec<_>>();
        let g2 = [&key.g2.delta_g2, &key.g2.gamma_g2, &key.g2.beta_g2];
        terms.extend(shared_terms(key.vk, &self.sums).into_iter().zip(g2));
        terms
    }
}

/// Weighs batch items.
fn weigh<E: MultiMillerLoop>(
    items: &[Item<E>],
    weights: &[E::Fr],
    ic_len: usize,
) -> WeightedBatch<E> {
    let mut proofs = Vec::with_capacity(items.len());
    let mut c = Vec::with_capacity(items.len());
    let mut ic_scalars = vec![E::Fr::ZERO; ic_len];
    for (Item { proof, inputs }, weight) in items.iter().zip(weights) {
        let a = multiexp_vartime(&[proof.a.to_curve()], std::slice::from_ref(weight));
        proofs.push((a, (-proof.b).into()));
        c.push(proof.c.to_curve());
        ic_scalars[0] += weight; // a_0 is implicitly set to 1
        for (input, ic_scalar) in inputs.iter().zip(&mut ic_scalars[1..]) {
            *ic_scalar += *weight * input;
        }
    }
    WeightedBatch {
        proofs,
        sums: WeightedSums {
            ic_scalars,
            c_sum: multiexp_vartime(&c, weights),
        },
    }
}

/// Returns the G1 terms that pair the batch sums with the verifying key.
fn shared_terms<E: MultiMillerLoop>(vk: &VerifyingKey<E>, sums: &WeightedSums<E>) -> [E::G1; 3] {
    let ic = vk.ic.iter().map(|ic| ic.to_curve()).collect::<Vec<_>>();
    let psi = multiexp_vartime(&ic, &sums.ic_scalars);
    let weight_sum = sums.weight_sum();
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
    [sums.c_sum, psi, alpha]
}

/// Runs a Miller loop, normalizing all G1 points with one shared inversion.
fn miller_loop<E: MultiMillerLoop>(terms: &[(E::G1, &E::G2Prepared)]) -> E::Result {
    let g1 = terms.iter().map(|(g1, _)| *g1).collect::<Vec<_>>();
    let mut affine = vec![E::G1Affine::identity(); g1.len()];
    E::G1::batch_normalize(&g1, &mut affine);
    let terms = affine
        .iter()
        .zip(terms.iter().map(|(_, g2)| *g2))
        .collect::<Vec<_>>();
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
    /// The first proof in the combined batches has weight one; every other proof
    /// has an independent nonzero weight as described in the module documentation.
    /// This shares the Miller-loop squares and final exponentiation.
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

        let first = self.randomize_terms(&mut rng, key, true);
        // Only one proof across both batches may have a fixed unit weight.
        let second = other.randomize_terms(&mut rng, other_key, false);
        let mut terms = first.terms(key);
        terms.extend(second.terms(other_key));

        if miller_loop::<E>(&terms).final_exponentiation() == E::Gt::identity() {
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
        let batch = self.randomize_terms(rng, pvk, true);
        if miller_loop::<E>(&batch.terms(pvk)).final_exponentiation() == E::Gt::identity() {
            Ok(())
        } else {
            Err(VerificationError::InvalidProof)
        }
    }

    fn randomize_terms<R: Rng + CryptoRng>(
        self,
        mut rng: R,
        pvk: &PreparedBatchVerifyingKey<'_, E>,
        first_is_unit: bool,
    ) -> WeightedBatch<E> {
        let weights = (0..self.items.len())
            .map(|i| {
                if first_is_unit && i == 0 {
                    E::Fr::ONE
                } else {
                    random_weight(&mut rng)
                }
            })
            .collect::<Vec<_>>();
        weigh(&self.items, &weights, pvk.vk.ic.len())
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
            sums: WeightedSums<E>,
            ml_result: Option<E::Result>,
        }

        impl<E: MultiMillerLoop> Accumulator<E> {
            fn new(ic_len: usize) -> Self {
                Accumulator {
                    sums: WeightedSums::new(ic_len),
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
            .enumerate()
            .map(|(chunk, items)| {
                let mut rng = UnwrapErr(SysRng);
                // Exactly one item in the whole batch has the unit weight. Other weights are
                // independent, rather than powers of one random value, so that they stay 128
                // bits long and keep the serial bound.
                let weights = (0..items.len())
                    .map(|i| {
                        if chunk == 0 && i == 0 {
                            E::Fr::ONE
                        } else {
                            random_weight(&mut rng)
                        }
                    })
                    .collect::<Vec<_>>();
                let batch = weigh(items, &weights, ic_len);
                let terms = batch.proof_terms().collect::<Vec<_>>();
                Accumulator {
                    ml_result: Some(miller_loop::<E>(&terms)),
                    sums: batch.sums,
                }
            })
            .reduce(
                || Accumulator::<E>::new(ic_len),
                |mut a, b| {
                    a.sums += b.sums;
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
                let g1 = shared_terms(vk, &acc.sums);
                let g2 = [&pvk.g2.delta_g2, &pvk.g2.gamma_g2, &pvk.g2.beta_g2];
                let terms = g1.into_iter().zip(g2).collect::<Vec<_>>();
                ml_result += miller_loop::<E>(&terms);

                if ml_result.final_exponentiation() == E::Gt::identity() {
                    Ok(())
                } else {
                    Err(VerificationError::InvalidProof)
                }
            }
        }
    }
}
