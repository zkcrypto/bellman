// For randomness (during paramgen and proof generation)
use rand::{RngExt, SeedableRng, TryCryptoRng, TryRng, rng, rngs::StdRng, seq::IndexedRandom};

// For benchmarking
use std::time::{Duration, Instant};

// Bring in some tools for using finite fiels
use ff::Field;

// We're going to use the BLS12-381 pairing-friendly elliptic curve.
use bls12_381::{Bls12, G1Projective, G2Affine, G2Projective, Scalar};

// We're going to use the Groth16 proving system.
use groth16::{
    PreparedVerifyingKey, Proof, VerifyingKey, batch, create_random_proof,
    generate_random_parameters, prepare_verifying_key, verify_proof,
};

use bellman::VerificationError;

mod common;

use common::*;

#[test]
fn test_mimc() {
    // This may not be cryptographically safe, use
    // `OsRng` (for example) in production software.
    let mut rng = rng();

    // Generate the MiMC round constants
    let constants = (0..MIMC_ROUNDS)
        .map(|_| Scalar::random(&mut rng))
        .collect::<Vec<_>>();

    println!("Creating parameters...");

    // Create parameters for our circuit
    let params = {
        let c = MiMCDemo {
            xl: None,
            xr: None,
            constants: &constants,
        };

        generate_random_parameters::<Bls12, _, _>(c, &mut rng).unwrap()
    };

    // Prepare the verification key (for proof verification)
    let pvk = prepare_verifying_key(&params.vk);

    println!("Creating proofs...");

    // Let's benchmark stuff!
    const SAMPLES: u32 = 50;
    let mut total_proving = Duration::new(0, 0);
    let mut total_verifying = Duration::new(0, 0);

    // Just a place to put the proof data, so we can
    // benchmark deserialization.
    let mut proof_vec = vec![];

    for _ in 0..SAMPLES {
        // Generate a random preimage and compute the image
        let xl = Scalar::random(&mut rng);
        let xr = Scalar::random(&mut rng);
        let image = mimc(xl, xr, &constants);

        proof_vec.truncate(0);

        let start = Instant::now();
        {
            // Create an instance of our circuit (with the
            // witness)
            let c = MiMCDemo {
                xl: Some(xl),
                xr: Some(xr),
                constants: &constants,
            };

            // Create a groth16 proof with our parameters.
            let proof = create_random_proof(c, &params, &mut rng).unwrap();

            proof.write(&mut proof_vec).unwrap();
        }

        total_proving += start.elapsed();

        let start = Instant::now();
        let proof = Proof::read(&proof_vec[..]).unwrap();
        // Check the proof
        assert!(verify_proof(&pvk, &proof, &[image]).is_ok());
        total_verifying += start.elapsed();
    }
    let proving_avg = total_proving / SAMPLES;
    let proving_avg =
        proving_avg.subsec_nanos() as f64 / 1_000_000_000f64 + (proving_avg.as_secs() as f64);

    let verifying_avg = total_verifying / SAMPLES;
    let verifying_avg =
        verifying_avg.subsec_nanos() as f64 / 1_000_000_000f64 + (verifying_avg.as_secs() as f64);

    println!("Average proving time: {:?} seconds", proving_avg);
    println!("Average verifying time: {:?} seconds", verifying_avg);
}

type Item = (Proof<Bls12>, Vec<Scalar>);

/// Returns a verifying key and a few valid proofs, generated deterministically.
fn batch_fixture() -> (VerifyingKey<Bls12>, PreparedVerifyingKey<Bls12>, Vec<Item>) {
    let mut rng = StdRng::seed_from_u64(0);
    let constants = (0..MIMC_ROUNDS)
        .map(|_| Scalar::random(&mut rng))
        .collect::<Vec<_>>();
    let params = generate_random_parameters::<Bls12, _, _>(
        MiMCDemo {
            xl: None,
            xr: None,
            constants: &constants,
        },
        &mut rng,
    )
    .unwrap();
    let items = (0..4)
        .map(|_| {
            let xl = Scalar::random(&mut rng);
            let xr = Scalar::random(&mut rng);
            let circuit = MiMCDemo {
                xl: Some(xl),
                xr: Some(xr),
                constants: &constants,
            };
            let proof = create_random_proof(circuit, &params, &mut rng).unwrap();
            (proof, vec![mimc(xl, xr, &constants)])
        })
        .collect();
    let pvk = prepare_verifying_key(&params.vk);
    (params.vk, pvk, items)
}

/// Makes an item invalid, in one of four ways selected by `kind`.
fn corrupt((proof, inputs): &mut Item, kind: usize) {
    match kind % 4 {
        0 => proof.a = (proof.a + G1Projective::generator()).into(),
        1 => proof.b = (proof.b + G2Projective::generator()).into(),
        2 => proof.c = (proof.c + G1Projective::generator()).into(),
        _ => inputs[0] += Scalar::ONE,
    }
}

/// Returns whether a batch result is the expected success, or a proof failure.
fn is_expected(result: Result<(), VerificationError>, valid: bool) -> bool {
    matches!(
        (result, valid),
        (Ok(()), true) | (Err(VerificationError::InvalidProof), false)
    )
}

/// Asserts that batch verification accepts `items` exactly when each item verifies alone.
fn assert_batch_matches_single(
    vk: &VerifyingKey<Bls12>,
    pvk: &PreparedVerifyingKey<Bls12>,
    items: &[Item],
    rng: &mut StdRng,
) {
    let valid = items
        .iter()
        .all(|(proof, inputs)| verify_proof(pvk, proof, inputs).is_ok());
    let batch = || {
        let mut batch = batch::Verifier::new();
        for item in items {
            batch.queue(item.clone());
        }
        batch
    };
    assert!(is_expected(batch().verify(&mut *rng, vk), valid));
    let prepared = batch::PreparedBatchVerifyingKey::from(vk);
    assert!(is_expected(batch().verify_prepared(rng, &prepared), valid));
    #[cfg(feature = "multicore")]
    {
        assert!(is_expected(batch().verify_multicore(vk), valid));
        assert!(is_expected(
            batch().verify_multicore_prepared(&prepared),
            valid
        ));
    }
}

#[test]
fn batch_verify() {
    let mut rng = rng();

    let mut batch = batch::Verifier::new();
    #[cfg(feature = "multicore")]
    let mut multicore_batch = batch::Verifier::new();
    #[cfg(feature = "multicore")]
    let mut invalid_multicore_batch = batch::Verifier::new();

    // Generate the MiMC round constants
    let constants = (0..MIMC_ROUNDS)
        .map(|_| Scalar::random(&mut rng))
        .collect::<Vec<_>>();

    println!("Creating parameters...");

    // Create parameters for our circuit
    let params = {
        let c = MiMCDemo {
            xl: None,
            xr: None,
            constants: &constants,
        };

        generate_random_parameters::<Bls12, _, _>(c, &mut rng).unwrap()
    };

    // Prepare the verification key (for proof verification)
    let pvk = prepare_verifying_key(&params.vk);

    println!("Creating proofs...");

    // Let's benchmark stuff!
    const SAMPLES: u32 = 50;
    let mut total_proving = Duration::new(0, 0);
    let mut total_verifying = Duration::new(0, 0);

    // Just a place to put the proof data, so we can
    // benchmark deserialization.
    let mut proof_vec = vec![];

    for _sample in 0..SAMPLES {
        // Generate a random preimage and compute the image
        let xl = Scalar::random(&mut rng);
        let xr = Scalar::random(&mut rng);
        let image = mimc(xl, xr, &constants);

        proof_vec.truncate(0);

        let start = Instant::now();
        {
            // Create an instance of our circuit (with the
            // witness)
            let c = MiMCDemo {
                xl: Some(xl),
                xr: Some(xr),
                constants: &constants,
            };

            // Create a groth16 proof with our parameters.
            let proof = create_random_proof(c, &params, &mut rng).unwrap();

            proof.write(&mut proof_vec).unwrap();
        }

        total_proving += start.elapsed();

        let start = Instant::now();
        let proof = Proof::read(&proof_vec[..]).unwrap();

        // Check the proof
        assert!(verify_proof(&pvk, &proof, &[image]).is_ok());

        total_verifying += start.elapsed();

        // Queue the proof and inputs for batch verification.
        #[cfg(feature = "multicore")]
        {
            multicore_batch.queue((proof.clone(), [image].into()));
            let invalid_image = if _sample == 0 {
                image + Scalar::ONE
            } else {
                image
            };
            invalid_multicore_batch.queue((proof.clone(), [invalid_image].into()));
        }
        batch.queue((proof, [image].into()));
    }

    let mut batch_verifying = Duration::new(0, 0);
    let batch_start = Instant::now();

    // Verify this batch for this specific verifying key
    assert!(batch.verify(rng, &params.vk).is_ok());
    #[cfg(feature = "multicore")]
    {
        assert!(multicore_batch.verify_multicore(&params.vk).is_ok());
        assert!(
            invalid_multicore_batch
                .verify_multicore(&params.vk)
                .is_err()
        );
    }

    batch_verifying += batch_start.elapsed();

    let proving_avg = total_proving / SAMPLES;
    let proving_avg =
        proving_avg.subsec_nanos() as f64 / 1_000_000_000f64 + (proving_avg.as_secs() as f64);

    let verifying_avg = total_verifying / SAMPLES;
    let verifying_avg =
        verifying_avg.subsec_nanos() as f64 / 1_000_000_000f64 + (verifying_avg.as_secs() as f64);

    let batch_amortized = batch_verifying / SAMPLES;
    let batch_amortized = batch_amortized.subsec_nanos() as f64 / 1_000_000_000f64
        + (batch_amortized.as_secs() as f64);

    println!("Average proving time: {:?} seconds", proving_avg);
    println!("Average verifying time: {:?} seconds", verifying_avg);
    println!(
        "Amortized batch verifying time: {:?} seconds",
        batch_amortized
    );
}

/// Exercises the `multicore` batch verifier.
///
/// `Verifier::verify_multicore` is gated behind the `multicore` feature, so it is only
/// compiled (and only reachable) when that feature is on. Without a test under the
/// feature, the path can rot unnoticed while the rest of the crate keeps building.
#[test]
#[cfg(feature = "multicore")]
fn batch_verify_multicore() {
    const SAMPLES: u32 = 4;

    let mut rng = rng();

    let constants = (0..MIMC_ROUNDS)
        .map(|_| Scalar::random(&mut rng))
        .collect::<Vec<_>>();

    let params = {
        let c = MiMCDemo {
            xl: None,
            xr: None,
            constants: &constants,
        };

        generate_random_parameters::<Bls12, _, _>(c, &mut rng).unwrap()
    };

    let mut valid = batch::Verifier::new();
    let mut tampered = batch::Verifier::new();

    for _ in 0..SAMPLES {
        let xl = Scalar::random(&mut rng);
        let xr = Scalar::random(&mut rng);
        let image = mimc(xl, xr, &constants);

        let c = MiMCDemo {
            xl: Some(xl),
            xr: Some(xr),
            constants: &constants,
        };
        let proof = create_random_proof(c, &params, &mut rng).unwrap();

        valid.queue((proof.clone(), [image].into()));
        // Same proof, but bound to a public input it does not attest to.
        tampered.queue((proof, [image + Scalar::ONE].into()));
    }

    assert!(valid.verify_multicore(&params.vk).is_ok());
    // Specifically `InvalidProof`, not `InvalidVerifyingKey`: the tampered batch must be
    // rejected by the pairing check, not waved away by the input-length precondition.
    assert!(matches!(
        tampered.verify_multicore(&params.vk),
        Err(VerificationError::InvalidProof)
    ));
}

#[test]
fn prepared_batch_verify() {
    let mut rng = rng();
    let constants = (0..MIMC_ROUNDS)
        .map(|_| Scalar::random(&mut rng))
        .collect::<Vec<_>>();
    let params = generate_random_parameters::<Bls12, _, _>(
        MiMCDemo {
            xl: None,
            xr: None,
            constants: &constants,
        },
        &mut rng,
    )
    .unwrap();
    let xl = Scalar::random(&mut rng);
    let xr = Scalar::random(&mut rng);
    let image = mimc(xl, xr, &constants);
    let proof = create_random_proof(
        MiMCDemo {
            xl: Some(xl),
            xr: Some(xr),
            constants: &constants,
        },
        &params,
        &mut rng,
    )
    .unwrap();
    let prepared = batch::PreparedBatchVerifyingKey::from(&params.vk);
    let reusable_g2 = batch::PreparedBatchG2::from(&params.vk);
    let borrowed = batch::PreparedBatchVerifyingKey::from_cached(&params.vk, &reusable_g2).unwrap();

    let mut valid_borrowed = batch::Verifier::new();
    valid_borrowed.queue((proof.clone(), vec![image]));
    assert!(valid_borrowed.verify_prepared(&mut rng, &borrowed).is_ok());

    for term in 0..3 {
        let mut mismatched = params.vk.clone();
        match term {
            0 => mismatched.beta_g2 = G2Affine::identity(),
            1 => mismatched.gamma_g2 = G2Affine::identity(),
            _ => mismatched.delta_g2 = G2Affine::identity(),
        }
        assert!(matches!(
            batch::PreparedBatchVerifyingKey::from_cached(&mismatched, &reusable_g2),
            Err(bellman::VerificationError::InvalidVerifyingKey)
        ));
    }

    assert!(
        batch::Verifier::<Bls12>::new()
            .verify_prepared(&mut rng, &prepared)
            .is_ok()
    );
    let mut malformed = batch::Verifier::new();
    malformed.queue((proof.clone(), vec![]));
    assert!(matches!(
        malformed.verify_prepared(&mut rng, &prepared),
        Err(bellman::VerificationError::InvalidVerifyingKey)
    ));
    #[cfg(feature = "multicore")]
    {
        assert!(
            batch::Verifier::<Bls12>::new()
                .verify_multicore_prepared(&prepared)
                .is_ok()
        );
        let mut malformed = batch::Verifier::new();
        malformed.queue((proof.clone(), vec![]));
        assert!(matches!(
            malformed.verify_multicore_prepared(&prepared),
            Err(bellman::VerificationError::InvalidVerifyingKey)
        ));
    }

    for count in [1, 2] {
        let mut valid = batch::Verifier::new();
        let mut invalid = batch::Verifier::new();
        #[cfg(feature = "multicore")]
        let mut valid_multicore = batch::Verifier::new();
        #[cfg(feature = "multicore")]
        let mut invalid_multicore = batch::Verifier::new();

        for i in 0..count {
            let valid_item = (proof.clone(), vec![image]);
            let invalid_item = (proof.clone(), vec![image + Scalar::from((i == 0) as u64)]);
            valid.queue(valid_item.clone());
            invalid.queue(invalid_item.clone());
            #[cfg(feature = "multicore")]
            {
                valid_multicore.queue(valid_item);
                invalid_multicore.queue(invalid_item);
            }
        }

        assert!(valid.verify_prepared(&mut rng, &prepared).is_ok());
        assert!(invalid.verify_prepared(&mut rng, &prepared).is_err());
        #[cfg(feature = "multicore")]
        {
            assert!(valid_multicore.verify_multicore_prepared(&prepared).is_ok());
            assert!(
                invalid_multicore
                    .verify_multicore_prepared(&prepared)
                    .is_err()
            );
        }
    }
}

#[test]
fn joint_prepared_batch_verify() {
    let mut rng = rng();
    let constants = (0..MIMC_ROUNDS)
        .map(|_| Scalar::random(&mut rng))
        .collect::<Vec<_>>();
    let circuit = || MiMCDemo {
        xl: None,
        xr: None,
        constants: &constants,
    };
    let params_a = generate_random_parameters::<Bls12, _, _>(circuit(), &mut rng).unwrap();
    let params_b = generate_random_parameters::<Bls12, _, _>(circuit(), &mut rng).unwrap();
    let key_a = batch::PreparedBatchVerifyingKey::from(&params_a.vk);
    let key_b = batch::PreparedBatchVerifyingKey::from(&params_b.vk);

    let (xl_a, xr_a) = (Scalar::random(&mut rng), Scalar::random(&mut rng));
    let (xl_b, xr_b) = (Scalar::random(&mut rng), Scalar::random(&mut rng));
    let image_a = mimc(xl_a, xr_a, &constants);
    let image_b = mimc(xl_b, xr_b, &constants);
    let proof_a = create_random_proof(
        MiMCDemo {
            xl: Some(xl_a),
            xr: Some(xr_a),
            constants: &constants,
        },
        &params_a,
        &mut rng,
    )
    .unwrap();
    let proof_b = create_random_proof(
        MiMCDemo {
            xl: Some(xl_b),
            xr: Some(xr_b),
            constants: &constants,
        },
        &params_b,
        &mut rng,
    )
    .unwrap();
    let make_batch = |proof: &Proof<Bls12>, image| {
        let mut verifier = batch::Verifier::new();
        verifier.queue((proof.clone(), vec![image]));
        verifier
    };

    assert!(
        make_batch(&proof_a, image_a)
            .verify_joint_prepared(make_batch(&proof_b, image_b), &mut rng, &key_a, &key_b)
            .is_ok()
    );
    assert!(matches!(
        make_batch(&proof_a, image_a + Scalar::ONE).verify_joint_prepared(
            make_batch(&proof_b, image_b),
            &mut rng,
            &key_a,
            &key_b
        ),
        Err(bellman::VerificationError::InvalidProof)
    ));
    assert!(matches!(
        make_batch(&proof_a, image_a).verify_joint_prepared(
            make_batch(&proof_b, image_b + Scalar::ONE),
            &mut rng,
            &key_a,
            &key_b,
        ),
        Err(bellman::VerificationError::InvalidProof)
    ));
    assert!(
        batch::Verifier::new()
            .verify_joint_prepared(make_batch(&proof_b, image_b), &mut rng, &key_a, &key_b)
            .is_ok()
    );
    assert!(
        make_batch(&proof_a, image_a)
            .verify_joint_prepared(batch::Verifier::new(), &mut rng, &key_a, &key_b)
            .is_ok()
    );
    assert!(
        batch::Verifier::<Bls12>::new()
            .verify_joint_prepared(batch::Verifier::new(), &mut rng, &key_a, &key_b)
            .is_ok()
    );

    let mut malformed = batch::Verifier::new();
    malformed.queue((proof_b, vec![]));
    assert!(matches!(
        make_batch(&proof_a, image_a).verify_joint_prepared(malformed, &mut rng, &key_a, &key_b),
        Err(bellman::VerificationError::InvalidVerifyingKey)
    ));
}

#[test]
fn batch_rejects_each_invalid_proof() {
    let (vk, pvk, proofs) = batch_fixture();
    let mut rng = StdRng::seed_from_u64(1);
    // Cover empty and singleton batches, and both sides of the multicore chunk
    // boundary. The first item has the unit weight.
    for size in [0, 1, 2, 8, 9, 17] {
        let mut items = proofs
            .iter()
            .cycle()
            .take(size)
            .cloned()
            .collect::<Vec<_>>();
        assert_batch_matches_single(&vk, &pvk, &items, &mut rng);
        for position in 0..size {
            let valid = items[position].clone();
            corrupt(&mut items[position], size + position);
            let (proof, inputs) = &items[position];
            assert!(verify_proof(&pvk, proof, inputs).is_err());
            assert_batch_matches_single(&vk, &pvk, &items, &mut rng);
            items[position] = valid;
        }
    }
}

#[test]
fn batch_matches_single_verification() {
    let (vk, pvk, proofs) = batch_fixture();
    for seed in 0..64 {
        let mut rng = StdRng::seed_from_u64(seed);
        let size = rng.random_range(1..=20);
        let mut items = (0..size)
            .map(|_| proofs.choose(&mut rng).unwrap().clone())
            .collect::<Vec<_>>();
        for _ in 0..rng.random_range(0..3) {
            let position = rng.random_range(0..size);
            corrupt(&mut items[position], rng.random_range(0..4));
        }
        assert_batch_matches_single(&vk, &pvk, &items, &mut rng);
    }
}

#[test]
fn batch_rejects_cancelling_errors() {
    let (vk, pvk, proofs) = batch_fixture();
    let mut rng = StdRng::seed_from_u64(2);

    // Match the adaptive chunk size in `verify_multicore_prepared_unchecked`.
    const BATCH_SIZE: usize = 17;
    #[cfg(feature = "multicore")]
    let threads = rayon::current_num_threads();
    #[cfg(not(feature = "multicore"))]
    let threads = 1;
    let chunk_size = BATCH_SIZE.div_ceil(threads).clamp(1, 8);

    // These errors cancel if both items get the same weight. In particular, errors at
    // chunk starts catch assigning the unit weight to the first item of every chunk.
    for (first, second) in [
        (0, 1),
        (0, chunk_size),
        (1, chunk_size + 1),
        (chunk_size - 1, chunk_size),
        (chunk_size, 2 * chunk_size),
    ] {
        let mut items = proofs
            .iter()
            .cycle()
            .take(BATCH_SIZE)
            .cloned()
            .collect::<Vec<_>>();
        items[first].0.c = (items[first].0.c + G1Projective::generator()).into();
        items[second].0.c = (items[second].0.c - G1Projective::generator()).into();
        assert_batch_matches_single(&vk, &pvk, &items, &mut rng);
    }
}

#[test]
fn joint_prepared_batch_rejects_cancelling_errors() {
    let (vk, pvk, proofs) = batch_fixture();
    let cache = batch::PreparedBatchG2::from(&vk);
    let key = batch::PreparedBatchVerifyingKey::from_cached(&vk, &cache).unwrap();
    let make_batch = |items: &[Item]| {
        let mut verifier = batch::Verifier::new();
        for item in items {
            verifier.queue(item.clone());
        }
        verifier
    };

    for size in [1, 3] {
        for invalid in [false, true] {
            let mut first = proofs[..size].to_vec();
            let mut second = proofs[..size].to_vec();
            if invalid {
                // Opposite errors cancel if the first proof of each side gets weight one.
                first[0].0.c = (first[0].0.c + G1Projective::generator()).into();
                second[0].0.c = (second[0].0.c - G1Projective::generator()).into();
                assert!(verify_proof(&pvk, &first[0].0, &first[0].1).is_err());
                assert!(verify_proof(&pvk, &second[0].0, &second[0].1).is_err());
            }

            // Every proof except the first across both batches draws exactly 16 bytes.
            // Repeated 0x02 bytes select a nonzero weight different from one.
            let mut rng = FixedBytes(vec![2; 16 * (2 * size - 1)].into_iter());
            assert!(is_expected(
                make_batch(&first).verify_joint_prepared(make_batch(&second), &mut rng, &key, &key),
                !invalid,
            ));
            assert_eq!(rng.0.len(), 0);
        }
    }
}

#[test]
fn batch_accepts_empty_batch() {
    let (mut vk, _, _) = batch_fixture();
    // A key with no `ic` points can be deserialized, and has no valid proofs.
    for ic_len in [1, 0] {
        vk.ic.truncate(ic_len);
        assert!(batch::Verifier::new().verify(rng(), &vk).is_ok());
        #[cfg(feature = "multicore")]
        assert!(batch::Verifier::new().verify_multicore(&vk).is_ok());
    }
}

/// Supplies fixed bytes, so that a test can choose the batch weights.
struct FixedBytes(std::vec::IntoIter<u8>);

impl TryRng for FixedBytes {
    type Error = std::convert::Infallible;

    fn try_next_u32(&mut self) -> Result<u32, Self::Error> {
        let mut bytes = [0; 4];
        self.try_fill_bytes(&mut bytes)?;
        Ok(u32::from_le_bytes(bytes))
    }

    fn try_next_u64(&mut self) -> Result<u64, Self::Error> {
        let mut bytes = [0; 8];
        self.try_fill_bytes(&mut bytes)?;
        Ok(u64::from_le_bytes(bytes))
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Self::Error> {
        for byte in dest {
            *byte = self.0.next().expect("the test supplies every random byte");
        }
        Ok(())
    }
}

impl TryCryptoRng for FixedBytes {}

#[test]
fn batch_retries_zero_weight() {
    let (vk, _, proofs) = batch_fixture();
    for valid in [true, false] {
        let mut items = proofs[..2].to_vec();
        if !valid {
            corrupt(&mut items[1], 3);
        }
        let mut batch = batch::Verifier::new();
        for item in items {
            batch.queue(item);
        }
        // The unit-weight item draws nothing. The other item first draws zero, which
        // would drop it from the batch, then draws the largest weight, 2^128 - 1.
        let mut rng = FixedBytes([[0; 16], [0xff; 16]].concat().into_iter());
        assert!(is_expected(batch.verify(&mut rng, &vk), valid));
        assert_eq!(rng.0.len(), 0);
    }
}
