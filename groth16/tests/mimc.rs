// For randomness (during paramgen and proof generation)
use rand::rng;

// For benchmarking
use std::time::{Duration, Instant};

// Bring in some tools for using finite fiels
use ff::Field;

// We're going to use the BLS12-381 pairing-friendly elliptic curve.
use bls12_381::{Bls12, Scalar};

// We're going to use the Groth16 proving system.
use groth16::{
    batch, create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
    Proof,
};

#[cfg(feature = "multicore")]
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

#[test]
fn batch_verify() {
    let mut rng = rng();

    let mut batch = batch::Verifier::new();

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

        // Queue the proof and inputs for batch verification.
        batch.queue((proof, [image].into()));
    }

    let mut batch_verifying = Duration::new(0, 0);
    let batch_start = Instant::now();

    // Verify this batch for this specific verifying key
    assert!(batch.verify(rng, &params.vk).is_ok());

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
