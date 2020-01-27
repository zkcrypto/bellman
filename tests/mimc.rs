// For randomness (during paramgen and proof generation)
use rand::thread_rng;

// For benchmarking
use std::time::{Duration, Instant};

// Bring in some tools for using pairing-friendly curves
use ff::{Field, ScalarEngine};
use paired::Engine;

// We're going to use the BLS12-381 pairing-friendly elliptic curve.
use paired::bls12_381::Bls12;

// We'll use these interfaces to construct our circuit.
use bellperson::{Circuit, ConstraintSystem, SynthesisError};

// We're going to use the Groth16 proving system.
use bellperson::groth16::{
    create_random_proof, create_random_proof_batch, generate_random_parameters,
    prepare_batch_verifying_key, prepare_verifying_key, verify_proof, verify_proofs_batch, Proof,
};

const MIMC_ROUNDS: usize = 322;

/// This is an implementation of MiMC, specifically a
/// variant named `LongsightF322p3` for BLS12-381.
/// See http://eprint.iacr.org/2016/492 for more
/// information about this construction.
///
/// ```
/// function LongsightF322p3(xL ⦂ Fp, xR ⦂ Fp) {
///     for i from 0 up to 321 {
///         xL, xR := xR + (xL + Ci)^3, xL
///     }
///     return xL
/// }
/// ```
fn mimc<E: Engine>(mut xl: E::Fr, mut xr: E::Fr, constants: &[E::Fr]) -> E::Fr {
    assert_eq!(constants.len(), MIMC_ROUNDS);

    for i in 0..MIMC_ROUNDS {
        let mut tmp1 = xl;
        tmp1.add_assign(&constants[i]);
        let mut tmp2 = tmp1;
        tmp2.square();
        tmp2.mul_assign(&tmp1);
        tmp2.add_assign(&xr);
        xr = xl;
        xl = tmp2;
    }

    xl
}

/// This is our demo circuit for proving knowledge of the
/// preimage of a MiMC hash invocation.
#[derive(Clone)]
struct MiMCDemo<'a, E: Engine> {
    xl: Option<E::Fr>,
    xr: Option<E::Fr>,
    constants: &'a [E::Fr],
}

/// Our demo circuit implements this `Circuit` trait which
/// is used during paramgen and proving in order to
/// synthesize the constraint system.
impl<'a, E: Engine> Circuit<E> for MiMCDemo<'a, E> {
    fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        assert_eq!(self.constants.len(), MIMC_ROUNDS);

        // Allocate the first component of the preimage.
        let mut xl_value = self.xl;
        let mut xl = cs.alloc(
            || "preimage xl",
            || xl_value.ok_or(SynthesisError::AssignmentMissing),
        )?;

        // Allocate the second component of the preimage.
        let mut xr_value = self.xr;
        let mut xr = cs.alloc(
            || "preimage xr",
            || xr_value.ok_or(SynthesisError::AssignmentMissing),
        )?;

        for i in 0..MIMC_ROUNDS {
            // xL, xR := xR + (xL + Ci)^3, xL
            let cs = &mut cs.namespace(|| format!("round {}", i));

            // tmp = (xL + Ci)^2
            let tmp_value = xl_value.map(|mut e| {
                e.add_assign(&self.constants[i]);
                e.square();
                e
            });
            let tmp = cs.alloc(
                || "tmp",
                || tmp_value.ok_or(SynthesisError::AssignmentMissing),
            )?;

            cs.enforce(
                || "tmp = (xL + Ci)^2",
                |lc| lc + xl + (self.constants[i], CS::one()),
                |lc| lc + xl + (self.constants[i], CS::one()),
                |lc| lc + tmp,
            );

            // new_xL = xR + (xL + Ci)^3
            // new_xL = xR + tmp * (xL + Ci)
            // new_xL - xR = tmp * (xL + Ci)
            let new_xl_value = xl_value.map(|mut e| {
                e.add_assign(&self.constants[i]);
                e.mul_assign(&tmp_value.unwrap());
                e.add_assign(&xr_value.unwrap());
                e
            });

            let new_xl = if i == (MIMC_ROUNDS - 1) {
                // This is the last round, xL is our image and so
                // we allocate a public input.
                cs.alloc_input(
                    || "image",
                    || new_xl_value.ok_or(SynthesisError::AssignmentMissing),
                )?
            } else {
                cs.alloc(
                    || "new_xl",
                    || new_xl_value.ok_or(SynthesisError::AssignmentMissing),
                )?
            };

            cs.enforce(
                || "new_xL = xR + (xL + Ci)^3",
                |lc| lc + tmp,
                |lc| lc + xl + (self.constants[i], CS::one()),
                |lc| lc + new_xl - xr,
            );

            // xR = xL
            xr = xl;
            xr_value = xl_value;

            // xL = new_xL
            xl = new_xl;
            xl_value = new_xl_value;
        }

        Ok(())
    }
}

#[test]
fn test_mimc() {
    // This may not be cryptographically safe, use
    // `OsRng` (for example) in production software.
    let rng = &mut thread_rng();

    // Generate the MiMC round constants
    let constants = (0..MIMC_ROUNDS)
        .map(|_| <Bls12 as ScalarEngine>::Fr::random(rng))
        .collect::<Vec<_>>();

    println!("Creating parameters...");

    // Create parameters for our circuit
    let params = {
        let c = MiMCDemo::<Bls12> {
            xl: None,
            xr: None,
            constants: &constants,
        };

        generate_random_parameters(c, rng).unwrap()
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
    let mut proofs = vec![];
    let mut images = vec![];

    for _ in 0..SAMPLES {
        // Generate a random preimage and compute the image
        let xl = <Bls12 as ScalarEngine>::Fr::random(rng);
        let xr = <Bls12 as ScalarEngine>::Fr::random(rng);
        let image = mimc::<Bls12>(xl, xr, &constants);

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
            let proof = create_random_proof(c, &params, rng).unwrap();

            proof.write(&mut proof_vec).unwrap();
        }

        total_proving += start.elapsed();

        let start = Instant::now();
        let proof = Proof::read(&proof_vec[..]).unwrap();
        // Check the proof
        assert!(verify_proof(&pvk, &proof, &[image]).unwrap());
        total_verifying += start.elapsed();
        proofs.push(proof);
        images.push(vec![image]);
    }

    // batch verification
    println!("Creating batch proofs...");
    let proving_batch = Instant::now();
    {
        // Create an instance of our circuit (with the
        // witness)
        let xl = <Bls12 as ScalarEngine>::Fr::random(rng);
        let xr = <Bls12 as ScalarEngine>::Fr::random(rng);

        let c = MiMCDemo {
            xl: Some(xl),
            xr: Some(xr),
            constants: &constants,
        };

        // Create a groth16 proof with our parameters.
        let proofs = create_random_proof_batch(vec![c; SAMPLES as usize], &params, rng).unwrap();
        assert_eq!(proofs.len(), 50);
    }

    let proving_batch = proving_batch.elapsed().subsec_nanos() as f64 / 1_000_000_000f64;
    println!(
        "Proving time batch: {:04}s ({:04}s / proof)",
        proving_batch,
        proving_batch / SAMPLES as f64,
    );

    let proving_avg = total_proving / SAMPLES;
    let proving_avg =
        proving_avg.subsec_nanos() as f64 / 1_000_000_000f64 + (proving_avg.as_secs() as f64);

    let verifying_avg = total_verifying / SAMPLES;
    let verifying_avg =
        verifying_avg.subsec_nanos() as f64 / 1_000_000_000f64 + (verifying_avg.as_secs() as f64);

    println!("Average proving time: {:08}s", proving_avg);
    println!("Average verifying time: {:08}s", verifying_avg);

    // batch verification
    {
        let pvk = prepare_batch_verifying_key(&params.vk);

        let start = Instant::now();
        let proofs: Vec<_> = proofs.iter().collect();
        let valid = verify_proofs_batch(&pvk, &mut rand::rngs::OsRng, &proofs, &images).unwrap();
        println!(
            "Batch verification of {} proofs: {:04}s ({:04}s/proof)",
            proofs.len(),
            (start.elapsed().subsec_nanos() as f64) / 1_000_000_000f64,
            ((start.elapsed().subsec_nanos() as f64) / 1_000_000_000f64) / proofs.len() as f64,
        );
        assert!(valid, "failed batch verification");

        // check that invalid proofs don't validate
        let mut bad_proofs = proofs
            .iter()
            .map(|p| (*p).clone())
            .collect::<Vec<Proof<_>>>();

        for i in 0..proofs.len() {
            use groupy::CurveProjective;

            let p = &mut bad_proofs[i];

            let mut a: <Bls12 as Engine>::G1 = p.a.into();
            a.add_assign(&<Bls12 as Engine>::G1::one());
            p.a = a.into_affine();
        }
        let bad_proofs_ref = bad_proofs.iter().collect::<Vec<_>>();
        assert!(
            !verify_proofs_batch(&pvk, &mut rand::rngs::OsRng, &bad_proofs_ref[..], &images)
                .unwrap()
        );
    }
}
