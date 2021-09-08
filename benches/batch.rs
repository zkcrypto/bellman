use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};

use bls12_381::Bls12;
use ff::Field;
use rand::thread_rng;

use bellman::groth16::{
    batch, create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
};

#[path = "../tests/common/mod.rs"]
mod common;

use common::*;

fn bench_batch_verify(c: &mut Criterion) {
    let mut group = c.benchmark_group("Batch Verification");

    for &n in [8usize, 16, 24, 32, 40, 48, 56, 64].iter() {
        group.throughput(Throughput::Elements(n as u64));

        let mut rng = thread_rng();

        // Generate the MiMC round constants
        let constants = (0..MIMC_ROUNDS)
            .map(|_| bls12_381::Scalar::random(&mut rng))
            .collect::<Vec<_>>();

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

        let proofs = {
            std::iter::repeat_with(|| {
                // Generate a random preimage and compute the image
                let xl = bls12_381::Scalar::random(&mut rng);
                let xr = bls12_381::Scalar::random(&mut rng);
                let image = mimc(xl, xr, &constants);

                // Create an instance of our circuit (with the
                // witness)
                let c = MiMCDemo {
                    xl: Some(xl),
                    xr: Some(xr),
                    constants: &constants,
                };

                // Create a groth16 proof with our parameters.
                let proof = create_random_proof(c, &params, &mut rng).unwrap();

                (proof, image)
            })
        }
        .take(n)
        .collect::<Vec<_>>();

        group.bench_with_input(
            BenchmarkId::new("Unbatched verification", n),
            &proofs,
            |b, proofs| {
                b.iter(|| {
                    for (proof, input) in proofs.iter() {
                        let _ = verify_proof(&pvk, proof, &[*input]);
                    }
                })
            },
        );

        group.bench_with_input(
            BenchmarkId::new("Batched verification", n),
            &proofs,
            |b, proofs| {
                b.iter(|| {
                    let mut batch = batch::Verifier::new();
                    for (proof, input) in proofs.iter() {
                        batch.queue((proof.clone(), vec![*input]));
                    }
                    batch.verify(&mut rng, &params.vk)
                })
            },
        );
    }

    group.finish();
}

criterion_group!(benches, bench_batch_verify);
criterion_main!(benches);
