use groth16::{batch, create_random_proof, generate_random_parameters};
use bls12_381::{Bls12, Scalar};
use criterion::{BenchmarkId, Criterion, Throughput, black_box, criterion_group, criterion_main};
use ff::Field;
use rand::rng;

#[path = "../tests/common/mod.rs"]
mod common;

use common::*;

fn bench_prepared_batch(c: &mut Criterion) {
    let mut group = c.benchmark_group("Groth16 batch key");

    for n in [1usize, 2, 8] {
        group.throughput(Throughput::Elements(n as u64));
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
        let proofs = (0..n)
            .map(|_| {
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
                (proof, image)
            })
            .collect::<Vec<_>>();
        let prepared = batch::PreparedBatchVerifyingKey::from(&params.vk);

        if n == 1 {
            group.bench_function("key setup", |b| {
                b.iter(|| {
                    black_box(batch::PreparedBatchVerifyingKey::from(black_box(
                        &params.vk,
                    )))
                })
            });
        }

        group.bench_with_input(BenchmarkId::new("serial raw", n), &proofs, |b, proofs| {
            b.iter(|| {
                let mut batch = batch::Verifier::new();
                for (proof, input) in proofs {
                    batch.queue((proof.clone(), vec![*input]));
                }
                black_box(batch.verify(&mut rng, &params.vk))
            });
        });
        group.bench_with_input(
            BenchmarkId::new("serial prepared", n),
            &proofs,
            |b, proofs| {
                b.iter(|| {
                    let mut batch = batch::Verifier::new();
                    for (proof, input) in proofs {
                        batch.queue((proof.clone(), vec![*input]));
                    }
                    black_box(batch.verify_prepared(&mut rng, &prepared))
                });
            },
        );

        #[cfg(feature = "multicore")]
        {
            group.bench_with_input(
                BenchmarkId::new("multicore raw", n),
                &proofs,
                |b, proofs| {
                    b.iter(|| {
                        let mut batch = batch::Verifier::new();
                        for (proof, input) in proofs {
                            batch.queue((proof.clone(), vec![*input]));
                        }
                        black_box(batch.verify_multicore(&params.vk))
                    });
                },
            );
            group.bench_with_input(
                BenchmarkId::new("multicore prepared", n),
                &proofs,
                |b, proofs| {
                    b.iter(|| {
                        let mut batch = batch::Verifier::new();
                        for (proof, input) in proofs {
                            batch.queue((proof.clone(), vec![*input]));
                        }
                        black_box(batch.verify_multicore_prepared(&prepared))
                    });
                },
            );
        }
    }
    group.finish();
}

criterion_group!(benches, bench_prepared_batch);
criterion_main!(benches);
