use std::hint::black_box;

use criterion::{BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};

use bellman::{Circuit, ConstraintSystem, SynthesisError};
use bls12_381::{Bls12, Scalar};
use ff::Field;
use rand::rng;

use groth16::{
    batch, create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
};

/// A circuit with the seven public inputs of a Sapling Spend. Verification cost depends on
/// the number of public inputs, not on the constraints.
struct SaplingSized {
    witnesses: Option<[Scalar; 7]>,
}

impl Circuit<Scalar> for SaplingSized {
    fn synthesize<CS: ConstraintSystem<Scalar>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        for i in 0..7 {
            let witness = self.witnesses.map(|witnesses| witnesses[i]);
            let x = cs.alloc(
                || format!("witness {i}"),
                || witness.ok_or(SynthesisError::AssignmentMissing),
            )?;
            let square = cs.alloc_input(
                || format!("square {i}"),
                || {
                    witness
                        .map(|witness| witness.square())
                        .ok_or(SynthesisError::AssignmentMissing)
                },
            )?;
            cs.enforce(
                || format!("square {i}"),
                |lc| lc + x,
                |lc| lc + x,
                |lc| lc + square,
            );
        }
        Ok(())
    }
}

fn bench_batch_verify(c: &mut Criterion) {
    let mut group = c.benchmark_group("Sapling-sized verification");
    let mut rng = rng();

    let params =
        generate_random_parameters::<Bls12, _, _>(SaplingSized { witnesses: None }, &mut rng)
            .unwrap();
    let pvk = prepare_verifying_key(&params.vk);

    let all_proofs = std::iter::repeat_with(|| {
        let witnesses: [Scalar; 7] = std::array::from_fn(|_| Scalar::random(&mut rng));
        let circuit = SaplingSized {
            witnesses: Some(witnesses),
        };
        let proof = create_random_proof(circuit, &params, &mut rng).unwrap();
        (proof, witnesses.map(|witness| witness.square()))
    })
    .take(256)
    .collect::<Vec<_>>();

    for n in [1, 8, 64, 256] {
        let proofs = &all_proofs[..n];
        group.throughput(Throughput::Elements(n as u64));

        group.bench_with_input(
            BenchmarkId::new("Unbatched verification", n),
            proofs,
            |b, proofs| {
                b.iter(|| {
                    for (proof, inputs) in proofs {
                        assert!(black_box(verify_proof(&pvk, proof, inputs)).is_ok());
                    }
                })
            },
        );

        group.bench_with_input(
            BenchmarkId::new("Batched verification", n),
            proofs,
            |b, proofs| {
                b.iter(|| {
                    let mut batch = batch::Verifier::new();
                    for (proof, inputs) in proofs {
                        batch.queue((proof.clone(), inputs.to_vec()));
                    }
                    assert!(black_box(batch.verify(&mut rng, &params.vk)).is_ok());
                })
            },
        );

        #[cfg(feature = "multicore")]
        group.bench_with_input(
            BenchmarkId::new("Batched multicore verification", n),
            proofs,
            |b, proofs| {
                b.iter(|| {
                    let mut batch = batch::Verifier::new();
                    for (proof, inputs) in proofs {
                        batch.queue((proof.clone(), inputs.to_vec()));
                    }
                    assert!(black_box(batch.verify_multicore(&params.vk)).is_ok());
                })
            },
        );
    }

    group.finish();
}

criterion_group!(benches, bench_batch_verify);
criterion_main!(benches);
