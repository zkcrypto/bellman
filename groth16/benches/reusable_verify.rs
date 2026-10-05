use bls12_381::{Bls12, Scalar};
use criterion::{Criterion, black_box, criterion_group, criterion_main};
use ff::Field;
use groth16::{
    create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
};
use rand::{SeedableRng, rngs::StdRng};

#[path = "../tests/common/mod.rs"]
mod common;

use common::*;

fn bench_reusable_verification(c: &mut Criterion) {
    let mut rng = StdRng::seed_from_u64(0x2026_0924);
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
    let pvk = prepare_verifying_key(&params.vk);
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
    verify_proof(&pvk, &proof, &[image]).unwrap();

    c.bench_function("Groth16 verify with reusable key", |b| {
        b.iter(|| verify_proof(black_box(&pvk), black_box(&proof), black_box(&[image])).unwrap())
    });
}

criterion_group!(benches, bench_reusable_verification);
criterion_main!(benches);
