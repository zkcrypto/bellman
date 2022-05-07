use bellman::{
    multicore::Worker,
    multiexp::{multiexp, FullDensity},
};
use bls12_381::{Bls12, Scalar};
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use ff::Field;
use group::{Curve, Group};
use pairing::Engine;
use rand_core::SeedableRng;
use rand_xorshift::XorShiftRng;
use std::sync::Arc;

fn bench_parts(c: &mut Criterion) {
    let mut rng = XorShiftRng::from_seed([7; 16]);
    let samples = 1 << 16;

    let v = Arc::new(
        (0..samples)
            .map(|_| Scalar::random(&mut rng))
            .collect::<Vec<_>>(),
    );
    let v_bits = Arc::new(v.iter().map(|e| e.into()).collect::<Vec<_>>());
    let g = Arc::new(
        (0..samples)
            .map(|_| <Bls12 as Engine>::G1::random(&mut rng).to_affine())
            .collect::<Vec<_>>(),
    );

    let pool = Worker::new();

    c.bench_with_input(
        BenchmarkId::new("multiexp", samples),
        &(pool, g, v_bits),
        |b, (pool, g, v_bits)| {
            b.iter(|| {
                let _: <Bls12 as Engine>::G1 =
                    multiexp(pool, (g.clone(), 0), FullDensity, v_bits.clone())
                        .wait()
                        .unwrap();
            })
        },
    );
}

criterion_group!(benches, bench_parts);
criterion_main!(benches);
