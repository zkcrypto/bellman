use bellperson::{Index, LinearCombination, Variable};
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use ff::{Field, ScalarEngine};
use paired::bls12_381::Bls12;

fn lc_benchmark(c: &mut Criterion) {
    c.bench_function("LinearCombination::add((Fr, Variable))", |b| {
        b.iter(|| {
            let mut lc = LinearCombination::<Bls12>::zero();
            for i in 0..100 {
                let coeff = <Bls12 as ScalarEngine>::Fr::one();
                lc = lc + (coeff, Variable::new_unchecked(Index::Aux(i)));
            }
            black_box(lc);
        });
    })
    .bench_function("LinearCombination::add(LinearCombination)", |b| {
        let mut lc1 = LinearCombination::<Bls12>::zero();
        let mut lc2 = LinearCombination::<Bls12>::zero();
        for i in 0..10 {
            let coeff = <Bls12 as ScalarEngine>::Fr::one();
            lc1 = lc1 + (coeff, Variable::new_unchecked(Index::Aux(i)));

            let coeff = <Bls12 as ScalarEngine>::Fr::one();
            lc2 = lc2 + (coeff, Variable::new_unchecked(Index::Aux(i * 2)));
        }

        b.iter(|| {
            let mut lc = lc1.clone();
            for _ in 0..10 {
                lc = lc + &lc2;
            }
            black_box(lc);
        });
    });
}

criterion_group!(benches, lc_benchmark);
criterion_main!(benches);
