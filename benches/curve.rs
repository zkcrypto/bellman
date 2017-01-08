#![feature(test)]
#![allow(unused_mut)]

extern crate rand;
extern crate bellman;
extern crate test;

use bellman::curves::*;
use bellman::curves::bls381::*;

const SAMPLES: usize = 30;

macro_rules! benchmark(
    ($name:ident, $engine:ident, $input:ident($rng:ident) = $pre:expr; $post:expr) => (
        #[bench]
        fn $name(b: &mut test::Bencher) {
            let $rng = &mut rand::thread_rng();
            let $engine = &Bls381::new();
            let $input: Vec<_> = (0..SAMPLES).map(|_| $pre).collect();

            let mut c = 0;

            b.iter(|| {
                c += 1;

                let mut $input = $input[c % SAMPLES].clone();

                $post
            })
        }
    )
);

benchmark!(g1_multiexp, e,
    input(rng) = {
        let mut g = G1::random(e, rng);
        let mut a = G1::random(e, rng);
        (
            (0..1000).map(|_| {
                g.add_assign(e, &a);
                a.double(e);
                g.to_affine(e)
            }).collect::<Vec<_>>(),
            (0..1000).map(|_| Fr::random(e, rng)).collect::<Vec<_>>(),
        )
    };

    e.multiexp::<G1>(&input.0, &input.1)
);

benchmark!(g2_multiexp, e,
    input(rng) = {
        let mut g = G2::random(e, rng);
        let mut a = G2::random(e, rng);
        (
            (0..1000).map(|_| {
                g.add_assign(e, &a);
                a.double(e);
                g.to_affine(e)
            }).collect::<Vec<_>>(),
            (0..1000).map(|_| Fr::random(e, rng)).collect::<Vec<_>>(),
        )
    };

    e.multiexp::<G2>(&input.0, &input.1)
);

benchmark!(full_pairing, e,
    input(rng) = (G1::random(e, rng), G2::random(e, rng));

    e.pairing(&input.0, &input.1)
);

benchmark!(g1_pairing_preparation, e,
    input(rng) = G1::random(e, rng);

    input.prepare(e)
);

benchmark!(g2_pairing_preparation, e,
    input(rng) = G2::random(e, rng);

    input.prepare(e)
);

benchmark!(miller_loop, e,
    input(rng) = (G1::random(e, rng).prepare(e), G2::random(e, rng).prepare(e));

    e.miller_loop([(&input.0, &input.1)].into_iter())
);

benchmark!(double_miller_loop, e,
    input(rng) = (G1::random(e, rng).prepare(e), G2::random(e, rng).prepare(e), G1::random(e, rng).prepare(e), G2::random(e, rng).prepare(e));

    e.miller_loop([
        (&input.0, &input.1),
        (&input.2, &input.3),
    ].into_iter())
);

benchmark!(final_exponentiation, e,
    input(rng) = e.miller_loop([
        (&G1::random(e, rng).prepare(e), &G2::random(e, rng).prepare(e)),
    ].into_iter());

    e.final_exponentiation(&input)
);

macro_rules! group_tests(
    (
        $name:ident,
        $mul:ident,
        $mul_mixed:ident,
        $add:ident
    ) => {
        benchmark!($mul, e,
            input(rng) = ($name::random(e, rng), Fr::random(e, rng));

            {input.0.mul_assign(e, &input.1); input.0}
        );

        benchmark!($mul_mixed, e,
            input(rng) = ($name::random(e, rng).to_affine(e), Fr::random(e, rng));

            {input.0.mul(e, &input.1)}
        );

        benchmark!($add, e,
            input(rng) = ($name::random(e, rng), $name::random(e, rng));

            {input.0.add_assign(e, &input.1); input.0}
        );
    };
);

macro_rules! field_tests(
    (
        @nosqrt,
        $name:ident,
        $mul:ident,
        $square:ident,
        $add:ident,
        $inverse:ident
    ) => {
        benchmark!($mul, e,
            input(rng) = ($name::random(e, rng), $name::random(e, rng));

            {input.0.mul_assign(e, &input.1); input.0}
        );

        benchmark!($square, e,
            input(rng) = $name::random(e, rng);

            {input.square(e); input}
        );

        benchmark!($add, e,
            input(rng) = ($name::random(e, rng), $name::random(e, rng));

            {input.0.add_assign(e, &input.1); input.0}
        );

        benchmark!($inverse, e,
            input(rng) = $name::random(e, rng);

            {input.inverse(e)}
        );
    };
    (
        $name:ident,
        $mul:ident,
        $square:ident,
        $add:ident,
        $inverse:ident,
        $sqrt:ident
    ) => {
        field_tests!(@nosqrt, $name, $mul, $square, $add, $inverse);

        benchmark!($sqrt, e,
            input(rng) = {let mut tmp = $name::random(e, rng); tmp.square(e); tmp};

            {input.sqrt(e)}
        );
    };
);

field_tests!(
    Fr,
    fr_multiplication,
    fr_squaring,
    fr_addition,
    fr_inverse,
    fr_sqrt
);

field_tests!(
    Fq,
    fq_multiplication,
    fq_squaring,
    fq_addition,
    fq_inverse,
    fq_sqrt
);

field_tests!(
    Fq2,
    fq2_multiplication,
    fq2_squaring,
    fq2_addition,
    fq2_inverse,
    fq2_sqrt
);

field_tests!(
    @nosqrt,
    Fq12,
    fq12_multiplication,
    fq12_squaring,
    fq12_addition,
    fq12_inverse
);

group_tests!(
    G1,
    g1_multiplication,
    g1_multiplication_mixed,
    g1_addition
);

group_tests!(
    G2,
    g2_multiplication,
    g2_multiplication_mixed,
    g2_addition
);
