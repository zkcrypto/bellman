#[cfg(test)]
mod test {
    use super::*;

    #[derive(Clone)]
    struct BenchmarkCircuit<E: Engine>{
        num_steps: usize,
        _marker: std::marker::PhantomData<E>
    }

    impl<E: Engine> Circuit<E> for BenchmarkCircuit<E> {
        fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
            // yeah, fibonacci...

            let one = E::Fr::one();
            let mut negative_one = one;
            negative_one.negate();

            let mut two = one;
            two.double();
            
            let mut a = cs.alloc(|| {
                Ok(E::Fr::one())
            })?;

            let mut b = cs.alloc(|| {
                Ok(E::Fr::one())
            })?;

            cs.enforce_zero_2((a, b), (one, negative_one))?;
            // cs.enforce_zero_2((b, CS::ONE), (one, negative_one))?;

            let mut c = cs.alloc(|| {
                Ok(two)
            })?;

            cs.enforce_zero_3((a, b, c), (one, one, negative_one))?;

            let mut a_value = one;
            let mut b_value = one;
            let mut c_value = two;

            for _ in 0..self.num_steps {
                a = b;
                b = c;

                a_value = b_value;
                b_value = c_value;
                c_value.add_assign(&a_value);

                c = cs.alloc(|| {
                    Ok(c_value)
                })?;

                cs.enforce_zero_3((a, b, c), (one, one, negative_one))?;
            }

            Ok(())
        }
    }

    #[test]
    fn test_bench_redshift() {
        use crate::pairing::Engine;
        use crate::ff::ScalarEngine;
        use

        type Fr = <Transparent252 as ScalarEngine>::Fr;
        type Transcr = Blake2sTranscript<Fr>;

        use crate::plonk::fft::cooley_tukey_ntt::*;
        use crate::plonk::commitments::transparent::fri::coset_combining_fri::*;
        use crate::plonk::commitments::transparent::fri::coset_combining_fri::fri::*;
        use crate::plonk::commitments::transparent::fri::coset_combining_fri::precomputation::*;
        use crate::plonk::commitments::transparent::iop_compiler::*;
        use crate::plonk::commitments::transparent::iop_compiler::coset_combining_blake2s_tree::*;

        use std::time::Instant;

        let log_2_rate = 4;
        let rate = 1 << log_2_rate;
        println!("Using rate {}", rate);
        let sizes = vec![(1 << 18) - 10, (1 << 19) - 10, (1 << 20) - 10, (1 << 21) - 10, (1 << 22) - 10, (1 << 23) - 10];
        let coset_schedules = vec![
            vec![3, 3, 3, 3, 3, 3], // 18
            vec![3, 3, 3, 3, 3, 2, 2], // 19
            vec![3, 3, 3, 3, 3, 3, 2], // 20
            vec![3, 3, 3, 3, 3, 3, 3], // 21 
            vec![3, 3, 3, 3, 3, 3, 2, 2], // 22 
            vec![3, 3, 3, 3, 3, 3, 3, 2], // 23 
        ];

        let worker = Worker::new();

        for (size, coset_schedule) in sizes.into_iter().zip(coset_schedules.into_iter()) {
            println!("Working for size {}", size);
            let coset_params = CosetParams {
                cosets_schedule: coset_schedule,
                coset_factor: Fr::multiplicative_generator()
            };

            let params = RedshiftParameters {
                lde_factor: rate,
                num_queries: 4,
                output_coeffs_at_degree_plus_one: 1,
                coset_params: coset_params
            };

            let circuit = BenchmarkCircuit::<Transparent252> {
                num_steps: size,
                _marker: std::marker::PhantomData
            };

            let omegas_bitreversed = BitReversedOmegas::<Fr>::new_for_domain_size(size.next_power_of_two());
            let omegas_inv_bitreversed = <OmegasInvBitreversed::<Fr> as CTPrecomputations::<Fr>>::new_for_domain_size(size.next_power_of_two());
            let omegas_inv_bitreversed_for_fri = <CosetOmegasInvBitreversed::<Fr> as FriPrecomputations::<Fr>>::new_for_domain_size(size.next_power_of_two() * rate);

            let (_, setup_precomp) = setup_with_precomputations::<Transparent252, _, _, Transcr>(
                &circuit,
                &params,
                &omegas_bitreversed
            ).unwrap();

            let mut prover = ProvingAssembly::<Transparent252>::new();
            circuit.synthesize(&mut prover).unwrap();
            prover.finalize();

            println!("Start proving");

            let start = Instant::now();

            let _ = prover.prove_with_setup_precomputed::<_, _, _, Transcr>(
                &setup_precomp, 
                &params, 
                &worker, 
                &omegas_bitreversed, 
                &omegas_inv_bitreversed,
                &omegas_inv_bitreversed_for_fri
            ).unwrap();

            println!("Proving taken {:?} for size {}", start.elapsed(), size);


        }
    }

    #[test]
    fn test_ifft_using_ntt() {
        use rand::{XorShiftRng, SeedableRng, Rand, Rng};
        use crate::plonk::fft::cooley_tukey_ntt::*;
        use crate::plonk::commitments::transparent::fri::coset_combining_fri::*;
        use crate::plonk::commitments::transparent::fri::coset_combining_fri::fri::*;
        use crate::plonk::commitments::transparent::fri::coset_combining_fri::precomputation::*;
        use crate::pairing::Engine;
        use crate::ff::ScalarEngine;
        use crate::plonk::transparent_engine::{TransparentEngine, PartialTwoBitReductionField};
        use crate::plonk::transparent_engine::proth_engine::Transparent252;

        use crate::multicore::*;
        use crate::source::*;

        type Fr = <Transparent252 as ScalarEngine>::Fr;

        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let poly_sizes = vec![100, 1000, 10_000, 1_000_000];

        let worker = Worker::new();

        for poly_size in poly_sizes.clone().into_iter() {
            let coeffs = (0..poly_size).map(|_| Fr::rand(rng)).collect::<Vec<_>>();
            let poly = Polynomial::<Fr, _>::from_values(coeffs).unwrap();
            let naive_result = poly.clone().icoset_fft_for_generator(&worker, &Fr::one());
            let omegas_inv_bitreversed = <OmegasInvBitreversed::<Fr> as CTPrecomputations::<Fr>>::new_for_domain_size((poly_size as usize).next_power_of_two());
            let ntt_result = poly.clone().ifft_using_bitreversed_ntt(&worker, &omegas_inv_bitreversed, &Fr::one()).unwrap();

            assert!(naive_result == ntt_result);
        }

        for poly_size in poly_sizes.into_iter() {
            let coeffs = (0..poly_size).map(|_| Fr::rand(rng)).collect::<Vec<_>>();
            let poly = Polynomial::<Fr, _>::from_values(coeffs).unwrap();
            let naive_result = poly.clone().icoset_fft_for_generator(&worker, &Fr::multiplicative_generator());
            let omegas_inv_bitreversed = <OmegasInvBitreversed::<Fr> as CTPrecomputations::<Fr>>::new_for_domain_size((poly_size as usize).next_power_of_two());
            let ntt_result = poly.clone().ifft_using_bitreversed_ntt(&worker, &omegas_inv_bitreversed, &Fr::multiplicative_generator()).unwrap();

            assert!(naive_result == ntt_result);
        }
    }

    #[test]
    fn test_fft_test_vectors() {
        use rand::{XorShiftRng, SeedableRng, Rand, Rng};
        use crate::plonk::fft::*;
        use crate::pairing::Engine;
        use crate::ff::ScalarEngine;
        use crate::plonk::transparent_engine::{TransparentEngine};
        use crate::plonk::transparent_engine::proth_engine::Transparent252;

        use crate::multicore::*;
        use crate::source::*;

        type Fr = <Transparent252 as ScalarEngine>::Fr;

        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let poly_sizes = vec![4, 8, 16];

        let worker = Worker::new();

        for poly_size in poly_sizes.clone().into_iter() {
            println!("Poly size {}", poly_size);
            let coeffs = (0..poly_size).map(|_| Fr::rand(rng)).collect::<Vec<_>>();
            println!("Coefficients");
            for c in coeffs.iter() {
                println!("{}", c.into_raw_repr());
            }
            println!("Generators");
            let poly = Polynomial::<Fr, _>::from_coeffs(coeffs).unwrap();
            let omega = poly.omega;
            for i in 0..poly_size {
                let gen = omega.pow([i as u64]);
                println!("Omega^{} = {}", i, gen.into_raw_repr());
            }
            println!("Result");
            let naive_result = poly.fft(&worker);
            let coeffs = naive_result.into_coeffs();
            for c in coeffs.iter() {
                println!("{}", c.into_raw_repr());
            }
        }
    }
}

#[cfg(test)]
mod test {

    use super::*;
    use crate::pairing::ff::{Field, PrimeField};
    use crate::pairing::{Engine};

    use crate::{SynthesisError};
    use std::marker::PhantomData;

    use crate::plonk::cs::gates::*;
    use crate::plonk::cs::*;

    struct TestCircuit<E:Engine>{
        _marker: PhantomData<E>
    }

    impl<E: Engine> Circuit<E> for TestCircuit<E> {
        fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
            let a = cs.alloc(|| {
                Ok(E::Fr::from_str("10").unwrap())
            })?;

            let b = cs.alloc(|| {
                Ok(E::Fr::from_str("20").unwrap())
            })?;

            let c = cs.alloc(|| {
                Ok(E::Fr::from_str("200").unwrap())
            })?;

            let one = E::Fr::one();

            let mut two = one;
            two.double();

            let mut negative_one = one;
            negative_one.negate();

            cs.enforce_zero_2((a, b), (two, negative_one))?;

            let ten = E::Fr::from_str("10").unwrap();
            cs.enforce_zero_2((b, c), (ten, negative_one))?;

            cs.enforce_mul_3((a, b, c))?;

            Ok(())
        }
    }

    struct InvalidTestCircuit<E:Engine>{
        _marker: PhantomData<E>
    }

    impl<E: Engine> Circuit<E> for InvalidTestCircuit<E> {
        fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
            let a = cs.alloc(|| {
                Ok(E::Fr::from_str("11").unwrap())
            })?;

            let b = cs.alloc(|| {
                Ok(E::Fr::from_str("20").unwrap())
            })?;

            let c = cs.alloc(|| {
                Ok(E::Fr::from_str("200").unwrap())
            })?;

            let one = E::Fr::one();

            let mut two = one;
            two.double();

            let mut negative_one = one;
            negative_one.negate();

            cs.enforce_zero_2((a, b), (two, negative_one))?;

            let ten = E::Fr::from_str("10").unwrap();
            cs.enforce_zero_2((b, c), (ten, negative_one))?;

            cs.enforce_mul_3((a, b, c))?;

            Ok(())
        }
    }

    #[test]
    fn test_small_circuit_transparent_verification() {
        use crate::pairing::bn256::{Bn256, Fr};
        use crate::plonk::utils::*;
        use crate::plonk::commitments::transparent::fri::*;
        use crate::plonk::commitments::transparent::iop::*;
        use crate::plonk::commitments::transcript::*;
        use crate::plonk::commitments::transparent::fri::naive_fri::naive_fri::*;
        use crate::plonk::commitments::transparent::iop::blake2s_trivial_iop::*;
        use crate::plonk::commitments::*;
        use crate::plonk::commitments::transparent::*;

        type Iop = TrivialBlake2sIOP<Fr>;
        type Fri = NaiveFriIop<Fr, Iop>;
        type Committer = StatelessTransparentCommitter<Fr, Fri, Blake2sTranscript<Fr>>;

        let meta = TransparentCommitterParameters {
            lde_factor: 16,
            num_queries: 2,
            output_coeffs_at_degree_plus_one: 1,
            fri_params: ()
        };

        let meta_large = TransparentCommitterParameters {
            lde_factor: 16,
            num_queries: 2,
            output_coeffs_at_degree_plus_one: 1,
            fri_params: ()
        };

        let circuit = TestCircuit::<Bn256> {
            _marker: PhantomData
        };

        let (setup, aux) = setup::<Bn256, Committer, _>(&circuit, meta).unwrap();

        let meta = TransparentCommitterParameters {
            lde_factor: 16,
            num_queries: 2,
            output_coeffs_at_degree_plus_one: 1,
            fri_params: ()
        };

        println!("Proving");

        let proof = prove_nonhomomorphic::<Bn256, Committer, Blake2sTranscript::<Fr>, _>(&circuit, &setup, &aux, meta.clone(), meta_large.clone()).unwrap();


        println!("Verifying");

        let valid = verify_nonhomomorphic::<Bn256, Committer, Blake2sTranscript::<Fr>>(&setup, &proof, meta, meta_large).unwrap();

        assert!(valid);
    }

    #[test]
    fn test_small_circuit_invalid_witness_transparent_verification() {
        use crate::pairing::bn256::{Bn256, Fr};
        use crate::plonk::utils::*;
        use crate::plonk::commitments::transparent::fri::*;
        use crate::plonk::commitments::transparent::iop::*;
        use crate::plonk::commitments::transcript::*;
        use crate::plonk::commitments::transparent::fri::naive_fri::naive_fri::*;
        use crate::plonk::commitments::transparent::iop::blake2s_trivial_iop::*;
        use crate::plonk::commitments::*;
        use crate::plonk::commitments::transparent::*;

        type Iop = TrivialBlake2sIOP<Fr>;
        type Fri = NaiveFriIop<Fr, Iop>;
        type Committer = StatelessTransparentCommitter<Fr, Fri, Blake2sTranscript<Fr>>;

        let meta = TransparentCommitterParameters {
            lde_factor: 16,
            num_queries: 2,
            output_coeffs_at_degree_plus_one: 1,
            fri_params: ()
        };

        let meta_large = TransparentCommitterParameters {
            lde_factor: 16,
            num_queries: 2,
            output_coeffs_at_degree_plus_one: 1,
            fri_params: ()
        };

        let circuit = InvalidTestCircuit::<Bn256> {
            _marker: PhantomData
        };

        let (setup, aux) = setup::<Bn256, Committer, _>(&circuit, meta.clone()).unwrap();

        println!("Proving");

        let proof = prove_nonhomomorphic::<Bn256, Committer, Blake2sTranscript::<Fr>, _>(&circuit, &setup, &aux, meta.clone(), meta_large.clone()).unwrap();

        println!("Verifying");

        let valid = verify_nonhomomorphic::<Bn256, Committer, Blake2sTranscript::<Fr>>(&setup, &proof, meta, meta_large).unwrap();

        assert!(!valid);
    }

    #[derive(Clone)]
    struct BenchmarkCircuit<E:Engine>{
        num_steps: usize,
        _marker: PhantomData<E>
    }

    impl<E: Engine> Circuit<E> for BenchmarkCircuit<E> {
        fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
            // yeah, fibonacci...

            let one = E::Fr::one();
            let mut negative_one = one;
            negative_one.negate();

            let mut two = one;
            two.double();
            
            let mut a = cs.alloc(|| {
                Ok(E::Fr::one())
            })?;

            let mut b = cs.alloc(|| {
                Ok(E::Fr::one())
            })?;

            cs.enforce_zero_2((a, CS::ONE), (one, negative_one))?;
            cs.enforce_zero_2((b, CS::ONE), (one, negative_one))?;

            let mut c = cs.alloc(|| {
                Ok(two)
            })?;

            cs.enforce_zero_3((a, b, c), (one, one, negative_one))?;

            let mut a_value = one;
            let mut b_value = one;
            let mut c_value = two;

            for _ in 0..self.num_steps {
                a = b;
                b = c;

                a_value = b_value;
                b_value = c_value;
                c_value.add_assign(&a_value);

                c = cs.alloc(|| {
                    Ok(c_value)
                })?;

                cs.enforce_zero_3((a, b, c), (one, one, negative_one))?;
            }

            Ok(())
        }
    }

    #[test]
    fn test_bench_fibonacci_circuit() {
        use crate::pairing::bn256::{Bn256, Fr};
        use crate::plonk::utils::*;
        use crate::plonk::commitments::transparent::fri::*;
        use crate::plonk::commitments::transparent::iop::*;
        use crate::plonk::commitments::transcript::*;
        use crate::plonk::commitments::transparent::fri::naive_fri::naive_fri::*;
        use crate::plonk::commitments::transparent::iop::blake2s_trivial_iop::*;
        use crate::plonk::commitments::*;
        use crate::plonk::commitments::transparent::*;
        use crate::plonk::tester::*;

        use std::time::Instant;

        type Iop = TrivialBlake2sIOP<Fr>;
        type Fri = NaiveFriIop<Fr, Iop>;
        type Committer = StatelessTransparentCommitter<Fr, Fri, Blake2sTranscript<Fr>>;

        let meta = TransparentCommitterParameters {
            lde_factor: 16,
            num_queries: 10,
            output_coeffs_at_degree_plus_one: 16,
            fri_params: ()
        };

        let meta_large = TransparentCommitterParameters {
            lde_factor: 16,
            num_queries: 10,
            output_coeffs_at_degree_plus_one: 16,
            fri_params: ()
        };

        let circuit = BenchmarkCircuit::<Bn256> {
            num_steps: 1_000_000,
            _marker: PhantomData
        };

        {
            let mut tester = TestingAssembly::<Bn256>::new();

            circuit.synthesize(&mut tester).expect("must synthesize");

            let satisfied = tester.is_satisfied();

            assert!(satisfied);

            println!("Circuit is satisfied");
        }

        println!("Start setup");
        let start = Instant::now();
        let (setup, aux) = setup::<Bn256, Committer, _>(&circuit, meta).unwrap();
        println!("Setup taken {:?}", start.elapsed());

        println!("Using circuit with N = {}", setup.n);

        let meta = TransparentCommitterParameters {
            lde_factor: 16,
            num_queries: 10,
            output_coeffs_at_degree_plus_one: 16,
            fri_params: ()
        };

        println!("Start proving");
        let start = Instant::now();
        let proof = prove_nonhomomorphic::<Bn256, Committer, Blake2sTranscript::<Fr>, _>(&circuit, &setup, &aux, meta.clone(), meta_large.clone()).unwrap();
        println!("Proof taken {:?}", start.elapsed());

        println!("Start verifying");
        let start = Instant::now();
        let valid = verify_nonhomomorphic::<Bn256, Committer, Blake2sTranscript::<Fr>>(&setup, &proof, meta, meta_large).unwrap();
        println!("Verification with unnecessary precomputation taken {:?}", start.elapsed());

        assert!(valid);
    }

    #[test]
    fn test_bench_homomorphic_plonk() {
        use rand::{XorShiftRng, SeedableRng, Rand, Rng};
        use crate::pairing::bn256::Bn256;
        use num_cpus;
        use crate::pairing::ff::ScalarEngine;
        use crate::pairing::CurveProjective;
        use crate::multiexp::*;
        use crate::multicore::*;
        use crate::source::*;
        use std::sync::Arc;
        use futures::{Future};

        const SAMPLES: usize = 1 << 20;
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let v = (0..SAMPLES).map(|_| <Bn256 as ScalarEngine>::Fr::rand(rng).into_repr()).collect::<Vec<_>>();
        let g = (0..SAMPLES).map(|_| <Bn256 as Engine>::G1::rand(rng).into_affine()).collect::<Vec<_>>();

        println!("Done generating test points and scalars");

        let pool = Worker::new();
        let start = std::time::Instant::now();

        let _sparse = multiexp(
            &pool,
            (Arc::new(g), 0),
            FullDensity,
            Arc::new(v)
        ).wait().unwrap();

        let per_one_poly = start.elapsed().as_micros();
        // a, b, c, z_1, z_2, t, opening at z (of length t), opening at z*omega(of length a)
        let total_expected_plonk = per_one_poly * (5 + 1 + 3 + 3 + 1); 
        println!("{} ms for expected plonk with ~ {} gates", total_expected_plonk/1000u128, SAMPLES);
    }

    #[test]
    fn test_bench_transparent_engine() {
        use crate::plonk::transparent_engine::proth_engine::*;
        use crate::plonk::utils::*;
        use crate::plonk::commitments::transparent::fri::*;
        use crate::plonk::commitments::transparent::iop::*;
        use crate::plonk::commitments::transcript::*;
        use crate::plonk::commitments::transparent::fri::naive_fri::naive_fri::*;
        use crate::plonk::commitments::transparent::iop::blake2s_trivial_iop::*;
        use crate::plonk::commitments::*;
        use crate::plonk::commitments::transparent::*;
        use crate::plonk::tester::*;

        use std::time::Instant;

        type Iop = TrivialBlake2sIOP<Fr>;
        type Fri = NaiveFriIop<Fr, Iop>;
        type Committer = StatelessTransparentCommitter<Fr, Fri, Blake2sTranscript<Fr>>;

        let mut negative_one = Fr::one();
        negative_one.negate();
        println!("-1 = {}", negative_one);

        let meta = TransparentCommitterParameters {
            lde_factor: 16,
            num_queries: 10,
            output_coeffs_at_degree_plus_one: 16,
            fri_params: ()
        };

        let meta_large = TransparentCommitterParameters {
            lde_factor: 16,
            num_queries: 10,
            output_coeffs_at_degree_plus_one: 16,
            fri_params: ()
        };

        let circuit = BenchmarkCircuit::<Transparent252> {
            num_steps: 1_000_000,
            _marker: PhantomData
        };

        {
            let mut tester = TestingAssembly::<Transparent252>::new();

            circuit.synthesize(&mut tester).expect("must synthesize");

            let satisfied = tester.is_satisfied();

            assert!(satisfied);

            println!("Circuit is satisfied");
        }

        println!("Start setup");
        let start = Instant::now();
        let (setup, aux) = setup::<Transparent252, Committer, _>(&circuit, meta).unwrap();
        println!("Setup taken {:?}", start.elapsed());

        println!("Using circuit with N = {}", setup.n);

        let meta = TransparentCommitterParameters {
            lde_factor: 16,
            num_queries: 10,
            output_coeffs_at_degree_plus_one: 16,
            fri_params: ()
        };

        println!("Start proving");
        let start = Instant::now();
        let proof = prove_nonhomomorphic::<Transparent252, Committer, Blake2sTranscript::<Fr>, _>(&circuit, &setup, &aux, meta.clone(), meta_large.clone()).unwrap();
        println!("Proof taken {:?}", start.elapsed());

        println!("Start verifying");
        let start = Instant::now();
        let valid = verify_nonhomomorphic::<Transparent252, Committer, Blake2sTranscript::<Fr>>(&setup, &proof, meta, meta_large).unwrap();
        println!("Verification with unnecessary precomputation taken {:?}", start.elapsed());

        assert!(valid);
    }

    #[test]
    fn test_bench_chunked_proof_on_transparent_engine() {
        use crate::plonk::transparent_engine::proth_engine::*;
        use crate::plonk::utils::*;
        use crate::plonk::commitments::transparent::fri::*;
        use crate::plonk::commitments::transparent::iop::*;
        use crate::plonk::commitments::transcript::*;
        use crate::plonk::commitments::transparent::fri::naive_fri::naive_fri::*;
        use crate::plonk::commitments::transparent::iop::blake2s_trivial_iop::*;
        use crate::plonk::commitments::*;
        use crate::plonk::commitments::transparent::*;
        use crate::plonk::tester::*;

        use std::time::Instant;

        type Iop = TrivialBlake2sIOP<Fr>;
        type Fri = NaiveFriIop<Fr, Iop>;
        type Committer = StatelessTransparentCommitter<Fr, Fri, Blake2sTranscript<Fr>>;

        let mut negative_one = Fr::one();
        negative_one.negate();
        println!("-1 = {}", negative_one);

        let meta = TransparentCommitterParameters {
            lde_factor: 16,
            num_queries: 10,
            output_coeffs_at_degree_plus_one: 16,
            fri_params: ()
        };

        let circuit = BenchmarkCircuit::<Transparent252> {
            num_steps: 1_000_000,
            _marker: PhantomData
        };

        {
            let mut tester = TestingAssembly::<Transparent252>::new();

            circuit.synthesize(&mut tester).expect("must synthesize");

            let satisfied = tester.is_satisfied();

            assert!(satisfied);

            println!("Circuit is satisfied");
        }

        println!("Start setup");
        let start = Instant::now();
        let (setup, aux) = setup::<Transparent252, Committer, _>(&circuit, meta.clone()).unwrap();
        println!("Setup taken {:?}", start.elapsed());

        println!("Using circuit with N = {}", setup.n);

        println!("Start proving");
        let start = Instant::now();
        let proof = prove_nonhomomorphic_chunked::<Transparent252, Committer, Blake2sTranscript::<Fr>, _>(&circuit, &aux, meta.clone()).unwrap();
        println!("Proof taken {:?}", start.elapsed());

        println!("Start verifying");
        let start = Instant::now();
        let valid = verify_nonhomomorphic_chunked::<Transparent252, Committer, Blake2sTranscript::<Fr>>(&setup, &proof, meta).unwrap();
        println!("Verification with unnecessary precomputation taken {:?}", start.elapsed());

        assert!(valid);
    }

    #[test]
    fn test_poly_eval_correctness() {
        use rand::{XorShiftRng, SeedableRng, Rand, Rng};
        use crate::pairing::bn256::Fr;
        use num_cpus;
        use crate::pairing::ff::ScalarEngine;
        use crate::pairing::CurveProjective;
        use crate::multiexp::*;
        use crate::multicore::*;
        use crate::source::*;
        use std::sync::Arc;
        use futures::{Future};

        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let poly_sizes = vec![1, 10, 100, 1000, 10_000, 1_000_000];

        let x: Fr = rng.gen();

        let worker = Worker::new();

        for poly_size in poly_sizes.into_iter() {
            let coeffs = (0..poly_size).map(|_| Fr::rand(rng)).collect::<Vec<_>>();
            let mut point = Fr::one();
            let mut result = Fr::zero();
            for c in coeffs.iter() {
                let mut tmp = point;
                tmp.mul_assign(&c);
                result.add_assign(&tmp);

                point.mul_assign(&x);
            }

            let poly = Polynomial::<Fr, _>::from_coeffs(coeffs).unwrap();
            let eval_result = poly.evaluate_at(&worker, x);
            assert!(eval_result == result, "failed for size {}", poly_size);
        }
    }

    #[test]
    fn test_poly_grand_product_correctness() {
        use rand::{XorShiftRng, SeedableRng, Rand, Rng};
        use crate::pairing::bn256::Fr;
        use num_cpus;
        use crate::pairing::ff::ScalarEngine;
        use crate::pairing::CurveProjective;
        use crate::multiexp::*;
        use crate::multicore::*;
        use crate::source::*;
        use std::sync::Arc;
        use futures::{Future};

        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let poly_sizes = vec![1, 10, 100, 1000, 10_000, 1_000_000];

        let worker = Worker::new();

        for poly_size in poly_sizes.into_iter() {
            let coeffs = (0..poly_size).map(|_| Fr::rand(rng)).filter(|el| !el.is_zero()).collect::<Vec<_>>();
            let poly = Polynomial::<Fr, _>::from_values_unpadded(coeffs).unwrap();
            let palallel_result = poly.calculate_grand_product(&worker).unwrap();
            let serial_result = poly.calculate_grand_product_serial().unwrap();

            if palallel_result != serial_result {
                for (i, (c0, c1)) in palallel_result.as_ref().iter()
                                .zip(serial_result.as_ref().iter())
                                .enumerate() 
                {
                    assert!(c0 == c1, "failed at value number {} for size {}", i, poly_size);
                }
            }
        }
    }

    #[test]
    fn test_bench_lde() {
        use rand::{XorShiftRng, SeedableRng, Rand, Rng};
        use crate::pairing::bn256::Fr;
        use crate::pairing::ff::ScalarEngine;
        use crate::pairing::CurveProjective;
        use std::time::Instant;
        use crate::multicore::*;
        use crate::plonk::commitments::transparent::utils::*;

        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let poly_sizes = vec![1, 10, 100, 1000, 10_000, 1_000_000, 2_000_000];

        let worker = Worker::new();

        for poly_size in poly_sizes.into_iter() {
            let coeffs = (0..poly_size).map(|_| Fr::rand(rng)).collect::<Vec<_>>();
        
            let poly = Polynomial::<Fr, _>::from_coeffs(coeffs).unwrap();
            let start = Instant::now();
            let _eval_result = poly.lde(&worker, 16);
            println!("LDE with factor 16 for size {} taken {:?}", poly_size, start.elapsed());

            let coeffs = (0..(16*poly_size)).map(|_| Fr::rand(rng)).collect::<Vec<_>>();
        
            let poly = Polynomial::<Fr, _>::from_coeffs(coeffs).unwrap();
            let start = Instant::now();
            let eval_result = poly.clone().fft(&worker);
            println!("FFT of the same size taken {:?}", start.elapsed());

            if log2_floor(poly.size()) % 2 == 0 {
                let log_n = log2_floor(poly.size());
                let omega = poly.omega;
                let mut coeffs = poly.into_coeffs();
                let start = Instant::now();
                crate::plonk::fft::radix_4::best_fft(&mut coeffs, &worker, &omega, log_n as u32);
                println!("Radix-4 FFT of the same size taken {:?}", start.elapsed());
                let to_compare = eval_result.into_coeffs();
                assert!(to_compare == coeffs);
            }


        }
    }
}