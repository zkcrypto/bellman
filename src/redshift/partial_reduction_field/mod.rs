
#[macro_use]
use crate::ff::*;

use crate::pairing::Engine;

#[macro_use]
mod impl_macro;

#[derive(PrimeField)]
#[PrimeFieldModulus = "3618502788666131213697322783095070105623107215331596699973092056135872020481"]
#[PrimeFieldGenerator = "3"]
pub struct Fr(FrRepr);

pub trait TransparentEngine: Engine {}

pub trait PartialReductionField: PrimeField {
    /// Adds another element by this element without reduction.
    fn add_assign_unreduced(&mut self, other: &Self);

    /// Subtracts another element by this element without reduction.
    fn sub_assign_unreduced(&mut self, other: &Self);

    /// Multiplies another element by this element without reduction.
    fn mul_assign_unreduced(&mut self, other: &Self);

    /// Reduces this element.
    fn reduce_once(&mut self);

    /// Reduces this element by max of three moduluses.
    fn reduce_completely(&mut self);

    fn overflow_factor(&self) -> usize;
}

pub trait PartialTwoBitReductionField: PartialReductionField {
    /// Subtracts another element by this element without reduction.
    fn sub_assign_twice_unreduced(&mut self, other: &Self);

    /// Reduces this element by two moduluses.
    fn reduce_twice(&mut self);

    /// Reduces this element by max of three moduluses.
    fn reduce_completely(&mut self);
}

pub mod engine {
    use super::Fr;

    #[macro_use]
    use super::impl_macro::*;

    transparent_engine_impl!{Transparent252, Fr}
}

pub use self::engine::Transparent252;

pub(crate) mod proth;
pub(crate) mod proth_engine;
pub mod precomputations;

#[cfg(test)]
mod test {
    #[test]
    fn test_bench_proth_lde() {
        use rand::{XorShiftRng, SeedableRng, Rand, Rng};
        use super::Fr as FrMontNaive;
        use super::proth::Fr as FrOptimized;
        use crate::redshift::polynomials::*;
        use std::time::Instant;
        use crate::multicore::*;

        let poly_sizes = vec![1_000_000, 2_000_000, 4_000_000];

        let worker = Worker::new();

        for poly_size in poly_sizes.into_iter() {
            let res1 = {
                let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
                let coeffs = (0..poly_size).map(|_| FrMontNaive::rand(rng)).collect::<Vec<_>>();
            
                let poly = Polynomial::<FrMontNaive, _>::from_coeffs(coeffs).unwrap();
                let start = Instant::now();
                let eval_result = poly.lde(&worker, 16).unwrap();
                println!("LDE with factor 16 for size {} with naive mont reduction taken {:?}", poly_size, start.elapsed());

                eval_result.into_coeffs()
            };

            let res2 = {
                let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
                let coeffs = (0..poly_size).map(|_| FrOptimized::rand(rng)).collect::<Vec<_>>();
            
                let poly = Polynomial::<FrOptimized, _>::from_coeffs(coeffs).unwrap();
                let start = Instant::now();
                let eval_result = poly.lde(&worker, 16).unwrap();
                println!("LDE with factor 16 for size {} with optimized mont reduction taken {:?}", poly_size, start.elapsed());

                eval_result.into_coeffs()
            };

            assert_eq!(format!("{}", res1[0]), format!("{}", res2[0]));

        }
    }

    #[test]
    fn test_proth_field() {
        use crate::ff::{Field, PrimeField};
        use super::Fr as FrMontNaive;
        use super::proth::Fr as FrOptimized;

        let one_naive = FrMontNaive::from_str("1").unwrap();
        let one_optimized = FrOptimized::from_str("1").unwrap();

        println!("{}", FrMontNaive::one());
        println!("{}", FrOptimized::one());

        println!("{}", one_naive.into_raw_repr());
        println!("{}", one_optimized.into_raw_repr());

        let mut tmp0 = one_naive;
        tmp0.mul_assign(&one_naive);

        let mut tmp1 = one_optimized;
        tmp1.mul_assign(&one_optimized);

        assert_eq!(tmp0.to_hex(), tmp1.to_hex());

        assert_eq!(FrMontNaive::multiplicative_generator().to_hex(), FrOptimized::multiplicative_generator().to_hex());
    }

    #[test]
    fn test_bench_precomputations_for_proth_fft() {
        use rand::{XorShiftRng, SeedableRng, Rand, Rng};
        use super::Fr as FrMontNaive;
        use super::proth::Fr as FrOptimized;
        use crate::redshift::polynomials::*;
        use std::time::Instant;
        use crate::multicore::*;
        use crate::redshift::fft::fft::best_fft;
        use crate::redshift::fft::with_precomputation::FftPrecomputations;
        use crate::redshift::fft::with_precomputation::fft::best_fft as best_fft_with_precomputations;
        use crate::redshift::domains::Domain;
        use super::precomputations::PrecomputedOmegas;
        
        let poly_sizes = vec![32_000_000, 64_000_000];

        let worker = Worker::new();

        for poly_size in poly_sizes.into_iter() {
            let domain = Domain::<FrOptimized>::new_for_size(poly_size).unwrap();
            let precomp = PrecomputedOmegas::<FrOptimized>::new_for_domain_size(domain.size as usize);
            let omega = domain.generator;
            let log_n = domain.power_of_two as u32;

            let poly_size = domain.size as usize;

            let res1 = {
                let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
                let mut coeffs = (0..poly_size).map(|_| FrOptimized::rand(rng)).collect::<Vec<_>>();
                let start = Instant::now();
                best_fft(&mut coeffs, &worker, &omega, log_n, None);
                println!("FFT for size {} without precomputation taken {:?}", poly_size, start.elapsed());

                coeffs
            };

            let res2 = {
                let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
                let mut coeffs = (0..poly_size).map(|_| FrOptimized::rand(rng)).collect::<Vec<_>>();
                let start = Instant::now();
                best_fft_with_precomputations(&mut coeffs, &worker, &omega, log_n, None, &precomp);
                println!("FFT for size {} with precomputation taken {:?}", poly_size, start.elapsed());

                coeffs
            };

            assert!(res1 == res2);

        }
    }

    #[test]
    fn test_bench_precomputations_for_proth_lde() {
        use rand::{XorShiftRng, SeedableRng, Rand, Rng};
        use super::Fr as FrMontNaive;
        use super::proth::Fr as FrOptimized;
        use crate::redshift::polynomials::*;
        use std::time::Instant;
        use crate::multicore::*;
        use crate::redshift::fft::with_precomputation::FftPrecomputations;
        use super::precomputations::PrecomputedOmegas;

        let poly_sizes = vec![1_000_000, 2_000_000, 4_000_000];

        let worker = Worker::new();

        for poly_size in poly_sizes.into_iter() {
            let res1 = {
                let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
                let coeffs = (0..poly_size).map(|_| FrMontNaive::rand(rng)).collect::<Vec<_>>();
            
                let poly = Polynomial::<FrMontNaive, _>::from_coeffs(coeffs).unwrap();
                let start = Instant::now();
                let eval_result = poly.lde(&worker, 16).unwrap();
                println!("LDE with factor 16 for size {} with naive mont reduction taken {:?}", poly_size, start.elapsed());

                eval_result.into_coeffs()
            };

            let res2 = {
                let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
                let coeffs = (0..poly_size).map(|_| FrOptimized::rand(rng)).collect::<Vec<_>>();
            
                let poly = Polynomial::<FrOptimized, _>::from_coeffs(coeffs).unwrap();
                let precomp = PrecomputedOmegas::<FrOptimized>::new_for_domain_size(poly.size());
                let start = Instant::now();
                let eval_result = poly.lde_using_multiple_cosets_with_precomputation(&worker, 16, &precomp).unwrap();
                println!("LDE with factor 16 for size {} with optimized mont reduction and precomputation taken {:?}", poly_size, start.elapsed());

                eval_result.into_coeffs()
            };

            assert_eq!(format!("{}", res1[0]), format!("{}", res2[0]));

        }
    }

    #[test]
    fn test_bench_ct_ploth_lde() {
        use rand::{XorShiftRng, SeedableRng, Rand, Rng};
        use super::proth::Fr as Fr;
        use crate::redshift::polynomials::*;
        use std::time::Instant;
        use crate::multicore::*;
        use crate::redshift::fft::cooley_tukey_ntt::{CTPrecomputations, BitReversedOmegas};

        let poly_sizes = vec![1_000_000, 2_000_000, 4_000_000];

        // let poly_sizes = vec![2];

        let worker = Worker::new();

        for poly_size in poly_sizes.into_iter() {
            let poly_size = poly_size as usize;

            let res1 = {
                let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
                let coeffs = (0..poly_size).map(|_| Fr::rand(rng)).collect::<Vec<_>>();
            
                let poly = Polynomial::<Fr, _>::from_coeffs(coeffs).unwrap();
                let start = Instant::now();
                let eval_result = poly.lde_using_multiple_cosets(&worker, 16).unwrap();
                println!("LDE with factor 16 for size {} taken {:?}", poly_size, start.elapsed());

                eval_result.into_coeffs()
            };

            let res2 = {
                let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
                let coeffs = (0..poly_size).map(|_| Fr::rand(rng)).collect::<Vec<_>>();
            
                let poly = Polynomial::<Fr, _>::from_coeffs(coeffs).unwrap();
                let precomp = BitReversedOmegas::<Fr>::new_for_domain_size(poly.size());
                let start = Instant::now();
                let eval_result = poly.lde_using_bitreversed_ntt(&worker, 16, &precomp).unwrap();
                println!("LDE with factor 16 for size {} with optimized ntt taken {:?}", poly_size, start.elapsed());

                eval_result.into_coeffs()
            };

            assert_eq!(res1, res2);

            assert!(res1 == res2);
        }
    }

    #[test]
    fn test_bench_partial_reduction_bitreversed_lde() {
        use crate::ff::Field;
        use crate::ff::PrimeField;
        use rand::{XorShiftRng, SeedableRng, Rand, Rng};
        use super::proth::Fr as Fr;
        use super::PartialTwoBitReductionField;
        use crate::redshift::polynomials::*;
        use std::time::Instant;
        use crate::multicore::*;
        use crate::redshift::fft::cooley_tukey_ntt::{CTPrecomputations, BitReversedOmegas};

        let poly_sizes = vec![32, 64, 1_000_000, 2_000_000, 4_000_000];

        let worker = Worker::new();

        for poly_size in poly_sizes.into_iter() {
            let poly_size = poly_size as usize;

            let res1 = {
                let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
                let coeffs = (0..poly_size).map(|_| Fr::rand(rng)).collect::<Vec<_>>();
            
                let poly = Polynomial::<Fr, _>::from_coeffs(coeffs).unwrap();
                let start = Instant::now();
                let eval_result = poly.lde(&worker, 16).unwrap();
                println!("LDE with factor 16 for size {} taken {:?}", poly_size, start.elapsed());

                eval_result.into_coeffs()
            };

            let mut res2 = {
                let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
                let coeffs = (0..poly_size).map(|_| Fr::rand(rng)).collect::<Vec<_>>();
            
                let poly = Polynomial::<Fr, _>::from_coeffs(coeffs).unwrap();
                let precomp = BitReversedOmegas::<Fr>::new_for_domain_size(poly.size());
                let start = Instant::now();
                let eval_result = poly.bitreversed_lde_using_bitreversed_ntt(&worker, 16, &precomp, &<Fr as Field>::one()).unwrap();
                println!("LDE with factor 16 for size {} bitreversed {:?}", poly_size, start.elapsed());

                eval_result
            };

            if poly_size < 1000 {
                res2.bitreverse_enumeration(&worker);
                assert!(res1 == res2.into_coeffs());
            }
        }
    }

    
}




