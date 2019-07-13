use crate::pairing::{
    CurveAffine,
    CurveProjective,
    Engine
};

use crate::pairing::ff::{
    PrimeField,
    Field,
    PrimeFieldRepr,
    ScalarEngine};

use std::sync::Arc;
use super::source::*;
use futures::{Future};
use super::worker::Worker;

use super::SynthesisError;

use cfg_if;

/// This genious piece of code works in the following way:
/// - choose `c` - the bit length of the region that one thread works on
/// - make `2^c - 1` buckets and initialize them with `G = infinity` (that's equivalent of zero)
/// - there is no bucket for "zero" cause it's not necessary
/// - go over the pairs `(base, scalar)`
/// - for each scalar calculate `scalar % 2^c` and add the base (without any multiplications!) to the 
/// corresponding bucket
/// - at the end each bucket will have an accumulated value that should be multiplied by the corresponding factor
/// between `1` and `2^c - 1` to get the right value
/// - here comes the first trick - you don't need to do multiplications at all, just add all the buckets together
/// starting from the first one `(a + b + c + ...)` and than add to the first sum another sum of the form
/// `(b + c + d + ...)`, and than the third one `(c + d + ...)`, that will result in the proper prefactor infront of every
/// accumulator, without any multiplication operations at all
/// - that's of course not enough, so spawn the next thread
/// - this thread works with the same bit width `c`, but SKIPS lowers bits completely, so it actually takes values
/// in the form `(scalar >> c) % 2^c`, so works on the next region
/// - spawn more threads until you exhaust all the bit length
/// - you will get roughly `[bitlength / c] + 1` inaccumulators
/// - double the highest accumulator enough times, add to the next one, double the result, add the next accumulator, continue
/// 
/// Demo why it works:
/// ```
///     a * G + b * H = (a_2 * (2^c)^2 + a_1 * (2^c)^1 + a_0) * G + (b_2 * (2^c)^2 + b_1 * (2^c)^1 + b_0) * H
/// ```
/// - make buckets over `0` labeled coefficients
/// - make buckets over `1` labeled coefficients
/// - make buckets over `2` labeled coefficients
/// - accumulators over each set of buckets will have an implicit factor of `(2^c)^i`, so before summing thme up
/// "higher" accumulators must be doubled `c` times
///
#[cfg(not(feature = "nightly"))]
fn multiexp_inner<Q, D, G, S>(
    pool: &Worker,
    bases: S,
    density_map: D,
    exponents: Arc<Vec<<G::Scalar as PrimeField>::Repr>>,
    // exponents: Arc<Vec<<<G::Engine as Engine>::Fr as PrimeField>::Repr>>,
    mut skip: u32,
    c: u32,
    handle_trivial: bool
) -> Box<dyn Future<Item=<G as CurveAffine>::Projective, Error=SynthesisError>>
    where for<'a> &'a Q: QueryDensity,
          D: Send + Sync + 'static + Clone + AsRef<Q>,
          G: CurveAffine,
          S: SourceBuilder<G>
{
    // Perform this region of the multiexp
    let this = {
        let bases = bases.clone();
        let exponents = exponents.clone();
        let density_map = density_map.clone();

        // This is a Pippenger’s algorithm
        pool.compute(move || {
            // Accumulate the result
            let mut acc = G::Projective::zero();

            // Build a source for the bases
            let mut bases = bases.new();

            // Create buckets to place remainders s mod 2^c,
            // it will be 2^c - 1 buckets (no bucket for zeroes)

            // Create space for the buckets
            let mut buckets = vec![<G as CurveAffine>::Projective::zero(); (1 << c) - 1];

            let zero = <G::Engine as ScalarEngine>::Fr::zero().into_repr();
            let one = <G::Engine as ScalarEngine>::Fr::one().into_repr();

            // Sort the bases into buckets
            for (&exp, density) in exponents.iter().zip(density_map.as_ref().iter()) {
                // Go over density and exponents
                if density {
                    if exp == zero {
                        bases.skip(1)?;
                    } else if exp == one {
                        if handle_trivial {
                            bases.add_assign_mixed(&mut acc)?;
                        } else {
                            bases.skip(1)?;
                        }
                    } else {
                        // Place multiplication into the bucket: Separate s * P as 
                        // (s/2^c) * P + (s mod 2^c) P
                        // First multiplication is c bits less, so one can do it,
                        // sum results from different buckets and double it c times,
                        // then add with (s mod 2^c) P parts
                        let mut exp = exp;
                        exp.shr(skip);
                        let exp = exp.as_ref()[0] % (1 << c);

                        if exp != 0 {
                            bases.add_assign_mixed(&mut buckets[(exp - 1) as usize])?;
                        } else {
                            bases.skip(1)?;
                        }
                    }
                }
            }

            // Summation by parts
            // e.g. 3a + 2b + 1c = a +
            //                    (a) + b +
            //                    ((a) + b) + c
            let mut running_sum = G::Projective::zero();
            for exp in buckets.into_iter().rev() {
                running_sum.add_assign(&exp);
                acc.add_assign(&running_sum);
            }

            Ok(acc)
        })
    };

    skip += c;

    if skip >= <G::Engine as ScalarEngine>::Fr::NUM_BITS {
        // There isn't another region.
        Box::new(this)
    } else {
        // There's another region more significant. Calculate and join it with
        // this region recursively.
        Box::new(
            this.join(multiexp_inner(pool, bases, density_map, exponents, skip, c, false))
                .map(move |(this, mut higher)| {
                    for _ in 0..c {
                        higher.double();
                    }

                    higher.add_assign(&this);

                    higher
                })
        )
    }
}


cfg_if! {
    if #[cfg(feature = "nightly")] {
        #[inline(always)]
        fn multiexp_inner_impl<Q, D, G, S>(
            pool: &Worker,
            bases: S,
            density_map: D,
            exponents: Arc<Vec<<G::Scalar as PrimeField>::Repr>>,
            skip: u32,
            c: u32,
            handle_trivial: bool
        ) -> Box<dyn Future<Item=<G as CurveAffine>::Projective, Error=SynthesisError>>
            where for<'a> &'a Q: QueryDensity,
                D: Send + Sync + 'static + Clone + AsRef<Q>,
                G: CurveAffine,
                S: SourceBuilder<G>
        {
            multiexp_inner_with_prefetch(pool, bases, density_map, exponents, skip, c, handle_trivial)
        }
    } else {
        #[inline(always)]
        fn multiexp_inner_impl<Q, D, G, S>(
            pool: &Worker,
            bases: S,
            density_map: D,
            exponents: Arc<Vec<<G::Scalar as PrimeField>::Repr>>,
            skip: u32,
            c: u32,
            handle_trivial: bool
        ) -> Box<dyn Future<Item=<G as CurveAffine>::Projective, Error=SynthesisError>>
            where for<'a> &'a Q: QueryDensity,
                D: Send + Sync + 'static + Clone + AsRef<Q>,
                G: CurveAffine,
                S: SourceBuilder<G>
        {
            multiexp_inner(pool, bases, density_map, exponents, skip, c, handle_trivial)
        }
    }  
}



#[cfg(feature = "nightly")]
extern crate prefetch;

#[cfg(feature = "nightly")]
fn multiexp_inner_with_prefetch<Q, D, G, S>(
    pool: &Worker,
    bases: S,
    density_map: D,
    exponents: Arc<Vec<<G::Scalar as PrimeField>::Repr>>,
    mut skip: u32,
    c: u32,
    handle_trivial: bool
) -> Box<dyn Future<Item=<G as CurveAffine>::Projective, Error=SynthesisError>>
    where for<'a> &'a Q: QueryDensity,
          D: Send + Sync + 'static + Clone + AsRef<Q>,
          G: CurveAffine,
          S: SourceBuilder<G>
{
    use prefetch::prefetch::*;
    // Perform this region of the multiexp
    let this = {
        let bases = bases.clone();
        let exponents = exponents.clone();
        let density_map = density_map.clone();

        // This is a Pippenger’s algorithm
        pool.compute(move || {
            // Accumulate the result
            let mut acc = G::Projective::zero();

            // Build a source for the bases
            let mut bases = bases.new();

            // Create buckets to place remainders s mod 2^c,
            // it will be 2^c - 1 buckets (no bucket for zeroes)

            // Create space for the buckets
            let mut buckets = vec![<G as CurveAffine>::Projective::zero(); (1 << c) - 1];

            let zero = <G::Engine as ScalarEngine>::Fr::zero().into_repr();
            let one = <G::Engine as ScalarEngine>::Fr::one().into_repr();
            let padding = Arc::new(vec![zero]);

            let mask = 1 << c;

            // Sort the bases into buckets
            for ((&exp, &next_exp), density) in exponents.iter()
                        .zip(exponents.iter().skip(1).chain(padding.iter()))
                        .zip(density_map.as_ref().iter()) {
                // no matter what happens - prefetch next bucket
                if next_exp != zero && next_exp != one {
                    let mut next_exp = next_exp;
                    next_exp.shr(skip);
                    let next_exp = next_exp.as_ref()[0] % mask;
                    if next_exp != 0 {
                        let p: *const <G as CurveAffine>::Projective = &buckets[(next_exp - 1) as usize];
                        prefetch::<Write, High, Data, _>(p);
                    }
                    
                }
                // Go over density and exponents
                if density {
                    if exp == zero {
                        bases.skip(1)?;
                    } else if exp == one {
                        if handle_trivial {
                            bases.add_assign_mixed(&mut acc)?;
                        } else {
                            bases.skip(1)?;
                        }
                    } else {
                        // Place multiplication into the bucket: Separate s * P as 
                        // (s/2^c) * P + (s mod 2^c) P
                        // First multiplication is c bits less, so one can do it,
                        // sum results from different buckets and double it c times,
                        // then add with (s mod 2^c) P parts
                        let mut exp = exp;
                        exp.shr(skip);
                        let exp = exp.as_ref()[0] % mask;

                        if exp != 0 {
                            bases.add_assign_mixed(&mut buckets[(exp - 1) as usize])?;
                        } else {
                            bases.skip(1)?;
                        }
                    }
                }
            }

            // Summation by parts
            // e.g. 3a + 2b + 1c = a +
            //                    (a) + b +
            //                    ((a) + b) + c
            let mut running_sum = G::Projective::zero();
            for exp in buckets.into_iter().rev() {
                running_sum.add_assign(&exp);
                acc.add_assign(&running_sum);
            }

            Ok(acc)
        })
    };

    skip += c;

    if skip >= <G::Engine as ScalarEngine>::Fr::NUM_BITS {
        // There isn't another region.
        Box::new(this)
    } else {
        // There's another region more significant. Calculate and join it with
        // this region recursively.
        Box::new(
            this.join(multiexp_inner_with_prefetch(pool, bases, density_map, exponents, skip, c, false))
                .map(move |(this, mut higher)| {
                    for _ in 0..c {
                        higher.double();
                    }

                    higher.add_assign(&this);

                    higher
                })
        )
    }
}

/// Perform multi-exponentiation. The caller is responsible for ensuring the
/// query size is the same as the number of exponents.
pub fn multiexp<Q, D, G, S>(
    pool: &Worker,
    bases: S,
    density_map: D,
    exponents: Arc<Vec<<<G::Engine as ScalarEngine>::Fr as PrimeField>::Repr>>
) -> Box<dyn Future<Item=<G as CurveAffine>::Projective, Error=SynthesisError>>
    where for<'a> &'a Q: QueryDensity,
          D: Send + Sync + 'static + Clone + AsRef<Q>,
          G: CurveAffine,
          S: SourceBuilder<G>
{
    let c = if exponents.len() < 32 {
        3u32
    } else {
        (f64::from(exponents.len() as u32)).ln().ceil() as u32
    };

    if let Some(query_size) = density_map.as_ref().get_query_size() {
        // If the density map has a known query size, it should not be
        // inconsistent with the number of exponents.

        assert!(query_size == exponents.len());
    }

    multiexp_inner_impl(pool, bases, density_map, exponents, 0, c, true)
}


/// Perform multi-exponentiation. The caller is responsible for ensuring that
/// the number of bases is the same as the number of exponents.
#[allow(dead_code)]
pub fn dense_multiexp<G: CurveAffine>(
    pool: &Worker,
    bases: & [G],
    exponents: & [<<G::Engine as ScalarEngine>::Fr as PrimeField>::Repr]
) -> Result<<G as CurveAffine>::Projective, SynthesisError>
{
    if exponents.len() != bases.len() {
        return Err(SynthesisError::AssignmentMissing);
    }
    let c = if exponents.len() < 32 {
        3u32
    } else {
        (f64::from(exponents.len() as u32)).ln().ceil() as u32
    };

    dense_multiexp_inner(pool, bases, exponents, 0, c, true)
}

fn dense_multiexp_inner<G: CurveAffine>(
    pool: &Worker,
    bases: & [G],
    exponents: & [<<G::Engine as ScalarEngine>::Fr as PrimeField>::Repr],
    mut skip: u32,
    c: u32,
    handle_trivial: bool
) -> Result<<G as CurveAffine>::Projective, SynthesisError>
{   
    use std::sync::{Mutex};
    // Perform this region of the multiexp. We use a different strategy - go over region in parallel,
    // then over another region, etc. No Arc required
    let this = {
        // let mask = (1u64 << c) - 1u64;
        let this_region = Mutex::new(<G as CurveAffine>::Projective::zero());
        let arc = Arc::new(this_region);
        pool.scope(bases.len(), |scope, chunk| {
            for (base, exp) in bases.chunks(chunk).zip(exponents.chunks(chunk)) {
                let this_region_rwlock = arc.clone();
                // let handle = 
                scope.spawn(move |_| {
                    let mut buckets = vec![<G as CurveAffine>::Projective::zero(); (1 << c) - 1];
                    // Accumulate the result
                    let mut acc = G::Projective::zero();
                    let zero = <G::Engine as ScalarEngine>::Fr::zero().into_repr();
                    let one = <G::Engine as ScalarEngine>::Fr::one().into_repr();

                    for (base, &exp) in base.iter().zip(exp.iter()) {
                        // let index = (exp.as_ref()[0] & mask) as usize;

                        // if index != 0 {
                        //     buckets[index - 1].add_assign_mixed(base);
                        // }

                        // exp.shr(c as u32);

                        if exp != zero {
                            if exp == one {
                                if handle_trivial {
                                    acc.add_assign_mixed(base);
                                }
                            } else {
                                let mut exp = exp;
                                exp.shr(skip);
                                let exp = exp.as_ref()[0] % (1 << c);
                                if exp != 0 {
                                    buckets[(exp - 1) as usize].add_assign_mixed(base);
                                }
                            }
                        }
                    }

                    // buckets are filled with the corresponding accumulated value, now sum
                    let mut running_sum = G::Projective::zero();
                    for exp in buckets.into_iter().rev() {
                        running_sum.add_assign(&exp);
                        acc.add_assign(&running_sum);
                    }

                    let mut guard = match this_region_rwlock.lock() {
                        Ok(guard) => guard,
                        Err(_) => {
                            panic!("poisoned!"); 
                            // poisoned.into_inner()
                        }
                    };

                    (*guard).add_assign(&acc);
                });
        
            }
        });

        let this_region = Arc::try_unwrap(arc).unwrap();
        let this_region = this_region.into_inner().unwrap();

        this_region
    };

    skip += c;

    if skip >= <G::Engine as ScalarEngine>::Fr::NUM_BITS {
        // There isn't another region, and this will be the highest region
        return Ok(this);
    } else {
        // next region is actually higher than this one, so double it enough times
        let mut next_region = dense_multiexp_inner(
            pool, bases, exponents, skip, c, false).unwrap();
        for _ in 0..c {
            next_region.double();
        }

        next_region.add_assign(&this);

        return Ok(next_region);
    }
}



#[test]
fn test_with_bls12() {
    fn naive_multiexp<G: CurveAffine>(
        bases: Arc<Vec<G>>,
        exponents: Arc<Vec<<G::Scalar as PrimeField>::Repr>>
    ) -> G::Projective
    {
        assert_eq!(bases.len(), exponents.len());

        let mut acc = G::Projective::zero();

        for (base, exp) in bases.iter().zip(exponents.iter()) {
            acc.add_assign(&base.mul(*exp));
        }

        acc
    }

    use rand::{self, Rand};
    use crate::pairing::bls12_381::Bls12;

    const SAMPLES: usize = 1 << 14;

    let rng = &mut rand::thread_rng();
    let v = Arc::new((0..SAMPLES).map(|_| <Bls12 as ScalarEngine>::Fr::rand(rng).into_repr()).collect::<Vec<_>>());
    let g = Arc::new((0..SAMPLES).map(|_| <Bls12 as Engine>::G1::rand(rng).into_affine()).collect::<Vec<_>>());

    let naive = naive_multiexp(g.clone(), v.clone());

    let pool = Worker::new();

    let fast = multiexp(
        &pool,
        (g, 0),
        FullDensity,
        v
    ).wait().unwrap();

    assert_eq!(naive, fast);
}

#[test]
fn test_speed_with_bn256() {
    use rand::{self, Rand};
    use crate::pairing::bn256::Bn256;
    use num_cpus;

    let cpus = num_cpus::get();
    const SAMPLES: usize = 1 << 22;

    let rng = &mut rand::thread_rng();
    let v = Arc::new((0..SAMPLES).map(|_| <Bn256 as ScalarEngine>::Fr::rand(rng).into_repr()).collect::<Vec<_>>());
    let g = Arc::new((0..SAMPLES).map(|_| <Bn256 as Engine>::G1::rand(rng).into_affine()).collect::<Vec<_>>());

    let pool = Worker::new();

    let start = std::time::Instant::now();

    let _fast = multiexp(
        &pool,
        (g, 0),
        FullDensity,
        v
    ).wait().unwrap();


    let duration_ns = start.elapsed().as_nanos() as f64;
    println!("Elapsed {} ns for {} samples", duration_ns, SAMPLES);
    let time_per_sample = duration_ns/(SAMPLES as f64);
    println!("Tested on {} samples on {} CPUs with {} ns per multiplication", SAMPLES, cpus, time_per_sample);
}


#[test]
fn test_dense_multiexp() {
    use rand::{XorShiftRng, SeedableRng, Rand, Rng};
    use crate::pairing::bn256::Bn256;
    use num_cpus;

    // const SAMPLES: usize = 1 << 22;
    const SAMPLES: usize = 1 << 16;
    let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    let v = (0..SAMPLES).map(|_| <Bn256 as ScalarEngine>::Fr::rand(rng).into_repr()).collect::<Vec<_>>();
    let g = (0..SAMPLES).map(|_| <Bn256 as Engine>::G1::rand(rng).into_affine()).collect::<Vec<_>>();

    println!("Done generating test points and scalars");

    let pool = Worker::new();

    let start = std::time::Instant::now();

    let dense = dense_multiexp(
        &pool, &g, &v.clone()).unwrap();

    let duration_ns = start.elapsed().as_nanos() as f64;
    println!("{} ns for dense for {} samples", duration_ns, SAMPLES);

    let start = std::time::Instant::now();

    let sparse = multiexp(
        &pool,
        (Arc::new(g), 0),
        FullDensity,
        Arc::new(v)
    ).wait().unwrap();

    let duration_ns = start.elapsed().as_nanos() as f64;
    println!("{} ns for sparse for {} samples", duration_ns, SAMPLES);

    assert_eq!(dense, sparse);
}


#[test]
fn test_bench_sparse_multiexp() {
    use rand::{XorShiftRng, SeedableRng, Rand, Rng};
    use crate::pairing::bn256::Bn256;
    use num_cpus;

    const SAMPLES: usize = 1 << 22;
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

    let duration_ns = start.elapsed().as_nanos() as f64;
    println!("{} ms for sparse for {} samples", duration_ns/1000.0f64, SAMPLES);
}