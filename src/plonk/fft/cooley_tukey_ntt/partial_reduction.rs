use crate::pairing::ff::PrimeField;
use crate::multicore::*;
use crate::plonk::domains::*;
use crate::plonk::transparent_engine::PartialTwoBitReductionField;

use super::CTPrecomputations;

pub(crate) fn serial_ct_ntt_partial_reduction<F: PartialTwoBitReductionField, P: CTPrecomputations<F>>(
    a: &mut [F],
    log_n: u32,
    precomputed_omegas: &P
)
{
    assert_eq!(a.len(), precomputed_omegas.domain_size());
    assert_eq!(a.len(), (1<<log_n) as usize);
    assert!(F::NUM_BITS % 64 >= 2);

    let n = a.len();
    if n == 1 {
        return;
    }
    let half_n = n / 2;

    let mut pairs_per_group = n / 2;
    let mut num_groups = 1;
    let mut distance = n / 2;

    let omegas_bit_reversed = precomputed_omegas.bit_reversed_omegas();

    {
        // special case for omega = 1
        debug_assert!(num_groups == 1);
        let idx_1 = 0;
        let idx_2 = pairs_per_group;

        for j in idx_1..idx_2 {
            let u = a[j];
            let v = a[j+distance];

            let mut tmp = u;
            tmp.sub_assign_unreduced(&v);

            a[j+distance] = tmp;
            a[j].add_assign_unreduced(&v);

            debug_assert!(a[j].overflow_factor() < 2);
            debug_assert!(a[j+distance].overflow_factor() < 2);
        }

        pairs_per_group /= 2;
        num_groups *= 2;
        distance /= 2;
    }

    // all elements are [0, 2p)

    while num_groups < half_n {
        debug_assert!(num_groups > 1);
        for k in 0..num_groups {
            let idx_1 = k * pairs_per_group * 2;
            let idx_2 = idx_1 + pairs_per_group;
            let s = omegas_bit_reversed[k];

            for j in idx_1..idx_2 {
                let mut u = a[j];
                let mut v = a[j+distance];

                debug_assert!(u.overflow_factor() < 4, "factor is {} for num groups {}", u.overflow_factor(), num_groups);
                u.reduce_twice();

                debug_assert!(v.overflow_factor() < 4, "factor is {} for num groups {}", v.overflow_factor(), num_groups);
                v.mul_assign_unreduced(&s);
                debug_assert!(v.overflow_factor() < 2, "factor is {} for num groups {}", v.overflow_factor(), num_groups);

                let mut tmp_v = u;
                let mut tmp_u = u;

                tmp_u.add_assign_unreduced(&v);
                tmp_v.sub_assign_twice_unreduced(&v);

                debug_assert!(tmp_u.overflow_factor() < 4, "factor is {} for num groups {}", tmp_u.overflow_factor(), num_groups);
                debug_assert!(tmp_v.overflow_factor() < 4, "factor is {} for num groups {}", tmp_v.overflow_factor(), num_groups);

                a[j+distance] = tmp_v;
                a[j] = tmp_u;
            }
        }

        pairs_per_group /= 2;
        num_groups *= 2;
        distance /= 2;
    }

    // here we should reduce completely

    {
        debug_assert!(num_groups > 1);
        for k in 0..num_groups {
            let idx_1 = k * pairs_per_group * 2;
            let idx_2 = idx_1 + pairs_per_group;
            let s = omegas_bit_reversed[k];

            for j in idx_1..idx_2 {
                let mut u = a[j];
                let mut v = a[j+distance];

                debug_assert!(u.overflow_factor() < 4, "factor is {} for num groups {}", u.overflow_factor(), num_groups);
                u.reduce_twice();
                debug_assert!(u.overflow_factor() < 2, "factor is {} for num groups {}", u.overflow_factor(), num_groups);

                debug_assert!(v.overflow_factor() < 4, "factor is {} for num groups {}", v.overflow_factor(), num_groups);
                v.mul_assign_unreduced(&s);
                debug_assert!(v.overflow_factor() < 2, "factor is {} for num groups {}", v.overflow_factor(), num_groups);

                let mut tmp_v = u;
                let mut tmp_u = u;

                tmp_u.add_assign_unreduced(&v);
                PartialTwoBitReductionField::reduce_completely(&mut tmp_u);

                tmp_v.sub_assign_twice_unreduced(&v);
                PartialTwoBitReductionField::reduce_completely(&mut tmp_v);

                debug_assert!(tmp_u.overflow_factor() < 1, "factor is {} for num groups {}", tmp_u.overflow_factor(), num_groups);
                debug_assert!(tmp_v.overflow_factor() < 1, "factor is {} for num groups {}", tmp_v.overflow_factor(), num_groups);

                a[j+distance] = tmp_v;
                a[j] = tmp_u;
            }
        }
    }
}

pub(crate) fn parallel_ct_ntt_partial_reduction<F: PartialTwoBitReductionField, P: CTPrecomputations<F>>(
    a: &mut [F],
    worker: &Worker,
    log_n: u32,
    log_cpus: u32,
    precomputed_omegas: &P
)
{
    assert!(log_n >= log_cpus);
    assert_eq!(a.len(), precomputed_omegas.domain_size());
    assert!(F::NUM_BITS % 64 >= 2);

    let n = a.len();
    if n == 1 {
        return;
    }
    let half_n = n / 2;

    let pairs_per_group = n / 2;
    let num_groups = 1;
    let distance = n / 2;

    let omegas_bit_reversed = precomputed_omegas.bit_reversed_omegas();

    let a = a as *mut [F];

    use std::sync::{Arc, Barrier};

    let num_remaining_rounds = log_n as usize;

    // TODO: later find a way to utilize all the cores in case of not power of twwo
    let to_spawn = (1 << log_cpus) as usize;

    let mut barriers = Vec::with_capacity(num_remaining_rounds);
    for _ in 0..num_remaining_rounds {
        let barrier = Barrier::new(to_spawn);
        barriers.push(barrier);
    }

    let barriers = Arc::new(barriers);

    worker.scope(0, |scope, _| {
        for thread_id in 0..to_spawn {
            let a = unsafe {&mut *a};
            let mut pairs_per_group = pairs_per_group;
            let mut num_groups = num_groups;
            let mut distance = distance;
            let barriers = barriers.clone();
            scope.spawn(move |_| {
                let mut round_id = 0;
                {
                    // special case for omega = 1
                    debug_assert!(num_groups == 1);
                    let group_start_idx = 0;
                    let group_end_idx = pairs_per_group;
                    let group_size = pairs_per_group;

                    let chunk = Worker::chunk_size_for_num_spawned_threads(group_size, to_spawn);

                    let start = group_start_idx + thread_id * chunk;
                    let end = if start + chunk <= group_end_idx {
                        start + chunk
                    } else {
                        group_end_idx
                    };

                    for j in start..end {
                        let u = unsafe { *a.get_unchecked(j) };
                        let v = unsafe { *a.get_unchecked(j+distance) };

                        // let u = a[j];
                        // let v = a[j+distance];

                        let mut tmp = u;
                        tmp.sub_assign_unreduced(&v);

                        unsafe { 
                            *a.get_unchecked_mut(j+distance) = tmp;
                            a.get_unchecked_mut(j).add_assign_unreduced(&v);
                        };

                        // a[j+distance] = tmp;
                        // a[j].add_assign_unreduced(&v);
                    }

                    pairs_per_group /= 2;
                    num_groups *= 2;
                    distance /= 2;

                    (&barriers[round_id]).wait();

                    round_id += 1;
                }

                // if pairs per group << num cpus we use splitting in k,
                // otherwise use splitting in indexes
                while num_groups < half_n {
                    if num_groups >= to_spawn {
                        // for each k we start at k*pairs*2 and end on k*pairs*2 + pairs
                        // for k+1 we start at (k+1)*pairs*2 = k*pairs*2 + pairs*2
                        // and end on (k+1)*pairs*2 + pairs = k*pairs*2 + pairs*3
                        // for k+2 we start at (k+2)*pairs*2 = k*pairs*2 + pairs*4
                        // and end on (k+2)*pairs*2 + pairs = k*pairs*2 + pairs*5
                        // so we do not overlap during the full run and do not need to sync

                        let chunk = Worker::chunk_size_for_num_spawned_threads(num_groups, to_spawn);
                        let start = thread_id * chunk;
                        let end = if start + chunk <= num_groups {
                            start + chunk
                        } else {
                            num_groups
                        };

                        for k in start..end {
                            let group_start_idx = k * pairs_per_group * 2;
                            let group_end_idx = group_start_idx + pairs_per_group;
                            let s = omegas_bit_reversed[k];

                            for j in group_start_idx..group_end_idx {
                                let mut u = unsafe { *a.get_unchecked(j) };
                                let mut v = unsafe { *a.get_unchecked(j+distance) };

                                // let mut u = a[j];
                                // let mut v = a[j+distance];

                                u.reduce_twice();
                                v.mul_assign_unreduced(&s);

                                let mut tmp_v = u;
                                let mut tmp_u = u;

                                tmp_u.add_assign_unreduced(&v);
                                tmp_v.sub_assign_twice_unreduced(&v);

                                unsafe { 
                                    *a.get_unchecked_mut(j+distance) = tmp_v;
                                    *a.get_unchecked_mut(j) = tmp_u;
                                };

                                // a[j+distance] = tmp_v;
                                // a[j] = tmp_u;
                            }
                        }
                    } else {
                        for k in 0..num_groups {
                            // for each k we start at k*pairs*2 and end on k*pairs*2 + pairs
                            // for k+1 we start at (k+1)*pairs*2 = k*pairs*2 + pairs*2
                            // and end on (k+1)*pairs*2 + pairs = k*pairs*2 + pairs*3
                            // for k+2 we start at (k+2)*pairs*2 = k*pairs*2 + pairs*4
                            // and end on (k+2)*pairs*2 + pairs = k*pairs*2 + pairs*5
                            // so we do not overlap during the full run and do not need to sync
                            let group_start_idx = k * pairs_per_group * 2;
                            let group_end_idx = group_start_idx + pairs_per_group;
                            let group_size = pairs_per_group;
                            let s = omegas_bit_reversed[k];

                            // we always split thread work in here

                            let chunk = Worker::chunk_size_for_num_spawned_threads(group_size, to_spawn);

                            let start = group_start_idx + thread_id * chunk;
                            let end = if start + chunk <= group_end_idx {
                                start + chunk
                            } else {
                                group_end_idx
                            };

                            for j in start..end {
                                let mut u = unsafe { *a.get_unchecked(j) };
                                let mut v = unsafe { *a.get_unchecked(j+distance) };

                                // let mut u = a[j];
                                // let mut v = a[j+distance];

                                u.reduce_twice();
                                v.mul_assign_unreduced(&s);

                                let mut tmp_v = u;
                                let mut tmp_u = u;

                                tmp_u.add_assign_unreduced(&v);
                                tmp_v.sub_assign_twice_unreduced(&v);

                                unsafe { 
                                    *a.get_unchecked_mut(j+distance) = tmp_v;
                                    *a.get_unchecked_mut(j) = tmp_u;
                                };

                                // a[j+distance] = tmp_v;
                                // a[j] = tmp_u;
                            }
                        }
                    }

                    pairs_per_group /= 2;
                    num_groups *= 2;
                    distance /= 2;

                    // use barrier to wait for all other threads
                    (&barriers[round_id]).wait();

                    round_id += 1;
                }

                // if pairs per group << num cpus we use splitting in k,
                // otherwise use splitting in indexes
                {
                    if num_groups >= to_spawn {
                        // for each k we start at k*pairs*2 and end on k*pairs*2 + pairs
                        // for k+1 we start at (k+1)*pairs*2 = k*pairs*2 + pairs*2
                        // and end on (k+1)*pairs*2 + pairs = k*pairs*2 + pairs*3
                        // for k+2 we start at (k+2)*pairs*2 = k*pairs*2 + pairs*4
                        // and end on (k+2)*pairs*2 + pairs = k*pairs*2 + pairs*5
                        // so we do not overlap during the full run and do not need to sync

                        let chunk = Worker::chunk_size_for_num_spawned_threads(num_groups, to_spawn);
                        let start = thread_id * chunk;
                        let end = if start + chunk <= num_groups {
                            start + chunk
                        } else {
                            num_groups
                        };

                        for k in start..end {
                            let group_start_idx = k * pairs_per_group * 2;
                            let group_end_idx = group_start_idx + pairs_per_group;
                            let s = omegas_bit_reversed[k];

                            for j in group_start_idx..group_end_idx {
                                let mut u = unsafe { *a.get_unchecked(j) };
                                let mut v = unsafe { *a.get_unchecked(j+distance) };

                                // let mut u = a[j];
                                // let mut v = a[j+distance];
                                
                                u.reduce_twice();
                                v.mul_assign_unreduced(&s);

                                let mut tmp_v = u;
                                let mut tmp_u = u;

                                tmp_u.add_assign_unreduced(&v);
                                PartialTwoBitReductionField::reduce_completely(&mut tmp_u);

                                tmp_v.sub_assign_twice_unreduced(&v);
                                PartialTwoBitReductionField::reduce_completely(&mut tmp_v);

                                unsafe { 
                                    *a.get_unchecked_mut(j+distance) = tmp_v;
                                    *a.get_unchecked_mut(j) = tmp_u;
                                };

                                // a[j+distance] = tmp_v;
                                // a[j] = tmp_u;
                            }
                        }
                    } else {
                        for k in 0..num_groups {
                            // for each k we start at k*pairs*2 and end on k*pairs*2 + pairs
                            // for k+1 we start at (k+1)*pairs*2 = k*pairs*2 + pairs*2
                            // and end on (k+1)*pairs*2 + pairs = k*pairs*2 + pairs*3
                            // for k+2 we start at (k+2)*pairs*2 = k*pairs*2 + pairs*4
                            // and end on (k+2)*pairs*2 + pairs = k*pairs*2 + pairs*5
                            // so we do not overlap during the full run and do not need to sync
                            let group_start_idx = k * pairs_per_group * 2;
                            let group_end_idx = group_start_idx + pairs_per_group;
                            let group_size = pairs_per_group;
                            let s = omegas_bit_reversed[k];

                            // we always split thread work in here

                            let chunk = Worker::chunk_size_for_num_spawned_threads(group_size, to_spawn);

                            let start = group_start_idx + thread_id * chunk;
                            let end = if start + chunk <= group_end_idx {
                                start + chunk
                            } else {
                                group_end_idx
                            };

                            for j in start..end {
                                let mut u = unsafe { *a.get_unchecked(j) };
                                let mut v = unsafe { *a.get_unchecked(j+distance) };

                                // let mut u = a[j];
                                // let mut v = a[j+distance];

                                u.reduce_twice();
                                v.mul_assign_unreduced(&s);

                                let mut tmp_v = u;
                                let mut tmp_u = u;

                                tmp_u.add_assign_unreduced(&v);
                                PartialTwoBitReductionField::reduce_completely(&mut tmp_u);

                                tmp_v.sub_assign_twice_unreduced(&v);
                                PartialTwoBitReductionField::reduce_completely(&mut tmp_v);

                                unsafe { 
                                    *a.get_unchecked_mut(j+distance) = tmp_v;
                                    *a.get_unchecked_mut(j) = tmp_u;
                                };

                                // a[j+distance] = tmp_v;
                                // a[j] = tmp_u;
                            }
                        }
                    }

                    // use barrier to wait for all other threads
                    (&barriers[round_id]).wait();
                }
            });
        }
    });
}



#[cfg(test)]
mod test {
    use crate::plonk::fft::cooley_tukey_ntt::*;

    #[test]
    fn test_bench_ct_serial_fft() {
        use rand::{XorShiftRng, SeedableRng, Rand, Rng};
        use crate::plonk::transparent_engine::proth::Fr;
        use crate::plonk::polynomials::*;
        use std::time::Instant;
        use super::*;
        use crate::multicore::*;
        use crate::plonk::commitments::transparent::utils::*;
        use crate::plonk::fft::fft::serial_fft;
        use super::CTPrecomputations;
        use super::super::BitReversedOmegas;
        use crate::plonk::domains::Domain;

        let poly_sizes = if cfg!(debug_assertions) {
            vec![10_000]
        } else {
            vec![1_000_000, 2_000_000, 4_000_000, 8_000_000]
        };
        // let poly_sizes = vec![8];

        fn check_permutation<F: PrimeField>(one: &[F], two: &[F]) -> (bool, Vec<usize>) {
            let mut permutation: Vec<usize> = (0..one.len()).collect();
            let mut valid = true;

            for (i, el) in one.iter().enumerate() {
                let mut idx = 0;
                let mut found = false;
                for (j, el2) in two.iter().enumerate() {
                    if *el == *el2 {
                        idx = j;
                        found = true;
                        break;
                    }
                }
                if !found {
                    println!("Not found for {}", i);
                    valid = false;
                    break;
                }
                permutation[i] = idx;
            }

            (valid, permutation)
        }

        // let worker = Worker::new();

        for poly_size in poly_sizes.into_iter() {
            let poly_size = poly_size as usize;
            let poly_size = poly_size.next_power_of_two();
            let precomp = BitReversedOmegas::<Fr>::new_for_domain_size(poly_size);
            // println!("{:?}", precomp.bit_reversed_omegas());
            let domain = Domain::<Fr>::new_for_size(poly_size as u64).unwrap();

            let omega = domain.generator;
            let log_n = domain.power_of_two as u32;

            let res1 = {
                let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
                let mut coeffs = (0..poly_size).map(|_| Fr::rand(rng)).collect::<Vec<_>>();
                let start = Instant::now();
                serial_fft(&mut coeffs, &omega, log_n);
                println!("serial FFT for size {} taken {:?}", poly_size, start.elapsed());

                coeffs
            };

            let (res2, elapsed2) = {
                let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
                let mut coeffs = (0..poly_size).map(|_| Fr::rand(rng)).collect::<Vec<_>>();
                // println!("Coeffs = {:?}", coeffs);
                let start = Instant::now();
                serial_ct_ntt(&mut coeffs, log_n, &precomp);
                let finish = start.elapsed();
                println!("serial NTT for size {} taken {:?}", poly_size, finish);

                let log_n = log_n as usize;
                for k in 0..poly_size {
                    let rk = bitreverse(k, log_n);
                    if k < rk {
                        coeffs.swap(rk, k);
                    }
                }

                (coeffs, finish)
            };

            let (res3, elapsed3) = {
                let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
                let mut coeffs = (0..poly_size).map(|_| Fr::rand(rng)).collect::<Vec<_>>();
                // println!("Coeffs = {:?}", coeffs);
                let start = Instant::now();
                serial_ct_ntt_partial_reduction(&mut coeffs, log_n, &precomp);
                let finish = start.elapsed();
                println!("serial PRR for size {} taken {:?}", poly_size, finish);

                let log_n = log_n as usize;
                for k in 0..poly_size {
                    let rk = bitreverse(k, log_n);
                    if k < rk {
                        coeffs.swap(rk, k);
                    }
                }

                (coeffs, finish)
            };

            let (res5, elapsed5) = {
                let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
                let mut coeffs = (0..poly_size).map(|_| Fr::rand(rng)).collect::<Vec<_>>();
                // println!("Coeffs = {:?}", coeffs);
                let start = Instant::now();
                serial_ct_ntt(&mut coeffs, log_n, &precomp);
                let finish = start.elapsed();
                println!("serial NTT for size {} taken {:?}", poly_size, finish);

                let log_n = log_n as usize;
                for k in 0..poly_size {
                    let rk = bitreverse(k, log_n);
                    if k < rk {
                        coeffs.swap(rk, k);
                    }
                }

                (coeffs, finish)
            };

            let ntt_time = (elapsed2 + elapsed5).div_f32(2.);
            let diff_pr = ntt_time.checked_sub(elapsed3);
            if let Some(diff) = diff_pr {
                println!("Partial reduction: speed up is {}%.", diff.as_nanos()*100/ntt_time.as_nanos());
            } else {
                println!("Partial reduction: no speed up.");
            }

            assert!(res1 == res2);
            assert!(res1 == res5);
            assert!(res1 == res3);
        }
    }

    #[test]
    fn test_bench_ct_parallel_fft() {
        use rand::{XorShiftRng, SeedableRng, Rand, Rng};
        use crate::plonk::transparent_engine::proth::Fr;
        use crate::plonk::polynomials::*;
        use std::time::Instant;
        use super::*;
        use crate::multicore::*;
        use crate::plonk::commitments::transparent::utils::*;
        use crate::plonk::fft::fft::parallel_fft;
        use super::CTPrecomputations;
        use super::super::BitReversedOmegas;
        use crate::plonk::domains::Domain;

        let poly_sizes = if cfg!(debug_assertions) {
            vec![10_000]
        } else {
            vec![2_000_000, 4_000_000, 8_000_000, 16_000_000]
        };

        // let poly_sizes = vec![1000usize];

        let worker = Worker::new();

        for poly_size in poly_sizes.into_iter() {
            let poly_size = poly_size as usize;
            let poly_size = poly_size.next_power_of_two();
            let precomp = BitReversedOmegas::<Fr>::new_for_domain_size(poly_size);
            let domain = Domain::<Fr>::new_for_size(poly_size as u64).unwrap();

            let omega = domain.generator;
            let log_n = domain.power_of_two as u32;

            let res1 = {
                let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
                let mut coeffs = (0..poly_size).map(|_| Fr::rand(rng)).collect::<Vec<_>>();
                let start = Instant::now();
                parallel_fft(&mut coeffs, &worker, &omega, log_n, worker.log_num_cpus());
                println!("parallel FFT for size {} taken {:?}", poly_size, start.elapsed());

                coeffs
            };

            let (res2, elapsed2) = {
                let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
                let mut coeffs = (0..poly_size).map(|_| Fr::rand(rng)).collect::<Vec<_>>();
                let start = Instant::now();
                parallel_ct_ntt(&mut coeffs, &worker, log_n, worker.log_num_cpus(), &precomp);
                let finish = start.elapsed();
                println!("parallel NTT for size {} taken {:?}", poly_size, finish);

                let log_n = log_n as usize;
                for k in 0..poly_size {
                    let rk = bitreverse(k, log_n);
                    if k < rk {
                        coeffs.swap(rk, k);
                    }
                }

                (coeffs, finish)
            };

            let (res3, elapsed3) = {
                let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
                let mut coeffs = (0..poly_size).map(|_| Fr::rand(rng)).collect::<Vec<_>>();
                let start = Instant::now();
                parallel_ct_ntt_partial_reduction(&mut coeffs, &worker, log_n, worker.log_num_cpus(), &precomp);
                let finish = start.elapsed();
                println!("parallel NTT with partial reduction for size {} taken {:?}", poly_size, finish);

                let log_n = log_n as usize;
                for k in 0..poly_size {
                    let rk = bitreverse(k, log_n);
                    if k < rk {
                        coeffs.swap(rk, k);
                    }
                }

                (coeffs, finish)
            };

            let ntt_time = elapsed2;
            let diff_pr = ntt_time.checked_sub(elapsed3);
            if let Some(diff) = diff_pr {
                println!("Partial reduction: speed up is {}%.", diff.as_nanos()*100/ntt_time.as_nanos());
            } else {
                println!("Partial reduction: no speed up.");
            }

            assert!(res1 == res2);
            assert!(res1 == res3);
        }
    }
}
