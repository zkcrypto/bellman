use crate::pairing::ff::PrimeField;
use crate::multicore::*;
use crate::plonk::domains::*;

pub(crate) mod partial_reduction;

pub trait CTPrecomputations<F: PrimeField>: Send + Sync {
    fn new_for_domain_size(size: usize) -> Self;
    fn bit_reversed_omegas(&self) -> &[F];
    fn domain_size(&self) -> usize;
}

#[inline(always)]
pub(crate) fn bitreverse(n: usize, l: usize) -> usize {
    let mut r = n.reverse_bits();
    // now we need to only use the bits that originally were "last" l, so shift

    r >>= (std::mem::size_of::<usize>() * 8) - l;

    r
}

#[inline(always)]
fn bitreverse_naive(mut n: u32, l: u32) -> u32 {
    // takes a bit reverse of the last l bits
    let mut r = 0;
    for _ in 0..l {
        r = (r << 1) | (n & 1);
        n >>= 1;
    }
    r
}


pub struct BitReversedOmegas<F: PrimeField> {
    pub omegas: Vec<F>,
    domain_size: usize
}

impl<F: PrimeField> BitReversedOmegas<F> {
    pub fn new_for_domain(domain: &Domain<F>, worker: &Worker) -> Self {
        let domain_size = domain.size as usize;
        
        let omega = domain.generator;
        let precomputation_size = domain_size / 2;
        // let precomputation_size = domain_size;

        let log_n = log2_floor(precomputation_size);

        let mut omegas = vec![F::zero(); precomputation_size];

        worker.scope(omegas.len(), |scope, chunk| {
            for (i, v) in omegas.chunks_mut(chunk).enumerate() {
                scope.spawn(move |_| {
                    let mut u = omega.pow(&[(i * chunk) as u64]);
                    for v in v.iter_mut() {
                        *v = u;
                        u.mul_assign(&omega);
                    }
                });
            }
        });

        if omegas.len() > 2 {
            for k in 0..omegas.len() {
                let rk = bitreverse(k, log_n as usize);
                // let rk_naive = bitreverse_naive(k as u32, log_n as u32);
                // debug_assert!(rk == rk_naive as usize);
                if k < rk {
                    omegas.swap(rk, k);
                }
            }
        }

        BitReversedOmegas{
            omegas,
            domain_size
        }
    }
}

impl<F: PrimeField> CTPrecomputations<F> for BitReversedOmegas<F>{
    fn new_for_domain_size(size: usize) -> Self {
        let domain = Domain::<F>::new_for_size(size as u64).expect("domain must exist");
        let worker = Worker::new();
        Self::new_for_domain(&domain, &worker)
    }

    fn bit_reversed_omegas(&self) -> &[F] {
        &self.omegas[..]
    }

    fn domain_size(&self) -> usize {
        self.domain_size
    }
}


pub(crate) fn log2_floor(num: usize) -> u32 {
    assert!(num > 0);

    let mut pow = 0;

    while (1 << (pow+1)) <= num {
        pow += 1;
    }

    pow
}

pub(crate) fn best_ct_ntt<F: PrimeField, P: CTPrecomputations<F>>(
    a: &mut [F], 
    worker: &Worker, 
    log_n: u32, 
    use_cpus_hint: Option<usize>, 
    precomputed_omegas: &P
)
{
    let log_cpus = if let Some(hint) = use_cpus_hint {
        assert!(hint <= worker.cpus);
        let hint = if hint > 0 {
            log2_floor(hint)
        } else {
            0
        };

        hint
    } else {
        worker.log_num_cpus()
    };

    if log_cpus == 0 || log_n <= log_cpus {
        serial_ct_ntt(a, log_n, precomputed_omegas);
    } else {
        parallel_ct_ntt(a, worker, log_n, log_cpus, precomputed_omegas);
    }
}

pub(crate) fn serial_ct_ntt<F: PrimeField, P: CTPrecomputations<F>>(
    a: &mut [F],
    log_n: u32,
    precomputed_omegas: &P
)
{
    assert_eq!(a.len(), precomputed_omegas.domain_size());
    assert_eq!(a.len(), (1<<log_n) as usize);

    let n = a.len();
    if n == 1 {
        return;
    }
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
            tmp.sub_assign(&v);

            a[j+distance] = tmp;
            a[j].add_assign(&v);
        }

        pairs_per_group /= 2;
        num_groups *= 2;
        distance /= 2;
    }

    while num_groups < n {
        debug_assert!(num_groups > 1);
        for k in 0..num_groups {
            let idx_1 = k * pairs_per_group * 2;
            let idx_2 = idx_1 + pairs_per_group;
            let s = omegas_bit_reversed[k];

            for j in idx_1..idx_2 {
                let u = a[j];
                let mut v = a[j+distance];
                v.mul_assign(&s);

                let mut tmp = u;
                tmp.sub_assign(&v);

                a[j+distance] = tmp;
                a[j].add_assign(&v);
            }
        }

        pairs_per_group /= 2;
        num_groups *= 2;
        distance /= 2;
    }

    // let log_n = log_n as usize;

    // for k in 0..n {
    //     let rk = bitreverse(k, log_n);
    //     if k < rk {
    //         a.swap(rk, k);
    //     }
    // }
}


// pub(crate) fn serial_ct_ntt<F: PrimeField, P: CTPrecomputations<F>>(
//     a: &mut [F],
//     // worker: &Worker,
//     log_n: u32,
//     // log_cpus: u32,
//     precomputed_omegas: &P
// )
// {
//     assert_eq!(a.len(), precomputed_omegas.domain_size());

//     let log_n = log_n as usize;
//     let n = a.len();

//     for k in 0..n {
//         let rk = bitreverse(k, log_n);
//         if k < rk {
//             a.swap(rk, k);
//         }
//     }

//     let mut current_size = a.len();
//     let mut num_subroutines = 1;
//     let mut distance = 1;

//     let omegas_bit_reversed = precomputed_omegas.bit_reversed_omegas();

//     while current_size > 1 {
//         for k in 0..num_subroutines {
//             let mut j = k;
//             let mut omega_idx = 0;
//             let step = 2*num_subroutines;

//             while j < n-1 {
//                 let omega = omegas_bit_reversed[omega_idx];
//                 let u = a[j];
//                 let v = a[j+distance];

//                 let mut tmp = u;
//                 tmp.sub_assign(&v);
//                 tmp.mul_assign(&omega);

//                 a[j+distance] = tmp;
//                 a[j].add_assign(&v);

//                 omega_idx += 1;
//                 j += step;
//             }
//         }

//         num_subroutines *= 2;
//         current_size /= 2;
//         distance *= 2;
//     }
// }


pub(crate) fn parallel_ct_ntt<F: PrimeField, P: CTPrecomputations<F>>(
    a: &mut [F],
    worker: &Worker,
    log_n: u32,
    log_cpus: u32,
    precomputed_omegas: &P
)
{
    assert!(log_n >= log_cpus);
    assert_eq!(a.len(), precomputed_omegas.domain_size());

    let n = a.len();
    if n == 1 {
        return;
    }
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
                        let u = a[j];
                        let v = a[j+distance];

                        let mut tmp = u;
                        tmp.sub_assign(&v);

                        a[j+distance] = tmp;
                        a[j].add_assign(&v);
                    }

                    pairs_per_group /= 2;
                    num_groups *= 2;
                    distance /= 2;

                    (&barriers[round_id]).wait();

                    round_id += 1;
                }

                // if pairs per group << num cpus we use splitting in k,
                // otherwise use splitting in indexes
                while num_groups < n {
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
                                let u = a[j];
                                let mut v = a[j+distance];
                                v.mul_assign(&s);

                                let mut tmp = u;
                                tmp.sub_assign(&v);

                                a[j+distance] = tmp;
                                a[j].add_assign(&v);
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
                                let u = a[j];
                                let mut v = a[j+distance];
                                v.mul_assign(&s);

                                let mut tmp = u;
                                tmp.sub_assign(&v);

                                a[j+distance] = tmp;
                                a[j].add_assign(&v);
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
            });
        }
    });

    // let log_n = log_n as usize;

    // for k in 0..n {
    //     let rk = bitreverse(k, log_n);
    //     // let rk_naive = bitreverse_naive(k as u32, log_n as u32);
    //     // debug_assert!(rk == rk_naive as usize);
    //     if k < rk {
    //         a.swap(rk, k);
    //     }
    // }
}


#[cfg(test)]
mod test {
    #[test]
    fn test_bit_reversed_omegas_computation() {
        use rand::{XorShiftRng, SeedableRng, Rand, Rng};
        use crate::plonk::transparent_engine::proth::Fr;
        use crate::plonk::polynomials::*;
        use std::time::Instant;
        use crate::multicore::*;
        use crate::plonk::commitments::transparent::utils::*;
        use super::CTPrecomputations;
        use super::BitReversedOmegas;

        // let poly_sizes = vec![1_000_000, 2_000_000, 4_000_000];

        let poly_sizes = vec![4];

        for poly_size in poly_sizes.into_iter() {
            let poly_size = poly_size as usize;
            let poly_size = poly_size.next_power_of_two();
            let precomp = BitReversedOmegas::<Fr>::new_for_domain_size(poly_size);
            println!("{:?}", precomp.bit_reversed_omegas());
        }
    }

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
        use super::BitReversedOmegas;
        use crate::plonk::domains::Domain;

        let poly_sizes = vec![1_000_000, 2_000_000, 4_000_000];

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

            let res2 = {
                let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
                let mut coeffs = (0..poly_size).map(|_| Fr::rand(rng)).collect::<Vec<_>>();
                // println!("Coeffs = {:?}", coeffs);
                let start = Instant::now();
                serial_ct_ntt(&mut coeffs, log_n, &precomp);
                println!("serial NTT for size {} taken {:?}", poly_size, start.elapsed());

                let log_n = log_n as usize;
                for k in 0..poly_size {
                    let rk = bitreverse(k, log_n);
                    if k < rk {
                        coeffs.swap(rk, k);
                    }
                }

                coeffs
            };

            assert!(res1 == res2);

            // let (valid, permutation) = check_permutation(&res1, &res2);

            // if valid {
            //     println!("Permutation = {:?}", permutation);
            // }

            // assert!(valid, "true = {:?}\n,got = {:?}", res1, res2);
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
        use super::BitReversedOmegas;
        use crate::plonk::domains::Domain;

        let poly_sizes = vec![1_000_000, 2_000_000, 4_000_000];

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

            let res2 = {
                let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
                let mut coeffs = (0..poly_size).map(|_| Fr::rand(rng)).collect::<Vec<_>>();
                let start = Instant::now();
                parallel_ct_ntt(&mut coeffs, &worker, log_n, worker.log_num_cpus(), &precomp);
                println!("parallel NTT for size {} taken {:?}", poly_size, start.elapsed());

                let log_n = log_n as usize;
                for k in 0..poly_size {
                    let rk = bitreverse(k, log_n);
                    if k < rk {
                        coeffs.swap(rk, k);
                    }
                }

                coeffs
            };

            assert!(res1 == res2);
        }
    }
}






