use ff::PrimeField;
use super::multicore::*;
use super::prefetch::*;

pub(crate) fn best_lde<F: PrimeField>(a: &mut [F], worker: &Worker, omega: &F, log_n: u32, lde_factor: usize)
{
    let log_cpus = worker.log_num_cpus();

    if log_n <= log_cpus {
        serial_lde(a, omega, log_n, lde_factor);
    } else {
        parallel_lde(a, worker, omega, log_n, log_cpus, lde_factor);
    }
}

pub(crate) fn serial_lde<F: PrimeField>(a: &mut [F], omega: &F, log_n: u32, lde_factor: usize)
{
    #[inline(always)]
    fn bitreverse(mut n: u32, l: u32) -> u32 {
        let mut r = 0;
        for _ in 0..l {
            r = (r << 1) | (n & 1);
            n >>= 1;
        }
        r
    }

    #[inline(always)]
    fn is_non_zero(idx: usize, lde_factor: usize, step: usize) -> bool {
        let idx_mod_f = idx & (lde_factor - 1);
        return idx_mod_f < (1 << step);
    }

    #[inline(always)]
    fn is_dense_round(lde_factor: usize, step: usize) -> bool {
        let f = lde_factor >> step;
        if f <= 1 {
            return true;
        }
       
        false
    }

    let n = a.len() as u32;
    let non_trivial_len = (a.len() / lde_factor) as u32;
    assert_eq!(n, 1 << log_n);

    for k in 0..n {
        if k >= non_trivial_len {
            break;
        }
        let rk = bitreverse(k, log_n);
        if k < rk {
            a.swap(rk as usize, k as usize);
        }
    }

    // even after bit reverses we can guarantee some distribution

    let mut m = 1;
    let mut step = 0;

    for _ in 0..log_n {
        let w_m = omega.pow(&[(n / (2*m)) as u64]);

        let step_by = 2*m as usize;
        if is_dense_round(lde_factor, step) {    
            // standard fft
            for k in (0..n).step_by(step_by) {
                {
                    prefetch_index::<F>(a, (k + m) as usize);
                    prefetch_index::<F>(a, k as usize);
                }
                let mut w = F::one();
                for j in 0..(m-1) {
                    {
                        prefetch_index::<F>(a, (k+j+1+m) as usize);
                        prefetch_index::<F>(a, (k+j+1) as usize);
                    }
                    let mut t = a[(k+j+m) as usize];
                    t.mul_assign(&w);
                    let mut tmp = a[(k+j) as usize];
                    tmp.sub_assign(&t);
                    a[(k+j+m) as usize] = tmp;
                    a[(k+j) as usize].add_assign(&t);
                    w.mul_assign(&w_m);
                } 

                let j = m - 1;
                let mut t = a[(k+j+m) as usize];
                t.mul_assign(&w);
                let mut tmp = a[(k+j) as usize];
                tmp.sub_assign(&t);
                a[(k+j+m) as usize] = tmp;
                a[(k+j) as usize].add_assign(&t);
                w.mul_assign(&w_m);
            }
        } else {
            // have some pain trying to save on memory reads and multiplications
            for k in (0..n).step_by(step_by) {
                {
                    let odd_idx = (k + m) as usize;
                    let even_idx = k as usize;
                    if is_non_zero(even_idx, lde_factor, step) || is_non_zero(odd_idx, lde_factor, step) {
                        prefetch_index::<F>(a, odd_idx);
                        prefetch_index::<F>(a, even_idx);
                    }
                }
                let mut w = F::one();
                for j in 0..(m-1) {
                    let odd_idx = (k+j+m) as usize;
                    let even_idx = (k+j) as usize;
                    {
                        if is_non_zero(even_idx+1, lde_factor, step) || is_non_zero(odd_idx+1, lde_factor, step) {
                            prefetch_index::<F>(a, odd_idx + 1);
                            prefetch_index::<F>(a, even_idx + 1);
                        }
                    }

                    let odd_is_non_zero = is_non_zero(odd_idx, lde_factor, step);
                    let even_is_non_zero = is_non_zero(even_idx, lde_factor, step);

                    // debug_assert!(!a[odd_idx].is_zero() == odd_is_non_zero, "expected for idx = {} to be non-zero: {} for step {}, value: {}", odd_idx, odd_is_non_zero, step, a[odd_idx]);
                    // debug_assert!(!a[even_idx].is_zero() == even_is_non_zero, "expected for idx = {} to be non-zero: {} for step {}, value: {}", even_idx, even_is_non_zero, step, a[even_idx]);

                    match (odd_is_non_zero, even_is_non_zero) {
                        (true, true) => {
                            let mut t = a[odd_idx];
                            t.mul_assign(&w);

                            let mut tmp = a[even_idx];
                            tmp.sub_assign(&t);

                            a[odd_idx] = tmp;
                            a[even_idx].add_assign(&t);
                        },
                        (false, true) => {
                            a[odd_idx] = a[even_idx];
                        },
                        (true, false) => {
                            let mut t = a[odd_idx];
                            t.mul_assign(&w);

                            let mut tmp = t;
                            tmp.negate();
                            
                            a[odd_idx] = tmp;
                            a[even_idx] = t;
                        },
                        (false, false) => {
                        }
                    }

                    w.mul_assign(&w_m);
                }

                let j = m-1;

                let odd_idx = (k+j+m) as usize;
                let even_idx = (k+j) as usize;

                let odd_is_non_zero = is_non_zero(odd_idx, lde_factor, step);
                let even_is_non_zero = is_non_zero(even_idx, lde_factor, step);

                // debug_assert!(!a[odd_idx].is_zero() == odd_is_non_zero, "expected for idx = {} to be non-zero: {} for step {}, value: {}", odd_idx, odd_is_non_zero, step, a[odd_idx]);
                // debug_assert!(!a[even_idx].is_zero() == even_is_non_zero, "expected for idx = {} to be non-zero: {} for step {}, value: {}", even_idx, even_is_non_zero, step, a[even_idx]);

                match (odd_is_non_zero, even_is_non_zero) {
                    (true, true) => {
                        let mut t = a[odd_idx];
                        t.mul_assign(&w);

                        let mut tmp = a[even_idx];
                        tmp.sub_assign(&t);

                        a[odd_idx] = tmp;
                        a[even_idx].add_assign(&t);
                    },
                    (false, true) => {
                        a[odd_idx] = a[even_idx];
                    },
                    (true, false) => {
                        let mut t = a[odd_idx];
                        t.mul_assign(&w);

                        let mut tmp = t;
                        tmp.negate();
                        
                        a[odd_idx] = tmp;
                        a[even_idx] = t;
                    },
                    (false, false) => {
                    }
                }

                w.mul_assign(&w_m);
            }
        }

        step += 1;
        m *= 2;
    }
}

pub(crate) fn parallel_lde<F: PrimeField>(
    a: &mut [F],
    worker: &Worker,
    omega: &F,
    log_n: u32,
    log_cpus: u32,
    lde_factor: usize
)
{
    assert!(log_n >= log_cpus);

    let num_cpus = 1 << log_cpus;
    let log_new_n = log_n - log_cpus;
    let mut tmp = vec![vec![F::zero(); 1 << log_new_n]; num_cpus];
    let new_omega = omega.pow(&[num_cpus as u64]);

    let non_trivial_len = a.len() / lde_factor;

    worker.scope(0, |scope, _| {
        let a = &*a;

        for (j, tmp) in tmp.iter_mut().enumerate() {
            scope.spawn(move |_| {
                // Shuffle into a sub-FFT
                let omega_j = omega.pow(&[j as u64]);
                let omega_step = omega.pow(&[(j as u64) << log_new_n]);

                let mut elt = F::one();
                for i in 0..(1 << log_new_n) {
                    for s in 0..num_cpus {
                        let idx = (i + (s << log_new_n)) % (1 << log_n);
                        if idx < non_trivial_len {
                            let mut t = a[idx];
                            t.mul_assign(&elt);
                            tmp[i].add_assign(&t);
                        }
                        elt.mul_assign(&omega_step);
                    }
                    elt.mul_assign(&omega_j);
                }

                let new_lde_factor = lde_factor >> log_cpus;
                if new_lde_factor <= 1 {
                    super::prefetch_fft::serial_fft(tmp, &new_omega, log_new_n);
                } else {
                    serial_lde(tmp, &new_omega, log_new_n, new_lde_factor);
                }
            });
        }
    });

    worker.scope(a.len(), |scope, chunk| {
        let tmp = &tmp;

        for (idx, a) in a.chunks_mut(chunk).enumerate() {
            scope.spawn(move |_| {
                let mut idx = idx * chunk;
                let mask = (1 << log_cpus) - 1;
                for a in a {
                    *a = tmp[idx & mask][idx >> log_cpus];
                    idx += 1;
                }
            });
        }
    });
}

// #[test]
// fn test_small_lde() {
//     use rand::{XorShiftRng, SeedableRng, Rand};
//     const LOG_N: usize = 2;
//     const BASE: usize = 1 << LOG_N;
//     const LOG_LDE: usize = 6;
//     const LDE_FACTOR: usize = 1 << LOG_LDE;
//     let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

//     use ff::Field;
//     use crate::experiments::vdf::Fr;
//     use crate::domains::Domain;
//     use crate::fft::multicore::Worker;
//     use std::time::Instant;

//     let worker = Worker::new();

//     let mut coeffs = (0..BASE).map(|_| Fr::rand(rng)).collect::<Vec<_>>();

//     coeffs.resize(BASE * LDE_FACTOR, Fr::zero());

//     let domain = Domain::<Fr>::new_for_size(coeffs.len() as u64).unwrap();
//     let omega = domain.generator;
//     let log_n = (LOG_N + LOG_LDE) as u32;

//     let mut reference = coeffs.clone();

//     let mut lde = coeffs;

//     let now = Instant::now();
//     crate::fft::best_fft(&mut reference[..], &worker, &omega, log_n);
//     println!("naive LDE taken {}ms", now.elapsed().as_millis());

//     // let now = Instant::now();
//     // crate::fft::fft::serial_fft(&mut reference[..], &omega, log_n);
//     // println!("naive LDE taken {}ms", now.elapsed().as_millis());

//     let now = Instant::now();
//     self::best_lde(&mut lde, &worker, &omega, log_n, LDE_FACTOR);
//     println!("LDE taken {}ms", now.elapsed().as_millis());

//     // let now = Instant::now();
//     // self::serial_lde(&mut lde, &omega, log_n, BASE);
//     // println!("LDE taken {}ms", now.elapsed().as_millis());

//     assert!(reference == lde);
// }

// #[test]
// fn test_small_prefetch_serial_lde() {
//     use rand::{XorShiftRng, SeedableRng, Rand};
//     const LOG_N: usize = 2;
//     const BASE: usize = 1 << LOG_N;
//     const LOG_LDE: usize = 6;
//     const LDE_FACTOR: usize = 1 << LOG_LDE;
//     let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

//     use ff::Field;
//     use crate::experiments::vdf::Fr;
//     use crate::domains::Domain;
//     use std::time::Instant;

//     let mut coeffs = (0..BASE).map(|_| Fr::rand(rng)).collect::<Vec<_>>();

//     coeffs.resize(BASE * LDE_FACTOR, Fr::zero());

//     let domain = Domain::<Fr>::new_for_size(coeffs.len() as u64).unwrap();
//     let omega = domain.generator;
//     let log_n = (LOG_N + LOG_LDE) as u32;

//     let mut reference = coeffs.clone();

//     let mut lde = coeffs;

//     let now = Instant::now();
//     crate::fft::fft::serial_fft(&mut reference[..], &omega, log_n);
//     println!("naive LDE taken {}ms", now.elapsed().as_millis());

//     let now = Instant::now();
//     self::serial_lde(&mut lde, &omega, log_n, LDE_FACTOR);
//     println!("LDE taken {}ms", now.elapsed().as_millis());

//     assert!(reference == lde);
// }

// #[test]
// fn test_large_prefetch_serial_lde() {
//     use rand::{XorShiftRng, SeedableRng, Rand};
//     const LOG_N: usize = 20;
//     const BASE: usize = 1 << LOG_N;
//     const LOG_LDE: usize = 7;
//     const LDE_FACTOR: usize = 1 << LOG_LDE;
//     let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

//     use ff::Field;
//     use crate::experiments::vdf::Fr;
//     use crate::domains::Domain;
//     use std::time::Instant;

//     let mut coeffs = (0..BASE).map(|_| Fr::rand(rng)).collect::<Vec<_>>();

//     coeffs.resize(BASE * LDE_FACTOR, Fr::zero());

//     let domain = Domain::<Fr>::new_for_size(coeffs.len() as u64).unwrap();
//     let omega = domain.generator;
//     let log_n = (LOG_N + LOG_LDE) as u32;

//     let mut reference = coeffs.clone();

//     let mut lde = coeffs;

//     let now = Instant::now();
//     crate::fft::fft::serial_fft(&mut reference[..], &omega, log_n);
//     println!("naive LDE taken {}ms", now.elapsed().as_millis());

//     let now = Instant::now();
//     self::serial_lde(&mut lde, &omega, log_n, LDE_FACTOR);
//     println!("LDE taken {}ms", now.elapsed().as_millis());

//     assert!(reference == lde);
// }

// #[test]
// fn test_large_prefetch_lde() {
//     use rand::{XorShiftRng, SeedableRng, Rand};
//     const LOG_N: usize = 22;
//     const BASE: usize = 1 << LOG_N;
//     const LOG_LDE: usize = 7;
//     const LDE_FACTOR: usize = 1 << LOG_LDE;
//     let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

//     use ff::Field;
//     use crate::experiments::vdf::Fr;
//     use crate::domains::Domain;
//     use crate::fft::multicore::Worker;
//     use crate::polynomials::Polynomial;
//     use std::time::Instant;

//     let worker = Worker::new();

//     let mut coeffs = (0..BASE).map(|_| Fr::rand(rng)).collect::<Vec<_>>();

//     let mut poly = Polynomial::from_coeffs(coeffs.clone()).unwrap();

//     poly.pad_by_factor(LDE_FACTOR).unwrap();
//     let now = Instant::now();
//     let naive_lde = poly.fft(&worker);
//     println!("naive LDE taken {}ms", now.elapsed().as_millis());

//     coeffs.resize(BASE * LDE_FACTOR, Fr::zero());

//     let domain = Domain::<Fr>::new_for_size(coeffs.len() as u64).unwrap();
//     let omega = domain.generator;
//     let log_n = (LOG_N + LOG_LDE) as u32;

//     let now = Instant::now();
//     let mut lde = coeffs.clone();
//     best_lde(&mut lde, &worker, &omega, log_n, LDE_FACTOR);
//     println!("LDE taken {}ms", now.elapsed().as_millis());


//     assert!(naive_lde.into_coeffs() == lde);
// }

