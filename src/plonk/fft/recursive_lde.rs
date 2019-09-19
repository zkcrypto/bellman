use ff::PrimeField;
use super::multicore::*;

// this is different from FFT by assumption that a lot of coeffs are zero
// and it is good to check for in in arithmetic

pub(crate) fn best_lde<F: PrimeField>(a: Vec<F>, worker: &Worker, omega: &F, log_n: u32) -> Vec<F>
{
    let log_cpus = worker.log_num_cpus();

    if log_n <= log_cpus {
        recursive_lde(&a, *omega, log_n)
    } else {
        parallel_lde(a, worker, omega, log_n, log_cpus)
    }
}

pub(crate) fn recursive_lde<F: PrimeField>(a: &[F], omega: F, log_n: u32) -> Vec<F>
{
    // println!("------------------------");
    // println!("A = {:?}", a);
    let mut all_zeroes = true;
    for a in a.iter() {
        if !a.is_zero() {
            all_zeroes = false;
            break;
        }
    }

    let n = a.len();

    if all_zeroes {
        return vec![F::zero(); n];
    }
    
    if n == 2 {
        let mut t0 = a[0];
        let mut t1 = t0;
        t0.add_assign(&a[1]);
        t1.sub_assign(&a[1]);

        return vec![t0, t1];
    }
    assert_eq!(n, 1 << log_n);

    let n_half = n / 2;

    // copy into subproblems
    let mut even = Vec::with_capacity(n_half);
    let mut odd = Vec::with_capacity(n_half);

    for c in a.chunks(2) {
        even.push(c[0]);
        odd.push(c[1]);
    }

    let mut w_n = omega;
    w_n.square();

    let next_log_n = log_n - 1;

    let y_0 = recursive_lde(&even, w_n, next_log_n);
    let y_1 = recursive_lde(&odd, w_n, next_log_n);

    let mut result = vec![F::zero(); n];

    let mut w = F::one();
    for (i, (y0, y1)) in y_0.into_iter()
                        .zip(y_1.into_iter())
                        .enumerate() {
        let mut tmp = y1;
        if !tmp.is_zero() {
            tmp.mul_assign(&w);

            result[i] = y0;
            result[i].add_assign(&tmp);

            result[i+n_half] = y0;
            result[i+n_half].sub_assign(&tmp);
        } else if !y0.is_zero() {
            result[i] = y0;
            result[i+n_half] = y0;
        } 

        w.mul_assign(&omega);
    }

    result
}

pub(crate) fn parallel_lde<F: PrimeField>(
    mut a: Vec<F>,
    worker: &Worker,
    omega: &F,
    log_n: u32,
    log_cpus: u32
) -> Vec<F>
{
    assert!(log_n >= log_cpus);

    let num_cpus = 1 << log_cpus;
    let log_new_n = log_n - log_cpus;
    let mut tmp = vec![vec![F::zero(); 1 << log_new_n]; num_cpus];
    let new_omega = omega.pow(&[num_cpus as u64]);

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
                        let mut t = a[idx];
                        if !t.is_zero() {
                            t.mul_assign(&elt);
                            tmp[i].add_assign(&t);
                        }
                        elt.mul_assign(&omega_step);
                    }
                    elt.mul_assign(&omega_j);
                }

                // Perform sub-FFT
                *tmp = recursive_lde(tmp, new_omega, log_new_n);
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

    a
}

#[test]
fn test_small_recursive_lde() {
    use rand::{XorShiftRng, SeedableRng, Rand, Rng};
    const LOG_N: usize = 4;
    const BASE: usize = 1 << LOG_N;
    const LOG_LDE: usize = 6;
    const LDE_FACTOR: usize = 1 << LOG_LDE;
    let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    use ff::Field;
    use crate::experiments::vdf::Fr;
    use crate::domains::Domain;
    use crate::fft::multicore::Worker;
    use std::time::Instant;

    let worker = Worker::new();

    let mut coeffs = (0..BASE).map(|_| Fr::rand(rng)).collect::<Vec<_>>();

    coeffs.resize(BASE * LDE_FACTOR, Fr::zero());

    let domain = Domain::<Fr>::new_for_size(coeffs.len() as u64).unwrap();
    let omega = domain.generator;
    let log_n = (LOG_N + LOG_LDE) as u32;

    let mut reference = coeffs.clone();

    let now = Instant::now();
    crate::fft::fft::best_fft(&mut reference[..], &worker, &omega, log_n);
    println!("naive LDE taken {}ms", now.elapsed().as_millis());

    // let now = Instant::now();
    // let _lde = best_lde(coeffs, &worker, &omega, log_n);
    // println!("LDE taken {}ms", now.elapsed().as_millis());
}

#[test]
fn test_large_recursive_lde() {
    use rand::{XorShiftRng, SeedableRng, Rand, Rng};
    const LOG_N: usize = 20;
    const BASE: usize = 1 << LOG_N;
    const LOG_LDE: usize = 6;
    const LDE_FACTOR: usize = 1 << LOG_LDE;
    let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    use ff::Field;
    use crate::experiments::vdf::Fr;
    use crate::domains::Domain;
    use crate::fft::multicore::Worker;
    use crate::polynomials::Polynomial;
    use std::time::Instant;

    let worker = Worker::new();

    let mut coeffs = (0..BASE).map(|_| Fr::rand(rng)).collect::<Vec<_>>();

    let mut poly = Polynomial::from_coeffs(coeffs.clone()).unwrap();

    poly.pad_by_factor(LDE_FACTOR).unwrap();
    let now = Instant::now();
    let naive_lde = poly.fft(&worker);
    println!("naive LDE taken {}ms", now.elapsed().as_millis());

    coeffs.resize(BASE * LDE_FACTOR, Fr::zero());

    let domain = Domain::<Fr>::new_for_size(coeffs.len() as u64).unwrap();
    let omega = domain.generator;
    let log_n = (LOG_N + LOG_LDE) as u32;

    let now = Instant::now();
    let lde = best_lde(coeffs, &worker, &omega, log_n);
    println!("LDE taken {}ms", now.elapsed().as_millis());

    assert!(naive_lde.into_coeffs() == lde);
}