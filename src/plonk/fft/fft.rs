use crate::pairing::ff::PrimeField;
use crate::multicore::*;

fn log2_floor(num: usize) -> u32 {
    assert!(num > 0);

    let mut pow = 0;

    while (1 << (pow+1)) <= num {
        pow += 1;
    }

    pow
}

pub(crate) fn best_fft<F: PrimeField>(a: &mut [F], worker: &Worker, omega: &F, log_n: u32, use_cpus_hint: Option<usize>)
{
    let log_cpus = if let Some(hint) = use_cpus_hint {
        assert!(hint <= worker.cpus);
        log2_floor(hint)
    } else {
        worker.log_num_cpus()
    };

    if log_cpus == 0 || log_n <= log_cpus {
        serial_fft(a, omega, log_n);
    } else {
        parallel_fft(a, worker, omega, log_n, log_cpus);
    }
}

pub(crate) fn serial_fft<F: PrimeField>(a: &mut [F], omega: &F, log_n: u32)
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

    let n = a.len() as u32;
    assert_eq!(n, 1 << log_n);

    for k in 0..n {
        let rk = bitreverse(k, log_n);
        if k < rk {
            a.swap(rk as usize, k as usize);
        }
    }

    let mut m = 1;
    for _ in 0..log_n {
        let w_m = omega.pow(&[(n / (2*m)) as u64]);

        let mut k = 0;
        while k < n {
            let mut w = F::one();
            for j in 0..m {
                
                let mut t = a[(k+j+m) as usize];
                t.mul_assign(&w);
                let mut tmp = a[(k+j) as usize];
                tmp.sub_assign(&t);
                a[(k+j+m) as usize] = tmp;
                a[(k+j) as usize].add_assign(&t);
                w.mul_assign(&w_m);
            }

            k += 2*m;
        }
        
        m *= 2;
    }
}

pub(crate) fn parallel_fft<F: PrimeField>(
    a: &mut [F],
    worker: &Worker,
    omega: &F,
    log_n: u32,
    log_cpus: u32
)
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

                        t.mul_assign(&elt);
                        tmp[i].add_assign(&t);
                        elt.mul_assign(&omega_step);
                    }
                    elt.mul_assign(&omega_j);
                }

                // Perform sub-FFT
                serial_fft(tmp, &new_omega, log_new_n);
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