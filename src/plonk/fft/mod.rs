pub(crate) mod fft;
pub(crate) mod lde;
pub(crate) mod radix_4;
pub(crate) mod with_precomputation;
pub(crate) mod cooley_tukey_ntt;

use cfg_if;

#[cfg(feature = "nightly")]
mod prefetch_lde;
#[cfg(feature = "nightly")]
mod prefetch_fft;
#[cfg(feature = "nightly")]
mod prefetch;

use crate::pairing::ff::PrimeField;
use crate::multicore::Worker;

cfg_if! {
    if #[cfg(feature = "nightly")] {
        #[inline(always)]
        pub(crate) fn best_lde<F: PrimeField>(a: &mut [F], worker: &Worker, omega: &F, log_n: u32, lde_factor: usize) {
            self::prefetch_lde::best_lde(a, worker, omega, log_n, lde_factor)
        }

        #[inline(always)]
        pub(crate) fn best_fft<F: PrimeField>(a: &mut [F], worker: &Worker, omega: &F, log_n: u32, use_cpus_hint: Option<usize>) {
            self::prefetch_fft::best_fft(a, worker, omega, log_n, use_cpus_hint)
        }

        #[inline(always)]
        pub(crate) fn serial_fft<F: PrimeField>(a: &mut [F], omega: &F, log_n: u32) {
            self::prefetch_fft::serial_fft(a, omega, log_n)
        }
    } else {
        #[inline(always)]
        pub(crate) fn best_lde<F: PrimeField>(a: &mut [F], worker: &Worker, omega: &F, log_n: u32, lde_factor: usize) {
            self::lde::best_lde(a, worker, omega, log_n, lde_factor)
        }
        #[inline(always)]
        pub(crate) fn best_fft<F: PrimeField>(a: &mut [F], worker: &Worker, omega: &F, log_n: u32, use_cpus_hint: Option<usize>) {
            self::fft::best_fft(a, worker, omega, log_n, use_cpus_hint)
        }
        #[inline(always)]
        pub(crate) fn serial_fft<F: PrimeField>(a: &mut [F], omega: &F, log_n: u32) {
            self::fft::serial_fft(a, omega, log_n)
        }
    }  
}

pub fn distribute_powers<F: PrimeField>(coeffs: &mut [F], worker: &Worker, g: F)
{
    worker.scope(coeffs.len(), |scope, chunk| {
        for (i, v) in coeffs.chunks_mut(chunk).enumerate() {
            scope.spawn(move |_| {
                let mut u = g.pow(&[(i * chunk) as u64]);
                for v in v.iter_mut() {
                    v.mul_assign(&u);
                    u.mul_assign(&g);
                }
            });
        }
    });
}

pub fn distribute_powers_serial<F: PrimeField>(coeffs: &mut [F], g: F)
{
    let mut u = F::one();
    for v in coeffs.iter_mut() {
        v.mul_assign(&u);
        u.mul_assign(&g);
    }
}