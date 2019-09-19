//! This module contains an `EvaluationDomain` abstraction for
//! performing various kinds of polynomial arithmetic on top of
//! the scalar field.
//!
//! In pairing-based SNARKs like Groth16, we need to calculate
//! a quotient polynomial over a target polynomial with roots
//! at distinct points associated with each constraint of the
//! constraint system. In order to be efficient, we choose these
//! roots to be the powers of a 2^n root of unity in the field.
//! This allows us to perform polynomial operations in O(n)
//! by performing an O(n log n) FFT over such a domain.

use ff::{Field, PrimeField};
use paired::{CurveProjective, Engine};

use super::SynthesisError;

use super::multicore::Worker;

use gpu;

pub struct EvaluationDomain<E: Engine, G: Group<E>> {
    coeffs: Vec<G>,
    exp: u32,
    omega: E::Fr,
    omegainv: E::Fr,
    geninv: E::Fr,
    minv: E::Fr,
}

impl<E: Engine, G: Group<E>> EvaluationDomain<E, G> {
    pub fn as_ref(&self) -> &[G] {
        &self.coeffs
    }

    pub fn as_mut(&mut self) -> &mut [G] {
        &mut self.coeffs
    }

    pub fn into_coeffs(self) -> Vec<G> {
        self.coeffs
    }

    pub fn from_coeffs(mut coeffs: Vec<G>) -> Result<EvaluationDomain<E, G>, SynthesisError> {
        // Compute the size of our evaluation domain
        let mut m = 1;
        let mut exp = 0;
        while m < coeffs.len() {
            m *= 2;
            exp += 1;

            // The pairing-friendly curve may not be able to support
            // large enough (radix2) evaluation domains.
            if exp >= E::Fr::S {
                return Err(SynthesisError::PolynomialDegreeTooLarge);
            }
        }
        // Compute omega, the 2^exp primitive root of unity
        let mut omega = E::Fr::root_of_unity();
        for _ in exp..E::Fr::S {
            omega.square();
        }

        // Extend the coeffs vector with zeroes if necessary
        coeffs.resize(m, G::group_zero());

        Ok(EvaluationDomain {
            coeffs: coeffs,
            exp: exp,
            omega: omega,
            omegainv: omega.inverse().unwrap(),
            geninv: E::Fr::multiplicative_generator().inverse().unwrap(),
            minv: E::Fr::from_str(&format!("{}", m))
                .unwrap()
                .inverse()
                .unwrap(),
        })
    }

    pub fn fft(&mut self, worker: &Worker, kern: &mut Option<gpu::FFTKernel<E::Fr>>) {
        best_fft(kern, &mut self.coeffs, worker, &self.omega, self.exp);
    }

    pub fn ifft(&mut self, worker: &Worker, kern: &mut Option<gpu::FFTKernel<E::Fr>>) {
        best_fft(kern, &mut self.coeffs, worker, &self.omegainv, self.exp);

        if let Some(ref mut k) = kern {
            gpu_mul_by_field(k, &mut self.coeffs, &self.minv, self.exp).expect("GPU Multiply By Field failed!");
        } else {
            worker
                .scope(self.coeffs.len(), |scope, chunk| {
                    let minv = self.minv;

                    for v in self.coeffs.chunks_mut(chunk) {
                        scope.spawn(move |_| {
                            for v in v {
                                v.group_mul_assign(&minv);
                            }
                        });
                    }
                })
                .unwrap();
        }
    }

    pub fn distribute_powers(&mut self, worker: &Worker, g: E::Fr) {
        worker
            .scope(self.coeffs.len(), |scope, chunk| {
                for (i, v) in self.coeffs.chunks_mut(chunk).enumerate() {
                    scope.spawn(move |_| {
                        let mut u = g.pow(&[(i * chunk) as u64]);
                        for v in v.iter_mut() {
                            v.group_mul_assign(&u);
                            u.mul_assign(&g);
                        }
                    });
                }
            })
            .unwrap();
    }

    pub fn coset_fft(&mut self, worker: &Worker, kern: &mut Option<gpu::FFTKernel<E::Fr>>) {
        self.distribute_powers(worker, E::Fr::multiplicative_generator());
        self.fft(worker, kern);
    }

    pub fn icoset_fft(&mut self, worker: &Worker, kern: &mut Option<gpu::FFTKernel<E::Fr>>) {
        let geninv = self.geninv;

        self.ifft(worker, kern);
        self.distribute_powers(worker, geninv);
    }

    /// This evaluates t(tau) for this domain, which is
    /// tau^m - 1 for these radix-2 domains.
    pub fn z(&self, tau: &E::Fr) -> E::Fr {
        let mut tmp = tau.pow(&[self.coeffs.len() as u64]);
        tmp.sub_assign(&E::Fr::one());

        tmp
    }

    /// The target polynomial is the zero polynomial in our
    /// evaluation domain, so we must perform division over
    /// a coset.
    pub fn divide_by_z_on_coset(&mut self, worker: &Worker, kern: &mut Option<gpu::FFTKernel<E::Fr>>) {
        let i = self
            .z(&E::Fr::multiplicative_generator())
            .inverse()
            .unwrap();

        if let Some(ref mut k) = kern {
            gpu_mul_by_field(k, &mut self.coeffs, &i, self.exp).expect("GPU Multiply By Field failed!");
        } else {
            worker
                .scope(self.coeffs.len(), |scope, chunk| {
                    for v in self.coeffs.chunks_mut(chunk) {
                        scope.spawn(move |_| {
                            for v in v {
                                v.group_mul_assign(&i);
                            }
                        });
                    }
                })
                .unwrap();
        }
    }

    /// Perform O(n) multiplication of two polynomials in the domain.
    pub fn mul_assign(&mut self, worker: &Worker, other: &EvaluationDomain<E, Scalar<E>>) {
        assert_eq!(self.coeffs.len(), other.coeffs.len());

        worker
            .scope(self.coeffs.len(), |scope, chunk| {
                for (a, b) in self
                    .coeffs
                    .chunks_mut(chunk)
                    .zip(other.coeffs.chunks(chunk))
                {
                    scope.spawn(move |_| {
                        for (a, b) in a.iter_mut().zip(b.iter()) {
                            a.group_mul_assign(&b.0);
                        }
                    });
                }
            })
            .unwrap();
    }

    /// Perform O(n) subtraction of one polynomial from another in the domain.
    pub fn sub_assign(&mut self, worker: &Worker, other: &EvaluationDomain<E, G>) {
        assert_eq!(self.coeffs.len(), other.coeffs.len());

        worker
            .scope(self.coeffs.len(), |scope, chunk| {
                for (a, b) in self
                    .coeffs
                    .chunks_mut(chunk)
                    .zip(other.coeffs.chunks(chunk))
                {
                    scope.spawn(move |_| {
                        for (a, b) in a.iter_mut().zip(b.iter()) {
                            a.group_sub_assign(&b);
                        }
                    });
                }
            })
            .unwrap();
    }
}

pub trait Group<E: Engine>: Sized + Copy + Clone + Send + Sync {
    fn group_zero() -> Self;
    fn group_mul_assign(&mut self, by: &E::Fr);
    fn group_add_assign(&mut self, other: &Self);
    fn group_sub_assign(&mut self, other: &Self);
}

pub struct Point<G: CurveProjective>(pub G);

impl<G: CurveProjective> PartialEq for Point<G> {
    fn eq(&self, other: &Point<G>) -> bool {
        self.0 == other.0
    }
}

impl<G: CurveProjective> Copy for Point<G> {}

impl<G: CurveProjective> Clone for Point<G> {
    fn clone(&self) -> Point<G> {
        *self
    }
}

impl<G: CurveProjective> Group<G::Engine> for Point<G> {
    fn group_zero() -> Self {
        Point(G::zero())
    }
    fn group_mul_assign(&mut self, by: &G::Scalar) {
        self.0.mul_assign(by.into_repr());
    }
    fn group_add_assign(&mut self, other: &Self) {
        self.0.add_assign(&other.0);
    }
    fn group_sub_assign(&mut self, other: &Self) {
        self.0.sub_assign(&other.0);
    }
}

pub struct Scalar<E: Engine>(pub E::Fr);

impl<E: Engine> PartialEq for Scalar<E> {
    fn eq(&self, other: &Scalar<E>) -> bool {
        self.0 == other.0
    }
}

impl<E: Engine> Copy for Scalar<E> {}

impl<E: Engine> Clone for Scalar<E> {
    fn clone(&self) -> Scalar<E> {
        *self
    }
}

impl<E: Engine> Group<E> for Scalar<E> {
    fn group_zero() -> Self {
        Scalar(E::Fr::zero())
    }
    fn group_mul_assign(&mut self, by: &E::Fr) {
        self.0.mul_assign(by);
    }
    fn group_add_assign(&mut self, other: &Self) {
        self.0.add_assign(&other.0);
    }
    fn group_sub_assign(&mut self, other: &Self) {
        self.0.sub_assign(&other.0);
    }
}

fn best_fft<E: Engine, T: Group<E>>(kern: &mut Option<gpu::FFTKernel<E::Fr>>, a: &mut [T], worker: &Worker, omega: &E::Fr, log_n: u32)
{
    if let Some(ref mut k) = kern {
        gpu_fft(k, a, omega, log_n).expect("GPU FFT failed!");
    } else {
        let log_cpus = worker.log_num_cpus();
        if log_n <= log_cpus {
            serial_fft(a, omega, log_n);
        } else {
            parallel_fft(a, worker, omega, log_n, log_cpus);
        }
    }
}

pub fn gpu_fft<E: Engine, T: Group<E>>(kern: &mut gpu::FFTKernel<E::Fr>, a: &mut [T], omega: &E::Fr, log_n: u32) -> gpu::GPUResult<()>
{
    // EvaluationDomain module is supposed to work only with E::Fr elements, and not CurveProjective
    // points. The Bellman authors have implemented an unnecessarry abstraction called Group<E>
    // which is implemented for both PrimeField and CurveProjective elements. As nowhere in the code
    // is the CurveProjective version used, T and E::Fr are guaranteed to be equal and thus have same
    // size.
    // For compatibility/performance reasons we decided to transmute the array to the desired type
    // as it seems safe and needs less modifications in the current structure of Bellman library.
    let a = unsafe { std::mem::transmute::<&mut [T], &mut [E::Fr]>(a) };
    kern.radix_fft(a, omega, log_n)?;
    Ok(())
}

pub fn gpu_mul_by_field<E: Engine, T: Group<E>>(kern: &mut gpu::FFTKernel<E::Fr>, a: &mut [T], minv: &E::Fr, log_n: u32) -> gpu::GPUResult<()>
{
    // The reason of unsafety is same as above.
    let a = unsafe { std::mem::transmute::<&mut [T], &mut [E::Fr]>(a) };
    kern.mul_by_field(a, minv, log_n)?;
    Ok(())
}

pub fn serial_fft<E: Engine, T: Group<E>>(a: &mut [T], omega: &E::Fr, log_n: u32)
{
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
        let w_m = omega.pow(&[(n / (2 * m)) as u64]);

        let mut k = 0;
        while k < n {
            let mut w = E::Fr::one();
            for j in 0..m {
                let mut t = a[(k + j + m) as usize];
                t.group_mul_assign(&w);
                let mut tmp = a[(k + j) as usize];
                tmp.group_sub_assign(&t);
                a[(k + j + m) as usize] = tmp;
                a[(k + j) as usize].group_add_assign(&t);
                w.mul_assign(&w_m);
            }

            k += 2 * m;
        }

        m *= 2;
    }
}

fn parallel_fft<E: Engine, T: Group<E>>(
    a: &mut [T],
    worker: &Worker,
    omega: &E::Fr,
    log_n: u32,
    log_cpus: u32,
) {
    assert!(log_n >= log_cpus);

    let num_cpus = 1 << log_cpus;
    let log_new_n = log_n - log_cpus;
    let mut tmp = vec![vec![T::group_zero(); 1 << log_new_n]; num_cpus];
    let new_omega = omega.pow(&[num_cpus as u64]);

    worker
        .scope(0, |scope, _| {
            let a = &*a;

            for (j, tmp) in tmp.iter_mut().enumerate() {
                scope.spawn(move |_| {
                    // Shuffle into a sub-FFT
                    let omega_j = omega.pow(&[j as u64]);
                    let omega_step = omega.pow(&[(j as u64) << log_new_n]);

                    let mut elt = E::Fr::one();
                    for i in 0..(1 << log_new_n) {
                        for s in 0..num_cpus {
                            let idx = (i + (s << log_new_n)) % (1 << log_n);
                            let mut t = a[idx];
                            t.group_mul_assign(&elt);
                            tmp[i].group_add_assign(&t);
                            elt.mul_assign(&omega_step);
                        }
                        elt.mul_assign(&omega_j);
                    }

                    // Perform sub-FFT
                    serial_fft(tmp, &new_omega, log_new_n);
                });
            }
        })
        .unwrap();

    // TODO: does this hurt or help?
    worker
        .scope(a.len(), |scope, chunk| {
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
        })
        .unwrap();
}

// Test multiplying various (low degree) polynomials together and
// comparing with naive evaluations.
#[test]
fn polynomial_arith() {
    use paired::bls12_381::Bls12;
    use rand::{self, Rand};

    fn test_mul<E: Engine, R: rand::Rng>(rng: &mut R) {
        let worker = Worker::new();

        for coeffs_a in 0..70 {
            for coeffs_b in 0..70 {
                let mut a: Vec<_> = (0..coeffs_a)
                    .map(|_| Scalar::<E>(E::Fr::rand(rng)))
                    .collect();
                let mut b: Vec<_> = (0..coeffs_b)
                    .map(|_| Scalar::<E>(E::Fr::rand(rng)))
                    .collect();

                // naive evaluation
                let mut naive = vec![Scalar(E::Fr::zero()); coeffs_a + coeffs_b];
                for (i1, a) in a.iter().enumerate() {
                    for (i2, b) in b.iter().enumerate() {
                        let mut prod = *a;
                        prod.group_mul_assign(&b.0);
                        naive[i1 + i2].group_add_assign(&prod);
                    }
                }

                a.resize(coeffs_a + coeffs_b, Scalar(E::Fr::zero()));
                b.resize(coeffs_a + coeffs_b, Scalar(E::Fr::zero()));

                let mut a = EvaluationDomain::from_coeffs(a).unwrap();
                let mut b = EvaluationDomain::from_coeffs(b).unwrap();

                a.fft(&worker, &mut None);
                b.fft(&worker, &mut None);
                a.mul_assign(&worker, &b);
                a.ifft(&worker, &mut None);

                for (naive, fft) in naive.iter().zip(a.coeffs.iter()) {
                    assert!(naive == fft);
                }
            }
        }
    }

    let rng = &mut rand::thread_rng();

    test_mul::<Bls12, _>(rng);
}

#[test]
fn fft_composition() {
    use paired::bls12_381::Bls12;
    use rand;

    fn test_comp<E: Engine, R: rand::Rng>(rng: &mut R) {
        let worker = Worker::new();

        for coeffs in 0..10 {
            let coeffs = 1 << coeffs;

            let mut v = vec![];
            for _ in 0..coeffs {
                v.push(Scalar::<E>(rng.gen()));
            }

            let mut domain = EvaluationDomain::from_coeffs(v.clone()).unwrap();
            domain.ifft(&worker, &mut None);
            domain.fft(&worker, &mut None);
            assert!(v == domain.coeffs);
            domain.fft(&worker, &mut None);
            domain.ifft(&worker, &mut None);
            assert!(v == domain.coeffs);
            domain.icoset_fft(&worker, &mut None);
            domain.coset_fft(&worker, &mut None);
            assert!(v == domain.coeffs);
            domain.coset_fft(&worker, &mut None);
            domain.icoset_fft(&worker, &mut None);
            assert!(v == domain.coeffs);
        }
    }

    let rng = &mut rand::thread_rng();

    test_comp::<Bls12, _>(rng);
}

#[test]
fn parallel_fft_consistency() {
    use paired::bls12_381::Bls12;
    use rand::{self, Rand};
    use std::cmp::min;

    fn test_consistency<E: Engine, R: rand::Rng>(rng: &mut R) {
        let worker = Worker::new();

        for _ in 0..5 {
            for log_d in 0..10 {
                let d = 1 << log_d;

                let v1 = (0..d)
                    .map(|_| Scalar::<E>(E::Fr::rand(rng)))
                    .collect::<Vec<_>>();
                let mut v1 = EvaluationDomain::from_coeffs(v1).unwrap();
                let mut v2 = EvaluationDomain::from_coeffs(v1.coeffs.clone()).unwrap();

                for log_cpus in log_d..min(log_d + 1, 3) {
                    parallel_fft(&mut v1.coeffs, &worker, &v1.omega, log_d, log_cpus);
                    serial_fft(&mut v2.coeffs, &v2.omega, log_d);

                    assert!(v1.coeffs == v2.coeffs);
                }
            }
        }
    }

    let rng = &mut rand::thread_rng();

    test_consistency::<Bls12, _>(rng);
}

pub fn gpu_fft_supported<E>(log_d: u32) -> gpu::GPUResult<gpu::FFTKernel<E::Fr>> where E: Engine {
    let log_test_size : u32 = std::cmp::min(E::Fr::S - 1, 10);
    let test_size : u32 = 1 << log_test_size;
    use rand::Rand;
    let rng = &mut rand::thread_rng();
    let mut kern = gpu::FFTKernel::create(test_size)?;
    let elems = (0..test_size).map(|_| Scalar::<E>(E::Fr::rand(rng))).collect::<Vec<_>>();
    let mut v1 = EvaluationDomain::from_coeffs(elems.clone()).unwrap();
    let mut v2 = EvaluationDomain::from_coeffs(elems.clone()).unwrap();
    gpu_fft(&mut kern, &mut v1.coeffs, &v1.omega, log_test_size)?;
    serial_fft(&mut v2.coeffs, &v2.omega, log_test_size);
    if v1.coeffs == v2.coeffs { Ok(gpu::FFTKernel::create(1 << log_d)?) }
    else { Err(gpu::GPUError {msg: "GPU FFT not supported!".to_string()} ) }
}

#[cfg(feature = "gpu")]
#[test]
pub fn gpu_fft_consistency() {
    use std::time::Instant;
    use paired::bls12_381::{Bls12, Fr};
    use rand::{Rand};
    let rng = &mut rand::thread_rng();

    let worker = Worker::new();
    let log_cpus = worker.log_num_cpus();
    let mut kern = gpu::FFTKernel::create(1 << 24).expect("Cannot initialize kernel!");

    for log_d in 1..25 {
        let d = 1 << log_d;

        let elems = (0..d).map(|_| Scalar::<Bls12>(Fr::rand(rng))).collect::<Vec<_>>();
        let mut v1 = EvaluationDomain::from_coeffs(elems.clone()).unwrap();
        let mut v2 = EvaluationDomain::from_coeffs(elems.clone()).unwrap();

        println!("Testing FFT for {} elements...", d);

        let mut now = Instant::now();
        gpu_fft(&mut kern, &mut v1.coeffs, &v1.omega, log_d).expect("GPU FFT failed!");
        let gpu_dur = now.elapsed().as_secs() * 1000 as u64 + now.elapsed().subsec_millis() as u64;
        println!("GPU took {}ms.", gpu_dur);

        now = Instant::now();
        if log_d <= log_cpus { serial_fft(&mut v2.coeffs, &v2.omega, log_d); }
        else { parallel_fft(&mut v2.coeffs, &worker, &v2.omega, log_d, log_cpus); }
        let cpu_dur = now.elapsed().as_secs() * 1000 as u64 + now.elapsed().subsec_millis() as u64;
        println!("CPU ({} cores) took {}ms.", 1 << log_cpus, cpu_dur);

        println!("Speedup: x{}", cpu_dur as f32 / gpu_dur as f32);

        assert!(v1.coeffs == v2.coeffs);
        println!("============================");
    }
}
