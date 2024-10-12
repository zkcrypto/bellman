//! This module contains an [`EvaluationDomain`] abstraction for performing
//! various kinds of polynomial arithmetic on top of the scalar field.
//!
//! In pairing-based SNARKs like [Groth16], we need to calculate a quotient
//! polynomial over a target polynomial with roots at distinct points associated
//! with each constraint of the constraint system. In order to be efficient, we
//! choose these roots to be the powers of a 2<sup>n</sup> root of unity in the
//! field. This allows us to perform polynomial operations in O(n) by performing
//! an O(n log n) FFT over such a domain.
//!
//! [`EvaluationDomain`]: crate::domain::EvaluationDomain
//! [Groth16]: https://eprint.iacr.org/2016/260

use ff::PrimeField;
use group::cofactor::CofactorCurve;
use rayon::join;

use super::SynthesisError;

use super::multicore::Worker;

pub struct EvaluationDomain<S: PrimeField, G: Group<S>> {
    coeffs: Vec<G>,
    exp: u32,
    omega: S,
    omegainv: S,
    geninv: S,
    minv: S,
}

impl<S: PrimeField, G: Group<S>> AsRef<[G]> for EvaluationDomain<S, G> {
    fn as_ref(&self) -> &[G] {
        &self.coeffs
    }
}

impl<S: PrimeField, G: Group<S>> AsMut<[G]> for EvaluationDomain<S, G> {
    fn as_mut(&mut self) -> &mut [G] {
        &mut self.coeffs
    }
}

impl<S: PrimeField, G: Group<S>> EvaluationDomain<S, G> {
    pub fn into_coeffs(self) -> Vec<G> {
        self.coeffs
    }

    pub fn from_coeffs(mut coeffs: Vec<G>) -> Result<EvaluationDomain<S, G>, SynthesisError> {
        // Compute the size of our evaluation domain
        let mut m = 1;
        let mut exp = 0;
        while m < coeffs.len() {
            m *= 2;
            exp += 1;

            // The pairing-friendly curve may not be able to support
            // large enough (radix2) evaluation domains.
            if exp >= S::S {
                return Err(SynthesisError::PolynomialDegreeTooLarge);
            }
        }

        // Compute omega, the 2^exp primitive root of unity
        let mut omega = S::ROOT_OF_UNITY;
        for _ in exp..S::S {
            omega = omega.square();
        }

        // Extend the coeffs vector with zeroes if necessary
        coeffs.resize(m, G::group_zero());

        Ok(EvaluationDomain {
            coeffs,
            exp,
            omega,
            omegainv: omega.invert().unwrap(),
            geninv: S::MULTIPLICATIVE_GENERATOR.invert().unwrap(),
            minv: S::from(m as u64).invert().unwrap(),
        })
    }

    pub fn fft(&mut self, worker: &Worker) {
        best_fft(&mut self.coeffs, worker, &self.omega, self.exp);
    }

    pub fn ifft(&mut self, worker: &Worker) {
        best_fft(&mut self.coeffs, worker, &self.omegainv, self.exp);

        worker.scope(self.coeffs.len(), |scope, chunk| {
            let minv = self.minv;

            for v in self.coeffs.chunks_mut(chunk) {
                scope.spawn(move |_scope| {
                    for v in v {
                        v.group_mul_assign(&minv);
                    }
                });
            }
        });
    }

    pub fn distribute_powers(&mut self, worker: &Worker, g: S) {
        worker.scope(self.coeffs.len(), |scope, chunk| {
            for (i, v) in self.coeffs.chunks_mut(chunk).enumerate() {
                scope.spawn(move |_scope| {
                    let mut u = g.pow_vartime(&[(i * chunk) as u64]);
                    for v in v.iter_mut() {
                        v.group_mul_assign(&u);
                        u.mul_assign(&g);
                    }
                });
            }
        });
    }

    pub fn coset_fft(&mut self, worker: &Worker) {
        self.distribute_powers(worker, S::MULTIPLICATIVE_GENERATOR);
        self.fft(worker);
    }

    pub fn icoset_fft(&mut self, worker: &Worker) {
        let geninv = self.geninv;

        self.ifft(worker);
        self.distribute_powers(worker, geninv);
    }

    /// This evaluates t(tau) for this domain, which is
    /// tau^m - 1 for these radix-2 domains.
    pub fn z(&self, tau: &S) -> S {
        let mut tmp = tau.pow_vartime(&[self.coeffs.len() as u64]);
        tmp.sub_assign(&S::ONE);

        tmp
    }

    /// The target polynomial is the zero polynomial in our
    /// evaluation domain, so we must perform division over
    /// a coset.
    pub fn divide_by_z_on_coset(&mut self, worker: &Worker) {
        let i = self.z(&S::MULTIPLICATIVE_GENERATOR).invert().unwrap();

        worker.scope(self.coeffs.len(), |scope, chunk| {
            for v in self.coeffs.chunks_mut(chunk) {
                scope.spawn(move |_scope| {
                    for v in v {
                        v.group_mul_assign(&i);
                    }
                });
            }
        });
    }

    /// Perform O(n) multiplication of two polynomials in the domain.
    pub fn mul_assign(&mut self, worker: &Worker, other: &EvaluationDomain<S, Scalar<S>>) {
        assert_eq!(self.coeffs.len(), other.coeffs.len());

        worker.scope(self.coeffs.len(), |scope, chunk| {
            for (a, b) in self
                .coeffs
                .chunks_mut(chunk)
                .zip(other.coeffs.chunks(chunk))
            {
                scope.spawn(move |_scope| {
                    for (a, b) in a.iter_mut().zip(b.iter()) {
                        a.group_mul_assign(&b.0);
                    }
                });
            }
        });
    }

    /// Perform O(n) subtraction of one polynomial from another in the domain.
    pub fn sub_assign(&mut self, worker: &Worker, other: &EvaluationDomain<S, G>) {
        assert_eq!(self.coeffs.len(), other.coeffs.len());

        worker.scope(self.coeffs.len(), |scope, chunk| {
            for (a, b) in self
                .coeffs
                .chunks_mut(chunk)
                .zip(other.coeffs.chunks(chunk))
            {
                scope.spawn(move |_scope| {
                    for (a, b) in a.iter_mut().zip(b.iter()) {
                        a.group_sub_assign(b);
                    }
                });
            }
        });
    }
}

pub trait Group<Scalar: PrimeField>: Sized + Copy + Clone + Send + Sync {
    fn group_zero() -> Self;
    fn group_mul_assign(&mut self, by: &Scalar);
    fn group_add_assign(&mut self, other: &Self);
    fn group_sub_assign(&mut self, other: &Self);
}

pub struct Point<G: CofactorCurve>(pub G);

impl<G: CofactorCurve> PartialEq for Point<G> {
    fn eq(&self, other: &Point<G>) -> bool {
        self.0 == other.0
    }
}

impl<G: CofactorCurve> Copy for Point<G> {}

impl<G: CofactorCurve> Clone for Point<G> {
    fn clone(&self) -> Point<G> {
        *self
    }
}

impl<G: CofactorCurve> Group<G::Scalar> for Point<G> {
    fn group_zero() -> Self {
        Point(G::identity())
    }
    fn group_mul_assign(&mut self, by: &G::Scalar) {
        self.0.mul_assign(by);
    }
    fn group_add_assign(&mut self, other: &Self) {
        self.0.add_assign(&other.0);
    }
    fn group_sub_assign(&mut self, other: &Self) {
        self.0.sub_assign(&other.0);
    }
}

pub struct Scalar<S: PrimeField>(pub S);

impl<S: PrimeField> PartialEq for Scalar<S> {
    fn eq(&self, other: &Scalar<S>) -> bool {
        self.0 == other.0
    }
}

impl<S: PrimeField> Copy for Scalar<S> {}

impl<S: PrimeField> Clone for Scalar<S> {
    fn clone(&self) -> Scalar<S> {
        *self
    }
}

impl<S: PrimeField> Group<S> for Scalar<S> {
    fn group_zero() -> Self {
        Scalar(S::ZERO)
    }
    fn group_mul_assign(&mut self, by: &S) {
        self.0.mul_assign(by);
    }
    fn group_add_assign(&mut self, other: &Self) {
        self.0.add_assign(&other.0);
    }
    fn group_sub_assign(&mut self, other: &Self) {
        self.0.sub_assign(&other.0);
    }
}

fn best_fft<S: PrimeField, T: Group<S>>(a: &mut [T], worker: &Worker, omega: &S, log_n: u32) {
    let n = a.len();
    assert_eq!(n, 1 << log_n);
    if log_n == 0 {
        return;
    }
    let log_cpus = worker.log_num_threads();

    let offset = 64 - log_n;
    for i in 0..n as u64 {
        let ri = i.reverse_bits() >> offset;
        if i < ri {
            a.swap(ri as usize, i as usize);
        }
    }

    // precompute twiddle factors
    let twiddles: Vec<_> = (0..(n / 2))
        .scan(S::ONE, |w, _| {
            let tw = *w;
            *w *= omega;
            Some(tw)
        })
        .collect();

    if log_n <= log_cpus {
        serial_fft(a, n, log_n, &twiddles);
    } else {
        parallel_fft(a, n, 1, &twiddles);
    }
}

#[allow(clippy::many_single_char_names)]
fn serial_fft<S: PrimeField, T: Group<S>>(a: &mut [T], n: usize, log_n: u32, twiddles: &[S]) {
    let mut chunk = 2_usize;
    let mut twiddle_chunk = n / 2;
    for _ in 0..log_n {
        a.chunks_mut(chunk).for_each(|coeffs| {
            let (left, right) = coeffs.split_at_mut(chunk / 2);

            // case when twiddle factor is one
            let (a, left) = left.split_at_mut(1);
            let (b, right) = right.split_at_mut(1);
            let t = b[0];
            b[0] = a[0];
            a[0].group_add_assign(&t);
            b[0].group_sub_assign(&t);

            left.iter_mut()
                .zip(right.iter_mut())
                .enumerate()
                .for_each(|(i, (a, b))| {
                    let mut t = *b;
                    t.group_mul_assign(&twiddles[(i + 1) * twiddle_chunk as usize]);
                    *b = *a;
                    a.group_add_assign(&t);
                    b.group_sub_assign(&t);
                });
        });
        chunk *= 2;
        twiddle_chunk /= 2;
    }
}

pub fn parallel_fft<S: PrimeField, T: Group<S>>(
    a: &mut [T],
    n: usize,
    twiddle_chunk: usize,
    twiddles: &[S],
) {
    if n == 2 {
        let t = a[1];
        a[1] = a[0];
        a[0].group_add_assign(&t);
        a[1].group_sub_assign(&t);
    } else {
        let (left, right) = a.split_at_mut(n / 2);
        join(
            || parallel_fft(left, n / 2, twiddle_chunk * 2, twiddles),
            || parallel_fft(right, n / 2, twiddle_chunk * 2, twiddles),
        );

        // case when twiddle factor is one
        let (a, left) = left.split_at_mut(1);
        let (b, right) = right.split_at_mut(1);
        let t = b[0];
        b[0] = a[0];
        a[0].group_add_assign(&t);
        b[0].group_sub_assign(&t);

        left.iter_mut()
            .zip(right.iter_mut())
            .enumerate()
            .for_each(|(i, (a, b))| {
                let mut t = *b;
                t.group_mul_assign(&twiddles[(i + 1) * twiddle_chunk]);
                *b = *a;
                a.group_add_assign(&t);
                b.group_sub_assign(&t);
            });
    }
}

// Test multiplying various (low degree) polynomials together and
// comparing with naive evaluations.
#[cfg(feature = "pairing")]
#[test]
fn polynomial_arith() {
    use bls12_381::Scalar as Fr;
    use rand_core::RngCore;

    fn test_mul<S: PrimeField, R: RngCore>(mut rng: &mut R) {
        let worker = Worker::new();

        for coeffs_a in 0..70 {
            for coeffs_b in 0..70 {
                let mut a: Vec<_> = (0..coeffs_a)
                    .map(|_| Scalar::<S>(S::random(&mut rng)))
                    .collect();
                let mut b: Vec<_> = (0..coeffs_b)
                    .map(|_| Scalar::<S>(S::random(&mut rng)))
                    .collect();

                // naive evaluation
                let mut naive = vec![Scalar(S::ZERO); coeffs_a + coeffs_b];
                for (i1, a) in a.iter().enumerate() {
                    for (i2, b) in b.iter().enumerate() {
                        let mut prod = *a;
                        prod.group_mul_assign(&b.0);
                        naive[i1 + i2].group_add_assign(&prod);
                    }
                }

                a.resize(coeffs_a + coeffs_b, Scalar(S::ZERO));
                b.resize(coeffs_a + coeffs_b, Scalar(S::ZERO));

                let mut a = EvaluationDomain::from_coeffs(a).unwrap();
                let mut b = EvaluationDomain::from_coeffs(b).unwrap();

                a.fft(&worker);
                b.fft(&worker);
                a.mul_assign(&worker, &b);
                a.ifft(&worker);

                for (naive, fft) in naive.iter().zip(a.coeffs.iter()) {
                    assert!(naive == fft);
                }
            }
        }
    }

    let rng = &mut rand::thread_rng();

    test_mul::<Fr, _>(rng);
}

#[cfg(feature = "pairing")]
#[test]
fn fft_composition() {
    use bls12_381::Scalar as Fr;
    use rand_core::RngCore;

    fn test_comp<S: PrimeField, R: RngCore>(mut rng: &mut R) {
        let worker = Worker::new();

        for coeffs in 0..10 {
            let coeffs = 1 << coeffs;

            let mut v = vec![];
            for _ in 0..coeffs {
                v.push(Scalar::<S>(S::random(&mut rng)));
            }

            let mut domain = EvaluationDomain::from_coeffs(v.clone()).unwrap();
            domain.ifft(&worker);
            domain.fft(&worker);
            assert!(v == domain.coeffs);
            domain.fft(&worker);
            domain.ifft(&worker);
            assert!(v == domain.coeffs);
            domain.icoset_fft(&worker);
            domain.coset_fft(&worker);
            assert!(v == domain.coeffs);
            domain.coset_fft(&worker);
            domain.icoset_fft(&worker);
            assert!(v == domain.coeffs);
        }
    }

    let rng = &mut rand::thread_rng();

    test_comp::<Fr, _>(rng);
}

#[cfg(feature = "pairing")]
#[test]
fn parallel_fft_consistency() {
    use bls12_381::Scalar as Fr;
    use rand_core::RngCore;

    fn test_consistency<S: PrimeField, R: RngCore>(mut rng: &mut R) {
        for _ in 0..5 {
            for log_n in 1..10 {
                let n = 1 << log_n;

                let v1 = (0..n)
                    .map(|_| Scalar::<S>(S::random(&mut rng)))
                    .collect::<Vec<_>>();
                let mut v1 = EvaluationDomain::from_coeffs(v1).unwrap();
                let mut v2 = EvaluationDomain::from_coeffs(v1.coeffs.clone()).unwrap();
                let twiddles: Vec<_> = (0..(n / 2))
                    .scan(S::ONE, |w, _| {
                        let tw = *w;
                        *w *= v2.omega;
                        Some(tw)
                    })
                    .collect();

                serial_fft(&mut v1.coeffs, n, log_n, &twiddles);
                parallel_fft(&mut v2.coeffs, n, 1, &twiddles);
                assert!(v1.coeffs == v2.coeffs);
            }
        }
    }

    let rng = &mut rand::thread_rng();

    test_consistency::<Fr, _>(rng);
}
