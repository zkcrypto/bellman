use crate::SynthesisError;
use ff::{Field, PrimeField, PrimeFieldRepr, ScalarEngine};
use pairing::{CurveAffine, CurveProjective, Engine};

pub trait ChainExt: Iterator {
    fn chain_ext<U>(self, other: U) -> Chain<Self, U::IntoIter>
    where
        Self: Sized,
        U: IntoIterator<Item = Self::Item>,
    {
        Chain {
            t: self,
            u: other.into_iter(),
        }
    }
}

impl<I: Iterator> ChainExt for I {}

#[derive(Clone)]
pub struct Chain<T, U> {
    t: T,
    u: U,
}

impl<T, U> Iterator for Chain<T, U>
where
    T: Iterator,
    U: Iterator<Item = T::Item>,
{
    type Item = T::Item;

    fn next(&mut self) -> Option<T::Item> {
        match self.t.next() {
            Some(v) => Some(v),
            None => match self.u.next() {
                Some(v) => Some(v),
                None => None,
            },
        }
    }
}

impl<T, U> ExactSizeIterator for Chain<T, U>
where
    T: Iterator,
    U: Iterator<Item = T::Item>,
    T: ExactSizeIterator,
    U: ExactSizeIterator,
{
    fn len(&self) -> usize {
        self.t.len() + self.u.len()
    }
}

impl<T, U> DoubleEndedIterator for Chain<T, U>
where
    T: Iterator,
    U: Iterator<Item = T::Item>,
    T: DoubleEndedIterator,
    U: DoubleEndedIterator,
{
    fn next_back(&mut self) -> Option<T::Item> {
        match self.u.next_back() {
            Some(v) => Some(v),
            None => match self.t.next_back() {
                Some(v) => Some(v),
                None => None,
            },
        }
    }
}

pub fn multiexp<
    'a,
    G: CurveAffine,
    IB: IntoIterator<Item = &'a G>,
    IS: IntoIterator<Item = &'a G::Scalar>,
>(
    g: IB,
    s: IS,
) -> G::Projective
where
    IB::IntoIter: ExactSizeIterator + Clone,
    IS::IntoIter: ExactSizeIterator,
{
    use std::sync::Arc;
    use futures::Future;
    use ff::PrimeFieldRepr;
    use pairing::CurveAffine;

    use crate::multicore::Worker;
    use crate::multiexp;
    use crate::multiexp::FullDensity;

    let s: Arc<Vec<<G::Scalar as PrimeField>::Repr>> = Arc::new(s.into_iter().map(|e| e.into_repr()).collect::<Vec<_>>());
    let g: Arc<Vec<G>> = Arc::new(g.into_iter().map(|e| *e).collect::<Vec<_>>());

    let pool = Worker::new();

    let result = multiexp::multiexp(
        &pool,
        (g, 0),
        FullDensity,
        s
    ).wait().unwrap();

    result
}

pub fn multiexp_serial<
    'a,
    G: CurveAffine,
    IB: IntoIterator<Item = &'a G>,
    IS: IntoIterator<Item = &'a G::Scalar>,
>(
    g: IB,
    s: IS,
) -> G::Projective
where
    IB::IntoIter: ExactSizeIterator + Clone,
    IS::IntoIter: ExactSizeIterator,
{
    let g = g.into_iter();
    let s = s.into_iter();
    assert_eq!(g.len(), s.len());

    let c = if s.len() < 32 {
        3u32
    } else {
        (f64::from(s.len() as u32)).ln().ceil() as u32
    };

    // Convert all of the scalars into representations
    let mut s = s.map(|s| s.into_repr()).collect::<Vec<_>>();

    let mut windows = vec![];
    let mut buckets = vec![];

    let mask = (1u64 << c) - 1u64;
    let mut cur = 0;
    let num_bits = <G::Engine as ScalarEngine>::Fr::NUM_BITS;
    while cur <= num_bits {
        let mut acc = G::Projective::zero();

        buckets.truncate(0);
        buckets.resize((1 << c) - 1, G::Projective::zero());

        let g = g.clone();

        for (s, g) in s.iter_mut().zip(g) {
            let index = (s.as_ref()[0] & mask) as usize;

            if index != 0 {
                buckets[index - 1].add_assign_mixed(g);
            }

            s.shr(c as u32);
        }

        let mut running_sum = G::Projective::zero();
        for exp in buckets.iter().rev() {
            running_sum.add_assign(exp);
            acc.add_assign(&running_sum);
        }

        windows.push(acc);

        cur += c;
    }

    let mut acc = G::Projective::zero();

    for window in windows.into_iter().rev() {
        for _ in 0..c {
            acc.double();
        }

        acc.add_assign(&window);
    }

    acc
}

/// Divides polynomial `a` in `x` by `x - b` with
/// no remainder.
pub fn kate_divison<'a, F: Field, I: IntoIterator<Item = &'a F>>(a: I, mut b: F) -> Vec<F>
where
    I::IntoIter: DoubleEndedIterator + ExactSizeIterator,
{
    b.negate();
    let a = a.into_iter();

    let mut q = vec![F::zero(); a.len() - 1];

    let mut tmp = F::zero();
    for (q, r) in q.iter_mut().rev().zip(a.rev()) {
        let mut lead_coeff = *r;
        lead_coeff.sub_assign(&tmp);
        *q = lead_coeff;
        tmp = lead_coeff;
        tmp.mul_assign(&b);
    }

    q
}

#[test]
fn laurent_division() {
    use ff::PrimeField;
    use pairing::bls12_381::{Fr};

    let mut poly = vec![
        Fr::from_str("328947234").unwrap(),
        Fr::from_str("3545623451111").unwrap(),
        Fr::from_str("112").unwrap(),
        Fr::from_str("55555").unwrap(),
        Fr::from_str("1235685").unwrap(),
    ];

    fn eval(poly: &[Fr], point: Fr) -> Fr {
        let point_inv = point.inverse().unwrap();

        let mut acc = Fr::zero();
        let mut tmp = Fr::one();
        for p in &poly[2..] {
            let mut t = *p;
            t.mul_assign(&tmp);
            acc.add_assign(&t);
            tmp.mul_assign(&point);
        }
        let mut tmp = point_inv;
        for p in poly[0..2].iter().rev() {
            let mut t = *p;
            t.mul_assign(&tmp);
            acc.add_assign(&t);
            tmp.mul_assign(&point_inv);
        }

        acc
    }

    let x = Fr::from_str("23").unwrap();
    let z = Fr::from_str("2000").unwrap();

    let p_at_x = eval(&poly, x);
    let p_at_z = eval(&poly, z);

    // poly = poly(X) - poly(z)
    poly[2].sub_assign(&p_at_z);

    let quotient_poly = kate_divison(&poly, z);

    let quotient = eval(&quotient_poly, x);

    // check that
    // quotient * (x - z) = p_at_x - p_at_z

    let mut lhs = x;
    lhs.sub_assign(&z);
    lhs.mul_assign(&quotient);

    let mut rhs = p_at_x;
    rhs.sub_assign(&p_at_z);

    assert_eq!(lhs, rhs);
}

pub fn multiply_polynomials<E: Engine>(a: Vec<E::Fr>, b: Vec<E::Fr>) -> Vec<E::Fr> {
    println!("Multiplying polynomails of degrees {} and {}", a.len(), b.len());
    let result_len = a.len() + b.len() - 1;

    use crate::multicore::Worker;
    use crate::domain::{EvaluationDomain, Scalar};

    let worker = Worker::new();
    let scalars_a: Vec<Scalar<E>> = a.into_iter().map(|e| Scalar::<E>(e)).collect();
    let mut domain_a = EvaluationDomain::from_coeffs_into_sized(scalars_a, result_len).unwrap();

    let scalars_b: Vec<Scalar<E>> = b.into_iter().map(|e| Scalar::<E>(e)).collect();
    let mut domain_b = EvaluationDomain::from_coeffs_into_sized(scalars_b, result_len).unwrap();

    domain_a.fft(&worker);
    domain_b.fft(&worker);

    domain_a.mul_assign(&worker, &domain_b);
    drop(domain_b);

    domain_a.ifft(&worker);

    let mut mul_result: Vec<E::Fr> = domain_a.into_coeffs().iter().map(|e| e.0).collect();

    mul_result.truncate(result_len);

    mul_result
}

pub fn multiply_polynomials_serial<E: Engine>(mut a: Vec<E::Fr>, mut b: Vec<E::Fr>) -> Vec<E::Fr> {
    let result_len = a.len() + b.len() - 1;

    // Compute the size of our evaluation domain
    let mut m = 1;
    let mut exp = 0;
    while m < result_len {
        m *= 2;
        exp += 1;

        // The pairing-friendly curve may not be able to support
        // large enough (radix2) evaluation domains.
        if exp >= E::Fr::S {
            panic!("polynomial too large")
        }
    }

    // Compute omega, the 2^exp primitive root of unity
    let mut omega = E::Fr::root_of_unity();
    for _ in exp..E::Fr::S {
        omega.square();
    }

    // Extend with zeroes
    a.resize(m, E::Fr::zero());
    b.resize(m, E::Fr::zero());

    serial_fft::<E>(&mut a[..], &omega, exp);
    serial_fft::<E>(&mut b[..], &omega, exp);

    for (a, b) in a.iter_mut().zip(b.iter()) {
        a.mul_assign(b);
    }

    serial_fft::<E>(&mut a[..], &omega.inverse().unwrap(), exp);

    a.truncate(result_len);

    let minv = E::Fr::from_str(&format!("{}", m))
        .unwrap()
        .inverse()
        .unwrap();

    for a in a.iter_mut() {
        a.mul_assign(&minv);
    }

    a
}

fn serial_fft<E: Engine>(a: &mut [E::Fr], omega: &E::Fr, log_n: u32) {
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
                t.mul_assign(&w);
                let mut tmp = a[(k + j) as usize];
                tmp.sub_assign(&t);
                a[(k + j + m) as usize] = tmp;
                a[(k + j) as usize].add_assign(&t);
                w.mul_assign(&w_m);
            }

            k += 2 * m;
        }

        m *= 2;
    }
}

pub trait OptionExt<T> {
    fn get(self) -> Result<T, SynthesisError>;
}

impl<T> OptionExt<T> for Option<T> {
    fn get(self) -> Result<T, SynthesisError> {
        match self {
            Some(t) => Ok(t),
            None => Err(SynthesisError::AssignmentMissing),
        }
    }
}

#[test]

fn test_mul() {
    use rand::{self, Rand};
    use pairing::bls12_381::Bls12;
    use pairing::bls12_381::Fr;

    const SAMPLES: usize = 100;

    let rng = &mut rand::thread_rng();
    let a = (0..SAMPLES).map(|_| Fr::rand(rng)).collect::<Vec<_>>();
    let b = (0..SAMPLES).map(|_| Fr::rand(rng)).collect::<Vec<_>>();

    let serial_res = multiply_polynomials_serial::<Bls12>(a.clone(), b.clone());
    let parallel_res = multiply_polynomials::<Bls12>(a, b);

    assert_eq!(serial_res.len(), parallel_res.len());
    assert_eq!(serial_res, parallel_res);
}