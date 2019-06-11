use crate::SynthesisError;
use crate::pairing::ff::{Field, PrimeField, PrimeFieldRepr, ScalarEngine};
use crate::pairing::{CurveAffine, CurveProjective, Engine};
use super::srs::SRS;

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

pub fn polynomial_commitment<
        'a,
        E: Engine,
        IS: IntoIterator<Item = &'a E::Fr>,
    >(
        max: usize,
        largest_negative_power: usize,
        largest_positive_power: usize,
        srs: &'a SRS<E>,
        s: IS,
    ) -> E::G1Affine
    where
        IS::IntoIter: ExactSizeIterator,
    {
        // smallest power is d - max - largest_negative_power; It should either be 0 for use of positive powers only,
        // of we should use part of the negative powers
        let d = srs.d;
        assert!(max >= largest_positive_power);
        // use both positive and negative powers for commitment
        if d < max + largest_negative_power + 1 {
            let min_power = largest_negative_power + max - d;
            let max_power = d + largest_positive_power - max;
            // need to use negative powers to make a proper commitment
            return multiexp(
                srs.g_negative_x_alpha[0..min_power].iter().rev()
                .chain_ext(srs.g_positive_x_alpha[..max_power].iter()),
                s
            ).into_affine();
        } else {
            return multiexp(
                srs.g_positive_x_alpha[(srs.d - max - largest_negative_power - 1)..].iter(),
                s
            ).into_affine();
        }
    }


/// For now this function MUST take a polynomial in a form f(x) - f(z)
pub fn polynomial_commitment_opening<
        'a,
        E: Engine,
        I: IntoIterator<Item = &'a E::Fr>
    >(
        largest_negative_power: usize,
        _largest_positive_power: usize,
        polynomial_coefficients: I,
        point: E::Fr,
        srs: &'a SRS<E>,
    ) -> E::G1Affine
        where I::IntoIter: DoubleEndedIterator + ExactSizeIterator,
    {
        // let poly = parallel_kate_divison::<E, _>(polynomial_coefficients, point);

        // use std::time::Instant;
        // let start = Instant::now();

        let poly = kate_divison(
            polynomial_coefficients,
            point,
        );

        // println!("Kate division of size {} taken {:?}", poly.len(), start.elapsed());

        let negative_poly = poly[0..largest_negative_power].iter().rev();
        let positive_poly = poly[largest_negative_power..].iter();
        multiexp(
            srs.g_negative_x[1..(negative_poly.len() + 1)].iter().chain_ext(
                srs.g_positive_x[0..positive_poly.len()].iter()
            ),
            negative_poly.chain_ext(positive_poly)
        ).into_affine()
    }

extern crate crossbeam;
use self::crossbeam::channel::{unbounded};

pub fn evaluate_at_consequitive_powers<'a, F: Field> (
    coeffs: &[F],
    first_power: F,
    base: F
) -> F
    {
    use crate::multicore::Worker;

    let (s, r) = unbounded();

    let worker = Worker::new();

    worker.scope(coeffs.len(), |scope, chunk| {
        for (i, coeffs) in coeffs.chunks(chunk).enumerate()
        {
            let s = s.clone();
            scope.spawn(move |_| {
                let mut current_power = base.pow(&[(i*chunk) as u64]);
                current_power.mul_assign(&first_power);

                let mut acc = F::zero();

                for p in coeffs {
                    let mut tmp = *p;
                    tmp.mul_assign(&current_power);
                    acc.add_assign(&tmp);

                    current_power.mul_assign(&base);
                }

                s.send(acc).expect("must send");
            });
        }
    });

    drop(s);

    // all threads in a scope have done working, so we can safely read
    let mut result = F::zero();

    loop {
        if r.is_empty() {
            break;
        }
        let value = r.recv().expect("must not be empty");
        result.add_assign(&value);
    }

    result
}

pub fn mut_evaluate_at_consequitive_powers<'a, F: Field> (
    coeffs: &mut [F],
    first_power: F,
    base: F
) -> F
    {
    use crate::multicore::Worker;

    let (s, r) = unbounded();

    let worker = Worker::new();

    worker.scope(coeffs.len(), |scope, chunk| {
        for (i, coeffs) in coeffs.chunks_mut(chunk).enumerate()
        {
            let s = s.clone();
            scope.spawn(move |_| {
                let mut current_power = base.pow(&[(i*chunk) as u64]);
                current_power.mul_assign(&first_power);

                let mut acc = F::zero();

                for p in coeffs {
                    p.mul_assign(&current_power);
                    acc.add_assign(&p);

                    current_power.mul_assign(&base);
                }

                s.send(acc).expect("must send");
            });
        }
    });

    drop(s);

    // all threads in a scope have done working, so we can safely read
    let mut result = F::zero();

    loop {
        if r.is_empty() {
            break;
        }
        let value = r.recv().expect("must not be empty");
        result.add_assign(&value);
    }

    result
}

/// Multiply each coefficient by some power of the base in a form
/// `first_power * base^{i}`
pub fn mut_distribute_consequitive_powers<'a, F: Field> (
    coeffs: &mut [F],
    first_power: F,
    base: F
)
    {
    use crate::multicore::Worker;

    let worker = Worker::new();

    worker.scope(coeffs.len(), |scope, chunk| {
        for (i, coeffs_chunk) in coeffs.chunks_mut(chunk).enumerate()
        {
            scope.spawn(move |_| {
                let mut current_power = base.pow(&[(i*chunk) as u64]);
                current_power.mul_assign(&first_power);

                for p in coeffs_chunk {
                    p.mul_assign(&current_power);

                    current_power.mul_assign(&base);
                }
            });
        }
    });
}

// pub fn multiexp<
//     'a,
//     G: CurveAffine,
//     IB: IntoIterator<Item = &'a G>,
//     IS: IntoIterator<Item = &'a G::Scalar>,
// >(
//     g: IB,
//     s: IS,
// ) -> G::Projective
// where
//     IB::IntoIter: ExactSizeIterator + Clone,
//     IS::IntoIter: ExactSizeIterator,
// {
//     use crate::multicore::Worker;
//     use crate::multiexp::dense_multiexp;

//     use std::time::Instant;
//     let start = Instant::now();

//     let s: Vec<<G::Scalar as PrimeField>::Repr> = s.into_iter().map(|e| e.into_repr()).collect::<Vec<_>>();
//     let g: Vec<G> = g.into_iter().map(|e| *e).collect::<Vec<_>>();

//     println!("Multiexp collecting taken {:?}", start.elapsed());

//     assert_eq!(s.len(), g.len(), "scalars and exponents must have the same length");

//     let start = Instant::now();
//     let pool = Worker::new();
//     println!("Multiexp pool creation taken {:?}", start.elapsed());

//     let start = Instant::now();

//     let result = dense_multiexp(
//         &pool,
//         &g,
//         &s
//     ).unwrap();

//     println!("Multiexp taken {:?}", start.elapsed());

//     result
// }

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
    use crate::multicore::Worker;
    use crate::multiexp::multiexp;
    use crate::source::FullDensity;
    use futures::Future;
    use std::sync::Arc;

    let s: Vec<<G::Scalar as PrimeField>::Repr> = s.into_iter().map(|e| e.into_repr()).collect::<Vec<_>>();
    let g: Vec<G> = g.into_iter().map(|e| *e).collect::<Vec<_>>();

    assert_eq!(s.len(), g.len(), "scalars and exponents must have the same length");

    let pool = Worker::new();

    // use std::time::Instant;
    // let start = Instant::now();

    let result = multiexp(
        &pool,
        (Arc::new(g), 0),
        FullDensity,
        Arc::new(s)
    ).wait().unwrap();

    // println!("Multiexp taken {:?}", start.elapsed());

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

/// Divides polynomial `a` in `x` by `x - b` with
/// no remainder using fft.
pub fn parallel_kate_divison<'a, E: Engine, I: IntoIterator<Item = &'a E::Fr>>(a: I, b: E::Fr) -> Vec<E::Fr>
where
    I::IntoIter: DoubleEndedIterator + ExactSizeIterator,
{
    // this implementation is only for division by `x - b` form polynomail,
    // so we can manuall calculate the reciproical poly of the form `x^2/(x-b)`
    // and the reminder

    // x^2 /(x - b) = x + b*x/(x - b) = (x + b) + b^2/(x - b)

    let reciproical = vec![b, E::Fr::one()]; // x + b

    // and remainder b^2
    let mut b_squared = b;
    b_squared.square();

    let mut b_neg = b;
    b_neg.negate();

    let divisor = vec![b_neg, E::Fr::one()];

    let poly: Vec<E::Fr> = a.into_iter().map(|el| el.clone()).collect();

    let (q, _) = kate_divison_inner::<E>(poly, divisor, reciproical, b_squared);

    // assert_eq!(r.len(), 0);

    q
}

fn kate_divison_inner<E: Engine>(
        poly: Vec<E::Fr>, 
        divisor: Vec<E::Fr>, 
        reciproical: Vec<E::Fr>, 
        remainder: E::Fr
    ) -> (Vec<E::Fr>, Vec<E::Fr>) {
    if poly.len() == 1 {
        return (vec![], poly);
    }
    // TODO: Change generic multiplications by multiplications by degree 1 polynomial
    let poly_degree = poly.len() - 1;
    let mut q = multiply_polynomials::<E>(poly.clone(), reciproical.clone());
    q.drain(0..2);
    // recursion step
    if poly_degree > 2 {
        let mut rec_step = poly.clone();
        mul_polynomial_by_scalar(&mut rec_step[..], remainder);
        // truncate low order terms 
        rec_step.drain(0..2);
        let (q2, _) = kate_divison_inner::<E>(rec_step, divisor.clone(), reciproical, remainder);
        // length of q2 is smaller
        add_polynomials(&mut q[..q2.len()], &q2[..]);
    }        

    // although r must be zero, calculate it for now
    if q.len() == 0 {
        return (q, poly);
    }

    // r = u - v*q
    let mut poly = poly;
    let tmp = multiply_polynomials::<E>(divisor, q.clone());
    sub_polynomials(&mut poly[..], &tmp[..]);

    return (q, poly);
}

/// Convenience function to check polynomail commitment
pub fn check_polynomial_commitment<E: Engine>(
    commitment: &E::G1Affine,
    point: &E::Fr,
    value: &E::Fr,
    opening: &E::G1Affine,
    max: usize,
    srs: &SRS<E>
) -> bool {
    // e(W , hα x )e(g^{v} * W{-z} , hα ) = e(F , h^{x^{−d +max}} )
    if srs.d < max {
        return false;
    }
    let alpha_x_precomp = srs.h_positive_x_alpha[1].prepare();
    let alpha_precomp = srs.h_positive_x_alpha[0].prepare();
    let mut neg_x_n_minus_d_precomp = srs.h_negative_x[srs.d - max];
    neg_x_n_minus_d_precomp.negate();
    let neg_x_n_minus_d_precomp = neg_x_n_minus_d_precomp.prepare();

    let w = opening.prepare();
    let mut gv = srs.g_positive_x[0].mul(value.into_repr());
    let mut z_neg = *point;
    z_neg.negate();
    let w_minus_z = opening.mul(z_neg.into_repr());
    gv.add_assign(&w_minus_z);

    let gv = gv.into_affine().prepare();

    E::final_exponentiation(&E::miller_loop(&[
            (&w, &alpha_x_precomp),
            (&gv, &alpha_precomp),
            (&commitment.prepare(), &neg_x_n_minus_d_precomp),
        ])).unwrap() == E::Fqk::one()
}

#[test]
fn laurent_division() {
    use crate::pairing::ff::PrimeField;
    use crate::pairing::bls12_381::{Fr};

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


// alternative implementation that does not require an `Evaluation domain` struct
pub fn multiply_polynomials_fft<E: Engine>(a: Vec<E::Fr>, b: Vec<E::Fr>) -> Vec<E::Fr> {
    use crate::multicore::Worker;
    use crate::domain::{best_fft, Scalar};
    use crate::group::Group;

    let result_len = a.len() + b.len() - 1;

    // m is a size of domain where Z polynomial does NOT vanish
    // in normal domain Z is in a form of (X-1)(X-2)...(X-N)
    let mut m = 1;
    let mut exp = 0;
    let mut omega = E::Fr::root_of_unity();
    let max_degree = (1 << E::Fr::S) - 1;

    if result_len > max_degree {
        panic!("multiplication result degree is too large");
    }

    while m < result_len {
        m *= 2;
        exp += 1;

        // The pairing-friendly curve may not be able to support
        // large enough (radix2) evaluation domains.
        if exp > E::Fr::S {
            panic!("multiplication result degree is too large");
        }
    }

    // If full domain is not needed - limit it,
    // e.g. if (2^N)th power is not required, just double omega and get 2^(N-1)th
    // Compute omega, the 2^exp primitive root of unity
    for _ in exp..E::Fr::S {
        omega.square();
    }

    let omegainv = omega.inverse().unwrap();
    let minv = E::Fr::from_str(&format!("{}", m)).unwrap().inverse().unwrap();

    let worker = Worker::new();

    let mut scalars_a: Vec<Scalar<E>> = a.into_iter().map(|e| Scalar::<E>(e)).collect();
    let mut scalars_b: Vec<Scalar<E>> = b.into_iter().map(|e| Scalar::<E>(e)).collect();
    scalars_a.resize(m, Scalar::<E>(E::Fr::zero()));
    scalars_b.resize(m, Scalar::<E>(E::Fr::zero()));


    best_fft(&mut scalars_a[..], &worker, &omega, exp);
    best_fft(&mut scalars_b[..], &worker, &omega, exp);

    // do the convolution
    worker.scope(scalars_a.len(), |scope, chunk| {
        for (a, b) in scalars_a.chunks_mut(chunk).zip(scalars_b.chunks(chunk)) {
            scope.spawn(move |_| {
                for (a, b) in a.iter_mut().zip(b.iter()) {
                    a.group_mul_assign(&b.0);
                }
            });
        }
    });

    // no longer need it
    drop(scalars_b);

    best_fft(&mut scalars_a[..], &worker, &omegainv, exp);
    worker.scope(scalars_a.len(), |scope, chunk| {
        for v in scalars_a.chunks_mut(chunk) {
            scope.spawn(move |_| {
                for v in v {
                    v.group_mul_assign(&minv);
                }
            });
        }
    });

    let mut mul_result: Vec<E::Fr> = scalars_a.into_iter().map(|e| e.0).collect();

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

// add polynomails in coefficient form
pub fn add_polynomials<F: Field>(a: &mut [F], b: &[F]) {
        use crate::multicore::Worker;
        use crate::domain::{EvaluationDomain, Scalar};

        let worker = Worker::new();

        assert_eq!(a.len(), b.len());

        worker.scope(a.len(), |scope, chunk| {
            for (a, b) in a.chunks_mut(chunk).zip(b.chunks(chunk))
            {
                scope.spawn(move |_| {
                    for (a, b) in a.iter_mut().zip(b.iter()) {
                        a.add_assign(b);
                    }
                });
            }
        });
}

// subtract polynomails in coefficient form
pub fn sub_polynomials<F: Field>(a: &mut [F], b: &[F]) {
    use crate::multicore::Worker;
    use crate::domain::{EvaluationDomain, Scalar};

    let worker = Worker::new();

    assert_eq!(a.len(), b.len());

    worker.scope(a.len(), |scope, chunk| {
        for (a, b) in a.chunks_mut(chunk).zip(b.chunks(chunk))
        {
            scope.spawn(move |_| {
                for (a, b) in a.iter_mut().zip(b.iter()) {
                    a.sub_assign(b);
                }
            });
        }
    });
}

// multiply coefficients of the polynomial by the scalar
pub fn mul_polynomial_by_scalar<F: Field>(a: &mut [F], b: F) {
        use crate::multicore::Worker;
        use crate::domain::{EvaluationDomain, Scalar};

        let worker = Worker::new();

        worker.scope(a.len(), |scope, chunk| {
            for a in a.chunks_mut(chunk)
            {
                scope.spawn(move |_| {
                    for a in a.iter_mut() {
                        a.mul_assign(&b);
                    }
                });
            }
        });
}

// elementwise add coeffs of one polynomial with coeffs of other, that are 
// first multiplied by a scalar 
pub fn mul_add_polynomials<F: Field>(a: &mut [F], b: &[F], c: F) {
        use crate::multicore::Worker;
        use crate::domain::{EvaluationDomain, Scalar};

        let worker = Worker::new();

        assert_eq!(a.len(), b.len());

        worker.scope(a.len(), |scope, chunk| {
            for (a, b) in a.chunks_mut(chunk).zip(b.chunks(chunk))
            {
                scope.spawn(move |_| {
                    for (a, b) in a.iter_mut().zip(b.iter()) {
                        let mut r = *b;
                        r.mul_assign(&c);

                        a.add_assign(&r);
                    }
                });
            }
        });
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
    use crate::pairing::bls12_381::Bls12;
    use crate::pairing::bls12_381::Fr;

    const SAMPLES: usize = 100;

    let rng = &mut rand::thread_rng();
    let a = (0..SAMPLES).map(|_| Fr::rand(rng)).collect::<Vec<_>>();
    let b = (0..SAMPLES).map(|_| Fr::rand(rng)).collect::<Vec<_>>();

    let serial_res = multiply_polynomials_serial::<Bls12>(a.clone(), b.clone());
    let parallel_res = multiply_polynomials::<Bls12>(a, b);

    assert_eq!(serial_res.len(), parallel_res.len());
    assert_eq!(serial_res, parallel_res);
}

#[test]
fn test_eval_at_powers() {
    use rand::{self, Rand, Rng};
    use crate::pairing::bls12_381::Bls12;
    use crate::pairing::bls12_381::Fr;

    const SAMPLES: usize = 100000;

    let rng = &mut rand::thread_rng();
    let a = (0..SAMPLES).map(|_| Fr::rand(rng)).collect::<Vec<_>>();
    let x: Fr = rng.gen();
    let n: u32 = rng.gen();

    let mut acc = Fr::zero();

    {
        let mut tmp = x.pow(&[n as u64]);

        for coeff in a.iter() {
            let mut c = *coeff;
            c.mul_assign(&tmp);
            acc.add_assign(&c);
            tmp.mul_assign(&x);
        }
    }

    let first_power = x.pow(&[n as u64]);
    let acc_parallel = evaluate_at_consequitive_powers(&a[..], first_power, x);

    assert_eq!(acc_parallel, acc);
}

#[test]
fn test_mut_eval_at_powers() {
    use rand::{self, Rand, Rng};
    use crate::pairing::bls12_381::Bls12;
    use crate::pairing::bls12_381::Fr;

    const SAMPLES: usize = 100000;

    let rng = &mut rand::thread_rng();
    let mut a = (0..SAMPLES).map(|_| Fr::rand(rng)).collect::<Vec<_>>();
    let mut b = a.clone();
    let x: Fr = rng.gen();
    let n: u32 = rng.gen();

    let mut acc = Fr::zero();

    {
        let mut tmp = x.pow(&[n as u64]);

        for coeff in a.iter_mut() {
            coeff.mul_assign(&tmp);
            acc.add_assign(&coeff);
            tmp.mul_assign(&x);
        }
    }

    let first_power = x.pow(&[n as u64]);
    let acc_parallel = mut_evaluate_at_consequitive_powers(&mut b[..], first_power, x);

    assert_eq!(acc_parallel, acc);
    assert!(a == b);
}

#[test]
fn test_mut_distribute_powers() {
    use rand::{self, Rand, Rng};
    use crate::pairing::bls12_381::Bls12;
    use crate::pairing::bls12_381::Fr;

    const SAMPLES: usize = 100000;

    let rng = &mut rand::thread_rng();
    let mut a = (0..SAMPLES).map(|_| Fr::rand(rng)).collect::<Vec<_>>();
    let mut b = a.clone();
    let x: Fr = rng.gen();
    let n: u32 = rng.gen();

    {
        let mut tmp = x.pow(&[n as u64]);

        for coeff in a.iter_mut() {
            coeff.mul_assign(&tmp);
            tmp.mul_assign(&x);
        }
    }

    let first_power = x.pow(&[n as u64]);
    mut_distribute_consequitive_powers(&mut b[..], first_power, x);

    assert!(a == b);
}


#[test]
fn test_trivial_parallel_kate_division() {
    use crate::pairing::ff::PrimeField;
    use crate::pairing::bls12_381::{Bls12, Fr};

    let mut minus_one = Fr::one();
    minus_one.negate();

    let z = Fr::one();

    // this is x^2 - 1
    let poly = vec![
        minus_one,
        Fr::from_str("0").unwrap(),
        Fr::from_str("1").unwrap(),
    ];

    let quotient_poly = kate_divison(&poly, z);

    let parallel_q_poly = parallel_kate_divison::<Bls12, _>(&poly, z);

    assert_eq!(quotient_poly, parallel_q_poly);
}

#[test]
fn test_less_trivial_parallel_kate_division() {
    use crate::pairing::ff::PrimeField;
    use crate::pairing::bls12_381::{Bls12, Fr};

    let z = Fr::one();

    let mut poly = vec![
        Fr::from_str("328947234").unwrap(),
        Fr::from_str("3545623451111").unwrap(),
        Fr::from_str("5").unwrap(),
        Fr::from_str("55555").unwrap(),
        Fr::from_str("1235685").unwrap(),
    ];

    fn eval(poly: &[Fr], point: Fr) -> Fr {
        let mut acc = Fr::zero();
        let mut tmp = Fr::one();
        for p in &poly[..] {
            let mut t = *p;
            t.mul_assign(&tmp);
            acc.add_assign(&t);
            tmp.mul_assign(&point);
        }
    
        acc
    }

    let p_at_z = eval(&poly, z);

    // poly = poly(X) - poly(z)
    poly[0].sub_assign(&p_at_z);

    let quotient_poly = kate_divison(&poly, z);

    let parallel_q_poly = parallel_kate_divison::<Bls12, _>(&poly, z);

    assert_eq!(quotient_poly, parallel_q_poly);
}


#[test]
fn test_parallel_kate_division() {
    use crate::pairing::ff::PrimeField;
    use crate::pairing::bls12_381::{Bls12, Fr};

    let mut poly = vec![
        Fr::from_str("328947234").unwrap(),
        Fr::from_str("3545623451111").unwrap(),
        Fr::from_str("0").unwrap(),
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

    let z = Fr::from_str("2000").unwrap();

    let p_at_z = eval(&poly, z);

    // poly = poly(X) - poly(z)
    poly[2].sub_assign(&p_at_z);

    let quotient_poly = kate_divison(&poly, z);

    let parallel_q_poly = parallel_kate_divison::<Bls12, _>(&poly, z);

    assert_eq!(quotient_poly, parallel_q_poly);
}