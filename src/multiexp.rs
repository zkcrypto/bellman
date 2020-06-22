use bit_vec::{self, BitVec};
use ff::{Field, PrimeField, PrimeFieldRepr, ScalarEngine};
use futures::Future;
use groupy::{CurveAffine, CurveProjective};
use log::{info, warn};
use std::io;
use std::iter;
use std::sync::Arc;

use super::multicore::Worker;
use super::SynthesisError;
use crate::gpu;

/// An object that builds a source of bases.
pub trait SourceBuilder<G: CurveAffine>: Send + Sync + 'static + Clone {
    type Source: Source<G>;

    fn new(self) -> Self::Source;
    fn get(self) -> (Arc<Vec<G>>, usize);
}

/// A source of bases, like an iterator.
pub trait Source<G: CurveAffine> {
    /// Parses the element from the source. Fails if the point is at infinity.
    fn add_assign_mixed(
        &mut self,
        to: &mut <G as CurveAffine>::Projective,
    ) -> Result<(), SynthesisError>;

    /// Skips `amt` elements from the source, avoiding deserialization.
    fn skip(&mut self, amt: usize) -> Result<(), SynthesisError>;
}

impl<G: CurveAffine> SourceBuilder<G> for (Arc<Vec<G>>, usize) {
    type Source = (Arc<Vec<G>>, usize);

    fn new(self) -> (Arc<Vec<G>>, usize) {
        (self.0.clone(), self.1)
    }

    fn get(self) -> (Arc<Vec<G>>, usize) {
        (self.0.clone(), self.1)
    }
}

impl<G: CurveAffine> Source<G> for (Arc<Vec<G>>, usize) {
    fn add_assign_mixed(
        &mut self,
        to: &mut <G as CurveAffine>::Projective,
    ) -> Result<(), SynthesisError> {
        if self.0.len() <= self.1 {
            return Err(io::Error::new(
                io::ErrorKind::UnexpectedEof,
                "expected more bases from source",
            )
            .into());
        }

        if self.0[self.1].is_zero() {
            return Err(SynthesisError::UnexpectedIdentity);
        }

        to.add_assign_mixed(&self.0[self.1]);

        self.1 += 1;

        Ok(())
    }

    fn skip(&mut self, amt: usize) -> Result<(), SynthesisError> {
        if self.0.len() <= self.1 {
            return Err(io::Error::new(
                io::ErrorKind::UnexpectedEof,
                "expected more bases from source",
            )
            .into());
        }

        self.1 += amt;

        Ok(())
    }
}

pub trait QueryDensity {
    /// Returns whether the base exists.
    type Iter: Iterator<Item = bool>;

    fn iter(self) -> Self::Iter;
    fn get_query_size(self) -> Option<usize>;
}

#[derive(Clone)]
pub struct FullDensity;

impl AsRef<FullDensity> for FullDensity {
    fn as_ref(&self) -> &FullDensity {
        self
    }
}

impl<'a> QueryDensity for &'a FullDensity {
    type Iter = iter::Repeat<bool>;

    fn iter(self) -> Self::Iter {
        iter::repeat(true)
    }

    fn get_query_size(self) -> Option<usize> {
        None
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct DensityTracker {
    pub bv: BitVec,
    pub total_density: usize,
}

impl<'a> QueryDensity for &'a DensityTracker {
    type Iter = bit_vec::Iter<'a>;

    fn iter(self) -> Self::Iter {
        self.bv.iter()
    }

    fn get_query_size(self) -> Option<usize> {
        Some(self.bv.len())
    }
}

impl DensityTracker {
    pub fn new() -> DensityTracker {
        DensityTracker {
            bv: BitVec::new(),
            total_density: 0,
        }
    }

    pub fn add_element(&mut self) {
        self.bv.push(false);
    }

    pub fn inc(&mut self, idx: usize) {
        if !self.bv.get(idx).unwrap() {
            self.bv.set(idx, true);
            self.total_density += 1;
        }
    }

    pub fn get_total_density(&self) -> usize {
        self.total_density
    }

    /// Extend by concatenating `other`. If `is_input_density` is true, then we are tracking an input density,
    /// and other may contain a redundant input for the `One` element. Coalesce those as needed and track the result.
    pub fn extend(&mut self, other: Self, is_input_density: bool) {
        if other.bv.is_empty() {
            // Nothing to do if other is empty.
            return;
        }

        if self.bv.is_empty() {
            // If self is empty, assume other's density.
            self.total_density = other.total_density;
            self.bv = other.bv;
            return;
        }

        if is_input_density {
            // Input densities need special handling to coalesce their first inputs.

            if other.bv[0] {
                // If other's first bit is set,
                if self.bv[0] {
                    // And own first bit is set, then decrement total density so the final sum doesn't overcount.
                    self.total_density -= 1;
                } else {
                    // Otherwise, set own first bit.
                    self.bv.set(0, true);
                }
            }
            // Now discard other's first bit, having accounted for it above, and extend self by remaining bits.
            self.bv.extend(other.bv.iter().skip(1));
        } else {
            // Not an input density, just extend straightforwardly.
            self.bv.extend(other.bv);
        }

        // Since any needed adjustments to total densities have been made, just sum the totals and keep the sum.
        self.total_density += other.total_density;
    }
}

fn multiexp_inner<Q, D, G, S>(
    pool: &Worker,
    bases: S,
    density_map: D,
    exponents: Arc<Vec<<<G::Engine as ScalarEngine>::Fr as PrimeField>::Repr>>,
    mut skip: u32,
    c: u32,
    handle_trivial: bool,
) -> Box<dyn Future<Item = <G as CurveAffine>::Projective, Error = SynthesisError>>
where
    for<'a> &'a Q: QueryDensity,
    D: Send + Sync + 'static + Clone + AsRef<Q>,
    G: CurveAffine,
    S: SourceBuilder<G>,
{
    // Perform this region of the multiexp
    let this = {
        let bases = bases.clone();
        let exponents = exponents.clone();
        let density_map = density_map.clone();

        pool.compute(move || {
            // Accumulate the result
            let mut acc = G::Projective::zero();

            // Build a source for the bases
            let mut bases = bases.new();

            // Create space for the buckets
            let mut buckets = vec![<G as CurveAffine>::Projective::zero(); (1 << c) - 1];

            let zero = <G::Engine as ScalarEngine>::Fr::zero().into_repr();
            let one = <G::Engine as ScalarEngine>::Fr::one().into_repr();

            // Sort the bases into buckets
            for (&exp, density) in exponents.iter().zip(density_map.as_ref().iter()) {
                if density {
                    if exp == zero {
                        bases.skip(1)?;
                    } else if exp == one {
                        if handle_trivial {
                            bases.add_assign_mixed(&mut acc)?;
                        } else {
                            bases.skip(1)?;
                        }
                    } else {
                        let mut exp = exp;
                        exp.shr(skip);
                        let exp = exp.as_ref()[0] % (1 << c);

                        if exp != 0 {
                            bases.add_assign_mixed(&mut buckets[(exp - 1) as usize])?;
                        } else {
                            bases.skip(1)?;
                        }
                    }
                }
            }

            // Summation by parts
            // e.g. 3a + 2b + 1c = a +
            //                    (a) + b +
            //                    ((a) + b) + c
            let mut running_sum = G::Projective::zero();
            for exp in buckets.into_iter().rev() {
                running_sum.add_assign(&exp);
                acc.add_assign(&running_sum);
            }

            Ok(acc)
        })
    };

    skip += c;

    if skip >= <G::Engine as ScalarEngine>::Fr::NUM_BITS {
        // There isn't another region.
        Box::new(this)
    } else {
        // There's another region more significant. Calculate and join it with
        // this region recursively.
        Box::new(
            this.join(multiexp_inner(
                pool,
                bases,
                density_map,
                exponents,
                skip,
                c,
                false,
            ))
            .map(move |(this, mut higher)| {
                for _ in 0..c {
                    higher.double();
                }

                higher.add_assign(&this);

                higher
            }),
        )
    }
}

/// Perform multi-exponentiation. The caller is responsible for ensuring the
/// query size is the same as the number of exponents.
pub fn multiexp<Q, D, G, S>(
    pool: &Worker,
    bases: S,
    density_map: D,
    exponents: Arc<Vec<<<G::Engine as ScalarEngine>::Fr as PrimeField>::Repr>>,
    kern: &mut Option<gpu::LockedMultiexpKernel<G::Engine>>,
) -> Box<dyn Future<Item = <G as CurveAffine>::Projective, Error = SynthesisError>>
where
    for<'a> &'a Q: QueryDensity,
    D: Send + Sync + 'static + Clone + AsRef<Q>,
    G: CurveAffine,
    G::Engine: paired::Engine,
    S: SourceBuilder<G>,
{
    if let Some(ref mut kern) = kern {
        if let Ok(p) = kern.with(|k: &mut gpu::MultiexpKernel<G::Engine>| {
            let mut exps = vec![exponents[0]; exponents.len()];
            let mut n = 0;
            for (&e, d) in exponents.iter().zip(density_map.as_ref().iter()) {
                if d {
                    exps[n] = e;
                    n += 1;
                }
            }

            let (bss, skip) = bases.clone().get();
            k.multiexp(pool, bss, Arc::new(exps.clone()), skip, n)
        }) {
            return Box::new(pool.compute(move || Ok(p)));
        }
    }

    let c = if exponents.len() < 32 {
        3u32
    } else {
        (f64::from(exponents.len() as u32)).ln().ceil() as u32
    };

    if let Some(query_size) = density_map.as_ref().get_query_size() {
        // If the density map has a known query size, it should not be
        // inconsistent with the number of exponents.
        assert!(query_size == exponents.len());
    }

    let future = multiexp_inner(pool, bases, density_map, exponents, 0, c, true);
    #[cfg(feature = "gpu")]
    {
        // Do not give the control back to the caller till the
        // multiexp is done. We may want to reacquire the GPU again
        // between the multiexps.
        let result = future.wait();
        Box::new(pool.compute(move || result))
    }
    #[cfg(not(feature = "gpu"))]
    future
}

#[cfg(feature = "pairing")]
#[test]
fn test_with_bls12() {
    fn naive_multiexp<G: CurveAffine>(
        bases: Arc<Vec<G>>,
        exponents: Arc<Vec<<G::Scalar as PrimeField>::Repr>>,
    ) -> G::Projective {
        assert_eq!(bases.len(), exponents.len());

        let mut acc = G::Projective::zero();

        for (base, exp) in bases.iter().zip(exponents.iter()) {
            acc.add_assign(&base.mul(*exp));
        }

        acc
    }

    use paired::{bls12_381::Bls12, Engine};
    use rand;

    const SAMPLES: usize = 1 << 14;

    let rng = &mut rand::thread_rng();
    let v = Arc::new(
        (0..SAMPLES)
            .map(|_| <Bls12 as ScalarEngine>::Fr::random(rng).into_repr())
            .collect::<Vec<_>>(),
    );
    let g = Arc::new(
        (0..SAMPLES)
            .map(|_| <Bls12 as Engine>::G1::random(rng).into_affine())
            .collect::<Vec<_>>(),
    );

    let naive = naive_multiexp(g.clone(), v.clone());

    let pool = Worker::new();

    let fast = multiexp(&pool, (g, 0), FullDensity, v).wait().unwrap();

    assert_eq!(naive, fast);
}

pub fn create_multiexp_kernel<E>(_log_d: usize, priority: bool) -> Option<gpu::MultiexpKernel<E>>
where
    E: paired::Engine,
{
    match gpu::MultiexpKernel::<E>::create(priority) {
        Ok(k) => {
            info!("GPU Multiexp kernel instantiated!");
            Some(k)
        }
        Err(e) => {
            warn!("Cannot instantiate GPU Multiexp kernel! Error: {}", e);
            None
        }
    }
}

#[cfg(feature = "gpu")]
#[test]
pub fn gpu_multiexp_consistency() {
    use paired::bls12_381::Bls12;
    use std::time::Instant;

    const MAX_LOG_D: usize = 20;
    const START_LOG_D: usize = 10;
    let mut kern = Some(gpu::LockedMultiexpKernel::<Bls12>::new(MAX_LOG_D, false));
    let pool = Worker::new();

    let rng = &mut rand::thread_rng();

    let mut bases = (0..(1 << 10))
        .map(|_| <Bls12 as paired::Engine>::G1::random(rng).into_affine())
        .collect::<Vec<_>>();
    for _ in 10..START_LOG_D {
        bases = [bases.clone(), bases.clone()].concat();
    }

    for log_d in START_LOG_D..(MAX_LOG_D + 1) {
        let g = Arc::new(bases.clone());

        let samples = 1 << log_d;
        println!("Testing Multiexp for {} elements...", samples);

        let v = Arc::new(
            (0..samples)
                .map(|_| <Bls12 as ScalarEngine>::Fr::random(rng).into_repr())
                .collect::<Vec<_>>(),
        );

        let mut now = Instant::now();
        let gpu = multiexp(&pool, (g.clone(), 0), FullDensity, v.clone(), &mut kern)
            .wait()
            .unwrap();
        let gpu_dur = now.elapsed().as_secs() * 1000 as u64 + now.elapsed().subsec_millis() as u64;
        println!("GPU took {}ms.", gpu_dur);

        now = Instant::now();
        let cpu = multiexp(&pool, (g.clone(), 0), FullDensity, v.clone(), &mut None)
            .wait()
            .unwrap();
        let cpu_dur = now.elapsed().as_secs() * 1000 as u64 + now.elapsed().subsec_millis() as u64;
        println!("CPU took {}ms.", cpu_dur);

        println!("Speedup: x{}", cpu_dur as f32 / gpu_dur as f32);

        assert_eq!(cpu, gpu);

        println!("============================");

        bases = [bases.clone(), bases.clone()].concat();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use rand::Rng;
    use rand_core::SeedableRng;
    use rand_xorshift::XorShiftRng;

    #[test]
    fn test_extend_density_regular() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for k in &[2, 4, 8] {
            for j in &[10, 20, 50] {
                let count: usize = k * j;

                let mut tracker_full = DensityTracker::new();
                let mut partial_trackers: Vec<DensityTracker> = Vec::with_capacity(count / k);
                for i in 0..count {
                    if i % k == 0 {
                        partial_trackers.push(DensityTracker::new());
                    }

                    let index: usize = i / k;
                    if rng.gen() {
                        tracker_full.add_element();
                        partial_trackers[index].add_element();
                    }

                    if !partial_trackers[index].bv.is_empty() {
                        let idx = rng.gen_range(0, partial_trackers[index].bv.len());
                        let offset: usize = partial_trackers
                            .iter()
                            .take(index)
                            .map(|t| t.bv.len())
                            .sum();
                        tracker_full.inc(offset + idx);
                        partial_trackers[index].inc(idx);
                    }
                }

                let mut tracker_combined = DensityTracker::new();
                for tracker in partial_trackers.into_iter() {
                    tracker_combined.extend(tracker, false);
                }
                assert_eq!(tracker_combined, tracker_full);
            }
        }
    }

    #[test]
    fn test_extend_density_input() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);
        let trials = 10;
        let max_bits = 10;
        let max_density = max_bits;

        // Create an empty DensityTracker.
        let empty = || DensityTracker::new();

        // Create a random DensityTracker with first bit unset.
        let unset = |rng: &mut XorShiftRng| {
            let mut dt = DensityTracker::new();
            dt.add_element();
            let n = rng.gen_range(1, max_bits);
            let target_density = rng.gen_range(0, max_density);
            for _ in 1..n {
                dt.add_element();
            }

            for _ in 0..target_density {
                if n > 1 {
                    let to_inc = rng.gen_range(1, n);
                    dt.inc(to_inc);
                }
            }
            assert!(!dt.bv[0]);
            assert_eq!(n, dt.bv.len());
            dbg!(&target_density, &dt.total_density);

            dt
        };

        // Create a random DensityTracker with first bit set.
        let set = |mut rng: &mut XorShiftRng| {
            let mut dt = unset(&mut rng);
            dt.inc(0);
            dt
        };

        for _ in 0..trials {
            {
                // Both empty.
                let (mut e1, e2) = (empty(), empty());
                e1.extend(e2, true);
                assert_eq!(empty(), e1);
            }
            {
                // First empty, second unset.
                let (mut e1, u1) = (empty(), unset(&mut rng));
                e1.extend(u1.clone(), true);
                assert_eq!(u1, e1);
            }
            {
                // First empty, second set.
                let (mut e1, s1) = (empty(), set(&mut rng));
                e1.extend(s1.clone(), true);
                assert_eq!(s1, e1);
            }
            {
                // First set, second empty.
                let (mut s1, e1) = (set(&mut rng), empty());
                let s2 = s1.clone();
                s1.extend(e1, true);
                assert_eq!(s1, s2);
            }
            {
                // First unset, second empty.
                let (mut u1, e1) = (unset(&mut rng), empty());
                let u2 = u1.clone();
                u1.extend(e1, true);
                assert_eq!(u1, u2);
            }
            {
                // First unset, second unset.
                let (mut u1, u2) = (unset(&mut rng), unset(&mut rng));
                let expected_total = u1.total_density + u2.total_density;
                u1.extend(u2, true);
                assert_eq!(expected_total, u1.total_density);
                assert!(!u1.bv[0]);
            }
            {
                // First unset, second set.
                let (mut u1, s1) = (unset(&mut rng), set(&mut rng));
                let expected_total = u1.total_density + s1.total_density;
                u1.extend(s1, true);
                assert_eq!(expected_total, u1.total_density);
                assert!(u1.bv[0]);
            }
            {
                // First set, second unset.
                let (mut s1, u1) = (set(&mut rng), unset(&mut rng));
                let expected_total = s1.total_density + u1.total_density;
                s1.extend(u1, true);
                assert_eq!(expected_total, s1.total_density);
                assert!(s1.bv[0]);
            }
            {
                // First set, second set.
                let (mut s1, s2) = (set(&mut rng), set(&mut rng));
                let expected_total = s1.total_density + s2.total_density - 1;
                s1.extend(s2, true);
                assert_eq!(expected_total, s1.total_density);
                assert!(s1.bv[0]);
            }
        }
    }
}
