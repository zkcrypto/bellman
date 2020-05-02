use super::multicore::Worker;
use bit_vec::{self, BitVec};
use ff::{Endianness, Field, PrimeField, ScalarEngine};
use futures::Future;
use group::{CurveAffine, CurveProjective};
use std::io;
use std::iter;
use std::ops::AddAssign;
use std::sync::Arc;

use super::SynthesisError;

/// An object that builds a source of bases.
pub trait SourceBuilder<G: CurveAffine>: Send + Sync + 'static + Clone {
    type Source: Source<G>;

    fn new(self) -> Self::Source;
}

/// A source of bases, like an iterator.
pub trait Source<G: CurveAffine> {
    fn next(&mut self) -> Result<&G, SynthesisError>;

    /// Skips `amt` elements from the source, avoiding deserialization.
    fn skip(&mut self, amt: usize) -> Result<(), SynthesisError>;
}

pub trait AddAssignFromSource: CurveProjective {
    /// Parses the element from the source. Fails if the point is at infinity.
    fn add_assign_from_source<S: Source<<Self as CurveProjective>::Affine>>(
        &mut self,
        source: &mut S,
    ) -> Result<(), SynthesisError> {
        AddAssign::<&<Self as CurveProjective>::Affine>::add_assign(self, source.next()?);
        Ok(())
    }
}
impl<G> AddAssignFromSource for G where G: CurveProjective {}

impl<G: CurveAffine> SourceBuilder<G> for (Arc<Vec<G>>, usize) {
    type Source = (Arc<Vec<G>>, usize);

    fn new(self) -> (Arc<Vec<G>>, usize) {
        (self.0.clone(), self.1)
    }
}

impl<G: CurveAffine> Source<G> for (Arc<Vec<G>>, usize) {
    fn next(&mut self) -> Result<&G, SynthesisError> {
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

        let ret = &self.0[self.1];
        self.1 += 1;

        Ok(ret)
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

pub struct DensityTracker {
    bv: BitVec,
    total_density: usize,
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
}

fn multiexp_inner<Q, D, G, S>(
    pool: &Worker,
    bases: S,
    density_map: D,
    exponents: Arc<Vec<<G::Engine as ScalarEngine>::Fr>>,
    mut skip: u32,
    c: u32,
    handle_trivial: bool,
) -> Box<dyn Future<Item = G, Error = SynthesisError>>
where
    for<'a> &'a Q: QueryDensity,
    D: Send + Sync + 'static + Clone + AsRef<Q>,
    G: CurveProjective,
    S: SourceBuilder<<G as CurveProjective>::Affine>,
{
    // Perform this region of the multiexp
    let this = {
        let bases = bases.clone();
        let exponents = exponents.clone();
        let density_map = density_map.clone();

        pool.compute(move || {
            // Accumulate the result
            let mut acc = G::zero();

            // Build a source for the bases
            let mut bases = bases.new();

            // Create space for the buckets
            let mut buckets = vec![G::zero(); (1 << c) - 1];

            let one = <G::Engine as ScalarEngine>::Fr::one();

            // Sort the bases into buckets
            for (&exp, density) in exponents.iter().zip(density_map.as_ref().iter()) {
                if density {
                    if exp.is_zero() {
                        bases.skip(1)?;
                    } else if exp == one {
                        if handle_trivial {
                            acc.add_assign_from_source(&mut bases)?;
                        } else {
                            bases.skip(1)?;
                        }
                    } else {
                        let mut exp = exp.to_repr();
                        <<G::Engine as ScalarEngine>::Fr as PrimeField>::ReprEndianness::toggle_little_endian(&mut exp);

                        let exp = exp
                            .as_ref()
                            .into_iter()
                            .map(|b| (0..8).map(move |i| (b >> i) & 1u8))
                            .flatten()
                            .skip(skip as usize)
                            .take(c as usize)
                            .enumerate()
                            .fold(0u64, |acc, (i, b)| acc + ((b as u64) << i));

                        if exp != 0 {
                            (&mut buckets[(exp - 1) as usize])
                                .add_assign_from_source(&mut bases)?;
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
            let mut running_sum = G::zero();
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
            .map(move |(this, mut higher): (_, G)| {
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
    exponents: Arc<Vec<<G::Engine as ScalarEngine>::Fr>>,
) -> Box<dyn Future<Item = G, Error = SynthesisError>>
where
    for<'a> &'a Q: QueryDensity,
    D: Send + Sync + 'static + Clone + AsRef<Q>,
    G: CurveProjective,
    S: SourceBuilder<<G as CurveProjective>::Affine>,
{
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

    multiexp_inner(pool, bases, density_map, exponents, 0, c, true)
}

#[cfg(feature = "pairing")]
#[test]
fn test_with_bls12() {
    fn naive_multiexp<G: CurveProjective>(
        bases: Arc<Vec<<G as CurveProjective>::Affine>>,
        exponents: Arc<Vec<G::Scalar>>,
    ) -> G {
        assert_eq!(bases.len(), exponents.len());

        let mut acc = G::zero();

        for (base, exp) in bases.iter().zip(exponents.iter()) {
            AddAssign::<&G>::add_assign(&mut acc, &base.mul(exp.to_repr()));
        }

        acc
    }

    use pairing::{bls12_381::Bls12, Engine};
    use rand;

    const SAMPLES: usize = 1 << 14;

    let rng = &mut rand::thread_rng();
    let v = Arc::new(
        (0..SAMPLES)
            .map(|_| <Bls12 as ScalarEngine>::Fr::random(rng))
            .collect::<Vec<_>>(),
    );
    let g = Arc::new(
        (0..SAMPLES)
            .map(|_| <Bls12 as Engine>::G1::random(rng).into_affine())
            .collect::<Vec<_>>(),
    );

    let naive: <Bls12 as Engine>::G1 = naive_multiexp(g.clone(), v.clone());

    let pool = Worker::new();

    let fast = multiexp(&pool, (g, 0), FullDensity, v).wait().unwrap();

    assert_eq!(naive, fast);
}
