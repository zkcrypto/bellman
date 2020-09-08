use super::multicore::Worker;
use bitvec::{array::BitArray, order::Lsb0, vec::BitVec};
use ff::PrimeField;
use futures::Future;
use group::prime::{PrimeCurve, PrimeCurveAffine};
use std::io;
use std::iter;
use std::ops::AddAssign;
use std::sync::Arc;

use super::SynthesisError;

/// An object that builds a source of bases.
pub trait SourceBuilder<G: PrimeCurveAffine>: Send + Sync + 'static + Clone {
    type Source: Source<G>;

    fn new(self) -> Self::Source;
}

/// A source of bases, like an iterator.
pub trait Source<G: PrimeCurveAffine> {
    fn next(&mut self) -> Result<&G, SynthesisError>;

    /// Skips `amt` elements from the source, avoiding deserialization.
    fn skip(&mut self, amt: usize) -> Result<(), SynthesisError>;
}

pub trait AddAssignFromSource: PrimeCurve {
    /// Parses the element from the source. Fails if the point is at infinity.
    fn add_assign_from_source<S: Source<<Self as PrimeCurve>::Affine>>(
        &mut self,
        source: &mut S,
    ) -> Result<(), SynthesisError> {
        AddAssign::<&<Self as PrimeCurve>::Affine>::add_assign(self, source.next()?);
        Ok(())
    }
}
impl<G> AddAssignFromSource for G where G: PrimeCurve {}

impl<G: PrimeCurveAffine> SourceBuilder<G> for (Arc<Vec<G>>, usize) {
    type Source = (Arc<Vec<G>>, usize);

    fn new(self) -> (Arc<Vec<G>>, usize) {
        (self.0.clone(), self.1)
    }
}

impl<G: PrimeCurveAffine> Source<G> for (Arc<Vec<G>>, usize) {
    fn next(&mut self) -> Result<&G, SynthesisError> {
        if self.0.len() <= self.1 {
            return Err(io::Error::new(
                io::ErrorKind::UnexpectedEof,
                "expected more bases from source",
            )
            .into());
        }

        if self.0[self.1].is_identity().into() {
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
}

impl<'a> QueryDensity for &'a DensityTracker {
    type Iter = std::iter::Cloned<bitvec::slice::Iter<'a, Lsb0, usize>>;

    fn iter(self) -> Self::Iter {
        self.bv.iter().cloned()
    }

    fn get_query_size(self) -> Option<usize> {
        Some(self.bv.len())
    }
}

impl DensityTracker {
    pub fn new() -> DensityTracker {
        DensityTracker { bv: BitVec::new() }
    }

    pub fn add_element(&mut self) {
        self.bv.push(false);
    }

    pub fn inc(&mut self, idx: usize) {
        if !self.bv.get(idx).unwrap() {
            self.bv.set(idx, true);
        }
    }

    pub fn get_total_density(&self) -> usize {
        self.bv.count_ones()
    }
}

fn multiexp_inner<Q, D, G, S>(
    pool: &Worker,
    bases: S,
    density_map: D,
    exponents: Arc<Vec<BitArray<Lsb0, <G::Scalar as PrimeField>::ReprBits>>>,
    mut skip: u32,
    c: u32,
    handle_trivial: bool,
) -> Box<dyn Future<Item = G, Error = SynthesisError>>
where
    for<'a> &'a Q: QueryDensity,
    D: Send + Sync + 'static + Clone + AsRef<Q>,
    G: PrimeCurve,
    S: SourceBuilder<<G as PrimeCurve>::Affine>,
{
    // Perform this region of the multiexp
    let this = {
        let bases = bases.clone();
        let exponents = exponents.clone();
        let density_map = density_map.clone();

        pool.compute(move || {
            // Accumulate the result
            let mut acc = G::identity();

            // Build a source for the bases
            let mut bases = bases.new();

            // Create space for the buckets
            let mut buckets = vec![G::identity(); (1 << c) - 1];

            // Sort the bases into buckets
            for (exp, density) in exponents.iter().zip(density_map.as_ref().iter()) {
                if density {
                    let (exp_is_zero, exp_is_one) = {
                        let (first, rest) = exp.split_first().unwrap();
                        let rest_unset = rest.not_any();
                        (!*first && rest_unset, *first && rest_unset)
                    };

                    if exp_is_zero {
                        bases.skip(1)?;
                    } else if exp_is_one {
                        if handle_trivial {
                            acc.add_assign_from_source(&mut bases)?;
                        } else {
                            bases.skip(1)?;
                        }
                    } else {
                        let exp = exp
                            .into_iter()
                            .skip(skip as usize)
                            .take(c as usize)
                            .cloned()
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
            let mut running_sum = G::identity();
            for exp in buckets.into_iter().rev() {
                running_sum.add_assign(&exp);
                acc.add_assign(&running_sum);
            }

            Ok(acc)
        })
    };

    skip += c;

    if skip >= G::Scalar::NUM_BITS {
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
                    higher = higher.double();
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
    exponents: Arc<Vec<BitArray<Lsb0, <G::Scalar as PrimeField>::ReprBits>>>,
) -> Box<dyn Future<Item = G, Error = SynthesisError>>
where
    for<'a> &'a Q: QueryDensity,
    D: Send + Sync + 'static + Clone + AsRef<Q>,
    G: PrimeCurve,
    S: SourceBuilder<<G as PrimeCurve>::Affine>,
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
    fn naive_multiexp<G: PrimeCurve>(
        bases: Arc<Vec<<G as PrimeCurve>::Affine>>,
        exponents: Arc<Vec<G::Scalar>>,
    ) -> G {
        assert_eq!(bases.len(), exponents.len());

        let mut acc = G::identity();

        for (base, exp) in bases.iter().zip(exponents.iter()) {
            AddAssign::<&G>::add_assign(&mut acc, &(*base * *exp));
        }

        acc
    }

    use bls12_381::{Bls12, Scalar};
    use ff::Field;
    use group::{Curve, Group};
    use pairing::Engine;
    use rand;

    const SAMPLES: usize = 1 << 14;

    let mut rng = rand::thread_rng();
    let v = Arc::new(
        (0..SAMPLES)
            .map(|_| Scalar::random(&mut rng))
            .collect::<Vec<_>>(),
    );
    let v_bits = Arc::new(v.iter().map(|e| e.to_le_bits()).collect::<Vec<_>>());
    let g = Arc::new(
        (0..SAMPLES)
            .map(|_| <Bls12 as Engine>::G1::random(&mut rng).to_affine())
            .collect::<Vec<_>>(),
    );

    let naive: <Bls12 as Engine>::G1 = naive_multiexp(g.clone(), v.clone());

    let pool = Worker::new();

    let fast = multiexp(&pool, (g, 0), FullDensity, v_bits).wait().unwrap();

    assert_eq!(naive, fast);
}
