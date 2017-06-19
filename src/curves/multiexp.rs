//! This module provides an abstract implementation of the Bos-Coster multi-exponentiation algorithm.

use super::{Engine, Curve, CurveAffine, Field, PrimeField, PrimeFieldRepr};
use super::wnaf;
use std::cmp::Ordering;
use std::collections::BinaryHeap;

pub trait Projective<E: Engine>: Sized + Copy + Clone + Send {
    type WindowTable;

    /// Constructs an identity element.
    fn identity(e: &E) -> Self;

    /// Adds this projective element to another projective element.
    fn add_to_projective(&self, e: &E, projective: &mut Self);

    /// Exponentiates by a scalar.
    fn exponentiate(
        &mut self,
        e: &E,
        scalar: <E::Fr as PrimeField<E>>::Repr,
        table: &mut Self::WindowTable,
        scratch: &mut wnaf::WNAFTable
    );

    /// Construct a blank window table
    fn new_window_table(e: &E) -> Self::WindowTable;
}

pub trait Chunk<E: Engine>: Send {
    type Projective: Projective<E>;

    /// Skips the next element from the source.
    fn skip(&mut self, e: &E) -> Result<(), ()>;

    /// Adds the next element from the source to a projective element
    fn add_to_projective(&mut self, e: &E, acc: &mut Self::Projective) -> Result<(), ()>;

    /// Turns the next element of the source into a projective element.
    fn into_projective(&mut self, e: &E) -> Result<Self::Projective, ()>;
}

/// An `ElementSource` is something that contains a sequence of group elements or
/// group element tuples.
pub trait ElementSource<E: Engine> {
    type Chunk: Chunk<E>;

    /// Gets the number of elements from the source.
    fn num_elements(&self) -> usize;

    /// Returns a chunk size and a vector of chunks.
    fn chunks(&mut self, chunks: usize) -> (usize, Vec<Self::Chunk>);
}

impl<'a, E: Engine, G: CurveAffine<E>> ElementSource<E> for &'a [G] {
    type Chunk = &'a [G];

    fn num_elements(&self) -> usize {
        self.len()
    }

    fn chunks(&mut self, chunks: usize) -> (usize, Vec<Self::Chunk>) {
        let chunk_size = (self.len() / chunks) + 1;

        (chunk_size, (*self).chunks(chunk_size).collect())
    }
}

impl<'a, E: Engine, G: CurveAffine<E>> Chunk<E> for &'a [G]
{
    type Projective = G::Jacobian;

    fn skip(&mut self, _: &E) -> Result<(), ()> {
        if self.len() == 0 {
            Err(())
        } else {
            *self = &self[1..];
            Ok(())
        }
    }

    /// Adds the next element from the source to a projective element
    fn add_to_projective(&mut self, e: &E, acc: &mut Self::Projective) -> Result<(), ()> {
        if self.len() == 0 {
            Err(())
        } else {
            acc.add_assign_mixed(e, &self[0]);
            *self = &self[1..];
            Ok(())
        }
    }

    /// Turns the next element of the accumulator into a projective element.
    fn into_projective(&mut self, e: &E) -> Result<Self::Projective, ()> {
        if self.len() == 0 {
            Err(())
        } else {
            let ret = Ok(self[0].to_jacobian(e));
            *self = &self[1..];
            ret
        }
    }
}

fn justexp<E: Engine>(
    largest: &<E::Fr as PrimeField<E>>::Repr,
    smallest: &<E::Fr as PrimeField<E>>::Repr
) -> bool
{
    use std::cmp::min;

    let abits = largest.num_bits();
    let bbits = smallest.num_bits();
    let limit = min(abits-bbits, 20);

    if bbits < (1<<limit) {
        true
    } else {
        false
    }
}

pub fn perform_multiexp<E: Engine, Source: ElementSource<E>>(
    e: &E,
    mut bases: Source,
    scalars: &[E::Fr]
) -> Result<<Source::Chunk as Chunk<E>>::Projective, ()>
{
    if bases.num_elements() != scalars.len() {
        return Err(())
    }

    use crossbeam;
    use num_cpus;

    let (chunk_len, bases) = bases.chunks(num_cpus::get());

    return crossbeam::scope(|scope| {
        let mut threads = vec![];

        for (mut chunk, scalars) in bases.into_iter().zip(scalars.chunks(chunk_len)) {
            threads.push(scope.spawn(move || {
                let mut heap: BinaryHeap<Exp<E>> = BinaryHeap::with_capacity(scalars.len());
                let mut elements = Vec::with_capacity(scalars.len());

                let mut acc = Projective::<E>::identity(e);
                let one = E::Fr::one(e);

                for scalar in scalars {
                    if scalar.is_zero() {
                        // Skip processing bases when we're multiplying by a zero anyway.
                        chunk.skip(e)?;
                    } else if *scalar == one {
                        // Just perform mixed addition when we're multiplying by one.
                        chunk.add_to_projective(e, &mut acc)?;
                    } else {
                        elements.push(chunk.into_projective(e)?);
                        heap.push(Exp {
                            scalar: scalar.into_repr(e),
                            index: elements.len() - 1
                        });
                    }
                }

                let mut window = <<Source::Chunk as Chunk<E>>::Projective as Projective<E>>::new_window_table(e);
                let mut scratch = wnaf::WNAFTable::new();

                // Now that the heap is populated...
                while let Some(mut greatest) = heap.pop() {
                    {
                        let second_greatest = heap.peek();
                        if second_greatest.is_none() || justexp::<E>(&greatest.scalar, &second_greatest.unwrap().scalar) {
                            // Either this is the last value or multiplying is considered more efficient than
                            // rewriting and reinsertion into the heap.
                            //opt_exp(engine, &mut elements[greatest.index], greatest.scalar, &mut table);
                            elements[greatest.index].exponentiate(e, greatest.scalar, &mut window, &mut scratch);
                            elements[greatest.index].add_to_projective(e, &mut acc);
                            continue;
                        } else {
                            // Rewrite
                            let second_greatest = second_greatest.unwrap();

                            greatest.scalar.sub_noborrow(&second_greatest.scalar);
                            let mut tmp = elements[second_greatest.index];
                            elements[greatest.index].add_to_projective(e, &mut tmp);
                            elements[second_greatest.index] = tmp;
                        }
                    }
                    if !greatest.scalar.is_zero() {
                        // Reinsert only nonzero scalars.
                        heap.push(greatest);
                    }
                }

                Ok(acc)
            }));
        }


        let mut acc = Projective::<E>::identity(e);
        for t in threads {
            t.join()?.add_to_projective(e, &mut acc);
        }

        Ok(acc)
    })
}

struct Exp<E: Engine> {
    scalar: <E::Fr as PrimeField<E>>::Repr,
    index: usize
}

impl<E: Engine> Ord for Exp<E> {
    fn cmp(&self, other: &Exp<E>) -> Ordering {
        self.scalar.cmp(&other.scalar)
    }
}

impl<E: Engine> PartialOrd for Exp<E> {
    fn partial_cmp(&self, other: &Exp<E>) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<E: Engine> PartialEq for Exp<E> {
    fn eq(&self, other: &Exp<E>) -> bool {
        self.scalar == other.scalar
    }
}

impl<E: Engine> Eq for Exp<E> { }
