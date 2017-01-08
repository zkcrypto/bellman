use rand;
use std::fmt;

use serde::{Serialize, Deserialize};

pub mod bls381;

pub trait Engine: Sized
{
    type Fq: PrimeField<Self>;
    type Fr: SnarkField<Self>;
    type Fqe: SqrtField<Self>;
    type Fqk: Field<Self>;
    type G1: Group<Self> + Convert<<Self::G1 as Group<Self>>::Affine, Self>;
    type G2: Group<Self> + Convert<<Self::G2 as Group<Self>>::Affine, Self>;

    fn new() -> Self;

    fn pairing<G1, G2>(&self, p: &G1, q: &G2) -> Self::Fqk
        where G1: Convert<<Self::G1 as Group<Self>>::Affine, Self>,
              G2: Convert<<Self::G2 as Group<Self>>::Affine, Self>
    {
        self.final_exponentiation(&self.miller_loop(
            [(
                &(*p.convert(self)).borrow().prepare(self),
                &(*q.convert(self)).borrow().prepare(self)
            )].into_iter()
        ))
    }
    fn miller_loop<'a, I>(&self, I) -> Self::Fqk
        where I: IntoIterator<Item=&'a (
                                    &'a <Self::G1 as Group<Self>>::Prepared,
                                    &'a <Self::G2 as Group<Self>>::Prepared
                               )>;
    fn final_exponentiation(&self, &Self::Fqk) -> Self::Fqk;

    fn multiexp<G: Group<Self>>(&self, &[G::Affine], &[Self::Fr]) -> G;
    fn batch_baseexp<G: Group<Self>>(&self, base: &G, scalars: &[Self::Fr]) -> Vec<G::Affine>;
}

pub trait Group<E: Engine>: Sized +
                            Copy +
                            Clone +
                            Send +
                            Sync +
                            fmt::Debug +
                            'static
{
    type Affine: GroupAffine<E, Self>;
    type Prepared: Clone + Send + Sync + 'static;

    fn zero(&E) -> Self;
    fn one(&E) -> Self;
    fn random<R: rand::Rng>(&E, &mut R) -> Self;

    fn is_zero(&self) -> bool;
    fn is_equal(&self, &E, other: &Self) -> bool;

    fn to_affine(&self, &E) -> Self::Affine;
    fn prepare(&self, &E) -> Self::Prepared;

    fn double(&mut self, &E);
    fn negate(&mut self, engine: &E);
    fn add_assign(&mut self, &E, other: &Self);
    fn sub_assign(&mut self, &E, other: &Self);
    fn add_assign_mixed(&mut self, &E, other: &Self::Affine);
    fn mul_assign<S: Convert<[u64], E>>(&mut self, &E, other: &S);

    fn optimal_window(&E, scalar_bits: usize) -> Option<usize>;
}

pub trait GroupAffine<E: Engine, G: Group<E>>: Copy +
                                               Clone +
                                               Sized +
                                               Send +
                                               Sync +
                                               fmt::Debug +
                                               PartialEq +
                                               Eq +
                                               'static
{
    type Uncompressed: GroupRepresentation<E, G>;

    fn to_jacobian(&self, &E) -> G;
    fn prepare(self, &E) -> G::Prepared;
    fn is_zero(&self) -> bool;
    fn mul<S: Convert<[u64], E>>(&self, &E, other: &S) -> G;
    fn negate(&mut self, &E);

    /// Returns true iff the point is on the curve and in the correct
    /// subgroup. This is guaranteed to return true unless the user
    /// invokes `to_affine_unchecked`.
    fn is_valid(&self, &E) -> bool;

    /// Produces an "uncompressed" representation of the curve point according
    /// to IEEE standards.
    fn to_uncompressed(&self, &E) -> Self::Uncompressed;
}

pub trait GroupRepresentation<E: Engine, G: Group<E>>: Serialize + Deserialize
{
    /// If the point representation is valid (lies on the curve, correct
    /// subgroup) this function will return it.
    fn to_affine(&self, e: &E) -> Result<G::Affine, ()> {
        let p = try!(self.to_affine_unchecked(e));

        if p.is_valid(e) {
            Ok(p)
        } else {
            Err(())
        }
    }

    /// Returns the point under the assumption that it is valid. Undefined
    /// behavior if `to_affine` would have rejected the point.
    fn to_affine_unchecked(&self, &E) -> Result<G::Affine, ()>;
}

pub trait Field<E: Engine>: Sized +
                            Eq +
                            PartialEq +
                            Copy +
                            Clone +
                            Send +
                            Sync +
                            fmt::Debug +
                            'static
{
    fn zero() -> Self;
    fn one(&E) -> Self;
    fn random<R: rand::Rng>(&E, &mut R) -> Self;
    fn is_zero(&self) -> bool;
    fn square(&mut self, engine: &E);
    fn double(&mut self, engine: &E);
    fn negate(&mut self, &E);
    fn add_assign(&mut self, &E, other: &Self);
    fn sub_assign(&mut self, &E, other: &Self);
    fn mul_assign(&mut self, &E, other: &Self);
    fn inverse(&self, &E) -> Option<Self>;
    fn frobenius_map(&mut self, &E, power: usize);
    fn pow<S: Convert<[u64], E>>(&self, engine: &E, exp: &S) -> Self
    {
        let mut res = Self::one(engine);

        for i in BitIterator::from((*exp.convert(engine)).borrow()) {
            res.square(engine);
            if i {
                res.mul_assign(engine, self);
            }
        }

        res
    }
}

pub trait SqrtField<E: Engine>: Field<E>
{
    /// Returns the square root of the field element, if it is
    /// quadratic residue.
    fn sqrt(&self, engine: &E) -> Option<Self>;
}

pub trait PrimeField<E: Engine>: SqrtField<E> + Convert<[u64], E>
{
    /// Little endian representation of a field element.
    type Repr: Convert<[u64], E>;
    fn from_u64(&E, u64) -> Self;
    fn from_str(&E, s: &str) -> Result<Self, ()>;
    fn from_repr(&E, Self::Repr) -> Result<Self, ()>;
    fn into_repr(&self, &E) -> Self::Repr;

    /// Returns an interator over all bits, most significant bit first.
    fn bits(&self, &E) -> BitIterator<Self::Repr>;

    /// Returns the field characteristic; the modulus.
    fn char(&E) -> Self::Repr;

    /// Returns how many bits are needed to represent an element of this
    /// field.
    fn num_bits(&E) -> usize;

    /// Returns how many bits of information can be reliably stored in the
    /// field element.
    fn capacity(&E) -> usize;
}

pub trait SnarkField<E: Engine>: PrimeField<E>
{
    fn s(&E) -> u64;
    fn multiplicative_generator(&E) -> Self;
    fn root_of_unity(&E) -> Self;
}

pub struct BitIterator<T> {
    t: T,
    n: usize
}

impl<T: AsRef<[u64]>> Iterator for BitIterator<T> {
    type Item = bool;

    fn next(&mut self) -> Option<bool> {
        if self.n == 0 {
            None
        } else {
            self.n -= 1;
            let part = self.n / 64;
            let bit = self.n - (64 * part);

            Some(self.t.as_ref()[part] & (1 << bit) > 0)
        }
    }
}

impl<'a> From<&'a [u64]> for BitIterator<&'a [u64]>
{
    fn from(v: &'a [u64]) -> Self {
        assert!(v.len() < 100);

        BitIterator {
            t: v,
            n: v.len() * 64
        }
    }
}

use std::ops::Deref;
use std::borrow::Borrow;

pub enum Cow<'a, T: 'a> {
    Owned(T),
    Borrowed(&'a T)
}

impl<'a, T: 'a> Deref for Cow<'a, T> {
    type Target = T;

    fn deref(&self) -> &T {
        match *self {
            Cow::Owned(ref v) => v,
            Cow::Borrowed(v) => v
        }
    }
}

pub trait Convert<T: ?Sized, E> {
    type Target: Borrow<T>;

    fn convert(&self, &E) -> Cow<Self::Target>;
}

impl<T, E> Convert<T, E> for T {
    type Target = T;

    fn convert(&self, _: &E) -> Cow<T> {
        Cow::Borrowed(self)
    }
}

macro_rules! bit_iter_impl(
    ($n:expr) => {
        impl From<[u64; $n]> for BitIterator<[u64; $n]> {
            fn from(v: [u64; $n]) -> Self {
                BitIterator {
                    t: v,
                    n: $n * 64
                }
            }
        }

        impl<E> Convert<[u64], E> for [u64; $n] {
            type Target = [u64; $n];

            fn convert(&self, _: &E) -> Cow<[u64; $n]> {
                Cow::Borrowed(self)
            }
        }
    };
);

bit_iter_impl!(1);
bit_iter_impl!(2);
bit_iter_impl!(3);
bit_iter_impl!(4);
bit_iter_impl!(5);
bit_iter_impl!(6);

#[cfg(test)]
mod tests;

#[test]
fn bls381_test_suite() {
    tests::test_engine::<bls381::Bls381>();
}
