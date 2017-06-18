use rand;
use std::fmt;

use std::borrow::Borrow;
use serde::{Serialize, Deserialize};
use super::BitIterator;

use super::{Cow, Convert};

pub mod bls381;
pub mod multiexp;
pub mod wnaf;
pub mod domain;

pub trait Engine: Sized + Clone + Send + Sync
{
    type Fq: PrimeField<Self> + Convert<<Self::Fq as PrimeField<Self>>::Repr, Self>;
    type Fr: SnarkField<Self> + Convert<<Self::Fr as PrimeField<Self>>::Repr, Self>;
    type Fqe: SqrtField<Self>;
    type Fqk: Field<Self>;
    type G1: Curve<Self> + Convert<<Self::G1 as Curve<Self>>::Affine, Self>;
    type G2: Curve<Self> + Convert<<Self::G2 as Curve<Self>>::Affine, Self>;

    fn new() -> Self;

    /// Operate over the thread-local engine instance
    fn with<R, F: for<'a> FnOnce(&'a Self) -> R>(F) -> R;

    fn pairing<G1, G2>(&self, p: &G1, q: &G2) -> Self::Fqk
        where G1: Convert<<Self::G1 as Curve<Self>>::Affine, Self>,
              G2: Convert<<Self::G2 as Curve<Self>>::Affine, Self>
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
                                    &'a <Self::G1 as Curve<Self>>::Prepared,
                                    &'a <Self::G2 as Curve<Self>>::Prepared
                               )>;
    fn final_exponentiation(&self, &Self::Fqk) -> Self::Fqk;

    /// Perform multi-exponentiation. g and s must have the same length.
    fn multiexp<G: Curve<Self>>(&self, g: &[G::Affine], s: &[Self::Fr]) -> Result<G, ()>;
    fn batch_baseexp<G: Curve<Self>, S: AsRef<[Self::Fr]>>(&self, table: &wnaf::WindowTable<Self, G>, scalars: S) -> Vec<G::Affine>;

    fn batchexp<G: Curve<Self>, S: AsRef<[Self::Fr]>>(&self, g: &mut [G::Affine], scalars: S, coeff: Option<&Self::Fr>);
}

pub trait Group<E: Engine>: Copy + Send + Sync + Sized
{
    fn group_zero(&E) -> Self;
    fn group_mul_assign(&mut self, &E, scalar: &E::Fr);
    fn group_add_assign(&mut self, &E, other: &Self);
    fn group_sub_assign(&mut self, &E, other: &Self);
}

pub trait Curve<E: Engine>: Sized +
                            Copy +
                            Clone +
                            Send +
                            Sync +
                            fmt::Debug +
                            'static +
                            Group<E> +
                            self::multiexp::Projective<E>
{
    type Affine: CurveAffine<E, Jacobian=Self>;
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
    fn mul_assign<S: Convert<<E::Fr as PrimeField<E>>::Repr, E>>(&mut self, &E, other: &S);

    fn optimal_window(&E, scalar_bits: usize) -> Option<usize>;
    fn optimal_window_batch(&self, &E, scalars: usize) -> wnaf::WindowTable<E, Self>;

    /// Performs optimal exponentiation of this curve element given the scalar, using
    /// wNAF when necessary.
    fn optimal_exp(
        &self,
        e: &E,
        scalar: <E::Fr as PrimeField<E>>::Repr,
        table: &mut wnaf::WindowTable<E, Self>,
        scratch: &mut wnaf::WNAFTable
    ) -> Self {
        let bits = scalar.num_bits();
        match Self::optimal_window(e, bits) {
            Some(window) => {
                table.set_base(e, *self, window);
                scratch.set_scalar(table, scalar);
                table.exp(e, scratch)
            },
            None => {
                let mut tmp = *self;
                tmp.mul_assign(e, &scalar);
                tmp
            }
        }
    }
}

pub trait CurveAffine<E: Engine>: Copy +
                                  Clone +
                                  Sized +
                                  Send +
                                  Sync +
                                  fmt::Debug +
                                  PartialEq +
                                  Eq +
                                  'static
{
    type Jacobian: Curve<E, Affine=Self>;
    type Uncompressed: CurveRepresentation<E, Affine=Self>;

    fn to_jacobian(&self, &E) -> Self::Jacobian;
    fn prepare(self, &E) -> <Self::Jacobian as Curve<E>>::Prepared;
    fn is_zero(&self) -> bool;
    fn mul<S: Convert<<E::Fr as PrimeField<E>>::Repr, E>>(&self, &E, other: &S) -> Self::Jacobian;
    fn negate(&mut self, &E);

    /// Returns true iff the point is on the curve and in the correct
    /// subgroup. This is guaranteed to return true unless the user
    /// invokes `to_affine_unchecked`.
    fn is_valid(&self, &E) -> bool;

    /// Produces an "uncompressed" representation of the curve point according
    /// to IEEE standards.
    fn to_uncompressed(&self, &E) -> Self::Uncompressed;
}

pub trait CurveRepresentation<E: Engine>: Serialize + for<'a> Deserialize<'a>
{
    type Affine: CurveAffine<E>;

    /// If the point representation is valid (lies on the curve, correct
    /// subgroup) this function will return it.
    fn to_affine(&self, e: &E) -> Result<Self::Affine, ()> {
        let p = try!(self.to_affine_unchecked(e));

        if p.is_valid(e) {
            Ok(p)
        } else {
            Err(())
        }
    }

    /// Returns the point under the assumption that it is valid. Undefined
    /// behavior if `to_affine` would have rejected the point.
    fn to_affine_unchecked(&self, &E) -> Result<Self::Affine, ()>;
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
    fn pow<S: AsRef<[u64]>>(&self, engine: &E, exp: S) -> Self
    {
        let mut res = Self::one(engine);

        for i in BitIterator::new(exp) {
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

pub trait PrimeFieldRepr: Clone + Eq + Ord + AsRef<[u64]> {
    fn from_u64(a: u64) -> Self;
    fn sub_noborrow(&mut self, other: &Self);
    fn add_nocarry(&mut self, other: &Self);
    fn num_bits(&self) -> usize;
    fn is_zero(&self) -> bool;
    fn is_odd(&self) -> bool;
    fn div2(&mut self);
}

pub trait PrimeField<E: Engine>: SqrtField<E>
{
    type Repr: PrimeFieldRepr;

    fn from_u64(&E, u64) -> Self;
    fn from_str(&E, s: &str) -> Result<Self, ()>;
    fn from_repr(&E, Self::Repr) -> Result<Self, ()>;
    fn into_repr(&self, &E) -> Self::Repr;

    /// Returns the field characteristic; the modulus.
    fn char(&E) -> Self::Repr;

    /// Returns how many bits are needed to represent an element of this
    /// field.
    fn num_bits(&E) -> usize;

    /// Returns how many bits of information can be reliably stored in the
    /// field element.
    fn capacity(&E) -> usize;
}

pub trait SnarkField<E: Engine>: PrimeField<E> + Group<E>
{
    fn s(&E) -> u64;
    fn multiplicative_generator(&E) -> Self;
    fn root_of_unity(&E) -> Self;
}

#[cfg(test)]
mod tests;

#[test]
fn bls381_test_suite() {
    tests::test_engine::<bls381::Bls381>();
}
