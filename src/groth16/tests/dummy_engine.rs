use bitvec::{array::BitArray, order::Lsb0};
use ff::{Field, PrimeField};
use group::{
    prime::{PrimeCurve, PrimeCurveAffine, PrimeGroup},
    Curve, Group, GroupEncoding, UncompressedEncoding, WnafGroup,
};
use pairing::{Engine, MillerLoopResult, MultiMillerLoop, PairingCurveAffine};

use rand_core::RngCore;
use std::fmt;
use std::iter::Sum;
use std::num::Wrapping;
use std::ops::{Add, AddAssign, BitAnd, Mul, MulAssign, Neg, Shr, Sub, SubAssign};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

const MODULUS_R: Wrapping<u32> = Wrapping(64513);

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Fr(Wrapping<u32>);

impl Default for Fr {
    fn default() -> Self {
        <Fr as Field>::zero()
    }
}

impl ConstantTimeEq for Fr {
    fn ct_eq(&self, other: &Fr) -> Choice {
        (self.0).0.ct_eq(&(other.0).0)
    }
}

impl fmt::Display for Fr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}", (self.0).0)
    }
}

impl From<u64> for Fr {
    fn from(v: u64) -> Fr {
        Fr(Wrapping((v % MODULUS_R.0 as u64) as u32))
    }
}

impl ConditionallySelectable for Fr {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Fr(Wrapping(u32::conditional_select(
            &(a.0).0,
            &(b.0).0,
            choice,
        )))
    }
}

impl Sum for Fr {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::zero(), ::std::ops::Add::add)
    }
}

impl<'r> Sum<&'r Fr> for Fr {
    fn sum<I: Iterator<Item = &'r Fr>>(iter: I) -> Self {
        iter.fold(Self::zero(), ::std::ops::Add::add)
    }
}

impl Neg for Fr {
    type Output = Self;

    fn neg(mut self) -> Self {
        if !<Fr as Field>::is_zero(&self) {
            self.0 = MODULUS_R - self.0;
        }
        self
    }
}

impl<'r> Add<&'r Fr> for Fr {
    type Output = Self;

    fn add(self, other: &Self) -> Self {
        let mut ret = self;
        AddAssign::add_assign(&mut ret, other);
        ret
    }
}

impl Add for Fr {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        self + &other
    }
}

impl<'r> AddAssign<&'r Fr> for Fr {
    fn add_assign(&mut self, other: &Self) {
        self.0 = (self.0 + other.0) % MODULUS_R;
    }
}

impl AddAssign for Fr {
    fn add_assign(&mut self, other: Self) {
        AddAssign::add_assign(self, &other);
    }
}

impl<'r> Sub<&'r Fr> for Fr {
    type Output = Self;

    fn sub(self, other: &Self) -> Self {
        let mut ret = self;
        SubAssign::sub_assign(&mut ret, other);
        ret
    }
}

impl Sub for Fr {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        self - &other
    }
}

impl<'r> SubAssign<&'r Fr> for Fr {
    fn sub_assign(&mut self, other: &Self) {
        self.0 = ((MODULUS_R + self.0) - other.0) % MODULUS_R;
    }
}

impl SubAssign for Fr {
    fn sub_assign(&mut self, other: Self) {
        SubAssign::sub_assign(self, &other);
    }
}

impl<'r> Mul<&'r Fr> for Fr {
    type Output = Self;

    fn mul(self, other: &Self) -> Self {
        let mut ret = self;
        MulAssign::mul_assign(&mut ret, other);
        ret
    }
}

impl Mul for Fr {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        self * &other
    }
}

impl<'r> MulAssign<&'r Fr> for Fr {
    fn mul_assign(&mut self, other: &Self) {
        self.0 = (self.0 * other.0) % MODULUS_R;
    }
}

impl MulAssign for Fr {
    fn mul_assign(&mut self, other: Self) {
        MulAssign::mul_assign(self, &other);
    }
}

impl BitAnd<u64> for Fr {
    type Output = u64;

    fn bitand(self, rhs: u64) -> u64 {
        (self.0).0 as u64 & rhs
    }
}

impl Shr<u32> for Fr {
    type Output = Fr;

    fn shr(mut self, rhs: u32) -> Fr {
        self.0 = Wrapping((self.0).0 >> rhs);
        self
    }
}

impl Field for Fr {
    fn random(mut rng: impl RngCore) -> Self {
        Fr(Wrapping(rng.next_u32()) % MODULUS_R)
    }

    fn zero() -> Self {
        Fr(Wrapping(0))
    }

    fn one() -> Self {
        Fr(Wrapping(1))
    }

    fn is_zero(&self) -> bool {
        (self.0).0 == 0
    }

    fn square(&self) -> Self {
        Fr((self.0 * self.0) % MODULUS_R)
    }

    fn double(&self) -> Self {
        Fr((self.0 << 1) % MODULUS_R)
    }

    fn invert(&self) -> CtOption<Self> {
        if <Fr as Field>::is_zero(self) {
            CtOption::new(<Fr as Field>::zero(), Choice::from(0))
        } else {
            CtOption::new(
                self.pow_vartime(&[(MODULUS_R.0 as u64) - 2]),
                Choice::from(1),
            )
        }
    }

    fn sqrt(&self) -> CtOption<Self> {
        // Tonelli-Shank's algorithm for q mod 16 = 1
        // https://eprint.iacr.org/2012/685.pdf (page 12, algorithm 5)
        let mut c = Fr::root_of_unity();
        // r = self^((t + 1) // 2)
        let mut r = self.pow_vartime([32u64]);
        // t = self^t
        let mut t = self.pow_vartime([63u64]);
        let mut m = Fr::S;

        while t != <Fr as Field>::one() {
            let mut i = 1;
            {
                let mut t2i = t.square();
                loop {
                    if t2i == <Fr as Field>::one() {
                        break;
                    }
                    t2i = t2i.square();
                    i += 1;
                }
            }

            for _ in 0..(m - i - 1) {
                c = c.square();
            }
            MulAssign::mul_assign(&mut r, &c);
            c = c.square();
            MulAssign::mul_assign(&mut t, &c);
            m = i;
        }

        CtOption::new(r, (r * r).ct_eq(self))
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct FrRepr([u8; 8]);

impl From<Fr> for FrRepr {
    fn from(v: Fr) -> FrRepr {
        FrRepr::from(&v)
    }
}

impl<'a> From<&'a Fr> for FrRepr {
    fn from(v: &'a Fr) -> FrRepr {
        FrRepr(((v.0).0 as u64).to_le_bytes())
    }
}

impl AsMut<[u8]> for FrRepr {
    fn as_mut(&mut self) -> &mut [u8] {
        &mut self.0[..]
    }
}

impl AsRef<[u8]> for FrRepr {
    fn as_ref(&self) -> &[u8] {
        &self.0[..]
    }
}

impl Default for FrRepr {
    fn default() -> FrRepr {
        FrRepr([0; 8])
    }
}

impl PrimeField for Fr {
    type Repr = FrRepr;
    type ReprBits = u64;

    const NUM_BITS: u32 = 16;
    const CAPACITY: u32 = 15;
    const S: u32 = 10;

    fn from_repr(repr: FrRepr) -> Option<Self> {
        let v = u64::from_le_bytes(repr.0);
        if v >= (MODULUS_R.0 as u64) {
            None
        } else {
            Some(Fr(Wrapping(v as u32)))
        }
    }

    fn to_repr(&self) -> FrRepr {
        FrRepr::from(*self)
    }

    fn to_le_bits(&self) -> BitArray<Lsb0, Self::ReprBits> {
        BitArray::new((self.0).0 as u64)
    }

    fn is_odd(&self) -> bool {
        (self.0).0 % 2 != 0
    }

    fn char_le_bits() -> BitArray<Lsb0, Self::ReprBits> {
        BitArray::new(MODULUS_R.0 as u64)
    }

    fn multiplicative_generator() -> Fr {
        Fr(Wrapping(5))
    }

    fn root_of_unity() -> Fr {
        Fr(Wrapping(57751))
    }
}

#[derive(Clone)]
pub struct DummyEngine;

impl Engine for DummyEngine {
    type Fr = Fr;
    type G1 = Fr;
    type G1Affine = Fr;
    type G2 = Fr;
    type G2Affine = Fr;

    // TODO: This should be F_645131 or something. Doesn't matter for now.
    type Gt = Fr;

    fn pairing(p: &Self::G1Affine, q: &Self::G2Affine) -> Self::Gt {
        Self::multi_miller_loop(&[(p, &(*q).into())]).final_exponentiation()
    }
}

impl MultiMillerLoop for DummyEngine {
    type G2Prepared = Fr;
    // TODO: This should be F_645131 or something. Doesn't matter for now.
    type Result = Fr;

    fn multi_miller_loop(terms: &[(&Self::G1Affine, &Self::G2Prepared)]) -> Self::Result {
        let mut acc = <Fr as Field>::zero();

        for &(a, b) in terms {
            let mut tmp = *a;
            MulAssign::mul_assign(&mut tmp, b);
            AddAssign::add_assign(&mut acc, &tmp);
        }

        acc
    }
}

impl MillerLoopResult for Fr {
    type Gt = Fr;

    /// Perform final exponentiation of the result of a miller loop.
    fn final_exponentiation(&self) -> Self::Gt {
        *self
    }
}

impl Group for Fr {
    type Scalar = Fr;

    fn random(rng: impl RngCore) -> Self {
        <Fr as Field>::random(rng)
    }

    fn identity() -> Self {
        <Fr as Field>::zero()
    }

    fn generator() -> Self {
        <Fr as Field>::one()
    }

    fn is_identity(&self) -> Choice {
        Choice::from(if <Fr as Field>::is_zero(self) { 1 } else { 0 })
    }

    fn double(&self) -> Self {
        <Fr as Field>::double(self)
    }
}

impl PrimeGroup for Fr {}

impl Curve for Fr {
    type AffineRepr = Fr;

    fn to_affine(&self) -> Fr {
        *self
    }
}

impl WnafGroup for Fr {
    fn recommended_wnaf_for_num_scalars(_: usize) -> usize {
        3
    }
}

impl PrimeCurve for Fr {
    type Affine = Fr;
}

#[derive(Copy, Clone, Default)]
pub struct FakePoint;

impl AsMut<[u8]> for FakePoint {
    fn as_mut(&mut self) -> &mut [u8] {
        unimplemented!()
    }
}

impl AsRef<[u8]> for FakePoint {
    fn as_ref(&self) -> &[u8] {
        unimplemented!()
    }
}

impl PrimeCurveAffine for Fr {
    type Curve = Fr;
    type Scalar = Fr;

    fn identity() -> Self {
        <Fr as Field>::zero()
    }

    fn generator() -> Self {
        <Fr as Field>::one()
    }

    fn is_identity(&self) -> Choice {
        Choice::from(if <Fr as Field>::is_zero(self) { 1 } else { 0 })
    }

    fn to_curve(&self) -> Self::Curve {
        *self
    }
}

impl GroupEncoding for Fr {
    type Repr = FakePoint;

    fn from_bytes(_bytes: &Self::Repr) -> CtOption<Self> {
        unimplemented!()
    }

    fn from_bytes_unchecked(_bytes: &Self::Repr) -> CtOption<Self> {
        unimplemented!()
    }

    fn to_bytes(&self) -> Self::Repr {
        unimplemented!()
    }
}

impl UncompressedEncoding for Fr {
    type Uncompressed = FakePoint;

    fn from_uncompressed(_bytes: &Self::Uncompressed) -> CtOption<Self> {
        unimplemented!()
    }

    fn from_uncompressed_unchecked(_bytes: &Self::Uncompressed) -> CtOption<Self> {
        unimplemented!()
    }

    fn to_uncompressed(&self) -> Self::Uncompressed {
        unimplemented!()
    }
}

impl PairingCurveAffine for Fr {
    type Pair = Fr;
    type PairingResult = Fr;

    fn pairing_with(&self, other: &Self::Pair) -> Self::PairingResult {
        self.mul(*other)
    }
}
