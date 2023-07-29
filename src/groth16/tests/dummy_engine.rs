use ff::{Field, FieldBits, PrimeField, PrimeFieldBits};
use group::{
    prime::{PrimeCurve, PrimeGroup},
    Curve, CurveAffine, Group, GroupEncoding, UncompressedEncoding, WnafGroup,
};
use pairing::{Engine, MillerLoopResult, MultiMillerLoop, PairingCurveAffine};

use rand_core::RngCore;
use std::iter::Sum;
use std::num::Wrapping;
use std::ops::{Add, AddAssign, BitAnd, Mul, MulAssign, Neg, Shr, Sub, SubAssign};
use std::{fmt, iter::Product};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

const MODULUS_R: Wrapping<u32> = Wrapping(64513);

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Fr(Wrapping<u32>);

impl Default for Fr {
    fn default() -> Self {
        <Fr as Field>::ZERO
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
        iter.fold(Self::ZERO, ::std::ops::Add::add)
    }
}

impl<'r> Sum<&'r Fr> for Fr {
    fn sum<I: Iterator<Item = &'r Fr>>(iter: I) -> Self {
        iter.fold(Self::ZERO, ::std::ops::Add::add)
    }
}

impl Product for Fr {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::ONE, ::std::ops::Mul::mul)
    }
}

impl<'r> Product<&'r Fr> for Fr {
    fn product<I: Iterator<Item = &'r Fr>>(iter: I) -> Self {
        iter.fold(Self::ONE, ::std::ops::Mul::mul)
    }
}

impl Neg for Fr {
    type Output = Self;

    fn neg(mut self) -> Self {
        if !<Fr as Field>::is_zero_vartime(&self) {
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

    #[allow(clippy::op_ref)]
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

    #[allow(clippy::op_ref)]
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

    #[allow(clippy::op_ref)]
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
    const ZERO: Self = Fr(Wrapping(0));
    const ONE: Self = Fr(Wrapping(1));

    fn random(mut rng: impl RngCore) -> Self {
        Fr(Wrapping(rng.next_u32()) % MODULUS_R)
    }

    fn is_zero(&self) -> Choice {
        (self.0).0.ct_eq(&0)
    }

    fn square(&self) -> Self {
        Fr((self.0 * self.0) % MODULUS_R)
    }

    fn double(&self) -> Self {
        Fr((self.0 << 1) % MODULUS_R)
    }

    fn invert(&self) -> CtOption<Self> {
        CtOption::new(
            self.pow_vartime(&[(MODULUS_R.0 as u64) - 2]),
            !<Fr as Field>::is_zero(self),
        )
    }

    fn sqrt_ratio(num: &Self, div: &Self) -> (Choice, Self) {
        ff::helpers::sqrt_ratio_generic(num, div)
    }

    #[allow(clippy::many_single_char_names)]
    fn sqrt(&self) -> CtOption<Self> {
        // Tonelli-Shank's algorithm for q mod 16 = 1
        // https://eprint.iacr.org/2012/685.pdf (page 12, algorithm 5)
        let mut c = Fr::ROOT_OF_UNITY;
        // r = self^((t + 1) // 2)
        let mut r = self.pow_vartime([32u64]);
        // t = self^t
        let mut t = self.pow_vartime([63u64]);
        let mut m = Fr::S;

        while t != <Fr as Field>::ONE {
            let mut i = 1;
            {
                let mut t2i = t.square();
                loop {
                    if t2i == <Fr as Field>::ONE {
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

#[derive(Copy, Clone, Debug, Default, Eq, PartialEq)]
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

impl PrimeField for Fr {
    type Repr = FrRepr;

    const NUM_BITS: u32 = 16;
    const CAPACITY: u32 = 15;
    const S: u32 = 10;

    fn from_repr(repr: FrRepr) -> CtOption<Self> {
        let v = u64::from_le_bytes(repr.0);
        let is_some = Choice::from(if v >= (MODULUS_R.0 as u64) { 0 } else { 1 });
        CtOption::new(Fr(Wrapping(v as u32)), is_some)
    }

    fn to_repr(&self) -> FrRepr {
        FrRepr::from(*self)
    }

    fn is_odd(&self) -> Choice {
        Choice::from(((self.0).0 % 2) as u8)
    }

    const MODULUS: &'static str = "64513";
    const TWO_INV: Self = Fr(Wrapping(32257));
    const MULTIPLICATIVE_GENERATOR: Self = Fr(Wrapping(5));
    const ROOT_OF_UNITY: Self = Fr(Wrapping(57751));
    const ROOT_OF_UNITY_INV: Self = Fr(Wrapping(12832));
    const DELTA: Self = Fr(Wrapping(38779));
}

impl PrimeFieldBits for Fr {
    type ReprBits = u64;

    fn to_le_bits(&self) -> FieldBits<Self::ReprBits> {
        FieldBits::new((self.0).0 as u64)
    }

    fn char_le_bits() -> FieldBits<Self::ReprBits> {
        FieldBits::new(MODULUS_R.0 as u64)
    }
}

#[derive(Clone, Debug)]
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
        Self::multi_miller_loop(&[(p, &(*q))]).final_exponentiation()
    }
}

impl MultiMillerLoop for DummyEngine {
    type G2Prepared = Fr;
    // TODO: This should be F_645131 or something. Doesn't matter for now.
    type Result = Fr;

    fn multi_miller_loop(terms: &[(&Self::G1Affine, &Self::G2Prepared)]) -> Self::Result {
        let mut acc = <Fr as Field>::ZERO;

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
        <Fr as Field>::ZERO
    }

    fn generator() -> Self {
        <Fr as Field>::ONE
    }

    fn is_identity(&self) -> Choice {
        <Fr as Field>::is_zero(self)
    }

    fn double(&self) -> Self {
        <Fr as Field>::double(self)
    }
}

impl PrimeGroup for Fr {}

impl Curve for Fr {
    type Affine = Fr;

    fn to_affine(&self) -> Fr {
        *self
    }
}

impl WnafGroup for Fr {
    fn recommended_wnaf_for_num_scalars(_: usize) -> usize {
        3
    }
}

impl PrimeCurve for Fr {}

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

impl CurveAffine for Fr {
    type Curve = Fr;
    type Scalar = Fr;

    fn identity() -> Self {
        <Fr as Field>::ZERO
    }

    fn generator() -> Self {
        <Fr as Field>::ONE
    }

    fn is_identity(&self) -> Choice {
        <Fr as Field>::is_zero(self)
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
