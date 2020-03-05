use crate::ff::*;
use super::{PartialReductionField, PartialTwoBitReductionField};

#[derive(Copy, Clone, PartialEq, Eq, Default)]
pub struct FrRepr(pub [u64; 4usize]);

pub struct Fr(FrRepr);

// const MODULUS: FrRepr = FrRepr([1u64, 0u64, 0u64, 576460752303423505u64]);

const MODULUS: FrRepr = FrRepr([1u64, 0u64, 0u64, 0x0800_0000_0000_0011]);
const MODULUS_TWICE: FrRepr = FrRepr([2u64, 0u64, 0u64, 0x1000_0000_0000_0022]);

const MODULUS_BITS: u32 = 252u32;

const REPR_SHAVE_BITS: u32 = 4u32;

const S: u32 = 192u32;

const C: u64 = 1u64;

// 0800 0000 0000 0011
const K: u64 = 576460752303423505u64;

const K_U128: u128 = 576460752303423505u128;

const NU: [u64; 5] = [
    0x0000028c81fffbff,
    0xfffffffeccf00000,
    0x0000000000907fff,
    0xffffffffffffbc00,
    0x1f
];

const R: FrRepr = FrRepr([
    18446744073709551585u64,
    18446744073709551615u64,
    18446744073709551615u64,
    576460752303422960u64,
]);

const R2: FrRepr = FrRepr([
    18446741271209837569u64,
    5151653887u64,
    18446744073700081664u64,
    576413109808302096u64,
]);

const GENERATOR: FrRepr = FrRepr([
    18446744073709551521u64,
    18446744073709551615u64,
    18446744073709551615u64,
    576460752303421872u64,
]);

const ROOT_OF_UNITY: FrRepr = FrRepr([
    4685640052668284376u64,
    12298664652803292137u64,
    735711535595279732u64,
    514024103053294630u64,
]);

// const INV: u64 = 18446744073709551615u64;

#[inline(always)]
fn add_carry(a: u64, carry: &mut u64) -> u64 {
    // use std::num::Wrapping;

    let (low, of) = a.overflowing_add(*carry);

    if of {
        *carry = 1u64;
    } else {
        *carry = 0u64;
    }

    low

    // let tmp = u128::from(a).wrapping_add(u128::from(*carry));

    // *carry = (tmp >> 64) as u64;

    // tmp as u64
}

#[inline(always)]
fn sub_borrow(a: u64, borrow: &mut u64) -> u64 {
    // use std::num::Wrapping;

    let (low, of) = a.overflowing_sub(*borrow);

    if of {
        *borrow = 1u64;
    } else {
        *borrow = 0u64;
    }

    low

    // let tmp = (1u128 << 64).wrapping_add(u128::from(a)).wrapping_sub(u128::from(*borrow));

    // *borrow = if tmp >> 64 == 0 { 1 } else { 0 };

    // tmp as u64
}
    
impl ::std::fmt::Debug for FrRepr {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "0x")?;
        for i in self.0.iter().rev() {
            write!(f, "{:016x}", i)?;
        }

        Ok(())
    }
}
impl ::rand::Rand for FrRepr {
    #[inline(always)]
    fn rand<R: ::rand::Rng>(rng: &mut R) -> Self {
        FrRepr(rng.gen())
    }
}
impl ::std::fmt::Display for FrRepr {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "0x")?;
        for i in self.0.iter().rev() {
            write!(f, "{:016x}", i)?;
        }

        Ok(())
    }
}
impl AsRef<[u64]> for FrRepr {
    #[inline(always)]
    fn as_ref(&self) -> &[u64] {
        &self.0
    }
}
impl AsMut<[u64]> for FrRepr {
    #[inline(always)]
    fn as_mut(&mut self) -> &mut [u64] {
        &mut self.0
    }
}
impl From<u64> for FrRepr {
    #[inline(always)]
    fn from(val: u64) -> FrRepr {
        use std::default::Default;
        let mut repr = Self::default();
        repr.0[0] = val;
        repr
    }
}
impl Ord for FrRepr {
    #[inline(always)]
    fn cmp(&self, other: &FrRepr) -> ::std::cmp::Ordering {
        for (a, b) in self.0.iter().rev().zip(other.0.iter().rev()) {
            if a < b {
                return ::std::cmp::Ordering::Less;
            } else if a > b {
                return ::std::cmp::Ordering::Greater;
            }
        }
        ::std::cmp::Ordering::Equal
    }
}
impl PartialOrd for FrRepr {
    #[inline(always)]
    fn partial_cmp(&self, other: &FrRepr) -> Option<::std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl crate::ff::PrimeFieldRepr for FrRepr {
    #[inline(always)]
    fn is_odd(&self) -> bool {
        self.0[0] & 1 == 1
    }
    #[inline(always)]
    fn is_even(&self) -> bool {
        !self.is_odd()
    }
    #[inline(always)]
    fn is_zero(&self) -> bool {
        self.0.iter().all(|&e| e == 0)
    }
    #[inline(always)]
    fn shr(&mut self, mut n: u32) {
        if n as usize >= 64 * 4usize {
            *self = Self::from(0);
            return;
        }
        while n >= 64 {
            let mut t = 0;
            for i in self.0.iter_mut().rev() {
                ::std::mem::swap(&mut t, i);
            }
            n -= 64;
        }
        if n > 0 {
            let mut t = 0;
            for i in self.0.iter_mut().rev() {
                let t2 = *i << (64 - n);
                *i >>= n;
                *i |= t;
                t = t2;
            }
        }
    }
    #[inline(always)]
    fn div2(&mut self) {
        let mut t = 0;
        for i in self.0.iter_mut().rev() {
            let t2 = *i << 63;
            *i >>= 1;
            *i |= t;
            t = t2;
        }
    }
    #[inline(always)]
    fn mul2(&mut self) {
        let mut last = 0;
        for i in &mut self.0 {
            let tmp = *i >> 63;
            *i <<= 1;
            *i |= last;
            last = tmp;
        }
    }
    #[inline(always)]
    fn shl(&mut self, mut n: u32) {
        if n as usize >= 64 * 4usize {
            *self = Self::from(0);
            return;
        }
        while n >= 64 {
            let mut t = 0;
            for i in &mut self.0 {
                ::std::mem::swap(&mut t, i);
            }
            n -= 64;
        }
        if n > 0 {
            let mut t = 0;
            for i in &mut self.0 {
                let t2 = *i >> (64 - n);
                *i <<= n;
                *i |= t;
                t = t2;
            }
        }
    }
    #[inline(always)]
    fn num_bits(&self) -> u32 {
        let mut ret = (4usize as u32) * 64;
        for i in self.0.iter().rev() {
            let leading = i.leading_zeros();
            ret -= leading;
            if leading != 64 {
                break;
            }
        }
        ret
    }
    #[inline(always)]
    fn add_nocarry(&mut self, other: &FrRepr) {
        let mut carry = 0;
        for (a, b) in self.0.iter_mut().zip(other.0.iter()) {
            *a = crate::ff::adc(*a, *b, &mut carry);
        }
    }
    #[inline(always)]
    fn sub_noborrow(&mut self, other: &FrRepr) {
        let mut borrow = 0;
        for (a, b) in self.0.iter_mut().zip(other.0.iter()) {
            *a = crate::ff::sbb(*a, *b, &mut borrow);
        }
    }
}

impl FrRepr {
    #[inline(always)]
    fn add_modulus_nocarry(&mut self) {
        let mut carry = MODULUS.0[0usize];
        self.0[0] = add_carry(self.0[0], &mut carry);
        self.0[1] = add_carry(self.0[1], &mut carry);
        self.0[2] = add_carry(self.0[2], &mut carry);

        self.0[3] = crate::ff::adc(self.0[3], MODULUS.0[3usize], &mut carry);
    }

    #[inline(always)]
    fn sub_modulus_noborrow(&mut self) {
        let mut borrow = MODULUS.0[0usize];
        // sub one, so just sub borrow
        self.0[0] = sub_borrow(self.0[0], &mut borrow);
        // sub borrow
        self.0[1] = sub_borrow(self.0[1], &mut borrow);
        // sub borrow
        self.0[2] = sub_borrow(self.0[2], &mut borrow);

        self.0[3] = crate::ff::sbb(self.0[3], MODULUS.0[3usize], &mut borrow);
    }

    #[inline(always)]
    fn add_modulus_twice_nocarry(&mut self) {
        let mut carry = MODULUS_TWICE.0[0];
        self.0[0] = add_carry(self.0[0], &mut carry);
        self.0[1] = add_carry(self.0[1], &mut carry);
        self.0[2] = add_carry(self.0[2], &mut carry);

        self.0[3] = crate::ff::adc(self.0[3], MODULUS_TWICE.0[3usize], &mut carry);
    }

    #[inline(always)]
    fn sub_modulus_twice_noborrow(&mut self) {
        let mut borrow = MODULUS_TWICE.0[0];
        // sub one, so just sub borrow
        self.0[0] = sub_borrow(self.0[0], &mut borrow);
        // sub borrow
        self.0[1] = sub_borrow(self.0[1], &mut borrow);
        // sub borrow
        self.0[2] = sub_borrow(self.0[2], &mut borrow);

        self.0[3] = crate::ff::sbb(self.0[3], MODULUS_TWICE.0[3usize], &mut borrow);
    }
}

impl ::std::marker::Copy for Fr {}
impl ::std::clone::Clone for Fr {
    fn clone(&self) -> Fr {
        *self
    }
}
impl ::std::cmp::PartialEq for Fr {
    fn eq(&self, other: &Fr) -> bool {
        self.0 == other.0
    }
}
impl ::std::cmp::Eq for Fr {}
    
impl ::std::fmt::Debug for Fr {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "{}({:?})", "Fr", self.into_repr())
    }
}

impl Ord for Fr {
    #[inline(always)]
    fn cmp(&self, other: &Fr) -> ::std::cmp::Ordering {
        self.into_repr().cmp(&other.into_repr())
    }
}

impl PartialOrd for Fr {
    #[inline(always)]
    fn partial_cmp(&self, other: &Fr) -> Option<::std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl ::std::fmt::Display for Fr {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "{}({:?})", "Fr", self.into_repr())
    }
}

impl ::rand::Rand for Fr {
    fn rand<R: ::rand::Rng>(rng: &mut R) -> Self {
        loop {
            let mut tmp = Fr(FrRepr::rand(rng));
            tmp.0.as_mut()[3usize] &= 0xffffffffffffffff >> REPR_SHAVE_BITS;
            if tmp.is_valid() {
                return tmp;
            }
        }
    }
}

impl From<Fr> for FrRepr {
    fn from(e: Fr) -> FrRepr {
        e.into_repr()
    }
}
    
impl crate::ff::PrimeField for Fr {
    type Repr = FrRepr;

    fn from_repr(r: FrRepr) -> Result<Fr, crate::ff::PrimeFieldDecodingError> {
        let mut r = Fr(r);
        if r.is_valid() {
            r.mul_assign(&Fr(R2));
            Ok(r)
        } else {
            Err(crate::ff::PrimeFieldDecodingError::NotInField(format!("{}", r.0)))
        }
    }

    fn from_raw_repr(r: FrRepr) -> Result<Self, crate::ff::PrimeFieldDecodingError> {
        let r = Fr(r);
        if r.is_valid() {
            Ok(r)
        } else {
            Err(crate::ff::PrimeFieldDecodingError::NotInField(format!("{}", r.0)))
        }
    }

    fn into_repr(&self) -> FrRepr {
        let mut r = *self;
        r.mont_reduce(
            (self.0).0[0usize],
            (self.0).0[1usize],
            (self.0).0[2usize],
            (self.0).0[3usize],
            0,
            0,
            0,
            0,
        );

        r.0
    }

    fn into_raw_repr(&self) -> FrRepr {
        let r = *self;
        r.0
    }

    fn char() -> FrRepr {
        MODULUS
    }

    const NUM_BITS: u32 = MODULUS_BITS;
    const CAPACITY: u32 = Self::NUM_BITS - 1;

    fn multiplicative_generator() -> Self {
        Fr(GENERATOR)
    }

    const S: u32 = S;
    fn root_of_unity() -> Self {
        Fr(ROOT_OF_UNITY)
    }
}


impl crate::ff::Field for Fr {
    #[inline]
    fn zero() -> Self {
        Fr(FrRepr::default())
    }

    #[inline]
    fn one() -> Self {
        Fr(R)
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.0.is_zero()
    }

    #[inline]
    fn add_assign(&mut self, other: &Fr) {
        self.0.add_nocarry(&other.0);
        self.reduce();
    }

    #[inline]
    fn double(&mut self) {
        self.0.mul2();
        self.reduce();
    }

    #[inline]
    fn sub_assign(&mut self, other: &Fr) {
        if other.0 > self.0 {
            self.0.add_modulus_nocarry();
            // self.0.add_nocarry(&MODULUS);
        }
        self.0.sub_noborrow(&other.0);
    }

    #[inline]
    fn negate(&mut self) {
        if !self.is_zero() {
            let mut tmp = MODULUS;
            tmp.sub_noborrow(&self.0);
            self.0 = tmp;
        }
    }

    fn inverse(&self) -> Option<Self> {
        if self.is_zero() {
            None
        } else {
            let one = FrRepr::from(1);
            let mut u = self.0;
            let mut v = MODULUS;
            let mut b = Fr(R2);
            let mut c = Self::zero();
            while u != one && v != one {
                while u.is_even() {
                    u.div2();
                    if b.0.is_even() {
                        b.0.div2();
                    } else {
                        b.0.add_modulus_nocarry();
                        // b.0.add_nocarry(&MODULUS);
                        b.0.div2();
                    }
                }
                while v.is_even() {
                    v.div2();
                    if c.0.is_even() {
                        c.0.div2();
                    } else {
                        c.0.add_modulus_nocarry();
                        // c.0.add_nocarry(&MODULUS);
                        c.0.div2();
                    }
                }
                if v < u {
                    u.sub_noborrow(&v);
                    b.sub_assign(&c);
                } else {
                    v.sub_noborrow(&u);
                    c.sub_assign(&b);
                }
            }
            if u == one {
                Some(b)
            } else {
                Some(c)
            }
        }
    }

    #[inline(always)]
    fn frobenius_map(&mut self, _: usize) {}

    #[inline]
    fn mul_assign(&mut self, other: &Fr) {
        let mut carry = 0;
        let r0 =
            crate::ff::mac_with_carry(0, (self.0).0[0usize], (other.0).0[0usize], &mut carry);
        let r1 =
            crate::ff::mac_with_carry(0, (self.0).0[0usize], (other.0).0[1usize], &mut carry);
        let r2 =
            crate::ff::mac_with_carry(0, (self.0).0[0usize], (other.0).0[2usize], &mut carry);
        let r3 =
            crate::ff::mac_with_carry(0, (self.0).0[0usize], (other.0).0[3usize], &mut carry);
        let r4 = carry;
        let mut carry = 0;
        let r1 =
            crate::ff::mac_with_carry(r1, (self.0).0[1usize], (other.0).0[0usize], &mut carry);
        let r2 =
            crate::ff::mac_with_carry(r2, (self.0).0[1usize], (other.0).0[1usize], &mut carry);
        let r3 =
            crate::ff::mac_with_carry(r3, (self.0).0[1usize], (other.0).0[2usize], &mut carry);
        let r4 =
            crate::ff::mac_with_carry(r4, (self.0).0[1usize], (other.0).0[3usize], &mut carry);
        let r5 = carry;
        let mut carry = 0;
        let r2 =
            crate::ff::mac_with_carry(r2, (self.0).0[2usize], (other.0).0[0usize], &mut carry);
        let r3 =
            crate::ff::mac_with_carry(r3, (self.0).0[2usize], (other.0).0[1usize], &mut carry);
        let r4 =
            crate::ff::mac_with_carry(r4, (self.0).0[2usize], (other.0).0[2usize], &mut carry);
        let r5 =
            crate::ff::mac_with_carry(r5, (self.0).0[2usize], (other.0).0[3usize], &mut carry);
        let r6 = carry;
        let mut carry = 0;
        let r3 =
            crate::ff::mac_with_carry(r3, (self.0).0[3usize], (other.0).0[0usize], &mut carry);
        let r4 =
            crate::ff::mac_with_carry(r4, (self.0).0[3usize], (other.0).0[1usize], &mut carry);
        let r5 =
            crate::ff::mac_with_carry(r5, (self.0).0[3usize], (other.0).0[2usize], &mut carry);
        let r6 =
            crate::ff::mac_with_carry(r6, (self.0).0[3usize], (other.0).0[3usize], &mut carry);
        let r7 = carry;
        self.mont_reduce(r0, r1, r2, r3, r4, r5, r6, r7);
    }

    #[inline]
    fn square(&mut self) {
        let mut carry = 0;
        let r1 =
            crate::ff::mac_with_carry(0, (self.0).0[0usize], (self.0).0[1usize], &mut carry);
        let r2 =
            crate::ff::mac_with_carry(0, (self.0).0[0usize], (self.0).0[2usize], &mut carry);
        let r3 =
            crate::ff::mac_with_carry(0, (self.0).0[0usize], (self.0).0[3usize], &mut carry);
        let r4 = carry;
        let mut carry = 0;
        let r3 =
            crate::ff::mac_with_carry(r3, (self.0).0[1usize], (self.0).0[2usize], &mut carry);
        let r4 =
            crate::ff::mac_with_carry(r4, (self.0).0[1usize], (self.0).0[3usize], &mut carry);
        let r5 = carry;
        let mut carry = 0;
        let r5 =
            crate::ff::mac_with_carry(r5, (self.0).0[2usize], (self.0).0[3usize], &mut carry);
        let r6 = carry;
        let r7 = r6 >> 63;
        let r6 = (r6 << 1) | (r5 >> 63);
        let r5 = (r5 << 1) | (r4 >> 63);
        let r4 = (r4 << 1) | (r3 >> 63);
        let r3 = (r3 << 1) | (r2 >> 63);
        let r2 = (r2 << 1) | (r1 >> 63);
        let r1 = r1 << 1;
        let mut carry = 0;
        let r0 =
            crate::ff::mac_with_carry(0, (self.0).0[0usize], (self.0).0[0usize], &mut carry);
        let r1 = crate::ff::adc(r1, 0, &mut carry);
        let r2 =
            crate::ff::mac_with_carry(r2, (self.0).0[1usize], (self.0).0[1usize], &mut carry);
        let r3 = crate::ff::adc(r3, 0, &mut carry);
        let r4 =
            crate::ff::mac_with_carry(r4, (self.0).0[2usize], (self.0).0[2usize], &mut carry);
        let r5 = crate::ff::adc(r5, 0, &mut carry);
        let r6 =
            crate::ff::mac_with_carry(r6, (self.0).0[3usize], (self.0).0[3usize], &mut carry);
        let r7 = crate::ff::adc(r7, 0, &mut carry);
        self.mont_reduce(r0, r1, r2, r3, r4, r5, r6, r7);
    }
}

impl std::default::Default for Fr {
    fn default() -> Self {
        Self::zero()
    }
}

impl Fr {
    #[inline(always)]
    fn is_valid(&self) -> bool {
        self.0 < MODULUS
    }

    #[inline(always)]
    fn is_below_modulus_twice(&self) -> bool {
        self.0 < MODULUS_TWICE
    }

    #[inline(always)]
    fn reduce(&mut self) {
        if !self.is_valid() {
            self.0.sub_modulus_noborrow();
            // self.0.sub_noborrow(&MODULUS);
        }
    }

    #[inline(always)]
    fn mont_reduce_unreduced(
        &mut self,
        r0: u64,
        mut r1: u64,
        mut r2: u64,
        mut r3: u64,
        mut r4: u64,
        mut r5: u64,
        mut r6: u64,
        mut r7: u64,
    ) {
        let k = (!r0).wrapping_add(1);
        let mut carry = 0;
        crate::ff::adc(r0, k, &mut carry);
        r1 = add_carry(r1, &mut carry);
        r2 = add_carry(r2, &mut carry);
        r3 = crate::ff::mac_with_carry(r3, k, MODULUS.0[3usize], &mut carry);
        r4 = add_carry(r4, &mut carry);

        let carry2 = carry;
        let k = (!r1).wrapping_add(1);
        let mut carry = 0;
        crate::ff::adc(r1, k, &mut carry);
        r2 = add_carry(r2, &mut carry);
        r3 = add_carry(r3, &mut carry);
        r4 = crate::ff::mac_with_carry(r4, k, MODULUS.0[3usize], &mut carry);
        r5 = crate::ff::adc(r5, carry2, &mut carry);

        let carry2 = carry;
        let k = (!r2).wrapping_add(1);
        let mut carry = 0;
        crate::ff::adc(r2, k, &mut carry);
        r3 = add_carry(r3, &mut carry);
        r4 = add_carry(r4, &mut carry);
        r5 = crate::ff::mac_with_carry(r5, k, MODULUS.0[3usize], &mut carry);
        r6 = crate::ff::adc(r6, carry2, &mut carry);

        let carry2 = carry;
        let k = (!r3).wrapping_add(1);
        let mut carry = 0;
        crate::ff::adc(r3, k, &mut carry);
        r4 = add_carry(r4, &mut carry);
        r5 = add_carry(r5, &mut carry);
        r6 = crate::ff::mac_with_carry(r6, k, MODULUS.0[3usize], &mut carry);
        r7 = crate::ff::adc(r7, carry2, &mut carry);

        (self.0).0[0usize] = r4;
        (self.0).0[1usize] = r5;
        (self.0).0[2usize] = r6;
        (self.0).0[3usize] = r7;
    }

    #[inline(always)]
    fn mont_reduce(&mut self,
        r0: u64,
        r1: u64,
        r2: u64,
        r3: u64,
        r4: u64,
        r5: u64,
        r6: u64,
        r7: u64,
    ) {
        self.mont_reduce_unreduced(r0, r1, r2, r3, r4, r5, r6, r7);
        self.reduce();
    }

    pub fn to_hex(&self) -> String {
        let mut buf: Vec<u8> = Vec::with_capacity(32);
        self.into_repr().write_be(&mut buf).unwrap();
        crate::ff::hex::encode(&buf)
    }

    pub fn from_hex(value: &str) -> Result<Fr, String> {
        let value = if value.starts_with("0x") { &value[2..] } else { value };
        if value.len() % 2 != 0 {return Err(format!("hex length must be even for full byte encoding: {}", value))}
        let mut buf = crate::ff::hex::decode(&value).map_err(|_| format!("could not decode hex: {}", value))?;
        buf.reverse();
        buf.resize(32, 0);
        let mut repr = FrRepr::default();
        repr.read_le(&buf[..]).map_err(|e| format!("could not read {}: {}", value, &e))?;
        Fr::from_repr(repr).map_err(|e| format!("could not convert into prime field: {}: {}", value, &e))
    }
}

impl crate::ff::SqrtField for Fr {
    fn legendre(&self) -> crate::ff::LegendreSymbol {
        let s = self.pow([0u64, 0u64, 9223372036854775808u64, 288230376151711752u64]);
        if s == Self::zero() {
            crate::ff::LegendreSymbol::Zero
        } else if s == Self::one() {
            crate::ff::LegendreSymbol::QuadraticResidue
        } else {
            crate::ff::LegendreSymbol::QuadraticNonResidue
        }
    }
    fn sqrt(&self) -> Option<Self> {
        match self.legendre() {
            crate::ff::LegendreSymbol::Zero => Some(*self),
            crate::ff::LegendreSymbol::QuadraticNonResidue => None,
            crate::ff::LegendreSymbol::QuadraticResidue => {
                let mut c = Fr(ROOT_OF_UNITY);
                let mut r = self.pow([288230376151711753u64, 0u64, 0u64, 0u64]);
                let mut t = self.pow([576460752303423505u64, 0u64, 0u64, 0u64]);
                let mut m = S;
                while t != Self::one() {
                    let mut i = 1;
                    {
                        let mut t2i = t;
                        t2i.square();
                        loop {
                            if t2i == Self::one() {
                                break;
                            }
                            t2i.square();
                            i += 1;
                        }
                    }
                    for _ in 0..(m - i - 1) {
                        c.square();
                    }
                    r.mul_assign(&c);
                    c.square();
                    t.mul_assign(&c);
                    m = i;
                }
                Some(r)
            }
        }
    }
}


impl PartialReductionField for Fr {
    #[inline(always)]
    fn add_assign_unreduced(&mut self, other: &Fr) {
        self.0.add_nocarry(&other.0);
    }

    #[inline(always)]
    fn sub_assign_unreduced(&mut self, other: &Self) {
        self.0.add_modulus_nocarry();
        self.0.sub_noborrow(&other.0);
    }

    #[inline]
    fn mul_assign_unreduced(&mut self, other: &Fr) {
        let mut carry = 0;
        let r0 =
            crate::ff::mac_with_carry(0, (self.0).0[0usize], (other.0).0[0usize], &mut carry);
        let r1 =
            crate::ff::mac_with_carry(0, (self.0).0[0usize], (other.0).0[1usize], &mut carry);
        let r2 =
            crate::ff::mac_with_carry(0, (self.0).0[0usize], (other.0).0[2usize], &mut carry);
        let r3 =
            crate::ff::mac_with_carry(0, (self.0).0[0usize], (other.0).0[3usize], &mut carry);
        let r4 = carry;
        let mut carry = 0;
        let r1 =
            crate::ff::mac_with_carry(r1, (self.0).0[1usize], (other.0).0[0usize], &mut carry);
        let r2 =
            crate::ff::mac_with_carry(r2, (self.0).0[1usize], (other.0).0[1usize], &mut carry);
        let r3 =
            crate::ff::mac_with_carry(r3, (self.0).0[1usize], (other.0).0[2usize], &mut carry);
        let r4 =
            crate::ff::mac_with_carry(r4, (self.0).0[1usize], (other.0).0[3usize], &mut carry);
        let r5 = carry;
        let mut carry = 0;
        let r2 =
            crate::ff::mac_with_carry(r2, (self.0).0[2usize], (other.0).0[0usize], &mut carry);
        let r3 =
            crate::ff::mac_with_carry(r3, (self.0).0[2usize], (other.0).0[1usize], &mut carry);
        let r4 =
            crate::ff::mac_with_carry(r4, (self.0).0[2usize], (other.0).0[2usize], &mut carry);
        let r5 =
            crate::ff::mac_with_carry(r5, (self.0).0[2usize], (other.0).0[3usize], &mut carry);
        let r6 = carry;
        let mut carry = 0;
        let r3 =
            crate::ff::mac_with_carry(r3, (self.0).0[3usize], (other.0).0[0usize], &mut carry);
        let r4 =
            crate::ff::mac_with_carry(r4, (self.0).0[3usize], (other.0).0[1usize], &mut carry);
        let r5 =
            crate::ff::mac_with_carry(r5, (self.0).0[3usize], (other.0).0[2usize], &mut carry);
        let r6 =
            crate::ff::mac_with_carry(r6, (self.0).0[3usize], (other.0).0[3usize], &mut carry);
        let r7 = carry;
        self.mont_reduce_unreduced(r0, r1, r2, r3, r4, r5, r6, r7);
    }

    #[inline(always)]
    fn reduce_once(&mut self) {
        self.reduce();
    }

    #[inline(always)]
    fn reduce_completely(&mut self) {
        self.reduce_once();
    }

    fn overflow_factor(&self) -> usize {
        let mut factor = 0usize;
        let mut this = *self;
        while !this.is_valid() {
            this.0.sub_modulus_noborrow();
            factor += 1;
        }

        factor
    }
}

impl PartialTwoBitReductionField for Fr {
    #[inline(always)]
    fn sub_assign_twice_unreduced(&mut self, other: &Self) {
        self.0.add_modulus_twice_nocarry();
        self.0.sub_noborrow(&other.0);
    }

    #[inline(always)]
    fn reduce_twice(&mut self) {
        if !self.is_below_modulus_twice() {
            self.0.sub_modulus_twice_noborrow();
        }
    }

    #[inline(always)]
    fn reduce_completely(&mut self) {
        self.reduce_twice();
        self.reduce_once();
    }
}