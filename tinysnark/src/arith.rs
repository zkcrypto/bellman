use libc::{c_ulong, c_long};
use std::ops::{Neg, Add, Mul};

extern "C" {
    fn tinysnark_fieldt_zero() -> FieldT;
    fn tinysnark_fieldt_one() -> FieldT;
    fn tinysnark_fieldt_neg(val: FieldT) -> FieldT;
    fn tinysnark_fieldt_inverse(val: FieldT) -> FieldT;
    fn tinysnark_fieldt_from_long(val: c_long) -> FieldT;
    fn tinysnark_long_from_fieldt(val: FieldT) -> c_ulong;
    fn tinysnark_fieldt_mul(a: FieldT, b: FieldT) -> FieldT;
    fn tinysnark_fieldt_add(a: FieldT, b: FieldT) -> FieldT;
}

#[derive(Copy, Clone, Debug)]
#[repr(simd)]
struct EightBytes(u64);

#[derive(Copy, Clone, Debug)]
#[repr(C)]
pub struct FieldT([u8; 32], [EightBytes; 0]);

impl FieldT {
    #[inline(always)]
    pub fn one() -> FieldT {
        unsafe { tinysnark_fieldt_one() }
    }

    #[inline(always)]
    pub fn zero() -> FieldT {
        unsafe { tinysnark_fieldt_zero() }
    }

    pub fn exp(&self, by: usize) -> FieldT {
        let mut acc = FieldT::one();
        for _ in 0..by {
            acc = acc * (*self);
        }

        acc
    }

    #[inline(always)]
    pub fn inverse(self) -> FieldT {
        unsafe { tinysnark_fieldt_inverse(self) }
    }

    #[cfg(test)]
    pub fn debug_equal(&self, is: [u8; 32]) -> bool {
        &FieldT(is, []) == self
    }
}

impl From<i64> for FieldT {
    #[inline(always)]
    fn from(num: i64) -> FieldT {
        unsafe { tinysnark_fieldt_from_long(num) }
    }
}

impl From<FieldT> for u64 {
    #[inline(always)]
    fn from(num: FieldT) -> u64 {
        unsafe { tinysnark_long_from_fieldt(num) }
    }
}

impl Neg for FieldT {
    type Output = FieldT;

    #[inline(always)]
    fn neg(self) -> FieldT {
        unsafe { tinysnark_fieldt_neg(self) }
    }
}

impl Add for FieldT {
    type Output = FieldT;

    #[inline(always)]
    fn add(self, other: FieldT) -> FieldT {
        unsafe { tinysnark_fieldt_add(self, other) }
    }
}

impl Mul for FieldT {
    type Output = FieldT;

    #[inline(always)]
    fn mul(self, other: FieldT) -> FieldT {
        unsafe { tinysnark_fieldt_mul(self, other) }
    }
}

impl PartialEq for FieldT {
    fn eq(&self, other: &FieldT) -> bool {
        for i in 0..32 {
            if (self.0)[i] != (other.0)[i] {
                return false;
            }
        }

        true
    }
}

impl Eq for FieldT { }
