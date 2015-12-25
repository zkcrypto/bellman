#![feature(box_syntax, test)]
extern crate libc;

mod arith;

pub use self::arith::*;

use std::sync::{Once, ONCE_INIT};

static START: Once = ONCE_INIT;
static mut INITIALIZED: bool = false;

extern "C" {
    fn tinysnark_init_public_params();
    fn tinysnark_test();
}

pub fn init() {
    START.call_once(|| {
        unsafe { tinysnark_init_public_params(); }
        unsafe { INITIALIZED = true; }
    });
}

pub fn is_initialized() -> bool {
    unsafe { INITIALIZED }
}

pub fn test() {
    unsafe { tinysnark_test(); }
}

#[cfg(test)]
mod tests {
    extern crate test;
    use super::{init, FieldT};
    use self::test::Bencher;

    #[test]
    fn test_one() {
        init();
        let one = FieldT::one();
        let negone = -one;
        let newone = -negone;

        assert!(one == newone);
        assert!(one != negone);
        assert!(newone != negone);

        assert_eq!(one, 1.into());
        assert_eq!(negone, (-1).into());

        assert!(one.debug_equal([251, 255, 255, 79, 28, 52, 150, 172, 41, 205, 96, 159, 149, 118, 252, 54, 46, 70, 121, 120, 111, 163, 110, 102, 47, 223, 7, 154, 193, 119, 10, 14]));
        assert!(negone.debug_equal([6, 0, 0, 160, 119, 193, 75, 151, 103, 163, 88, 218, 178, 113, 55, 241, 46, 18, 8, 9, 71, 162, 225, 81, 250, 192, 41, 71, 177, 214, 89, 34]));
    }

    #[test]
    fn test_math() {
        init();

        assert_eq!(FieldT::one() + 10.into(), 11.into());
        assert_eq!(FieldT::from(2) + 2.into(), FieldT::from(2) * 2.into());
        assert_eq!(FieldT::from(2), FieldT::from(-1) + FieldT::one() * 3.into());

        assert_eq!(FieldT::one(), FieldT::from(100) * FieldT::from(100).inverse());
    }

    #[test]
    fn test_conversions() {
        init();

        for i in 0..10000 {
            let num: FieldT = i.into();
            let back: u64 = num.into();

            assert_eq!(i, back as i64);
        }

        assert_eq!(u64::from(FieldT::from(-1)), 4891460686036598784);
    }
}