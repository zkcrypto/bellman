#![allow(unused_imports)]

extern crate pairing as pairing_import;
extern crate rand;
extern crate bit_vec;
extern crate byteorder;

pub mod domain;
pub mod groth16;

#[cfg(feature = "gm17")]
pub mod gm17;
#[cfg(feature = "sonic")]
pub mod sonic;

mod group;
mod source;
mod multiexp;

#[cfg(test)]
mod tests;

#[cfg(feature = "multicore")]
mod multicore;

#[cfg(feature = "singlecore")]
mod singlecore;

mod worker {
    #[cfg(feature = "multicore")]
    pub use crate::multicore::*;

    #[cfg(feature = "singlecore")]
    pub use crate::singlecore::*;
}

pub mod pairing {
    pub use pairing_import::*;
}

mod cs;
pub use self::cs::*;

static mut VERBOSE_SWITCH: i8 = -1;

use std::str::FromStr;
use std::env;

fn verbose_flag() -> bool {
    unsafe {
        if VERBOSE_SWITCH < 0 {
            VERBOSE_SWITCH = FromStr::from_str(&env::var("BELLMAN_VERBOSE").unwrap_or(String::new())).unwrap_or(1);
        }
        match VERBOSE_SWITCH {
            1 => true,
            _ => false,
        }
    }
}