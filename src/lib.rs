#![allow(unused_imports)]
#![allow(unused_macros)]
#[macro_use]

extern crate cfg_if;
extern crate pairing as pairing_import;
extern crate rand;
extern crate bit_vec;
extern crate byteorder;

#[macro_use]
mod log;

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

cfg_if! {
    if #[cfg(feature = "multicore")] {
        mod multicore;
        mod worker {
            pub use crate::multicore::*;
        }
    } else {
        mod singlecore;
        mod worker {
            pub use crate::singlecore::*;
        }
    }
}

pub mod pairing {
    pub use pairing_import::*;
}

mod cs;
pub use self::cs::*;

// todo move to log module after removing all references
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