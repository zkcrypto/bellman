#![allow(unused_imports)]
#![allow(unused_macros)]
#[macro_use]

extern crate cfg_if;
extern crate pairing_ce as pairing_import;
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
        #[cfg(feature = "wasm")]
        compile_error!("Multicore feature is not yet compatible with wasm target arch");

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

use std::str::FromStr;
use std::env;

fn verbose_flag() -> bool {
    option_env!("BELLMAN_VERBOSE").unwrap_or("0") == "1"
}