# bellman 
[![Crates.io](https://img.shields.io/crates/v/bellman.svg)](https://crates.io/crates/bellman)
[![Docs.rs](https://docs.rs/bellman/badge.svg)](https://docs.rs/bellman)[![License](https://img.shields.io/crates/l/bellman)](#license)

`bellman` is a crate for building zk-SNARK circuits in Rust. It provides essential traits, primitive structures, and gadgets (like booleans and number abstractions) for efficient circuit design. Built with flexibility and performance in mind, `bellman` supports generic scalar field types via the `ff` and `group` crates.

## Features
- **zk-SNARK Circuit Design**: Construct circuits generically over a scalar field type.
- **Groth16 Proving System**: Built-in support for the Groth16 zk-SNARK proving system.
- **Primitive Gadgets**: Includes implementations for booleans, arithmetic, and number abstractions.
- **Efficient Arithmetic**: Optimized operations modulo a scalar field's prime.

## Installation
Add `bellman` to your `Cargo.toml`:
```toml
[dependencies]
bitvec = "1"
blake2s_simd = "1"
ff = "0.13"
group = "0.13"
pairing = { version = "0.23", optional = true }
rand_core = "0.6"
byteorder = "1"
subtle = "2.2.1"

# Optional multicore dependencies
crossbeam-channel = { version = "0.5.1", optional = true }
lazy_static = { version = "1.4.0", optional = true }
log = { version = "0.4", optional = true }
num_cpus = { version = "1", optional = true }
rayon = { version = "1.5.1", optional = true }

[dev-dependencies]
bls12_381 = "0.8"
criterion = "0.4"
hex-literal = "0.3"
pairing = "0.23"
rand = "0.8"
rand_xorshift = "0.3"
sha2 = "0.10"

[features]
multicore = ["crossbeam-channel", "lazy_static", "log", "num_cpus", "rayon", "rand_core/getrandom"]
default = ["multicore"]
```

Then, import it in your code:
```
extern crate bellman;
```
## Usage
`bellman` is designed for developers interested in building zk-SNARK circuits in Rust. It allows you to define circuits using traits and constraints over a specified field, such as the `Bls12` field used in Groth16.

For more complex usage and examples, you can refer to the [official bellman-examples repository](https://github.com/arcalinea/bellman-examples), which provides additional code samples and guidance.

## Roadmap
We aim to make `bellman` more modular and easier to use for developers:
- **Modularize the Groth16 Proving System:** Move the Groth16 implementation into a separate crate for cleaner separation of concerns.
- **Expand the Gadget Library:** Add more useful gadgets for complex circuit creation.
- **Improve Documentation:** Continue enhancing the documentation with tutorials and guides for new users.

## License

`bellman` is licensed under either:

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or
   http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

You can choose either license.

### Contribution

Contributions are welcome! Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in the work by you shall be dual-licensed as above, without any additional terms or conditions. Please see the [CONTRIBUTING.md](./CONTRIBUTING.md) for more details.
