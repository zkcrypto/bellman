# bellman 
[![Crates.io](https://img.shields.io/crates/v/bellman.svg)](https://crates.io/crates/bellman)
[![Docs.rs](https://docs.rs/bellman/badge.svg)](https://docs.rs/bellman)[![License](https://img.shields.io/crates/l/bellman)](#license)

`bellman` is a Rust crate for constructing zk-SNARK circuits. It provides essential tools to build efficient cryptographic circuits, offering generic field operations and supporting various gadgets for arithmetic and boolean operations. `bellman` enables the creation of cryptographic proofs that are useful in privacy-preserving protocols, blockchain, and more.
## Project Overview

This crate offers an implementation of zk-SNARKs (zero-knowledge succinct non-interactive arguments of knowledge) through a customizable circuit building API. It's designed for developers looking to build cryptographic circuits for applications such as privacy-preserving protocols and blockchain.


## Features
- **zk-SNARK Circuit Construction**: Build cryptographic circuits using a variety of field types.
- **Groth16 Proving System**: Efficient support for the Groth16 proving system.
- **Optimized Arithmetic Operations**: Operations over finite fields.
- **Simple API for Circuit Definition**: Focuses on usability and modularity for easy integration with other Rust projects.

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

## Troubleshooting

**Common Issues**
1. **Compilation Errors:** If you run into errors during compilation, ensure that your Rust toolchain is up-to-date. You can update it using:
```
   rustup update
```
3. Dependency Conflicts: If you face issues with dependency versions, check the `Cargo.toml` for compatibility with your project’s versions. Use `cargo update` to resolve dependency version mismatches.
4. **Missing Features:** If you're using optional features (e.g., multicore processing), ensure all required dependencies are added under the [`features`] section in your `Cargo.toml`

**Running Tests**

To run the included tests, use:
```
cargo test
```

## Acknowledgements
- **Sean Bowe:** Creator of bellman and zk-SNARKs research.
- **Jack Grigg:** Contributed to the development and optimization of bellman.
- **zkcrypto Team:** Maintains the zk-SNARK ecosystem and various cryptographic primitives.
## License

`bellman` is licensed under either:

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or
   http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

You can choose either license.

### Contribution

Contributions are welcome! Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in the work by you shall be dual-licensed as above, without any additional terms or conditions. Please see the [CONTRIBUTING.md](./CONTRIBUTING.md) for more details.
