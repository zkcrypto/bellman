# bellman [![Crates.io](https://img.shields.io/crates/v/bellman.svg)](https://crates.io/crates/bellman) #

`bellman` is a crate for building zk-SNARK circuits. It provides circuit traits
and primitive structures, as well as basic gadget implementations such as
booleans and number abstractions.

## Roadmap

`bellman` is being refactored into a generic proving library. Currently it is
pairing-specific, and different types of proving systems need to be implemented
as sub-modules. After the refactor, `bellman` will be generic using the `ff` and
`group` crates, while specific proving systems will be separate crates that pull
in the dependencies they require.

## License

Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or
   http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in the work by you, as defined in the Apache-2.0
license, shall be dual licensed as above, without any additional terms or
conditions.
