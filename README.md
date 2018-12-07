# Plasma cash history SNARK

Compacts history in Plasma Cashes by hiding Merkle proofs under the private witness. Currently contains only non-inclusion circuit, with inclusion being trivially extended.

Without much optimization is requires 4270718 constraints for 128 block of non-inclusion for 24 tree depth.

Public inputs to the zkSNARK:

- Start of the interval index (if single coin - just index)
- Interval length (is single coin - 1)
- Set of roots for which this coin index is proved to be non-included

## License

Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in the work by you, as defined in the Apache-2.0
license, shall be dual licensed as above, without any additional terms or
conditions.
