# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Fixed
- Fixed a regression introduced in 0.2.1 in single-proof verification using
  `PreparedVerifyingKey`, affecting `groth16::verify_proof` and
  `groth16::batch::Item::verify_single`. These APIs now correctly handle:
  - Public inputs whose scalar field uses a big-endian `PrimeField::Repr`.
  - Public inputs whose scalar field uses a full-width little-endian
    representation, when wNAF recoding generates a carry beyond its last byte.

  Batch verification APIs were not affected.

### Changed
- Improved single-proof verification performance for proofs with multiple public
  inputs over groups with little-endian scalars.
- The breaking change to the auto trait impls of `PreparedVerifyingKey` in 0.2.1
  has been reverted.

## [0.2.1] - 2026-11-14
### Added
- `groth16::batch` APIs for reusing verifying-key terms across batches:
  - `PreparedBatchG2`
  - `PreparedBatchVerifyingKey`
  - `Verifier::verify_prepared`
  - `Verifier::verify_multicore_prepared`, behind the `multicore` feature.
  - `Verifier::verify_joint_prepared` for verifying two batches under different
    verifying keys.

### Changed
- Raised `pairing` minimum version to `0.24.2`, to improve prepared verifying
  key performance.
- Improved verification performance, with additional preparation work and memory
  usage for `groth16::PreparedVerifyingKey`.
  - **Breaking change:** The `Unpin`, `UnwindSafe`, and `RefUnwindSafe` auto
    trait impls for `PreparedVerifyingKey<E>` now additionally require the
    corresponding trait on `E::G1`. Generic downstream code relying on the
    previous bounds may need updating. The impact is considered negligible:
    `PreparedVerifyingKey`s are normally loaded into a global lock and reused
    through shared references, and neither initialization nor ordinary
    verification requires these traits.
- `groth16::batch::Verifier::{verify, verify_multicore}` are faster. For scalar
  fields wider than 128 bits, a batch containing an invalid proof is now
  accepted with probability at most `1 / (2^128 - 1)` (previously `1 / (r - 1)`
  for `verify` and `8 / (r - 1)` for `verify_multicore`, where `r` is the scalar
  field order).

## [0.2.0] - 2026-09-26
### Added
- The `multicore` feature, which the crate's source already referenced but never
  declared. Without it `groth16::batch::Verifier::verify_multicore` (gated on
  that feature) could not be compiled by any consumer.

### Changed
- MSRV bumped to `1.85`.
- Bumped dependencies to `ff 0.14`, `group 0.14`, `rand_core 0.10`,
  `pairing 0.24`, `bellman 0.15`.

## [0.1.0] - 2024-07-15
Initial release (moved from `bellman::groth16`)
