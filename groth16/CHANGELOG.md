# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]
### Added
- The `multicore` feature, which the crate's source already referenced but never
  declared. Without it `groth16::batch::Verifier::verify_multicore` (gated on
  that feature) could not be compiled by any consumer.

### Changed
- MSRV bumped to `1.85.0`.
- Bumped dependencies to `ff 0.14`, `group 0.14`, `rand_core 0.10`,
  `pairing 0.24`.

### Fixed
- `groth16::batch::Verifier::verify_multicore` drew its blinding factors from
  `rand_core::OsRng`, which `rand_core 0.10` removed. It now uses
  `rand::rngs::SysRng` wrapped in `rand_core::UnwrapErr`.

## [0.1.0] - 2024-07-15
Initial release (moved from `bellman::groth16`)
