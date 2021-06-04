# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.10.0] - 2021-06-04
### Added
- `bellman::groth16::batch::Verifier`, for performing batched Groth16 proof
  verification.

### Changed
- Bumped dependencies to `bitvec 0.22`, `ff 0.10`, `group 0.10`, `pairing 0.20`.
- MSRV is now 1.51.0.

## [0.9.0] - 2021-01-26
### Changed
- Bumped dependencies to `bitvec 0.20`, `ff 0.9`, `group 0.9`, `pairing 0.19`,
  `rand_core 0.6`.
- MSRV is now 1.47.0.
