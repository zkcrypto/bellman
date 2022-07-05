# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to Rust's notion of
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.13.1] - 2022-07-05
### Added
- `bellman::groth16::batch::Verifier` now has a `verify_multicore` method (when
  the `multicore` feature is enabled) which will internally use the global rayon
  thread pool to parallelize the verification of a batch of proofs.

### Changed
- The `multicore` feature now enables the `getrandom` feature of the `rand_core`
  crate.

## [0.13.0] - 2022-05-06
### Added
- `bellman::multiexp::Exponent`

### Changed
- `bellman::multiexp::multiexp` now takes exponents as `Arc<Vec<Exponent<_>>>`
  instead of `Arc<Vec<FieldBits<_>>>`.

### Fixed
- Migrating from `bitvec 0.22` to `bitvec 1.0` caused a performance regression
  in `bellman::multiexp::multiexp`, slowing down proof creation. Some of that
  performance has been regained by refactoring `multiexp`.

## [0.12.0] - 2022-05-04
### Changed
- MSRV bumped to `1.56.0`
- Bumped dependencies to `ff 0.12`, `group 0.12`, `pairing 0.22`, `bitvec 1.0`, `blake2s_simd 1.0`.

## [0.11.2] - 2022-05-04
### Fixed
- Groth16 prover now correctly computes query densitites with respect to linear
  combinations that contain coefficients of zero.
- Fixed an infinite recursion bug in the `Display` implementation for `SynthesisError`.

## [0.11.1] - 2021-09-09
### Fixed
- Compiling with `--no-default-features --features groth16` (i.e. disabling the
  `multicore` feature flag) works again.

### Changed
- `bellman::multicore::Waiter::wait` now consumes `self` (better reflecting the
  fact that you can't wait on the same result twice), instead of taking `&self`
  with `multicore` enabled and `&mut self` with multicore disabled.

## [0.11.0] - 2021-09-08
### Added
- `bellman` now uses `rayon` for multithreading when the (default) `multicore`
  feature flag is enabled. This means that, when this flag is enabled, the
  `RAYON_NUM_THREADS` environment variable controls the number of threads that
  `bellman` will use. The default, which has not changed, is to use the same
  number of threads as logical CPUs.
- `bellman::multicore::Waiter`
- `Default` bound for `bellman::multiexp::DensityTracker`.
- `Default` bound for `bellman::gadgets::test::TestConstraintSystem`.

### Changed
- Bumped dependencies to `ff 0.11`, `group 0.11`, `pairing 0.21`.
- `bellman::multicore` has migrated from `crossbeam` to `rayon`:
  - `bellman::multicore::Worker::compute` now returns
    `bellman::multicore::Waiter`.
  - `bellman::multiexp::multiexp` now returns
    `bellman::multicore::Waiter<Result<G, SynthesisError>>` instead of
    `Box<dyn Future<Item = G, Error = SynthesisError>>`.
  - `bellman::multicore::log_num_cpus` is renamed to `log_num_threads`.
- `bellman::multiexp::SourceBuilder::new` is renamed to `SourceBuilder::build`.

### Removed
- `bellman::multicore::WorkerFuture` (replaced by `Waiter`).

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
