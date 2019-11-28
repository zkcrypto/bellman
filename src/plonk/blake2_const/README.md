# blake2b_simd [![Build Status](https://travis-ci.org/oconnor663/blake2_simd.svg?branch=master)](https://travis-ci.org/oconnor663/blake2_simd) [![docs.rs](https://docs.rs/blake2b_simd/badge.svg)](https://docs.rs/blake2b_simd) [![crates.io](https://img.shields.io/crates/v/blake2b_simd.svg)](https://crates.io/crates/blake2b_simd)<br>blake2s_simd [![Build Status](https://travis-ci.org/oconnor663/blake2_simd.svg?branch=master)](https://travis-ci.org/oconnor663/blake2_simd) [![docs.rs](https://docs.rs/blake2s_simd/badge.svg)](https://docs.rs/blake2s_simd) [![crates.io](https://img.shields.io/crates/v/blake2s_simd.svg)](https://crates.io/crates/blake2s_simd)

An implementation of the BLAKE2(b/s/bp/sp) family of hash functions with:

- 100% stable Rust.
- SIMD implementations based on Samuel Neves' [`blake2-avx2`](https://github.com/sneves/blake2-avx2).
  These are very fast. See the Performance section below.
- Portable, safe implementations for other platforms.
- Dynamic CPU feature detection. Binaries include multiple implementations by default and
  choose the fastest one the processor supports at runtime.
- All the features from the [the BLAKE2 spec](https://blake2.net/blake2.pdf), like adjustable
  length, keying, and associated data for tree hashing.
- The `blake2` command line utility, published as the
  [`blake2_bin`](https://crates.io/crates/blake2_bin) crate, with command line flags for all
  the BLAKE2 variants and associated data features.
- `no_std` support. The `std` Cargo feature is on by default, for CPU feature detection and
  for implementing `std::io::Write`.
- Support for computing multiple BLAKE2b and BLAKE2s hashes in parallel, matching the
  efficiency of BLAKE2bp and BLAKE2sp. See the `many` module in each crate.

## Example

```rust
use blake2b_simd::{blake2b, Params};

let expected = "ca002330e69d3e6b84a46a56a6533fd79d51d97a3bb7cad6c2ff43b354185d6d\
                c1e723fb3db4ae0737e120378424c714bb982d9dc5bbd7a0ab318240ddd18f8d";
let hash = blake2b(b"foo");
assert_eq!(expected, &hash.to_hex());

let hash = Params::new()
    .hash_length(16)
    .key(b"The Magic Words are Squeamish Ossifrage")
    .personal(b"L. P. Waterhouse")
    .to_state()
    .update(b"foo")
    .update(b"bar")
    .update(b"baz")
    .finalize();
assert_eq!("ee8ff4e9be887297cf79348dc35dab56", &hash.to_hex());
```

An example using the included `blake2` command line utility:

```bash
$ cargo install blake2_bin
$ echo hi | blake2 -sp
49228db2a2fa8d25e8b3b2aca5a70234c71490516eaca9cba007b27d59c532b8
```

## Performance

To run small benchmarks yourself, run `cargo +nightly bench`. If you
have OpenSSL, libsodium, and Clang installed on your machine, you can
add `--all-features` to include comparison benchmarks with other native
libraries.

The `benches/bench_multiprocess` sub-crate runs various hash functions
on long inputs in memory and tries to average over many sources of
variability. Here are the results from my laptop for `cargo run --release`:

- Intel Core i5-8250U, Arch Linux, kernel version 5.1.9
- libsodium version 1.0.18
- OpenSSL version 1.1.1.c
- rustc 1.35.0
- Clang 8.0.0

```table
╭─────────────────────────┬────────────╮
│ blake2s_simd many::hash │ 2.458 GB/s │
│ blake2s_simd BLAKE2sp   │ 2.446 GB/s │
│ sneves BLAKE2sp         │ 2.311 GB/s │
│ blake2b_simd many::hash │ 2.229 GB/s │
│ blake2b_simd BLAKE2bp   │ 2.221 GB/s │
│ sneves BLAKE2bp         │ 2.032 GB/s │
│ libsodium BLAKE2b       │ 1.111 GB/s │
│ blake2b_simd BLAKE2b    │ 1.055 GB/s │
│ sneves BLAKE2b          │ 1.054 GB/s │
│ OpenSSL SHA-1           │ 0.972 GB/s │
│ blake2s_simd BLAKE2s    │ 0.686 GB/s │
│ OpenSSL SHA-512         │ 0.667 GB/s │
╰─────────────────────────┴────────────╯
```

Note that `libsodium BLAKE2b` beats `blake2b_simd BLAKE2b` and `sneves
BLAKE2b` by about 5%. This turns out to be a GCC vs LLVM effect. The
Arch Linux libsodium package is built with GCC, which seems to do better
than Clang or rustc under `-mavx2`/`target_feature(enable="avx2")`. If I
build `sneves BLAKE2b` under GCC, it catches up with libsodium, and if I
build libsodium under Clang, it's 14% slower. However, GCC doesn't seem
to benefit from `-march=native`/`target-cpu=native`, while Clang and
rustc do better:

```table
╭─────────────────────────┬────────────╮
│ blake2s_simd many::hash │ 2.586 GB/s │
│ blake2s_simd BLAKE2sp   │ 2.570 GB/s │
│ sneves BLAKE2sp         │ 2.372 GB/s │
│ blake2b_simd many::hash │ 2.368 GB/s │
│ blake2b_simd BLAKE2bp   │ 2.353 GB/s │
│ sneves BLAKE2bp         │ 2.234 GB/s │
│ sneves BLAKE2b          │ 1.211 GB/s │
│ blake2b_simd BLAKE2b    │ 1.206 GB/s │
│ blake2s_simd BLAKE2s    │ 0.730 GB/s │
╰─────────────────────────┴────────────╯
```

The `benches/bench_blake2_bin.py` script benchmarks the `blake2` command
line utility against several Coreutils hashes, on a 1 GB file of random
data. Here are the results from my laptop:

```table
╭─────────────────────┬────────────╮
│ blake2 -sp          │ 1.729 GB/s │
│ blake2 -bp          │ 1.622 GB/s │
│ blake2 -b           │ 0.917 GB/s │
│ coreutils sha1sum   │ 0.856 GB/s │
│ coreutils b2sum     │ 0.714 GB/s │
│ blake2 -s           │ 0.633 GB/s │
│ coreutils md5sum    │ 0.622 GB/s │
│ coreutils sha512sum │ 0.620 GB/s │
╰─────────────────────┴────────────╯
```

## Links

- [v0.1.0 announcement on r/rust](https://www.reddit.com/r/rust/comments/96q69x/code_review_request_an_avx2_implementation_of/)
- [v0.5.1 announcement on r/rust](https://www.reddit.com/r/rust/comments/brqilo/blake2b_simd_is_joined_by_blake2s_simd_with_new/)
- the [experimental Bao hash](https://github.com/oconnor663/bao), based on this BLAKE2 implementation
