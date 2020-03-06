This is Rust FFI wrapper around the
[`blake2-avx2`](https://github.com/sneves/blake2-avx2) C implementation,
which is vendored here and statically linked. It's intended for
benchmarking only. This code assumes AVX2 support and isn't suitable for
shipping.
