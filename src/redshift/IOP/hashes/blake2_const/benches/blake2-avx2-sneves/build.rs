fn main() {
    // GCC vs Clang and -mavx2 vs -march=native both have big effects on
    // performance. We hardcode `clang -mavx2` here for an apples-to-apples
    // comparison with rustc and #[target_feature(enable = "avx2")].
    std::env::set_var("CC", "clang");
    cc::Build::new()
        .file("./blake2-avx2/blake2b.c")
        .file("./blake2-avx2/blake2bp.c")
        .file("./blake2-avx2/blake2sp.c")
        // The implementation includes two other input loading strategies.
        // In my testing, shuffles are the fastest.
        // .define("PERMUTE_WITH_NONE", "1")
        // .define("PERMUTE_WITH_GATHER", "1")
        .define("PERMUTE_WITH_SHUFFLES", "1")
        // Enable AVX2 for GCC and Clang.
        .flag_if_supported("-mavx2")
        // Enable AVX2 for MSVC
        .flag_if_supported("/arch:AVX2")
        .compile("blake2-avx2");
}
