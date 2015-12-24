extern crate gcc;

fn main() {
    // we don't need ate-pairing for ALT_BN128, but
    // i'll keep this in case i need it for some reason...
    /*
    let mut cfg = gcc::Config::new();

     cfg.cpp(true)
        .define("BN_SUPPORT_SNARK", None)
        .include("ate-pairing/include")
        .include("xbyak")
        .file("ate-pairing/src/zm.cpp")
        .file("ate-pairing/src/zm2.cpp")
        .compile("libzm.a");
    */

    println!("cargo:rustc-link-lib=gmp");
    println!("cargo:rustc-link-lib=gmpxx");

    let mut cfg = gcc::Config::new();

     cfg.cpp(true)
        .define("NO_PROCPS", None)
        .define("STATIC", None)
        .define("CURVE_ALT_BN128", None)
        .flag("-std=c++11")
        .include("libsnark/src")
        .file("tinysnark.cpp")
        .file("libsnark/src/algebra/curves/alt_bn128/alt_bn128_g1.cpp")
        .file("libsnark/src/algebra/curves/alt_bn128/alt_bn128_g2.cpp")
        .file("libsnark/src/algebra/curves/alt_bn128/alt_bn128_init.cpp")
        .file("libsnark/src/algebra/curves/alt_bn128/alt_bn128_pairing.cpp")
        .file("libsnark/src/algebra/curves/alt_bn128/alt_bn128_pp.cpp")
        .file("libsnark/src/common/utils.cpp")
        .file("libsnark/src/common/profiling.cpp")
    ;
    
    cfg.compile("libtinysnark.a");
}