use std::env;
use std::path::PathBuf;
use std::process::Command;

fn target_name() -> &'static str {
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    {
        if is_x86_feature_detected!("avx512f") {
            assert!(
                is_x86_feature_detected!("avx512vl"),
                "AVX-512F supported but not AVX-512VL. This isn't SkylakeX.",
            );
            return "SkylakeX";
        } else if is_x86_feature_detected!("avx2") {
            return "Haswell";
        }
    }
    if std::mem::size_of::<usize>() == 8 {
        "generic64"
    } else if std::mem::size_of::<usize>() == 4 {
        "generic32"
    } else {
        panic!("unexpected word size {}", std::mem::size_of::<usize>())
    }
}

fn main() {
    // Do local CPU feature detection to determine which version to build. This
    // wouldn't be correct if we were building a distributable binary, because
    // the features of the target machine wouldn't necessarily be the same as
    // the features of the build machine. But this build is just for
    // benchmarks, so it's fine.
    let target = target_name();
    let manifest_dir: PathBuf = env::var("CARGO_MANIFEST_DIR").unwrap().into();
    let k12_dir = manifest_dir.join("K12");
    let build_dir = k12_dir.join(format!("bin/{}", target));
    let build_status = Command::new("make")
        .arg(format!("{}/libk12.a", target))
        .current_dir(&k12_dir)
        .status()
        .unwrap();
    assert!(build_status.success());
    println!("cargo:rustc-link-search={}", build_dir.to_str().unwrap());
    println!("cargo:rustc-link-lib=static=k12");
}
