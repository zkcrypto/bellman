use std::env;
use std::path::{Path, PathBuf};
use std::process::{self, Command};

fn project_root() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("parent failed")
}

fn run_test_command(project: &str, flags: &[&str]) {
    let project_dir = Path::new(project_root()).join(project);
    println!("=== TEST COMMAND ===");
    println!(
        "cd {} && cargo test {}",
        project_dir.to_string_lossy(),
        flags.join(" ")
    );
    println!();
    let status = Command::new(env!("CARGO"))
        .arg("test")
        .args(flags)
        .current_dir(project_dir)
        .status()
        .expect("spawn failed");

    if !status.success() {
        process::exit(1);
    }
}

fn main() {
    // Set CARGO_TARGET_DIR for all the test runs (unless the caller already set
    // it), so that they can share build artifacts.
    let target_dir = env::var_os("CARGO_TARGET_DIR")
        .map(Into::<PathBuf>::into)
        .unwrap_or(project_root().join("target"));
    env::set_var("CARGO_TARGET_DIR", &target_dir);

    // Test all the sub-projects under both std and no_std.
    for &project in &["blake2b", "blake2s", ".", "blake2_bin"] {
        for &no_std in &[false, true] {
            let mut flags = Vec::new();
            if no_std {
                flags.push("--no-default-features");
            }
            run_test_command(project, &flags);
        }
    }

    // In addition, run the root project under release mode. This lets the fuzz
    // tests use a much larger iteration count.
    run_test_command(".", &["--release"]);
}
