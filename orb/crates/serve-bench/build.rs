//! Link the leanc-compiled proven serve into the microbench, using the SAME
//! recipe as `crates/dataplane/build.rs`: compile the byte-marshalling shim,
//! point the linker at `libdrorb.a` (the proven serve), the Lean runtime, and
//! the crypto backend when present.

use std::path::PathBuf;
use std::process::Command;

fn main() {
    // crates/serve-bench -> crates -> <repo root>.
    let manifest = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap());
    let repo_root = manifest
        .parent()
        .and_then(|p| p.parent())
        .expect("crates/serve-bench must sit two levels under the repo root")
        .to_path_buf();

    // Active Lean toolchain prefix.
    let prefix = {
        let out = Command::new("lean")
            .arg("--print-prefix")
            .output()
            .expect("`lean --print-prefix` failed — is the Lean toolchain on PATH?");
        assert!(out.status.success(), "`lean --print-prefix` returned non-zero");
        PathBuf::from(String::from_utf8(out.stdout).unwrap().trim())
    };
    let lean_include = prefix.join("include");
    let lean_lib = prefix.join("lib").join("lean");

    // 1. Compile the marshalling shim against <lean/lean.h>.
    let shim = manifest.join("ffi").join("drorb_ffi.c");
    println!("cargo:rerun-if-changed={}", shim.display());
    let obj_out = PathBuf::from(std::env::var("OUT_DIR").unwrap());
    let shim_obj = obj_out.join("drorb_ffi.o");
    let cc = std::env::var("CC").unwrap_or_else(|_| "cc".to_string());
    let status = Command::new(&cc)
        .args(["-c", "-O2", "-fPIC"])
        .arg("-I")
        .arg(&lean_include)
        .arg("-o")
        .arg(&shim_obj)
        .arg(&shim)
        .status()
        .expect("failed to spawn C compiler for drorb_ffi.c");
    assert!(status.success(), "compiling drorb_ffi.c failed");
    let shim_lib = obj_out.join("libdrorb_ffi.a");
    let _ = std::fs::remove_file(&shim_lib);
    let status = Command::new("ar")
        .arg("crs")
        .arg(&shim_lib)
        .arg(&shim_obj)
        .status()
        .expect("failed to archive drorb_ffi.o");
    assert!(status.success(), "ar on drorb_ffi.o failed");

    // 2. The leanc-compiled proven serve archive (built by ffi/build-dataplane-lib.sh).
    let drorb_a = repo_root
        .join(".lake")
        .join("build")
        .join("lib")
        .join("libdrorb.a");
    assert!(
        drorb_a.exists(),
        "missing {} — run ffi/build-dataplane-lib.sh first",
        drorb_a.display()
    );
    println!("cargo:rerun-if-changed={}", drorb_a.display());

    println!("cargo:rustc-link-search=native={}", obj_out.display());
    println!(
        "cargo:rustc-link-search=native={}",
        drorb_a.parent().unwrap().display()
    );
    println!("cargo:rustc-link-search=native={}", lean_lib.display());

    println!("cargo:rustc-link-lib=static=drorb");
    println!("cargo:rustc-link-lib=static=drorb_ffi");
    println!("cargo:rustc-link-lib=dylib=leanshared");

    // Crypto backend, linked when present (the deployStepIngress serve closure
    // references no crypto symbols, so absence is fine for this path).
    let crypto_shim = repo_root.join("ffi").join("crypto_shim.o");
    if crypto_shim.exists() {
        println!("cargo:rerun-if-changed={}", crypto_shim.display());
        println!("cargo:rustc-link-arg={}", crypto_shim.display());
    }
    let aes_dir = repo_root.join("target").join("release");
    if aes_dir.join("libaes_fallback.a").exists() {
        println!("cargo:rustc-link-search=native={}", aes_dir.display());
        println!("cargo:rustc-link-lib=static=aes_fallback");
    }
    let hacl_dist = std::env::var("HACL_DIST").unwrap_or_else(|_| {
        let home = std::env::var("HOME").unwrap();
        format!("{home}/src/hacl-star/dist/gcc-compatible")
    });
    if std::path::Path::new(&hacl_dist).join("libevercrypt.a").exists() {
        println!("cargo:rustc-link-search=native={hacl_dist}");
        println!("cargo:rustc-link-lib=static=evercrypt");
    }

    println!("cargo:rustc-link-arg=-Wl,-rpath,{}", lean_lib.display());
    if std::env::var("CARGO_CFG_TARGET_OS").as_deref() == Ok("macos") {
        println!("cargo:rustc-link-arg=-Wl,-no_data_const");
    }
}
