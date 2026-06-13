// build.rs — rpath plumbing for the SHARED Lean kernel link.
//
// This crate is a pyo3 cdylib built with `DREGG_LEAN_LINK=shared` (set by
// `.cargo/config.toml`): dregg-lean-ffi's build script links the verified Lean kernel
// against the toolchain's `libleanshared` (+ `libLake_shared`) instead of the static
// runtime archives, and those `rustc-link-lib=dylib=…` / `rustc-link-search` directives
// PROPAGATE here through its `links = "dregg_lean"` key. What does NOT propagate is
// `cargo:rustc-link-arg` — so the rpath that lets the finished extension module FIND
// libleanshared at `import dregg` time must be emitted HERE, on the crate that owns the
// final cdylib link.
//
// Dev builds get an rpath into the active elan toolchain (resolved exactly the way
// dregg-lean-ffi resolves it: `DREGG_LEAN_SYSROOT` override, else `lake env` in the
// sibling `metatheory/`). The wheel/distribution story is documented in README.md.

use std::path::PathBuf;
use std::process::Command;

/// The project's `metatheory` Lean directory (sibling of this crate), overridable via
/// `DREGG_METATHEORY_DIR` — mirrors dregg-lean-ffi/build.rs `metatheory_dir`.
fn metatheory_dir() -> Option<PathBuf> {
    if let Ok(dir) = std::env::var("DREGG_METATHEORY_DIR") {
        let p = PathBuf::from(dir);
        if p.join("lean-toolchain").exists() {
            return Some(p);
        }
    }
    let crate_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let candidate = crate_dir.parent().map(|p| p.join("metatheory"));
    candidate.filter(|p| p.join("lean-toolchain").exists())
}

/// The Lean sysroot — `DREGG_LEAN_SYSROOT` override, else `lake env printenv
/// LEAN_SYSROOT` against the project toolchain (mirrors dregg-lean-ffi/build.rs).
fn lean_sysroot() -> Option<PathBuf> {
    if let Ok(s) = std::env::var("DREGG_LEAN_SYSROOT") {
        if !s.trim().is_empty() {
            return Some(PathBuf::from(s.trim()));
        }
    }
    if let Some(meta) = metatheory_dir() {
        if let Ok(out) = Command::new("lake")
            .args(["env", "printenv", "LEAN_SYSROOT"])
            .current_dir(&meta)
            .output()
        {
            let s = String::from_utf8_lossy(&out.stdout).trim().to_string();
            if !s.is_empty() {
                return Some(PathBuf::from(s));
            }
        }
    }
    None
}

fn main() {
    println!("cargo:rerun-if-env-changed=DREGG_LEAN_LINK");
    println!("cargo:rerun-if-env-changed=DREGG_LEAN_SYSROOT");
    println!("cargo:rerun-if-env-changed=DREGG_METATHEORY_DIR");

    if std::env::var("DREGG_LEAN_LINK").as_deref() != Ok("shared") {
        return;
    }
    let Some(sysroot) = lean_sysroot() else {
        println!(
            "cargo:warning=dregg-sdk-py: DREGG_LEAN_LINK=shared but the Lean sysroot could \
             not be resolved (no DREGG_LEAN_SYSROOT and `lake env` failed in metatheory/) — \
             no rpath emitted; the built module will need LD_LIBRARY_PATH (Linux) / \
             DYLD_LIBRARY_PATH (macOS) pointing at $LEAN_SYSROOT/lib/lean to import."
        );
        return;
    };
    // `-Wl,-rpath,…` is understood by both ld64 (macOS) and GNU/lld (Linux). lib/lean
    // holds libleanshared + libLake_shared; lib/ is where gmp/uv-adjacent pieces live on
    // some toolchains — emit both, matching dregg-lean-ffi's search paths.
    println!(
        "cargo:rustc-link-arg=-Wl,-rpath,{}",
        sysroot.join("lib").join("lean").display()
    );
    println!(
        "cargo:rustc-link-arg=-Wl,-rpath,{}",
        sysroot.join("lib").display()
    );
}
