// build.rs — rpath plumbing for the Tier-D SHARED Lean executor link.
//
// pg-dregg's `tier-d` feature pulls `dregg-lean-ffi`, which links the verified Lean
// executor. On the pgrx EXTENSION (a cdylib postgres `dlopen`s into the backend),
// the Lean runtime must be linked SHARED (`DREGG_LEAN_LINK=shared`): the static
// runtime archives cannot be linked into a shared object on ELF (`libleanrt.a`'s
// mimalloc members use local-exec TLS — `R_X86_64_TPOFF32` vs `-shared`,
// `dregg-lean-ffi/build.rs` `shared_link_mode`). Under that mode dregg-lean-ffi
// emits `rustc-link-lib=dylib=leanshared` (+ siblings) which PROPAGATE here through
// its `links = "dregg_lean"` key — but `cargo:rustc-link-arg` does NOT propagate, so
// the rpath that lets postgres FIND `libleanshared` when it loads the extension `.so`
// must be emitted HERE, on the crate that owns the final cdylib link. (Same split
// sdk-py's `build.rs` documents; this is the pg-dregg analogue.)
//
// This is a NO-OP unless `DREGG_LEAN_LINK=shared` is set (the cdylib link mode the
// extension uses), so the default postgres-free core build + the static `tier-d`
// test binaries emit nothing (a static link needs no rpath). The rpath points at the
// active elan toolchain's `lib/lean` (resolved exactly as dregg-lean-ffi resolves it:
// `DREGG_LEAN_SYSROOT` override, else `lake env` in the sibling `metatheory/`).

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

    // Only the SHARED cdylib link (the extension `.so`) needs the rpath. The default
    // build + static test binaries set nothing here.
    if std::env::var("DREGG_LEAN_LINK").as_deref() != Ok("shared") {
        return;
    }
    let Some(sysroot) = lean_sysroot() else {
        println!(
            "cargo:warning=pg-dregg: DREGG_LEAN_LINK=shared but the Lean sysroot could not be \
             resolved (no DREGG_LEAN_SYSROOT and `lake env` failed in metatheory/) — no rpath \
             emitted; the loaded extension will need DYLD_LIBRARY_PATH (macOS) / LD_LIBRARY_PATH \
             (Linux) pointing at $LEAN_SYSROOT/lib/lean for postgres to dlopen it."
        );
        return;
    };
    // `-Wl,-rpath,…` is understood by both ld64 (macOS) and GNU/lld (Linux). lib/lean
    // holds libleanshared + libLake_shared; lib/ holds the gmp/uv-adjacent pieces on
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
