// Assemble the linked serve object into a static archive and hand it to the
// linker.
//
// For this scaffold the object is a small stand-in (`cake_serve_stub.c`) that
// reproduces the runtime ABI exactly: a global `serve` export-function symbol
// (SysV args rdi/rsi/rdx/rcx = ctrl, req, len, resp), a `cml_main` init entry,
// and the heap/stack region slots — with the slots given per-thread storage so
// each shard has its own heap. To link the real emitted stage instead, swap
// `SRC` for the compiler-emitted object's `.S`/`.c` (its `serve` symbol has the
// same SysV signature) and provide the heap slots per-thread as documented in
// src/lib.rs.
use std::process::Command;

const SRC: &str = "cake_serve_stub.c";

fn main() {
    let out = std::env::var("OUT_DIR").unwrap();
    println!("cargo:rerun-if-changed={}", SRC);
    println!("cargo:rerun-if-changed=build.rs");

    let obj = format!("{}/cake_serve_stub.o", out);
    let ok = Command::new("cc")
        .args(["-c", "-O2", "-fPIC", SRC, "-o", &obj])
        .status()
        .expect("failed to spawn cc")
        .success();
    assert!(ok, "compiling {} failed", SRC);

    let lib = format!("{}/libcakeservestub.a", out);
    let _ = std::fs::remove_file(&lib);
    let ok = Command::new("ar")
        .args(["rcs", &lib, &obj])
        .status()
        .expect("failed to spawn ar")
        .success();
    assert!(ok, "archiving {} failed", obj);

    println!("cargo:rustc-link-search=native={}", out);
    println!("cargo:rustc-link-lib=static=cakeservestub");
}
