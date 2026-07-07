//! Link the leanc-compiled proven serve into the Rust dataplane.
//!
//! Prerequisite (run once, and after any change to Dataplane.lean or its
//! closure): `ffi/build-dataplane-lib.sh`, which runs `lake build
//! Dataplane:static` and archives the compiled module objects into
//! `.lake/build/lib/libdrorb.a`.
//!
//! This script then:
//!   1. compiles the byte-marshalling shim (`ffi/drorb_ffi.c`) against the Lean
//!      toolchain headers, into `libdrorb_ffi.a`;
//!   2. points the linker at `libdrorb.a` (the proven serve) and the Lean
//!      runtime shared library (`libleanshared`), with an rpath so the runtime
//!      is found at execution time.
//!
//! The toolchain is located with `lean --print-prefix` (elan puts `lean` on
//! PATH); no absolute install path is hard-coded.

use std::path::PathBuf;
use std::process::Command;

fn main() {
    // Repo root: crates/dataplane -> crates -> <root>.
    let manifest = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap());
    let repo_root = manifest
        .parent()
        .and_then(|p| p.parent())
        .expect("crates/dataplane must sit two levels under the repo root")
        .to_path_buf();

    // Active Lean toolchain prefix (contains include/lean/lean.h and lib/lean).
    let prefix = {
        let out = Command::new("lean")
            .arg("--print-prefix")
            .output()
            .expect("`lean --print-prefix` failed — is the Lean toolchain (elan) on PATH?");
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

    // 2. The leanc-compiled proven serve archive (built by build-dataplane-lib.sh).
    let drorb_a = repo_root.join(".lake").join("build").join("lib").join("libdrorb.a");
    assert!(
        drorb_a.exists(),
        "missing {} — run ffi/build-dataplane-lib.sh first (lake build Dataplane:static + archive)",
        drorb_a.display()
    );
    println!("cargo:rerun-if-changed={}", drorb_a.display());

    // Link search paths.
    println!("cargo:rustc-link-search=native={}", obj_out.display());
    println!(
        "cargo:rustc-link-search=native={}",
        drorb_a.parent().unwrap().display()
    );
    println!("cargo:rustc-link-search=native={}", lean_lib.display());

    // The proven serve, then the marshalling shim, then the Lean runtime.
    println!("cargo:rustc-link-lib=static=drorb");
    println!("cargo:rustc-link-lib=static=drorb_ffi");
    println!("cargo:rustc-link-lib=dylib=leanshared");

    // The `Crypto` @[extern] seam (ed25519/x25519/AES-GCM/HKDF/SHA) is resolved
    // against the SAME backend the `orb` exe uses: the crypto FFI shim, the
    // AES-GCM Rust fallback, and the F*-verified HACL*/EverCrypt (Project
    // Everest). No unverified C (no libsodium/OpenSSL) crosses this seam.
    //
    // These inputs are linked WHEN PRESENT. The dataplane's serve closure
    // (`deployStepIngress`) references no crypto symbols, so a build whose serve
    // archive needs none of them links cleanly without the crypto toolchain
    // present. The linker remains the ground truth: if the serve archive does
    // reference a crypto symbol and its provider is absent, the link fails with
    // an undefined-symbol error rather than silently succeeding. A serve archive
    // that reaches the Jwt gate therefore still requires the full backend below;
    // one that does not (the current ingress path) does not.
    //
    // Prerequisites, when needed: ffi/build-crypto-shim.sh (ffi/crypto_shim.o),
    // ffi/build-aes-fallback.sh (target/release/libaes_fallback.a), and a built
    // libevercrypt.a. Selective (non-whole-archive) linking pulls only the
    // referenced members, so the second Rust staticlib does not duplicate std.
    let crypto_shim = repo_root.join("ffi").join("crypto_shim.o");
    if crypto_shim.exists() {
        println!("cargo:rerun-if-changed={}", crypto_shim.display());
        println!("cargo:rustc-link-arg={}", crypto_shim.display());
    } else {
        println!("cargo:warning=crypto shim {} absent — linking without it (fine when the serve closure references no crypto)", crypto_shim.display());
    }

    // The CGI process-spawn shim (`ffi/cgi_exec.o`, a POSIX fork/execve/pipe/waitpid
    // gateway). The deployed serve's application layer reaches the `.cgi` route
    // handler (`Cgi.serveCgi` -> `drorb_cgi_exec`), so libdrorb.a references this
    // symbol; link the object when present. Prerequisite: ffi/build-cgi-shim.sh.
    let cgi_exec = repo_root.join("ffi").join("cgi_exec.o");
    if cgi_exec.exists() {
        println!("cargo:rerun-if-changed={}", cgi_exec.display());
        println!("cargo:rustc-link-arg={}", cgi_exec.display());
    } else {
        println!("cargo:warning=ffi/cgi_exec.o absent — run ffi/build-cgi-shim.sh (the serve closure now reaches the CGI route)");
    }

    // The QUIC datagram fork (`drorb_serve_datagram`) reaches `QuicHeaderProt`,
    // whose module object references `drorb_chacha20` — the ONE QUIC
    // header-protection keystream extern (RFC 9001 §5.4.4), defined in
    // ffi/mac_udp.c against EverCrypt's verified ChaCha20 block. Link that object
    // when present so the datagram closure resolves; the byte-stream `drorb_serve`
    // path never references it, so a build without the datagram export links
    // cleanly without it. (mac_udp.o also carries `orb_mac_serve_udp`, unused by
    // this host and left inert.)
    let mac_udp = repo_root.join("ffi").join("mac_udp.o");
    if mac_udp.exists() {
        println!("cargo:rerun-if-changed={}", mac_udp.display());
        println!("cargo:rustc-link-arg={}", mac_udp.display());
    } else {
        println!("cargo:warning=ffi/mac_udp.o absent — linking without it (fine when the serve closure references no QUIC header protection)");
    }

    // The TLS front door (`drorb_tls_serve`) does its own blocking socket I/O
    // through the `ffi/derp_net.o` byte-mover (`drorb_tcp_send` / `_recv_exact` /
    // `_close`) — the same TCP shim the DERP live driver links. libdrorb.a
    // references these symbols once `Dataplane` imports `TlsHandshake.Post` and
    // the TLS seam is archived, so link the object when present. Prerequisite:
    // ffi/build-derp-net.sh (produces ffi/derp_net.o).
    let derp_net = repo_root.join("ffi").join("derp_net.o");
    if derp_net.exists() {
        println!("cargo:rerun-if-changed={}", derp_net.display());
        println!("cargo:rustc-link-arg={}", derp_net.display());
    } else {
        println!("cargo:warning=ffi/derp_net.o absent — run ffi/build-derp-net.sh (the TLS front door needs its TCP byte-mover)");
    }

    // The RFC 8446 §9.1 certificate signature backend (`ffi/tls_p256_shim.o`:
    // `drorb_p256_ecdsa_sign` / `drorb_rsapss_sha256_sign` over HACL*'s verified
    // Hacl_P256 / Hacl_RSAPSS). The TLS front door's multi-certificate pool
    // (`Dataplane.deployedCerts`) instantiates the ECDSA-P256 / RSA-PSS
    // CertificateVerify signers through `TlsCrypto.Sig`, so libdrorb.a references
    // these symbols; link the object when present. Prerequisite:
    // ffi/build-tls-p256-shim.sh.
    let tls_p256 = repo_root.join("ffi").join("tls_p256_shim.o");
    if tls_p256.exists() {
        println!("cargo:rerun-if-changed={}", tls_p256.display());
        println!("cargo:rustc-link-arg={}", tls_p256.display());
    } else {
        println!("cargo:warning=ffi/tls_p256_shim.o absent — run ffi/build-tls-p256-shim.sh (the TLS front door's RSA/ECDSA cert pool needs its HACL* signer)");
    }

    let aes_dir = repo_root.join("target").join("release");
    if aes_dir.join("libaes_fallback.a").exists() {
        println!("cargo:rustc-link-search=native={}", aes_dir.display());
        println!("cargo:rustc-link-lib=static=aes_fallback");
    } else {
        println!("cargo:warning=libaes_fallback.a absent — linking without it (fine when the serve closure references no crypto)");
    }

    // HACL*/EverCrypt distribution (external toolchain). Overridable via
    // HACL_DIST; defaults to the extracted gcc-compatible dist under $HOME.
    let hacl_dist = std::env::var("HACL_DIST").unwrap_or_else(|_| {
        let home = std::env::var("HOME").unwrap();
        format!("{home}/src/hacl-star/dist/gcc-compatible")
    });
    if std::path::Path::new(&hacl_dist).join("libevercrypt.a").exists() {
        println!("cargo:rustc-link-search=native={hacl_dist}");
        println!("cargo:rustc-link-lib=static=evercrypt");
    } else {
        println!("cargo:warning=libevercrypt.a absent under {hacl_dist} — linking without it (fine when the serve closure references no crypto)");
    }

    // Find the runtime dylibs (libleanshared + its libleanshared_1 sibling) at
    // run time without an env var.
    println!("cargo:rustc-link-arg=-Wl,-rpath,{}", lean_lib.display());
    // ld64 on current macOS rejects the toolchain objects' __DATA_CONST segment
    // (missing SG_READ_ONLY); keep the data segment writable — the same
    // workaround the lakefile's exes use. macOS-only: the GNU linker on Linux
    // does not know this flag.
    if std::env::var("CARGO_CFG_TARGET_OS").as_deref() == Ok("macos") {
        println!("cargo:rustc-link-arg=-Wl,-no_data_const");
    }
}
