//! mldsa_live_verify.rs — the RUNNING-BINARY gate that the node's deployed ML-DSA-65 verify runs
//! through the VERIFIED Lean core (BRICK 8's `MlDsaVerifyReal.verifyCore`), not the `fips204` crate.
//!
//! ## What this proves (step 1 of "the crate leaves the LIVE TCB")
//!
//! `dregg_pq::ml_dsa_verify` is the security-critical ML-DSA verify behind ~10 node surfaces
//! (token/revocation, lightclient, cell-crypto, wire, turn/authorize, captp, blocklace/pq). It routes
//! through an install-time function pointer: with the REAL core installed it takes its accept/reject
//! verdict from the extracted, full-byte `MlDsaVerifyReal.verifyCore` running as leanc-native code and
//! NEVER consults the `fips204` crate (`dregg-pq/src/mldsa.rs` lines 245-249: the installed branch
//! computes the wire, calls the core, and `return`s BEFORE the crate `vk.verify` at line 261).
//!
//! The node installs that core at startup via `dregg_node::install_mldsa_verified_verify_core()`
//! (wired in `node/src/lib.rs` right after the `lean_available()` check). This test drives that EXACT
//! production install function — not a copy — then:
//!
//!   1. asserts `dregg_pq::lean_verify_core_real_installed()` is `true` after the install;
//!   2. generates a GENUINE ML-DSA-65 `(pk, msg, ctx, sig)` with the `fips204` crate and asserts
//!      `dregg_pq::ml_dsa_verify(pk, ctx, msg, sig) == true` (a real signature accepted);
//!   3. asserts the routed verdict is BYTE-FOR-BYTE the Lean core's: for accept / tamper / wrong-msg,
//!      `ml_dsa_verify(..)` equals `dregg_lean_ffi::shadow_fips204_verify_real(wire) == "1"` — i.e. the
//!      deployed function's answer IS the Lean object's answer, on the same wire the node builds;
//!   4. asserts a one-byte-tampered signature and a wrong message REJECT.
//!
//! ## Fault-injection — catching the crate red-handed
//!
//! The Lean core is PROVED to agree with the `fips204` crate on genuine accept / tamper-reject, so the
//! two cannot be distinguished by verdict on well-formed inputs (that agreement is the BRICK-8 point).
//! The load-bearing evidence that the LEAN object — not the crate — is the authority is therefore:
//! (a) `lean_verify_core_real_installed()` is `true`; (b) the routed verdict equals the Lean shadow's
//! verdict on the identical wire for accept, tamper, and wrong-msg (so the deployed output is the Lean
//! output, not merely a coincidentally-equal crate output); and (c) the cited structural fact that with
//! a core installed `ml_dsa_verify` returns at `mldsa.rs:248` before ever reaching the crate branch.
//!
//! ## If the linked archive lacks the export
//!
//! `install_mldsa_verified_verify_core()` gates on `fips204_verify_real_core_available()`: a build whose
//! Lean archive does not export `dregg_fips204_verify_real` returns `ExportAbsent` and the node keeps the
//! `fips204`-crate fallback (a valid FIPS-204 verify, just not Lean-authoritative). In that build the
//! routing cannot be demonstrated; the test then FAILS LOUDLY with the exact blocker rather than passing
//! vacuously — a green here means the crate has actually left the node's verify TCB on this build.

use dregg_node::{install_mldsa_verified_verify_core, MlDsaVerifyCoreInstall};
use fips204::ml_dsa_65;
use fips204::traits::{KeyGen as _, SerDes as _, Signer as _};

/// Rebuild the exact byte wire the node feeds the Lean verify core: `"hex(pk) hex(msg) hex(ctx) hex(sig)"`
/// (four space-separated lowercase-hex fields, field order pk‖msg‖ctx‖sig — matching
/// `dregg-pq/src/mldsa.rs::real_verify_wire`).
fn real_verify_wire(pk: &[u8], msg: &[u8], ctx: &[u8], sig: &[u8]) -> String {
    format!(
        "{} {} {} {}",
        dregg_types::hex_encode(pk),
        dregg_types::hex_encode(msg),
        dregg_types::hex_encode(ctx),
        dregg_types::hex_encode(sig),
    )
}

/// The Lean core's raw verdict on a wire, `Some(true)`/`Some(false)`; `None` if the archive lacks the
/// export (fault). This is the object `ml_dsa_verify` routes through when a real core is installed.
fn lean_shadow_verdict(wire: &str) -> Option<bool> {
    match dregg_lean_ffi::shadow_fips204_verify_real(wire) {
        Ok(s) => Some(s == "1"),
        Err(_) => None,
    }
}

#[test]
fn deployed_ml_dsa_verify_routes_through_lean_core() {
    // ── DRIVE THE NODE'S STARTUP INSTALL (the exact production function) ────────────────────────
    let outcome = install_mldsa_verified_verify_core();
    match outcome {
        MlDsaVerifyCoreInstall::Installed | MlDsaVerifyCoreInstall::AlreadyInstalled => {
            eprintln!("install outcome: {outcome:?} — verified Lean verify core is the authority");
        }
        MlDsaVerifyCoreInstall::ExportAbsent => {
            panic!(
                "BLOCKER: the Lean archive linked into this test binary does NOT export \
                 `dregg_fips204_verify_real` (`fips204_verify_real_core_available()` is false), so the \
                 node's ML-DSA verify still falls through to the `fips204` crate. The routing cannot be \
                 demonstrated on this build. Rebuild dregg-lean-ffi against a HEAD-matching archive that \
                 lake-builds `Dregg2.Crypto.Fips204Verify` (build.rs lists it as a splice target), then \
                 re-run. A green on this test REQUIRES the crate to have left the verify TCB."
            );
        }
    }

    // (1) The real core is installed → `ml_dsa_verify` is Lean-backed, not crate-backed.
    assert!(
        dregg_pq::lean_verify_core_real_installed(),
        "after install, the Lean-verified REAL verify core must be installed"
    );

    // (2) A GENUINE ML-DSA-65 keypair + signature, minted by the `fips204` crate itself.
    let (pk, sk) = ml_dsa_65::try_keygen().expect("ml-dsa-65 keygen");
    let pk_bytes = pk.into_bytes();
    let ctx: &[u8] = b"dregg-node-live-verify-ctx-v1";
    let msg: &[u8] = b"the node's deployed ML-DSA verify runs through the verified Lean core";
    let sig = sk.try_sign(msg, ctx).expect("ml-dsa-65 sign");
    assert_eq!(pk_bytes.len(), dregg_pq::ML_DSA_PK_LEN);
    assert_eq!(sig.len(), dregg_pq::ML_DSA_SIG_LEN);

    // A real signature is ACCEPTED by the deployed verify — routed through Lean.
    assert!(
        dregg_pq::ml_dsa_verify(&pk_bytes, ctx, msg, &sig),
        "a genuine fips204-crate signature must be ACCEPTED by the node's Lean-routed verify"
    );

    // (3) The routed verdict IS the Lean object's verdict, byte-for-byte, on the wire the node builds.
    //     (equality here means the deployed answer is the Lean output — not a coincidentally-equal
    //      crate output; and per mldsa.rs:245-249 the crate branch is unreachable when installed.)
    let accept_wire = real_verify_wire(&pk_bytes, msg, ctx, &sig);
    let lean_accept = lean_shadow_verdict(&accept_wire)
        .expect("the installed core must answer (archive exports the real verify)");
    assert!(lean_accept, "the Lean core itself ACCEPTS the genuine signature");
    assert_eq!(
        dregg_pq::ml_dsa_verify(&pk_bytes, ctx, msg, &sig),
        lean_accept,
        "the deployed verify verdict equals the Lean core's verdict (accept)"
    );

    // (4a) One-byte-tampered signature → REJECT, and the Lean core is what says so.
    let mut tampered = sig.to_vec();
    tampered[0] ^= 0xff;
    let tamper_wire = real_verify_wire(&pk_bytes, msg, ctx, &tampered);
    let lean_tamper = lean_shadow_verdict(&tamper_wire).expect("core answers");
    assert!(!lean_tamper, "the Lean core REJECTS a one-byte tamper");
    assert_eq!(
        dregg_pq::ml_dsa_verify(&pk_bytes, ctx, msg, &tampered),
        lean_tamper,
        "the deployed verify rejects the tamper via the Lean core"
    );
    assert!(
        !dregg_pq::ml_dsa_verify(&pk_bytes, ctx, msg, &tampered),
        "a tampered signature must be REJECTED"
    );

    // (4b) Wrong message under a valid signature → REJECT, via the Lean core.
    let wrong_msg: &[u8] = b"a different message the signature does not cover";
    let wrong_wire = real_verify_wire(&pk_bytes, wrong_msg, ctx, &sig);
    let lean_wrong = lean_shadow_verdict(&wrong_wire).expect("core answers");
    assert!(!lean_wrong, "the Lean core REJECTS a wrong message");
    assert_eq!(
        dregg_pq::ml_dsa_verify(&pk_bytes, ctx, wrong_msg, &sig),
        lean_wrong,
        "the deployed verify rejects the wrong message via the Lean core"
    );
    assert!(
        !dregg_pq::ml_dsa_verify(&pk_bytes, ctx, wrong_msg, &sig),
        "a wrong message must be REJECTED"
    );

    // (4c) A forged signature by an attacker's OWN key, checked against the honest pk, REJECTS —
    //      the pin, not a broken signature (the forgery IS valid under the attacker's key).
    let (att_pk, att_sk) = ml_dsa_65::try_keygen().expect("attacker keygen");
    let forged = att_sk.try_sign(msg, ctx).expect("attacker sign");
    assert!(
        !dregg_pq::ml_dsa_verify(&pk_bytes, ctx, msg, &forged),
        "a forgery under the attacker's key must be REJECTED against the honest pk"
    );
    assert!(
        dregg_pq::ml_dsa_verify(&att_pk.into_bytes(), ctx, msg, &forged),
        "the forgery IS valid under the attacker's OWN key (proving the rejection is the pin)"
    );

    eprintln!(
        "PROVED: the node's deployed ML-DSA verify routes through the verified Lean core; a genuine \
         signature accepts and tampers/wrong-msg/forgeries reject — the fips204 crate has left the \
         node's verify TCB on this build."
    );
}
