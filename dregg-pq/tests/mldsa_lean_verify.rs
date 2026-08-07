//! BRICK 8 — the FINALE gate: prove the DEPLOYED `dregg_pq::ml_dsa_verify` routes its
//! security-critical accept/reject through the Lean-verified REAL ML-DSA-65 verify core
//! (`Dregg2.Crypto.Fips204Verify.verifyRealFFI` over `MlDsaVerifyReal.verifyCore`, run as leanc-native
//! code via `dregg_lean_ffi::shadow_fips204_verify_real`), NOT the `fips204` crate.
//!
//! The core is installed here (a dev-dep on `dregg-lean-ffi` links the archive — the shipping `dregg-pq`
//! leaf never does). We then exercise `ml_dsa_verify` over a GENUINE `fips204` keypair+signature:
//!   * the honest signature ACCEPTS,
//!   * a one-byte-tampered signature REJECTS,
//!   * a wrong message REJECTS,
//! and the Lean-backed verdict AGREES with the crate's own `PublicKey::verify` on all three — so the swap
//! is behavior-preserving while the AUTHORITY has moved to the verified Lean object.
//!
//! If the leanc/FFI link is absent (a stale archive missing the export), this test FAILS LOUDLY at the
//! `fips204_verify_real_core_available` assertion rather than silently exercising the crate fallback.

use dregg_pq::{
    ML_DSA_PK_LEN, ML_DSA_SIG_LEN, MlDsaKey, install_lean_verify_core_real,
    lean_verify_core_real_installed, ml_dsa_verify,
};
use fips204::ml_dsa_65;
use fips204::traits::{SerDes as _, Verifier as _};

const CTX: &[u8] = b"dregg-pq-brick8-gate-ctx-v1";

/// Install the leanc-native REAL verify core (idempotent: the install is once-per-process).
fn install_core() {
    // ── EXPLICIT OPT-IN to the unaudited fallback, and WHY it is correct here ──────────
    // `dregg-pq`'s refusal gate (`src/audit.rs`) aborts any process that answers a PQ
    // operation with the unaudited `fips204` / `ml-kem` crates. This test is one of the
    // few legitimate exceptions, and it must SAY SO rather than be silently exempted.
    //
    // The authority UNDER TEST here is the Lean-verified REAL verify core: it is installed
    // below, its availability is ASSERTED (not assumed), and every accept/reject verdict
    // this test checks comes from it. What the `fips204` crate is used for is producing the
    // GENUINE keypair + signature that the Lean core is then asked to judge, and serving as
    // the differential oracle its verdict is compared against. That is the whole point of
    // the test — a Lean verify that only ever saw Lean-produced signatures would prove
    // nothing about real-world ones — so the crate is the SUBJECT here, never the authority.
    //
    // The SIGN path is what trips the gate (`MlDsaKey::sign` below), and it is deliberately
    // left on the crate. Note this is not merely a test artifact: `install_verified_mldsa_
    // sign_core_real` has exactly ONE caller in either tree (`node/src/lib.rs`), so most
    // processes still sign with the unaudited crate. See §P.4 of the drorb crypto-TCB ledger.
    //
    // SAFETY: set before this process performs any PQ operation. Test binaries run each
    // integration-test file in its own process, and `install_core()` is the first statement
    // of every test in this file, so no other thread can be mid-operation.
    unsafe { std::env::set_var("DREGG_ALLOW_UNAUDITED_PQ", "1") };

    let _ = install_lean_verify_core_real(|w| dregg_lean_ffi::shadow_fips204_verify_real(w).ok());
}

/// The `fips204` crate's OWN verify bool — the non-authoritative cross-check the routed verify must agree
/// with (the crate is no longer the authority in `ml_dsa_verify`, only a behavioral witness here).
fn crate_verify(pk_bytes: &[u8], ctx: &[u8], msg: &[u8], sig: &[u8]) -> bool {
    let Ok(pk_arr) = <[u8; ML_DSA_PK_LEN]>::try_from(pk_bytes) else {
        return false;
    };
    let Ok(sig_arr) = <[u8; ML_DSA_SIG_LEN]>::try_from(sig) else {
        return false;
    };
    let Ok(vk) = ml_dsa_65::PublicKey::try_from_bytes(pk_arr) else {
        return false;
    };
    vk.verify(msg, &sig_arr, ctx)
}

#[test]
fn ml_dsa_verify_is_lean_backed_accepts_real_rejects_tampers_and_agrees_with_crate() {
    install_core();

    // The whole point of BRICK 8: the leanc-linked REAL verify core is present and installed. If not, the
    // routed verify would fall back to the crate — fail loudly here instead of testing the wrong thing.
    assert!(
        dregg_lean_ffi::fips204_verify_real_core_available(),
        "the leanc-native REAL ML-DSA verify core must be linked+present — rebuild dregg-lean-ffi so \
         the `dregg_fips204_verify_real` export is spliced into the archive"
    );
    assert!(
        lean_verify_core_real_installed(),
        "the real verify core must be installed so `ml_dsa_verify` is Lean-backed"
    );

    // A GENUINE ML-DSA-65 keypair + signature from the `fips204` crate (MlDsaKey uses it under the hood).
    let key = MlDsaKey::from_ed25519_seed(&[42u8; 32]);
    let pk = key.public_bytes();
    let msg = b"brick 8: the deployed verify runs the Lean-verified core over the real bytes";
    let sig = key.sign(CTX, msg);
    assert_eq!(pk.len(), ML_DSA_PK_LEN);
    assert_eq!(sig.len(), ML_DSA_SIG_LEN);

    // 1. ACCEPT the genuine signature — through the Lean core — and agree with the crate's own bool.
    assert!(
        ml_dsa_verify(&pk, CTX, msg, &sig),
        "the Lean-backed verify ACCEPTS the genuine signature"
    );
    assert!(
        crate_verify(&pk, CTX, msg, &sig),
        "sanity: the crate also accepts it"
    );
    assert_eq!(
        ml_dsa_verify(&pk, CTX, msg, &sig),
        crate_verify(&pk, CTX, msg, &sig),
        "Lean-backed verdict AGREES with the crate on the honest signature"
    );

    // 2. REJECT a one-byte-tampered signature (fail-closed), agreeing with the crate.
    let mut tampered = sig.clone();
    tampered[100] ^= 0xff;
    assert!(
        !ml_dsa_verify(&pk, CTX, msg, &tampered),
        "the Lean-backed verify REJECTS a tampered signature"
    );
    assert_eq!(
        ml_dsa_verify(&pk, CTX, msg, &tampered),
        crate_verify(&pk, CTX, msg, &tampered),
        "Lean-backed verdict AGREES with the crate on the tampered signature"
    );

    // 3. REJECT a wrong message under a valid signature, agreeing with the crate.
    let wrong = b"a different message than the one that was actually signed";
    assert!(
        !ml_dsa_verify(&pk, CTX, wrong, &sig),
        "the Lean-backed verify REJECTS a wrong message"
    );
    assert_eq!(
        ml_dsa_verify(&pk, CTX, wrong, &sig),
        crate_verify(&pk, CTX, wrong, &sig),
        "Lean-backed verdict AGREES with the crate on the wrong message"
    );

    // 4. Malformed inputs still fail closed (length gate, before any backend).
    assert!(!ml_dsa_verify(&[], CTX, msg, &sig));
    assert!(!ml_dsa_verify(&pk, CTX, msg, &[]));
}

/// ⚑ **THE NEGATIVE POLE, AT THE WIRE — because at the `bool` it is still free.**
///
/// `ml_dsa_verify` returns `bool`, so `!ml_dsa_verify(…, &tampered)` above is satisfied by ANY
/// fail-closed path: a genuine cryptographic reject, a broken archive, or — until 2026-08-07 — a
/// wire the Lean parser could not read, which `verifyRealFFI` rendered as `"0"`, exactly what a
/// forged signature renders as. Three of the assertions in the test above were therefore
/// indistinguishable from "`dregg_pq::real_verify_wire` and `Fips204Verify.parseByteE` disagree and
/// nothing was verified".
///
/// This test closes that by reading the RAW reply. The tampered signature must come back as the
/// literal `"0"` — the verdict code — and NOT as a `"2 <fault>"` malformed code. If the wire ever
/// drifts, this goes RED and names it, instead of the tamper assertions passing for free.
#[test]
fn the_tampered_rejection_is_a_verdict_not_an_unreadable_wire() {
    install_core();
    assert!(
        dregg_lean_ffi::fips204_verify_real_core_available(),
        "the leanc-native REAL ML-DSA verify core must be linked+present"
    );

    let key = MlDsaKey::from_ed25519_seed(&[42u8; 32]);
    let pk = key.public_bytes();
    let msg = b"brick 8: the deployed verify runs the Lean-verified core over the real bytes";
    let sig = key.sign(CTX, msg);
    let mut tampered = sig.clone();
    tampered[100] ^= 0xff;

    // The exact wire `dregg_pq::ml_dsa_verify` marshals: `hex(pk) hex(msg) hex(ctx) hex(sig)`.
    let hex = |b: &[u8]| b.iter().map(|x| format!("{x:02x}")).collect::<String>();
    let wire_for = |s: &[u8]| format!("{} {} {} {}", hex(&pk), hex(msg), hex(CTX), hex(s));

    let honest = dregg_lean_ffi::shadow_fips204_verify_real(&wire_for(&sig))
        .expect("the linked core answers");
    assert_eq!(honest, "1", "the genuine signature must ACCEPT on the wire");

    let forged = dregg_lean_ffi::shadow_fips204_verify_real(&wire_for(&tampered))
        .expect("the linked core answers");
    assert_eq!(
        forged, "0",
        "a one-byte tamper must come back as the REJECT verdict `\"0\"`. If this is a `\"2 …\"` \
         code, the Lean side could not READ the wire this test built and NOTHING was verified — \
         which before 2026-08-07 was also spelled `\"0\"` and passed silently."
    );

    // And an unreadable wire is a DIFFERENT string, so the two are distinguishable by value.
    let malformed =
        dregg_lean_ffi::shadow_fips204_verify_real("zz zz zz zz").expect("the linked core answers");
    assert!(
        malformed.starts_with('2'),
        "an unreadable wire must render the malformed code, got {malformed:?}"
    );
    assert_ne!(
        forged, malformed,
        "a forged signature and a wire nothing parsed must not be the same answer"
    );
}
