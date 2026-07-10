//! mldsa_live_sign.rs — the RUNNING-BINARY gate for the ML-DSA-65 SIGN side of "the crate leaves the
//! LIVE TCB". With the brick-8 SIGN analog now deployed, the SIGN direction reaches the same bar the
//! VERIFY direction already had: the `fips204` crate leaves the node's SIGN TCB.
//!
//! ## What is real (read this before trusting a green)
//!
//! The VERIFY side was already done: BRICK 8's FULL-BYTE `MlDsaVerifyReal.verifyCore` is the authority
//! behind the deployed `dregg_pq::ml_dsa_verify` (see `mldsa_live_verify.rs`).
//!
//! The SIGN side now matches it. The REAL, full-byte sign core `Dregg2.Crypto.MlDsaSignReal.signCore` — the
//! deterministic (`rnd = 0`) Fiat–Shamir-with-aborts signer (skDecode / ExpandMask / NTT / SampleInBall /
//! ExpandA / MakeHint / rejection loop over the real 4032/3309-byte codec, PROVED byte-exact vs the `fips204`
//! crate's deterministic signature) — is `@[export]`ed as `dregg_fips204_sign_real` and installed behind the
//! DEPLOYED byte-level signer `dregg_pq::MlDsaKey::sign` via `install_lean_sign_core_real`. Once installed,
//! `MlDsaKey::sign` / `ml_dsa_sign_from_seed` PRODUCE the 3309-byte signature from the Lean-verified object
//! over the real `sk ‖ msg ‖ ctx` bytes and NEVER consult the `fips204` crate — **the crate leaves the
//! node's SIGN TCB.** On that path the signer is DETERMINISTIC (`rnd = 0`, the FIPS 204 deterministic
//! variant — spec-valid; the crate fallback path is hedged/randomized).
//!
//! This gate proves:
//!
//!   (A) The extracted, verified SCALAR sign object (`Fips204Verify.signCore`, the n=1 model) runs LIVE and
//!       round-trips through the extracted scalar `verifyCore` — both verdicts from the leanc-native Lean
//!       objects, the `fips204` crate consulted for neither.
//!
//!   (B) The DEPLOYED byte-level `MlDsaKey::sign` is now Lean-PRODUCED: after installing the real sign core,
//!       a genuine 3309-byte signature is produced by the extracted `MlDsaSignReal.signCore` — byte-identical
//!       to the leanc-native `shadow_fips204_sign_real` on the same wire (so the deployed path went through
//!       Lean, not the crate), byte-identical to the `fips204` crate's DETERMINISTIC signature on a FRESH
//!       message (so Lean reproduces the crate spec live, not just on the pinned KAT), deterministic across
//!       calls (the hedged crate fallback would differ), and ACCEPTED by both the Lean-verified real verify
//!       core AND the `fips204` crate verifier. The crate has left the SIGN TCB.

use dregg_node::{
    MlDsaSignCoreInstall, MlDsaSignCoreRealInstall, MlDsaVerifyCoreInstall,
    install_mldsa_verified_sign_core, install_mldsa_verified_sign_core_real,
    install_mldsa_verified_verify_core,
};
use fips204::ml_dsa_65;
use fips204::traits::{KeyGen as _, SerDes as _, Signer as _, Verifier as _};

/// Marshal `(sk, msg, ctx)` into the byte wire the Lean real sign core reads — the SAME format
/// `dregg_pq::real_sign_wire` uses: `"hex(sk) hex(msg) hex(ctx)"` (three space-separated lowercase-hex
/// fields; an empty field is the empty token between two spaces).
fn real_sign_wire(sk: &[u8], msg: &[u8], ctx: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut s = String::new();
    for (i, field) in [sk, msg, ctx].into_iter().enumerate() {
        if i != 0 {
            s.push(' ');
        }
        for &b in field {
            s.push(HEX[(b >> 4) as usize] as char);
            s.push(HEX[(b & 0x0f) as usize] as char);
        }
    }
    s
}

fn decode_hex(s: &str) -> Vec<u8> {
    fn nib(c: u8) -> u8 {
        match c {
            b'0'..=b'9' => c - b'0',
            b'a'..=b'f' => c - b'a' + 10,
            _ => panic!("non-hex byte in shadow reply"),
        }
    }
    s.as_bytes()
        .chunks_exact(2)
        .map(|p| (nib(p[0]) << 4) | nib(p[1]))
        .collect()
}

/// Drive the EXACT production scalar sign-core install and fail loudly if the linked archive lacks the
/// export (a green must mean the verified sign object actually ran live, never a vacuous skip).
fn install_scalar_sign_core_or_panic() {
    match install_mldsa_verified_sign_core() {
        MlDsaSignCoreInstall::Installed | MlDsaSignCoreInstall::AlreadyInstalled => {}
        MlDsaSignCoreInstall::ExportAbsent => panic!(
            "BLOCKER: the Lean archive linked into this test binary does NOT export `dregg_fips204_sign` \
             (`fips204_sign_core_available()` is false), so the verified SCALAR sign core cannot be \
             installed. Rebuild dregg-lean-ffi against a HEAD-matching archive that lake-builds \
             `Dregg2.Crypto.Fips204Verify`, then re-run."
        ),
    }
}

/// (A) The extracted, verified SCALAR sign core runs live and its output round-trips through the extracted
/// (scalar) verify core — both verdicts from the Lean objects, the `fips204` crate consulted for neither.
#[test]
fn verified_scalar_sign_core_runs_live_and_roundtrips() {
    install_scalar_sign_core_or_panic();
    assert!(
        dregg_pq::lean_sign_core_installed(),
        "after install, the Lean-verified (scalar) sign core must be installed behind ml_dsa_sign_core"
    );

    // Honest sample: secret (s1,s2,t0)=(5,1,3), message μ=7, mask y=40 → accepted signature (c̃,z,h)=(7,45,0).
    let sig_wire = dregg_pq::ml_dsa_sign_core("5 1 3 7 40")
        .expect("sign core installed ⇒ Some(_)")
        .expect("honest sample ⇒ an accepted signature, not REJECT");
    assert_eq!(
        sig_wire, "7 45 0",
        "the live Lean signCore emits the accepted signature wire"
    );

    // ROUND-TRIP through the extracted (scalar) verifyCore, ALSO run live via the Lean archive.
    let verify_wire = format!("3 7 {sig_wire}");
    let lean_verdict = dregg_lean_ffi::shadow_fips204_verify(&verify_wire)
        .expect("the linked archive exports the (scalar) verify core");
    assert_eq!(
        lean_verdict, "1",
        "the extracted signCore output ACCEPTS through the extracted verifyCore — round-trip runs live"
    );

    // Rejected samples are honestly Some(None) (resample) — NOT a faked accept.
    assert_eq!(dregg_pq::ml_dsa_sign_core("5 1 3 7 261888"), Some(None));
    assert_eq!(dregg_pq::ml_dsa_sign_core("5 1 3 7 1000000"), Some(None));
    assert_eq!(dregg_pq::ml_dsa_sign_core("garbage"), Some(None));

    eprintln!(
        "PROVED (A): the extracted verified SCALAR sign core runs LIVE; an honest sample signs and \
         round-trips through the extracted verifyCore, bad samples honestly reject."
    );
}

/// (B) THE CLOSURE — the DEPLOYED byte-level `MlDsaKey::sign` is now Lean-PRODUCED (the crate leaves the
/// SIGN TCB). Install the REAL sign core (and the REAL verify core), then sign a FRESH message with the
/// deployed signer and check the produced 3309-byte signature is: byte-identical to the leanc-native
/// `shadow_fips204_sign_real` on the same wire (routed through Lean, crate not consulted), byte-identical to
/// the crate's DETERMINISTIC signature (Lean reproduces the crate spec live), deterministic across calls,
/// and accepted by BOTH the Lean-verified real verify core AND the `fips204` crate verifier.
#[test]
fn deployed_byte_sign_is_lean_produced_crate_leaves_tcb() {
    // Install the REAL sign core behind the deployed `MlDsaKey::sign`.
    match install_mldsa_verified_sign_core_real() {
        MlDsaSignCoreRealInstall::Installed | MlDsaSignCoreRealInstall::AlreadyInstalled => {}
        MlDsaSignCoreRealInstall::ExportAbsent => panic!(
            "BLOCKER: the Lean archive linked into this test binary does NOT export \
             `dregg_fips204_sign_real` (`fips204_sign_real_core_available()` is false), so the deployed \
             `MlDsaKey::sign` cannot be routed through Lean. Rebuild dregg-lean-ffi against a HEAD-matching \
             archive that lake-builds `Dregg2.Crypto.MlDsaSignReal`, then re-run."
        ),
    }
    assert!(
        dregg_pq::lean_sign_core_real_installed(),
        "after install, the Lean-verified REAL sign core must be the producer behind MlDsaKey::sign"
    );
    // Also install the REAL verify core so we can check acceptance via Lean.
    match install_mldsa_verified_verify_core() {
        MlDsaVerifyCoreInstall::Installed | MlDsaVerifyCoreInstall::AlreadyInstalled => {}
        MlDsaVerifyCoreInstall::ExportAbsent => {
            panic!(
                "BLOCKER: archive lacks `dregg_fips204_verify_real`; rebuild against a HEAD-matching archive."
            )
        }
    }

    let seed = [3u8; 32];
    let ctx: &[u8] = b"dregg-node-live-sign-ctx-v1";
    let msg: &[u8] = b"a FRESH message the pinned KAT never covered - Lean signs it live";

    // The DEPLOYED byte-level signer, now routed through the extracted Lean `signCore`.
    let key = dregg_pq::MlDsaKey::from_ed25519_seed(&seed);
    let dep = key.sign(ctx, msg);
    assert_eq!(
        dep.len(),
        dregg_pq::ML_DSA_SIG_LEN,
        "the deployed signer emits a real full-byte ML-DSA-65 signature (3309 bytes)"
    );

    // Reconstruct the crate keypair from the SAME seed (byte-identical to what MlDsaKey derives).
    let (pk_crate, sk_crate) = ml_dsa_65::KG::keygen_from_seed(&seed);
    let sk_bytes = sk_crate.clone().into_bytes();

    // (1) ROUTED THROUGH LEAN, CRATE NOT CONSULTED: the deployed signature is byte-identical to the
    // leanc-native `shadow_fips204_sign_real` on the same `sk ‖ msg ‖ ctx` wire.
    let wire = real_sign_wire(&sk_bytes, msg, ctx);
    let shadow = dregg_lean_ffi::shadow_fips204_sign_real(&wire)
        .expect("the linked archive exports the real sign core");
    assert_ne!(
        shadow, "ERR",
        "the real sign core produced a signature (not a malformed-wire ERR)"
    );
    assert_eq!(
        dep,
        decode_hex(&shadow),
        "the deployed MlDsaKey::sign output is byte-identical to the leanc-native shadow — the deployed \
         path went THROUGH the Lean object; the fips204 crate was not consulted"
    );

    // (2) LEAN REPRODUCES THE CRATE SPEC LIVE: byte-identical to the crate's DETERMINISTIC (rnd=0)
    // signature on this FRESH message — not just the pinned KAT.
    let det = sk_crate
        .try_sign_with_seed(&[0u8; 32], msg, ctx)
        .expect("crate deterministic sign");
    assert_eq!(
        dep,
        det.to_vec(),
        "the deployed Lean signer reproduces the fips204 crate's DETERMINISTIC signature byte-for-byte, \
         LIVE, on a fresh message"
    );

    // (3) DETERMINISTIC across calls (the hedged crate fallback would differ run-to-run).
    let dep2 = key.sign(ctx, msg);
    assert_eq!(
        dep, dep2,
        "the installed Lean path is deterministic (rnd=0) — same seed/ctx/msg ⇒ same bytes"
    );

    // (4a) ACCEPTED by the Lean-verified REAL verify core (which routes ml_dsa_verify through Lean).
    assert!(
        dregg_pq::ml_dsa_verify(&key.public_bytes(), ctx, msg, &dep),
        "the Lean-produced signature is accepted by the deployed Lean-routed verify"
    );

    // (4b) ACCEPTED by the fips204 crate verifier too (a genuine, spec-valid ML-DSA-65 signature).
    let sig_arr = <[u8; ml_dsa_65::SIG_LEN]>::try_from(dep.as_slice()).expect("sig len");
    assert!(
        pk_crate.verify(msg, &sig_arr, ctx),
        "the Lean-produced signature is accepted by the fips204 crate verifier — a genuine ML-DSA-65 sig"
    );

    // Domain separation still rides the caller's ctx: the signature does not verify under a different ctx.
    assert!(
        !pk_crate.verify(msg, &sig_arr, b"different-ctx"),
        "domain separation holds — the ctx is bound into the signature"
    );

    eprintln!(
        "PROVED (B): the DEPLOYED byte-level `MlDsaKey::sign` is now produced by the extracted, Lean-verified \
         `MlDsaSignReal.signCore` (byte-identical to the leanc-native shadow AND to the crate's deterministic \
         signature on a fresh message, deterministic, accepted by both the Lean verify core and the crate). \
         The `fips204` crate has LEFT the node's SIGN TCB."
    );
}
