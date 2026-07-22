//! GUARD C — the anti-illusion test: the TOY seams are not on any deployed path, and this is
//! precisely which primitives remain CRATE-AUTHORITATIVE.
//!
//! # What changed (and why this file was rewritten)
//!
//! This test used to assert something broader and now FALSE: that "the deployed sign/KEM paths are
//! crate-authoritative". That was true when the only Lean seams for sign/KEM were TOY-scoped. It is
//! no longer true. `dregg-pq` now carries REAL, full-byte cores for all six PQ operations,
//! and every archive-linked host installs them at startup:
//!
//!   * ML-DSA-65 VERIFY  — `install_verified_mldsa_verify_core`   (node, SDK, starbridge-v2, drorb)
//!   * ML-DSA-65 SIGN    — `install_verified_mldsa_sign_core_real` (node, SDK, starbridge-v2, drorb)
//!   * ML-DSA-65 KEYGEN  — `install_verified_mldsa_keygen_core_real` (node, SDK)
//!   * ML-KEM-768 KEM    — `install_verified_mlkem_{keygen,encaps,decaps}_core` (node, SDK)
//!
//! On an installed host `MlDsaKey::try_sign` PRODUCES its bytes from the extracted Lean
//! `MlDsaSignReal.signCore` and never calls `fips204` at all — observed under gdb in the drorb
//! dataplane, where a breakpoint on `dregg_fips204_sign_real_str` fires on every sign while one on
//! `fips204::ml_dsa::sign_internal::<false, 6, 5, 48, 3309, 4032, 768>` never fires.
//!
//! # What this test still proves, and it is worth proving
//!
//! The TOY seams (`install_lean_sign_core`, `install_lean_encaps_core`, `install_lean_decaps_core`)
//! carry SCALAR (n=1) / bit-`m` reductions, and NOTHING deployed consults them. They are easy to
//! mistake for the real ones — the names differ by a `_real` suffix. So the assertions below install
//! the toy seams with a POISON payload and drive the real deployed fns: if any deployed path ever
//! got wired to a toy seam, this test breaks loudly.
//!
//! # What remains outside these verified cores (the honest residual)
//!
//! 1. **The classical halves.** Ed25519 (`ed25519-dalek`) and X25519 (`x25519-dalek`).
//! 2. **The combiner.** The X-Wing concat-KDF is Rust `hkdf`/`sha2`, not a verified object.
//! 3. **Any host that never installs.** A process that skips the installs still has `fips204` /
//!    `ml-kem` behind sign/verify/KEM — but since the audit gate landed it ABORTS on first use
//!    rather than substituting silently. That is the gate's whole job.
//!
//! ★ Anything asserted here is about THIS test binary, which by construction cannot link the 546 MB
//! Lean archive and therefore always runs the crate fallback. That is a property of the test
//! binary, NOT a description of a deployed process. The deployed routing is proven where the
//! archive is actually linked: `drorb crates/dataplane/src/pq.rs`
//! (`verified_sign_core_is_the_deployed_sign_authority`) and `node/tests/mldsa_live_sign.rs`.

use dregg_pq::{
    MlDsaKey, install_lean_decaps_core, install_lean_encaps_core, install_lean_sign_core,
    lean_sign_core_installed, ml_dsa_sign_from_seed, ml_dsa_verify,
};

/// EXPLICIT OPT-IN to the unaudited fallback, and why it is still correct in THIS file.
///
/// `dregg-pq`'s refusal gate (`src/audit.rs`) aborts any process that answers a PQ operation with
/// the unaudited `fips204` / `ml-kem` crates unless this is set. This test binary is the canonical
/// legitimate exception, but for a NARROWER reason than it used to claim:
///
/// It is not that "the deployed paths are crate-authoritative" — they are not, for sign, verify and
/// KEM. It is that a `dregg-pq` INTEGRATION TEST cannot link the Lean archive, so no verified core
/// can exist in this process. To demonstrate that the toy seams are off the deployed path at all,
/// the deployed fns must actually run, and here they can only run on the crate fallback.
///
/// ★ This opt-in is scoped to a test binary that makes no assurance claim. Setting it in a serving
/// process — or to quiet the gate rather than install a core — is the exact failure the gate exists
/// to prevent.
///
/// SAFETY: set before this process performs any PQ operation. Each integration-test file runs in
/// its own process, and `opt_in()` is the first statement of every test in this file.
fn opt_in() {
    unsafe { std::env::set_var("DREGG_ALLOW_UNAUDITED_PQ", "1") };
}

const CTX: &[u8] = b"dregg-pq-guard-c-seam-scope-honesty-v1";
const SEED: [u8; 32] = [0x5au8; 32];

/// A sentinel the deployed path could only emit if it had (wrongly) routed through the installed toy sign
/// seam. The deployed `MlDsaKey::sign` must NEVER return this.
const POISON_SIG: &[u8] =
    b"TOY-SIGN-SEAM-OUTPUT-IF-YOU-SEE-THIS-THE-DEPLOYED-SIGNER-ROUTED-THROUGH-THE-TOY-SEAM";

#[test]
fn the_deployed_signer_ignores_an_installed_poison_sign_seam() {
    opt_in();
    let key = MlDsaKey::from_ed25519_seed(&SEED);
    let pk = key.public_bytes();
    let msg = b"guard C: the deployed signer is crate-authoritative, not seam-routed";

    // Install the TOY sign seam with a POISON closure. If the deployed `MlDsaKey::sign` ever consulted the
    // seam, the returned bytes would be this poison payload (not a valid ML-DSA-65 signature). `let _`: the
    // install is once-per-process and a prior test in this binary may already have set it.
    let _ = install_lean_sign_core(|_wire| Some(String::from_utf8_lossy(POISON_SIG).into_owned()));
    assert!(
        lean_sign_core_installed(),
        "the toy sign seam is installed (this or a prior install) — the deployed signer must ignore it"
    );

    // The deployed signer (hedged/randomized) still produces a FULL, CRATE-VALID ML-DSA-65 signature — one
    // the poison seam could never have produced. This is the proof the seam is NOT on the deployed path.
    let sig = key.sign(CTX, msg);
    assert_eq!(
        sig.len(),
        dregg_pq::ML_DSA_SIG_LEN,
        "the deployed signature is a full ML-DSA-65 signature (crate path), not the toy seam's wire"
    );
    assert_ne!(
        &sig[..],
        POISON_SIG,
        "the deployed signer never emits the toy-seam poison bytes"
    );
    // No verify core is installed in this test binary, so `ml_dsa_verify` uses the `fips204` crate to check
    // the signature — a poison-seam output would fail this; a genuine crate signature passes.
    assert!(
        ml_dsa_verify(&pk, CTX, msg, &sig),
        "the deployed `MlDsaKey::sign` output VERIFIES — the crate signed it, the toy seam did not"
    );

    // The from-seed convenience signer is the same crate path and likewise ignores the poison seam.
    let sig2 = ml_dsa_sign_from_seed(&SEED, CTX, msg).expect("sign from seed");
    assert_ne!(&sig2[..], POISON_SIG);
    assert!(
        ml_dsa_verify(&pk, CTX, msg, &sig2),
        "the deployed `ml_dsa_sign_from_seed` output VERIFIES — crate-authoritative"
    );
}

#[test]
fn installing_the_toy_kem_seams_does_not_change_the_deployed_hybrid_kem() {
    opt_in();
    use dregg_pq::hybrid_kem::{initiate, responder_offer};

    // A full hybrid handshake BEFORE any KEM seam is installed (the `ml-kem` + `x25519-dalek` crate path).
    // The handshake uses fresh OS entropy per run, so we cannot compare keys across runs — instead we assert
    // the INVARIANT that must hold on every deployed path: initiator and responder derive the SAME session
    // key, and it is a full 32-byte combined key (never the toy seam's `"u v K"` wire).
    let handshake_agrees = || {
        let (offer, responder) = responder_offer();
        let (msg, initiator_key) = initiate(&offer).expect("initiate");
        let responder_key = responder.finish(&msg).expect("finish");
        assert_eq!(
            initiator_key, responder_key,
            "hybrid KEM correctness: both parties derive the same 32-byte session key"
        );
        initiator_key
    };
    let key_before = handshake_agrees();

    // Install BOTH toy KEM seams with POISON closures. If the deployed KEM ever routed through them, the
    // derived secret would change / the handshake would diverge.
    let _ = install_lean_encaps_core(|_wire| Some("POISONED-ENCAPS-u v K".to_string()));
    let _ = install_lean_decaps_core(|_wire| Some("POISONED-DECAPS-K".to_string()));

    // AFTER installing the toy seams: the deployed hybrid KEM still round-trips correctly (both parties
    // still agree) — proving `initiate`/`finish` never consulted the seams. (Keys differ from `key_before`
    // only because of fresh per-run entropy, not because of the seams; the load-bearing invariant is the
    // in-run agreement, which would BREAK if the poison seams were on the deployed path.)
    let key_after = handshake_agrees();

    assert_eq!(
        key_after.len(),
        32,
        "the deployed hybrid session key is a full 32-byte combined key (crate path), not the toy seam wire"
    );
    // Cross-check the two runs produced distinct keys (fresh entropy) — i.e. we really re-ran the deployed
    // path both times, not a memoized constant.
    assert_ne!(
        key_before, key_after,
        "each deployed handshake uses fresh OS entropy (we exercised the real path twice)"
    );
}

/// THE SCOPE PIN, machine-checked: installing a TOY seam must never look like installing the REAL
/// core. The two live in SEPARATE `OnceLock`s (`LEAN_SIGN_CORE` vs `LEAN_SIGN_CORE_REAL`) and the
/// deployed `try_sign` reads ONLY the latter. The names differ by a `_real` suffix, so a future
/// edit that crossed them would be easy to miss in review and catastrophic in effect: a process
/// could report an installed sign core, satisfy the audit gate, and still be signing with `fips204`.
///
/// This also states the scope of THIS binary precisely: no REAL core is installed here (an
/// integration test cannot link the Lean archive), which is exactly why `opt_in()` is needed above,
/// and exactly why nothing in this file may be read as a claim about a deployed process.
#[test]
fn a_toy_seam_install_never_reports_the_real_core_as_installed() {
    opt_in();

    // Install the TOY sign seam (poison payload; `let _` because install is once-per-process).
    let _ = install_lean_sign_core(|_wire| Some(String::from_utf8_lossy(POISON_SIG).into_owned()));
    assert!(
        lean_sign_core_installed(),
        "the TOY sign seam is installed in this process"
    );

    // ...and the REAL core is STILL not installed. Separate cell, separate question.
    assert!(
        !dregg_pq::lean_sign_core_real_installed(),
        "installing the TOY sign seam must NOT make the REAL sign core report as installed — they \
         are distinct OnceLocks and only the REAL one is read by the deployed MlDsaKey::try_sign"
    );

    // The same separation on the KEM side.
    let _ = install_lean_encaps_core(|_wire| Some("POISONED-ENCAPS-u v K".to_string()));
    let _ = install_lean_decaps_core(|_wire| Some("POISONED-DECAPS-K".to_string()));
    assert!(
        !dregg_pq::mlkem_encaps_real_core_installed(),
        "installing the TOY encaps seam must NOT make the REAL encaps core report as installed"
    );
    assert!(
        !dregg_pq::mlkem_decaps_real_core_installed(),
        "installing the TOY decaps seam must NOT make the REAL decaps core report as installed"
    );

    // The toy seams likewise cannot masquerade as either REAL keygen core. This test binary deliberately
    // opts into crate fallbacks because it does not link the Lean archive; archive-linked hosts install the
    // two real cores and do not take these fallback branches.
    assert!(
        !dregg_pq::lean_keygen_core_real_installed(),
        "toy sign install must not report the REAL ML-DSA keygen core as installed"
    );
    assert!(
        !dregg_pq::mlkem_keygen_real_core_installed(),
        "toy KEM installs must not report the REAL ML-KEM keygen core as installed"
    );
    let key = MlDsaKey::from_ed25519_seed(&SEED);
    assert_eq!(
        key.public_bytes().len(),
        dregg_pq::ML_DSA_PK_LEN,
        "the explicit test-only fallback still produces a full ML-DSA-65 public key"
    );
    let (ek, dk) = dregg_pq::ml_kem768_keygen();
    assert_eq!(
        (ek.len(), dk.len()),
        (1184, 2400),
        "the explicit test-only fallback still produces a full ML-KEM-768 keypair"
    );
}
