//! GUARD C — the anti-illusion test: SIGN and KEM are still CRATE-AUTHORITATIVE in every deployed process.
//!
//! `dregg-pq` exposes three Lean-verify SEAMS that mirror the verify-side one — `install_lean_sign_core`,
//! `install_lean_encaps_core`, `install_lean_decaps_core`. Unlike the verify seam (which the node installs
//! and which `ml_dsa_verify` genuinely routes through — see `tests/mldsa_lean_verify.rs`), these three are
//! TOY-SCOPED: the installed objects are the SCALAR (n=1) `signCore` / bit-`m` `encapsCore`/`decapsCore`,
//! and NOTHING deployed consults them. The deployed byte-level signer (`MlDsaKey::sign` /
//! `ml_dsa_sign_from_seed`) uses the `fips204` crate directly; the deployed hybrid KEM
//! (`hybrid_kem::initiate` / `HybridResponder::finish`) uses the `ml-kem` + `x25519-dalek` crates directly.
//!
//! This test DOCUMENTS-IN-CODE that the deployed sign/KEM paths do NOT route through the toy seams — so no
//! reader can be left with the false impression that they behave like the verify seam. If someone later
//! wires the deployed signer/KEM through these seams, THIS test breaks, forcing the honest-scope comments in
//! `dregg-pq/src/{mldsa,hybrid_kem}.rs` to be updated in the same breath.
//!
//! The assertions are BEHAVIORAL (the strongest form the audit asked for): we install the toy seams with a
//! POISON payload, then drive the real deployed fns and assert their output is a CRATE-VALID cryptographic
//! object that the poison seam could never have produced. NOTE: ML-DSA signing is HEDGED (randomized via
//! `OsRng` — see `fips204::traits::try_sign`), and the hybrid handshake draws fresh ephemeral keys per run,
//! so byte-equality across calls is NOT the right invariant. The right invariant is that the deployed output
//! stays a valid, full-size crate object (verifies / round-trips) with a poison seam installed — which it
//! could not if the seam were on the deployed path. No leanc/FFI link is needed for the assertions
//! themselves — the toy seams are pure Rust closures.

use dregg_pq::{
    MlDsaKey, install_lean_decaps_core, install_lean_encaps_core, install_lean_sign_core,
    lean_sign_core_installed, ml_dsa_sign_from_seed, ml_dsa_verify,
};

const CTX: &[u8] = b"dregg-pq-guard-c-seam-scope-honesty-v1";
const SEED: [u8; 32] = [0x5au8; 32];

/// A sentinel the deployed path could only emit if it had (wrongly) routed through the installed toy sign
/// seam. The deployed `MlDsaKey::sign` must NEVER return this.
const POISON_SIG: &[u8] =
    b"TOY-SIGN-SEAM-OUTPUT-IF-YOU-SEE-THIS-THE-DEPLOYED-SIGNER-ROUTED-THROUGH-THE-TOY-SEAM";

#[test]
fn the_deployed_signer_ignores_an_installed_poison_sign_seam() {
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
