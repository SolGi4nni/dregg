//! LANE classify-B — reachability PROOF for `realm-model/src/identity.rs`'s
//! `HybridSig::verify` cofactored ed25519 leg. Proof-by-EXECUTION, not by reading:
//!
//!   (A) The ed leg IS cofactored-weak IN ISOLATION: a small-order ed public key
//!       with signature (R = small-order point, s = 0) makes `HybridSig::verify`
//!       return TRUE for an arbitrary message (the attacker also supplies their
//!       OWN real ML-DSA key/sig for the pq half). So if any caller ever verified
//!       a hybrid sig WITHOUT pinning the key, this would be a live universal forgery.
//!
//!   (B) The forgery is NOT REACHABLE at either shipped caller: `rotate_identity`
//!       and `recover_identity` FIRST gate on the signer's key COMMITMENT
//!       (`commit_hybrid(ed_pk, ml_pk) == committed current key` / registered
//!       guardian). The attacker cannot find a small-order ed_pk whose blake3
//!       commitment equals a legitimately-minted key's commitment. So the key is
//!       PINNED-BY-COMMITMENT at the callers — this is defense-in-depth, not a
//!       live forgery. VERDICT: PINNED-KEY.
//!
//! Run: `cargo test -p realm-model --test classify_b_reachability_probe`

use realm_model::RealmWorld;
use realm_model::identity::{
    HybridKey, HybridSig, SuccessionKind, commit_hybrid, succession_message,
};

// See `hybrid_identity_succession.rs` — `HybridKey::from_seed`'s ML-DSA half aborts the process
// with no verified core installed, and this binary asserted nothing. Installed at process start.
dregg_pq_testkit::install_at_process_start!();

/// The eight canonical small-order ed25519 point encodings (compressed y). Any of
/// these is a valid `VerifyingKey` that the COFACTORED `verify` accepts a
/// no-secret signature under. `verify_strict` rejects them (RFC 8032 §5.1.7).
const SMALL_ORDER: [[u8; 32]; 8] = [
    [
        0x01, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0,
    ],
    [
        0xec, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0x7f,
    ],
    [
        0x00, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0,
    ],
    [
        0x00, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0x80,
    ],
    [
        0x26, 0xe8, 0x95, 0x8f, 0xc2, 0xb2, 0x27, 0xb0, 0x45, 0xc3, 0xf4, 0x89, 0xf2, 0xef, 0x98,
        0xf0, 0xd5, 0xdf, 0xac, 0x05, 0xd3, 0xc6, 0x33, 0x39, 0xb1, 0x38, 0x02, 0x88, 0x6d, 0x53,
        0xfc, 0x05,
    ],
    [
        0x26, 0xe8, 0x95, 0x8f, 0xc2, 0xb2, 0x27, 0xb0, 0x45, 0xc3, 0xf4, 0x89, 0xf2, 0xef, 0x98,
        0xf0, 0xd5, 0xdf, 0xac, 0x05, 0xd3, 0xc6, 0x33, 0x39, 0xb1, 0x38, 0x02, 0x88, 0x6d, 0x53,
        0xfc, 0x85,
    ],
    [
        0xc7, 0x17, 0x6a, 0x70, 0x3d, 0x4d, 0xd8, 0x4f, 0xba, 0x3c, 0x0b, 0x76, 0x0d, 0x10, 0x67,
        0x0f, 0x2a, 0x20, 0x53, 0xfa, 0x2c, 0x39, 0xcc, 0xc6, 0x4e, 0xc7, 0xfd, 0x77, 0x92, 0xac,
        0x03, 0x7a,
    ],
    [
        0xc7, 0x17, 0x6a, 0x70, 0x3d, 0x4d, 0xd8, 0x4f, 0xba, 0x3c, 0x0b, 0x76, 0x0d, 0x10, 0x67,
        0x0f, 0x2a, 0x20, 0x53, 0xfa, 0x2c, 0x39, 0xcc, 0xc6, 0x4e, 0xc7, 0xfd, 0x77, 0x92, 0xac,
        0x03, 0xfa,
    ],
];

/// (A) The cofactored ed leg accepts a no-secret forgery IN ISOLATION.
#[test]
fn hybrid_verify_accepts_a_small_order_forgery_in_isolation() {
    let msg = b"any message at all";
    // The attacker's OWN real ML-DSA key/sig for the pq half (they control both
    // halves of the self-contained envelope).
    let attacker_ml = HybridKey::from_seed(&[0x42; 32]);
    let ml_pk = attacker_ml.ml_pk().to_vec();
    let ml_sig = attacker_ml.sign(msg).unwrap().ml_sig;

    let mut forged = false;
    for pk in SMALL_ORDER {
        // The no-secret forgery: R = the same small-order point, s = 0 → sig = pk ‖ 0^32.
        let mut ed_sig = [0u8; 64];
        ed_sig[..32].copy_from_slice(&pk);
        let sig = HybridSig {
            ed_pk: pk,
            ml_pk: ml_pk.clone(),
            ed_sig,
            ml_sig: ml_sig.clone(),
        };
        if sig.verify(msg) {
            forged = true;
        }
    }
    assert!(
        forged,
        "expected at least one small-order key to forge the cofactored ed leg — \
         if this fails the leg may already be strict (re-audit the verdict)"
    );
}

/// (B) The forgery is BLOCKED at the shipped caller: `rotate_identity` rejects a
/// hybrid sig whose signer commitment is not the identity's committed current key,
/// BEFORE the cofactored `verify` is ever consulted. The key is PINNED-BY-COMMITMENT.
#[test]
fn rotate_identity_pins_the_key_and_blocks_a_wrong_key_forgery() {
    let mut world = RealmWorld::new();
    let me = world.mint_identity("pip", "seed-pip").unwrap();
    let current = world.current_key_commit(&me.id).unwrap();
    let epoch = world.identity_epoch(&me.id);
    let new_commit = [0x99u8; 32];

    // A small-order-ed forged sig over the REAL succession message. Its signer
    // commitment is commit_hybrid(small_pk, attacker_ml_pk) — not the current key.
    let attacker_ml = HybridKey::from_seed(&[0x42; 32]);
    let ml_pk = attacker_ml.ml_pk().to_vec();
    let msg = succession_message(
        &me.id,
        epoch,
        &current,
        &new_commit,
        SuccessionKind::SelfSigned,
    );
    let ml_sig = attacker_ml.sign(&msg).unwrap().ml_sig;
    let small_pk = SMALL_ORDER[0];
    let mut ed_sig = [0u8; 64];
    ed_sig[..32].copy_from_slice(&small_pk);
    let forged = HybridSig {
        ed_pk: small_pk,
        ml_pk: ml_pk.clone(),
        ed_sig,
        ml_sig,
    };

    // The forged sig would pass `verify` in isolation had the message matched a
    // small-order-verifiable case, but the CALLER never reaches verify: the
    // signer-commitment gate rejects first.
    assert_ne!(
        forged.signer_commitment(),
        current,
        "attacker cannot make a small-order key's blake3 commitment equal the minted key's"
    );
    let res = world.rotate_identity(&me.id, new_commit, &forged);
    assert!(
        matches!(res, Err(realm_model::Refused::WrongSuccessionKey { .. })),
        "rotate must reject a non-current signer BEFORE consulting the cofactored verify; got {res:?}"
    );

    // Positive control: the LEGIT current key (never small-order — clamped from a
    // seed) rotates fine, so PINNED-KEY strictness does not break the honest path.
    let birth = world.birth_key("seed-pip");
    assert_eq!(birth.commitment(), current);
    let good_sig = birth.sign(&msg).unwrap();
    // sanity: legit commit_hybrid twin
    assert_eq!(commit_hybrid(&birth.ed_pk(), birth.ml_pk()), current);
    let ok = world.rotate_identity(&me.id, new_commit, &good_sig);
    assert!(
        ok.is_ok(),
        "the honest current key must still rotate; got {ok:?}"
    );
}
