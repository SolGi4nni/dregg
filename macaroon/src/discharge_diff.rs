//! # Differential: Lean `MacaroonDischarge` model  ⟺  the REAL macaroon third-party discharge flow.
//!
//! This is the Rust side of the differential for
//! `metatheory/Dregg2/Authority/MacaroonDischarge.lean` — the faithful executable Lean model of the
//! macaroon THIRD-PARTY DISCHARGE sub-tree and its replay-binding tooth (`bind_discharge` /
//! `verify_discharge`, `macaroon/src/macaroon.rs:267-347`). The Lean side proves, relative to the
//! `MacKernel` keyed-hash portal and the `BindingHashCR` collision-resistance carrier:
//!
//!  * `bound_discharge_verifies`              — an honestly-bound discharge verifies against its parent.
//!  * `unbound_discharge_rejected`            — an UNBOUND discharge is rejected unconditionally
//!                                              (fail-closed, even with a perfect chain and zero caveats).
//!  * `binding_not_replayable_to_other_root`  — a discharge bound to root tail `p` is rejected against
//!                                              any different tail `p' ≠ p` (the no-cross-root-replay tooth).
//!  * `rebinding_changes_replay`              — re-binding to a different parent changes the discharge
//!                                              tail (needs a fresh MAC query under the discharge key).
//!
//! The Lean `foldBytes` / `Discharge.replay` / `verifyDischarge` are tiny transcriptions of the Rust
//! HMAC chain replay + the binding check. This differential pins that the verified Lean semantics IS
//! the semantics the macaroon crate actually computes — same discipline as `threshold_decrypt_diff`
//! and `epoch_diff`:
//!
//!  1. **Replay agreement** — the Lean `foldBytes(mac dkey nonce, fp)` + binding step is re-run here
//!     against the REAL `crypto::hmac_sha256` chain and `crypto::binding_hash`, byte-for-byte.
//!  2. **Binding-tooth agreement** — the Lean `binding_not_replayable_to_other_root` /
//!     `unbound_discharge_rejected` decisions are re-run against the REAL `Macaroon::verify` (which
//!     calls the private `verify_discharge`) over the genuine third-party flow: a bound discharge
//!     verifies; an unbound one is rejected; and a discharge bound to one root is rejected when
//!     replayed against a DIFFERENT (less-attenuated) root.
//!  3. **CR distinguisher** — the Lean `binding_body_distinguishes_roots` (different root tails ⇒
//!     different binding bodies, under `BindingHashCR`) is re-run against `crypto::binding_hash`.
//!
//! The HMAC EUF-CMA (`MacKernel.unforgeable`) and SHA-256 collision-resistance (`BindingHashCR`) are
//! the named Lean carriers; here they are exercised concretely through the real primitives.

#![cfg(test)]

use crate::caveat::CaveatSet;
use crate::crypto;
use crate::macaroon::{create_discharge, Macaroon};

// ───────────────────────────── Lean model, transcribed to Rust ─────────────────────────────
// These mirror `MacaroonDischarge.lean` §1 exactly.

/// Lean `foldBytes t0 bs` (`MacaroonDischarge.lean` §1): left fold `mac` over caveat encodings.
fn lean_fold_bytes(t0: [u8; 32], bs: &[Vec<u8>]) -> [u8; 32] {
    let mut t = t0;
    for b in bs {
        t = crypto::hmac_sha256(&t, b);
    }
    t
}

/// Lean `Discharge.replay bindingHash d` (`MacaroonDischarge.lean` §1): seed `mac dkey nonce`, fold
/// the first-party encodings, then — if bound — one more `mac` over `bindingHash(parent_tail)`.
fn lean_discharge_replay(
    dkey: &[u8; 32],
    nonce_bytes: &[u8],
    fp: &[Vec<u8>],
    bound_to: Option<&[u8; 32]>,
) -> [u8; 32] {
    let base = lean_fold_bytes(crypto::hmac_sha256(dkey, nonce_bytes), fp);
    match bound_to {
        None => base,
        Some(parent_tail) => {
            // The Lean `bindingHash : Tag → Bytes` abstracts the WIRE-ENCODED binding caveat body,
            // which the real `bind_discharge` HMACs (`WireCaveat::encode` = `[type_id LE u16][body]`,
            // caveat.rs:95-100; CAV_BIND_TO_PARENT = 255 → `[255, 0]`, then `body = binding_hash`).
            let binding_hash = crypto::binding_hash(parent_tail);
            let mut binding_body = Vec::with_capacity(2 + 32);
            binding_body.extend_from_slice(&crate::caveat::CAV_BIND_TO_PARENT.to_le_bytes());
            binding_body.extend_from_slice(&binding_hash);
            crypto::hmac_sha256(&base, &binding_body)
        }
    }
}

// ───────────────────────────── helpers: drive the real 3P flow ─────────────────────────────

/// Build a root macaroon with one third-party caveat, returning (root, discharge_key, ticket).
fn root_with_3p(root_key: &[u8; 32], shared_key: &[u8; 32]) -> (Macaroon, [u8; 32], Vec<u8>) {
    let mut mac = Macaroon::new(root_key, b"kid-root".to_vec(), "https://dregg.dev".into());
    mac.add_third_party("https://auth.dregg.dev", shared_key, CaveatSet::new())
        .unwrap();
    let tp_caveats = mac.caveats.third_party_caveats();
    let tp = crate::caveat_3p::ThirdPartyCaveat::decode_body(&tp_caveats[0].body).unwrap();
    let wire_ticket = crate::caveat_3p::ThirdPartyCaveat::decrypt_ticket(&tp.ticket, shared_key).unwrap();
    let mut dk = [0u8; 32];
    dk.copy_from_slice(&wire_ticket.discharge_key);
    (mac, dk, tp.ticket.clone())
}

// ───────────────────────────── §1 replay agreement ─────────────────────────────

#[test]
fn lean_replay_matches_real_discharge_chain() {
    // A discharge's stored tail (built by create_discharge then bind_discharge) must equal the Lean
    // `Discharge.replay` of its own fields. We reconstruct the discharge's (dkey, nonce, fp, bound).
    let root_key = crypto::random_key();
    let shared_key = crypto::random_key();
    let (mac, dk, ticket) = root_with_3p(&root_key, &shared_key);

    let mut discharge = create_discharge(ticket, &dk, "https://auth.dregg.dev".into(), &[]);
    // Record the UNBOUND tail and compare to Lean replay (no binding).
    let nonce_bytes = discharge.nonce.encode();
    let lean_unbound = lean_discharge_replay(&dk, &nonce_bytes, &[], None);
    assert_eq!(
        discharge.tail, lean_unbound,
        "unbound discharge tail must equal Lean foldBytes(mac dkey nonce, [])"
    );

    // Now bind to the root and compare the bound tail to Lean replay WITH the binding step.
    let parent_tail = mac.tail;
    mac.bind_discharge(&mut discharge);
    let lean_bound = lean_discharge_replay(&dk, &nonce_bytes, &[], Some(&parent_tail));
    assert_eq!(
        discharge.tail, lean_bound,
        "bound discharge tail must equal Lean replay with bindingHash(parent_tail) step"
    );
}

// ───────────────────────────── §2 bound verifies / unbound rejected ─────────────────────────────

#[test]
fn bound_discharge_verifies() {
    // Lean `bound_discharge_verifies`: an honestly-bound discharge verifies against its parent.
    let root_key = crypto::random_key();
    let shared_key = crypto::random_key();
    let (mac, dk, ticket) = root_with_3p(&root_key, &shared_key);
    let mut discharge = create_discharge(ticket, &dk, "https://auth.dregg.dev".into(), &[]);
    mac.bind_discharge(&mut discharge);
    assert!(
        mac.verify(&root_key, &[discharge]).is_ok(),
        "bound discharge must verify"
    );
}

#[test]
fn unbound_discharge_rejected() {
    // Lean `unbound_discharge_rejected`: an UNBOUND discharge is rejected unconditionally — even
    // though its own chain is perfect and it has zero caveats. Fail-closed (DischargeUnbound).
    let root_key = crypto::random_key();
    let shared_key = crypto::random_key();
    let (mac, dk, ticket) = root_with_3p(&root_key, &shared_key);
    // Create the discharge but DO NOT bind it.
    let discharge = create_discharge(ticket, &dk, "https://auth.dregg.dev".into(), &[]);
    assert!(
        mac.verify(&root_key, &[discharge]).is_err(),
        "unbound discharge must be rejected (fail-closed)"
    );
}

// ───────────────────────────── §3 no cross-root replay (the binding tooth) ──────────────────────

#[test]
fn binding_not_replayable_to_other_root() {
    // Lean `binding_not_replayable_to_other_root`: a discharge bound to root R1 must be REJECTED
    // when replayed against a DIFFERENT (less-attenuated / different) root R2.
    let shared_key = crypto::random_key();

    // Root R1 with the 3P caveat.
    let root_key1 = crypto::random_key();
    let (mac1, dk, ticket) = root_with_3p(&root_key1, &shared_key);

    // Build a discharge and bind it to R1.
    let mut discharge = create_discharge(ticket.clone(), &dk, "https://auth.dregg.dev".into(), &[]);
    mac1.bind_discharge(&mut discharge);
    assert!(
        mac1.verify(&root_key1, &[discharge.clone()]).is_ok(),
        "bound discharge verifies against its OWN root"
    );

    // A DIFFERENT root R2 (different root key ⇒ different tail) that also embeds a 3P caveat with the
    // SAME ticket/shared key. The discharge bound to R1's tail must NOT verify against R2.
    let root_key2 = crypto::random_key();
    let (mac2, _dk2, _t2) = root_with_3p(&root_key2, &shared_key);
    // The binding body in `discharge` names R1's tail; R2's tail differs (different root key), so the
    // binding check fails (DischargeUnbound / unbound for R2).
    assert_ne!(
        mac1.tail,
        mac2.tail,
        "the two roots must have different tails"
    );
    assert!(
        mac2.verify(&root_key2, &[discharge]).is_err(),
        "a discharge bound to R1 must NOT verify against a different root R2 (no cross-root replay)"
    );
}

#[test]
fn binding_body_distinguishes_roots() {
    // Lean `binding_body_distinguishes_roots`: different root tails ⇒ different binding bodies
    // (under BindingHashCR). Re-run against the real crypto::binding_hash.
    let t1 = crypto::random_key();
    let mut t2 = t1;
    t2[0] ^= 0x01; // a different tail
    assert_ne!(t1, t2);
    assert_ne!(
        crypto::binding_hash(&t1),
        crypto::binding_hash(&t2),
        "distinct tails must yield distinct binding bodies"
    );
    // determinism (sanity).
    assert_eq!(crypto::binding_hash(&t1), crypto::binding_hash(&t1));
}
