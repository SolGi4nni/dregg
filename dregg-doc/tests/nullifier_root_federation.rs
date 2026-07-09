//! THE LAST FEDERATION SEAM, CLOSED: publish the CI nullifier accumulator's
//! committed root to the federation ledger, so cross-node anti-replay is complete —
//! every node shares the consumed-verdict set via the ledger, not a private
//! in-process structure.
//!
//! Three poles, each biting:
//!  (i)   ROUND-TRIP     — publish root R -> fetch R from the modeled federation
//!                         response -> R == acc.root().
//!  (ii)  OWNER-SIGNED   — the update signature over (cell_id ‖ old ‖ new) verifies
//!                         against cell_id-as-pubkey; a wrong key or a tampered
//!                         new-root is rejected.
//!  (iii) CROSS-NODE     — node A inserts a nullifier + publishes the new root; node
//!        REPLAY REFUSED   B fetches that root and, with A's membership proof, confirms
//!                         the nullifier is consumed (a fresh nullifier's
//!                         non-membership proof also verifies) — so B refuses A's
//!                         already-spent verdict using ONLY the ledger-published root,
//!                         never A's full accumulator.
#![cfg(feature = "substrate")]

use dregg_doc::{
    CiNullifierAccumulator, CiVerdict, NullifierFetchError, UpdateCommitmentRequest, ci_nullifier,
    fetch_nullifier_root, publish_nullifier_root, verify_nullifier_update_signature,
};
use ed25519_dalek::SigningKey;

/// A verdict distinguished by `command_id`; distinct `tag`s yield distinct canonical
/// encodings, hence distinct nullifiers.
fn verdict(tag: u8) -> CiVerdict {
    CiVerdict {
        input_root: [0x11; 32],
        command_id: [tag; 32],
        confinement_id: [0x33; 32],
        exit_code: 0,
        output_digest: [0x44; 32],
    }
}

const BASE: [u8; 32] = [0x55; 32];

/// A deterministic owner key whose PUBLIC key doubles as the nullifier cell id
/// (node's sovereign-cell convention: the cell id IS the owner ed25519 pubkey).
fn owner_key() -> SigningKey {
    SigningKey::from_bytes(&[0xA1; 32])
}

/// The modeled `GET /api/cell/{id}` response after a node accepts `req`: the ledger
/// now carries `req.new_commitment` as the cell's committed `state_commitment`. This
/// is the ONLY stand-in — the live HTTP transport — and it echoes exactly the hex the
/// WRITE published, so the READ path is exercised end-to-end against a real body.
fn ledger_response_after(req: &UpdateCommitmentRequest) -> String {
    format!(
        r#"{{"found":true,"state_commitment":"{}"}}"#,
        req.new_commitment
    )
}

// POLE (i): ROUND-TRIP — publish R, fetch R back out of the federation response, R
// equals the accumulator's own root.
#[test]
fn round_trip_publish_then_fetch_equals_root() {
    let key = owner_key();
    let cell_id = key.verifying_key().to_bytes();

    let mut acc = CiNullifierAccumulator::new();
    acc.insert(ci_nullifier(BASE, &verdict(1)));
    let r = acc.root();

    let req = publish_nullifier_root(&cell_id, &acc, &key, CiNullifierAccumulator::new().root());
    // The published new-commitment is exactly the accumulator root, hex-encoded.
    let fetched = fetch_nullifier_root(&ledger_response_after(&req)).expect("root parses");
    assert_eq!(fetched, r, "fetch(publish(R)) == acc.root() == R");

    // A not-found / no-commitment response is a typed refusal, not a bogus root.
    assert_eq!(
        fetch_nullifier_root(r#"{"found":false}"#),
        Err(NullifierFetchError::NotFound)
    );
    assert_eq!(
        fetch_nullifier_root(r#"{"found":true,"state_commitment":""}"#),
        Err(NullifierFetchError::NoCommitment)
    );
    assert_eq!(
        fetch_nullifier_root(r#"{"found":true,"state_commitment":"zz"}"#),
        Err(NullifierFetchError::BadCommitmentHex)
    );
}

// POLE (ii): OWNER-SIGNED — a genuine publish verifies against cell_id-as-pubkey; a
// wrong signing key and a tampered new-root are both rejected (exactly as node's
// post_update_commitment check would reject them).
#[test]
fn update_is_owner_signed_and_tamper_evident() {
    let key = owner_key();
    let cell_id = key.verifying_key().to_bytes();

    let mut acc = CiNullifierAccumulator::new();
    acc.insert(ci_nullifier(BASE, &verdict(7)));
    let genesis = CiNullifierAccumulator::new().root();

    let req = publish_nullifier_root(&cell_id, &acc, &key, genesis);
    assert!(
        verify_nullifier_update_signature(&req),
        "a genuine owner-signed update verifies against cell_id-as-pubkey"
    );

    // Wrong signing key: the signature no longer matches cell_id (== the RIGHT
    // owner's pubkey). node signs with `wrong` but the id is still `cell_id`.
    let wrong = SigningKey::from_bytes(&[0xB2; 32]);
    let mut forged = req.clone();
    // Re-sign under the wrong key while keeping the (correct) cell_id — this is a
    // request whose signer is not the cell owner.
    let forged_by_wrong = publish_nullifier_root(&cell_id, &acc, &wrong, genesis);
    forged.signature = forged_by_wrong.signature;
    assert!(
        !verify_nullifier_update_signature(&forged),
        "a signature by a non-owner key is rejected"
    );

    // Tampered new-root: flip the committed root under an otherwise-genuine signature.
    let mut tampered = req.clone();
    let mut bad = [0u8; 32];
    bad.copy_from_slice(&data_hex_decode(&tampered.new_commitment).expect("hex")[..]);
    bad[0] ^= 0xFF;
    tampered.new_commitment = data_hex_encode(&bad);
    assert!(
        !verify_nullifier_update_signature(&tampered),
        "a mutated new-root under a genuine signature is rejected"
    );
}

// POLE (iii): CROSS-NODE REPLAY REFUSED — node A inserts + publishes; node B, holding
// ONLY the fetched shared root + A's membership proof, confirms the nullifier is
// consumed and refuses A's already-spent verdict. A fresh nullifier's non-membership
// proof also verifies against the same shared root.
#[test]
fn cross_node_replay_refused_via_shared_root() {
    let key = owner_key();
    let cell_id = key.verifying_key().to_bytes();

    // ── Node A: consume a verdict's nullifier and publish the advanced root. ──
    let mut node_a = CiNullifierAccumulator::new();
    let spent = ci_nullifier(BASE, &verdict(1));
    let fresh = ci_nullifier(BASE, &verdict(2));
    let old_root = node_a.root();
    node_a.insert(spent);

    let req = publish_nullifier_root(&cell_id, &node_a, &key, old_root);
    assert!(verify_nullifier_update_signature(&req));

    // ── Node B: fetch the shared root from the FEDERATION, holding none of A's
    //    accumulator. Its only inputs are {shared root, nullifier, proof}. ──
    let shared_root = fetch_nullifier_root(&ledger_response_after(&req)).expect("root parses");
    assert_eq!(
        shared_root,
        node_a.root(),
        "B's ledger root == A's committed root"
    );

    // A hands B a membership proof for the SPENT nullifier (the light-client witness).
    let membership = node_a
        .membership_proof(&spent)
        .expect("spent nullifier has a membership proof");
    assert!(
        CiNullifierAccumulator::verify_membership(&shared_root, &membership),
        "node B confirms the verdict is CONSUMED against the shared root alone → REPLAY REFUSED"
    );

    // A fresh (never-spent) verdict's non-membership proof verifies against the SAME
    // shared root — so B can also safely admit a genuinely-new verdict.
    let non_membership = node_a
        .non_membership_proof(&fresh)
        .expect("fresh nullifier has a non-membership proof");
    assert!(
        CiNullifierAccumulator::verify_non_membership(&shared_root, &non_membership),
        "a fresh verdict's non-membership verifies against the shared root → safe to land"
    );

    // The proofs are exclusive: no membership for the fresh one, no non-membership
    // for the spent one — B cannot be tricked into either mistake.
    assert!(node_a.membership_proof(&fresh).is_none());
    assert!(node_a.non_membership_proof(&spent).is_none());

    // The whole point: node B held NO part of A's structure — only the ledger root
    // and the proof — yet refused the replay. That is cross-node anti-replay.
}

// --- Local hex helpers for the tamper pole (the crate's are private). ---
fn data_hex_decode(s: &str) -> Option<Vec<u8>> {
    if s.len() % 2 != 0 {
        return None;
    }
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).ok())
        .collect()
}
fn data_hex_encode(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}
