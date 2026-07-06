//! LIVE-BYZANTINE Attack 5b forge — the SERVED state attestation carries no
//! committee binding (the store now does — Fix B landed — but the API wire is
//! still count-only).
//!
//! The deployed cross-node committee quorum (`node::finalization_votes`, v2)
//! binds `(block_id, merkle_root)` and, since Fix B, is back-filled into the
//! persisted root's `finalization_quorum`
//! (`blocklace_sync.rs::backfill_finalization_quorums`). But
//! `GET /api/federation/roots` (`api.rs::get_federation_roots`) still surfaces
//! a root as `{ merkle_root, signatures: quorum_signatures.len() }` — a COUNT,
//! with no committee verification and no `finalization_quorum` exposure.
//!
//! This forge shows a single Byzantine node can present TWO conflicting state
//! roots for the SAME finalized block, each passing the count-only gate the API
//! serves, so a light client trusting that surface cannot arbitrate them — the
//! committee certificate over the state is not in the SERVED artifact. (It also
//! models the pre-back-fill TRAILING-HEAD shape: a root persisted before its
//! votes converge legitimately carries an empty `finalization_quorum`.)
//!
//! It ALSO pins the Fix-B discriminator itself: `finalization_quorum` +
//! `verify_finalization_quorum` (the committee's v2 finalization votes OVER
//! `(block_id, merkle_root)`) is crypto-bound, not a count — the property the
//! served surface must expose (and a light client verify) to close Attack 5b.
//!
//! Uses only `dregg_persist` re-exported types (no signing, no manifest edit) so
//! it never touches the actively-edited `persist/src/tests.rs`.
//!
//! See `docs/audit/LIVE-BYZANTINE.md` Attack 5b (and Attack 3 — the same weld).

use dregg_persist::StoredAttestedRoot;
use dregg_persist::federation::{FederationId, PublicKey, Signature};

/// A full-mode attested root as the deployed commit path FIRST persists it
/// (the trailing-head shape, before `backfill_finalization_quorums` attaches the
/// converged votes): bound to a blocklace block + height, carrying a single
/// (producer-local) `quorum_signatures` entry, threshold 3 (the N3 committee
/// shape), and an EMPTY `finalization_quorum` — also exactly the shape a forger
/// who holds no committee keys can mint.
fn full_mode_root(
    block_id: [u8; 32],
    merkle_root: [u8; 32],
    producer: PublicKey,
) -> StoredAttestedRoot {
    StoredAttestedRoot {
        merkle_root,
        note_tree_root: None,
        nullifier_set_root: None,
        height: 1,
        timestamp: 1_700_000_000,
        blocklace_block_id: Some(block_id),
        finality_round: Some(1),
        // Full mode pushes ONLY the local signature (1 < threshold 3).
        quorum_signatures: vec![(producer, Signature([0x01; 64]))],
        threshold_qc: None,
        threshold: 3,
        federation_id: FederationId::PLACEHOLDER,
        receipt_stream_root: None,
        // Empty at first persist (the quorum trails over gossip; Fix B
        // back-fills it) — and empty forever on a forged root.
        finalization_quorum: Vec::new(),
    }
}

/// A single Byzantine node signs two CONFLICTING state roots for the SAME
/// finalized block (same `blocklace_block_id`, same height, different
/// `merkle_root`). Both pass the count-only gate the API serves, and neither
/// carries a committee finalization quorum — so nothing in the served artifact
/// lets a light client tell the honest root from the forged one.
#[test]
fn byzantine_conflicting_state_roots_both_pass_count_only_gate() {
    let byz = PublicKey([0xBB; 32]);
    let block_id = [0xCD; 32];

    let honest = full_mode_root(block_id, [0xAA; 32], byz);
    let forged = full_mode_root(block_id, [0x00; 32], byz);

    // Same finalized block, CONFLICTING state.
    assert_eq!(honest.blocklace_block_id, forged.blocklace_block_id);
    assert_eq!(honest.height, forged.height);
    assert_ne!(honest.merkle_root, forged.merkle_root);

    // (1) The count-only gate the API's `signatures:` field reflects: a single
    // self-signature meets `is_structurally_complete()` only when threshold <= 1.
    // At the N3 threshold (3) a full-mode root is NOT structurally complete — the
    // count is 1. So a count-trusting consumer sees `signatures: 1` for BOTH
    // conflicting roots and has no committee evidence either way.
    assert_eq!(honest.quorum_signatures.len(), 1);
    assert_eq!(forged.quorum_signatures.len(), 1);
    assert!(!honest.is_structurally_complete());
    assert!(!forged.is_structurally_complete());

    // A Byzantine node CAN also declare threshold 1 (a self-federation) to make
    // its forged root `is_structurally_complete()` — the count gate cannot stop it.
    let forged_solo = StoredAttestedRoot {
        threshold: 1,
        ..forged.clone()
    };
    assert!(
        forged_solo.is_structurally_complete(),
        "count-only completeness cannot distinguish a forged solo-threshold root"
    );

    // (2) THE SERVED GAP: neither of these roots carries a committee finalization
    // quorum over its state (trailing-head / forged shape), and the API surfaces
    // nothing that would distinguish a back-filled root anyway — a light client
    // reading the served artifact has NO committee certificate binding
    // `merkle_root`.
    assert!(!honest.has_finalization_quorum());
    assert!(!forged.has_finalization_quorum());

    let committee = vec![PublicKey([1; 32]), PublicKey([2; 32]), PublicKey([3; 32])];
    assert!(
        !honest.verify_finalization_quorum(&committee),
        "an empty finalization_quorum cannot certify state (nothing to verify)"
    );
    assert!(!forged.verify_finalization_quorum(&committee));
}

/// Pin the Fix-B gate's SOUNDNESS: `verify_finalization_quorum` is crypto-bound,
/// not a count — a Byzantine node cannot forge a state quorum by stuffing
/// `finalization_quorum` with junk signatures or non-committee keys. This is the
/// property the served root must eventually carry to close Attack 5b/3.
#[test]
fn finalization_quorum_rejects_forged_and_noncommittee_signatures() {
    let committee = vec![PublicKey([1; 32]), PublicKey([2; 32]), PublicKey([3; 32])];

    // A root claiming a 3-of-3 committee quorum, but every signature is junk.
    let mut root = full_mode_root([0xCD; 32], [0xAA; 32], PublicKey([1; 32]));
    root.finalization_quorum = committee
        .iter()
        .map(|pk| (*pk, Signature([0x00; 64])))
        .collect();
    assert!(root.has_finalization_quorum());
    assert!(
        !root.verify_finalization_quorum(&committee),
        "junk signatures over the (block_id, merkle_root) preimage must NOT certify — \
         the gate verifies Ed25519, it does not count entries"
    );

    // A quorum of NON-committee keys (a Sybil minting fresh keypairs) is rejected
    // even if it were to carry valid signatures: the keys are not in the committee.
    let outsiders = vec![PublicKey([9; 32]), PublicKey([8; 32]), PublicKey([7; 32])];
    let mut sybil = full_mode_root([0xCD; 32], [0xAA; 32], PublicKey([9; 32]));
    sybil.finalization_quorum = outsiders
        .iter()
        .map(|pk| (*pk, Signature([0x00; 64])))
        .collect();
    assert!(
        !sybil.verify_finalization_quorum(&committee),
        "non-committee signers cannot form a finalization quorum (Sybil rejected)"
    );

    // A sub-threshold count (below `threshold`) is rejected regardless of validity.
    let mut short = full_mode_root([0xCD; 32], [0xAA; 32], PublicKey([1; 32]));
    short.finalization_quorum = vec![(PublicKey([1; 32]), Signature([0x00; 64]))];
    assert!(!short.verify_finalization_quorum(&committee));
}
