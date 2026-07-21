//! Comprehensive tests for the persistent store.
//!
//! Tests cover: CRUD for each storage type, recovery after simulated restart,
//! concurrent access safety, edge cases, and integrity checking.

use crate::federation::{PublicKey, Signature, StoredAttestedRoot};
use crate::{PersistentStore, StoreError};

// =============================================================================
// Helpers
// =============================================================================

fn new_store() -> PersistentStore {
    PersistentStore::open_in_memory().expect("failed to open in-memory store")
}

// =============================================================================
// Durable receipt log
// =============================================================================

#[test]
fn receipt_log_append_is_dense_immutable_and_idempotent() {
    let store = new_store();
    let first = b"signed-receipt-zero";

    store.append_receipt_chain_entry(0, first).unwrap();
    store
        .append_receipt_chain_entry(0, first)
        .expect("byte-identical retry is idempotent");
    assert!(matches!(
        store.append_receipt_chain_entry(0, b"different-receipt"),
        Err(StoreError::Integrity(_))
    ));
    assert!(matches!(
        store.append_receipt_chain_entry(2, b"gap"),
        Err(StoreError::Integrity(_))
    ));
    assert_eq!(store.load_receipt_chain().unwrap(), vec![first.to_vec()]);
    assert_eq!(store.receipt_chain_len().unwrap(), 1);
}

#[test]
fn receipt_log_gap_is_boot_integrity_error_not_a_shorter_prefix() {
    let store = new_store();
    store
        .append_receipt_chain_entry(0, b"signed-receipt-zero")
        .unwrap();

    // Inject the exact durable corruption boot must refuse: index one is absent
    // while a later accepted receipt remains in the table.
    let txn = store.db.begin_write().unwrap();
    {
        let mut table = txn.open_table(crate::tables::RECEIPT_CHAIN).unwrap();
        table.insert(2, b"signed-receipt-two".as_slice()).unwrap();
    }
    txn.commit().unwrap();

    assert!(matches!(
        store.load_receipt_chain(),
        Err(StoreError::Integrity(_))
    ));
    assert!(matches!(
        store.receipt_chain_len(),
        Err(StoreError::Integrity(_))
    ));
    assert!(matches!(
        store.append_receipt_chain_entry(1, b"would-paper-over-gap"),
        Err(StoreError::Integrity(_))
    ));
}

fn sample_attested_root(height: u64) -> StoredAttestedRoot {
    StoredAttestedRoot {
        merkle_root: [height as u8; 32],
        note_tree_root: None,
        nullifier_set_root: None,
        height,
        timestamp: 1000 + height as i64 * 100,
        blocklace_block_id: None,
        finality_round: None,
        quorum_signatures: vec![
            (PublicKey([0x11; 32]), Signature([0x22; 64])),
            (PublicKey([0x33; 32]), Signature([0x44; 64])),
            (PublicKey([0x55; 32]), Signature([0x66; 64])),
        ],
        threshold_qc: None,
        threshold: 2,
        federation_id: dregg_types::FederationId::PLACEHOLDER,
        receipt_stream_root: None,
        finalization_quorum: Vec::new(),
    }
}

// =============================================================================
// Federation (Revocation) Tests
// =============================================================================

#[test]
fn revocation_store_and_check() {
    let store = new_store();

    assert!(!store.is_revoked("token-1").unwrap());
    store.store_revocation("token-1").unwrap();
    assert!(store.is_revoked("token-1").unwrap());
    assert!(!store.is_revoked("token-2").unwrap());
}

#[test]
fn revocation_idempotent() {
    let store = new_store();

    store.store_revocation("token-1").unwrap();
    store.store_revocation("token-1").unwrap(); // Should not error.
    assert_eq!(store.revocation_count().unwrap(), 1);
}

#[test]
fn revocation_count() {
    let store = new_store();

    assert_eq!(store.revocation_count().unwrap(), 0);
    store.store_revocation("a").unwrap();
    store.store_revocation("b").unwrap();
    store.store_revocation("c").unwrap();
    assert_eq!(store.revocation_count().unwrap(), 3);
}

#[test]
fn revocation_list() {
    let store = new_store();

    store.store_revocation("beta").unwrap();
    store.store_revocation("alpha").unwrap();
    store.store_revocation("gamma").unwrap();

    let mut list = store.list_revocations().unwrap();
    list.sort();
    assert_eq!(list, vec!["alpha", "beta", "gamma"]);
}

#[test]
fn revocation_batch() {
    let store = new_store();

    let count = store
        .store_revocations_batch(&["x", "y", "z", "x"])
        .unwrap();
    // "x" appears twice but should only be counted once.
    assert_eq!(count, 3);
    assert_eq!(store.revocation_count().unwrap(), 3);
    assert!(store.is_revoked("x").unwrap());
    assert!(store.is_revoked("y").unwrap());
    assert!(store.is_revoked("z").unwrap());
}

#[test]
fn revocation_time() {
    let store = new_store();

    store.store_revocation_at("token-1", 1234567890).unwrap();
    assert_eq!(store.revocation_time("token-1").unwrap(), Some(1234567890));
    assert_eq!(store.revocation_time("token-2").unwrap(), None);
}

// =============================================================================
// Federation (Attested Root) Tests
// =============================================================================

/// DIAGNOSIS — the N3 committee-restart hole (`node/src/blocklace_sync.rs`
/// full-mode commit path).
///
/// The commit path persists a full-mode attested root with only the LOCAL
/// node's single signature and `threshold = committee size`. On restart,
/// `verify_signed_anchor_and_rollback` (`node/src/state.rs`) calls
/// [`StoredAttestedRoot::verify_signatures`], which requires
/// `quorum_signatures.len() >= threshold` valid committee signatures over the
/// root's canonical `signing_message()`. A single-signature root therefore
/// fails and a full-mode committee node fail-closes after finalizing >=1
/// height (solo/threshold-1 is unaffected).
///
/// This test PINS both halves of the CORRECT recovery-anchor behavior so the
/// eventual fix is measured against the right bar (and so the anchor is never
/// silently weakened):
///   * a genuinely sub-quorum root (1 sig, threshold 3) is REFUSED — the
///     recovery anchor is correct security hardening and must stay strict;
///   * a genuine committee quorum (>=threshold valid sigs over the SAME
///     message) is ACCEPTED — exactly the record the persistence layer must
///     produce to close the hole WITHOUT relaxing the check;
///   * a quorum-COUNT of signatures that do not verify over this root's
///     message (they signed a different merkle_root) is still REFUSED — the
///     anchor binds the committed state root, not just a signature count.
#[test]
fn full_mode_single_sig_root_is_refused_genuine_quorum_accepted() {
    use dregg_types::{SigningKey, sign};

    // A 3-member committee (the N3 full-mode shape); threshold = 3.
    let sks: Vec<SigningKey> = (1u8..=3)
        .map(|s| SigningKey::from_bytes(&[s; 32]))
        .collect();
    let committee: Vec<PublicKey> = sks.iter().map(|k| k.public_key()).collect();

    // Build the attested root the way the full-mode commit path does.
    let mut root = StoredAttestedRoot {
        merkle_root: [0xAB; 32],
        note_tree_root: None,
        nullifier_set_root: None,
        height: 1,
        timestamp: 1_700_000_000,
        blocklace_block_id: Some([0xCD; 32]),
        finality_round: Some(1),
        quorum_signatures: Vec::new(),
        threshold_qc: None,
        threshold: 3,
        federation_id: dregg_types::FederationId::PLACEHOLDER,
        receipt_stream_root: Some([0xEF; 32]),
        finalization_quorum: Vec::new(),
    };
    let msg = root.signing_message();

    // ── THE BUG: full mode persists ONLY the local signature. 1 < 3. ──
    root.quorum_signatures = vec![(committee[0], sign(&sks[0], &msg))];
    assert!(
        !root.verify_signatures(&committee),
        "a single-signature full-mode root MUST be refused on restart — the \
         recovery anchor is correct; the persistence under-feeds it (N3 hole)"
    );

    // ── THE FIX TARGET: a genuine committee quorum over the SAME message. ──
    root.quorum_signatures = sks
        .iter()
        .map(|k| (k.public_key(), sign(k, &msg)))
        .collect();
    assert!(
        root.verify_signatures(&committee),
        "a genuine >=threshold committee quorum over the root's signing message \
         MUST be accepted — this is the record the commit path must persist"
    );

    // ── The anchor stays strict against forgery: >=threshold signatures that
    //    do NOT verify over THIS root's message (they signed a different
    //    merkle_root) are still refused. ──
    let other = StoredAttestedRoot {
        merkle_root: [0x00; 32],
        ..root.clone()
    };
    let other_msg = other.signing_message();
    root.quorum_signatures = sks
        .iter()
        .map(|k| (k.public_key(), sign(k, &other_msg)))
        .collect();
    assert!(
        !root.verify_signatures(&committee),
        "three signatures over a DIFFERENT merkle_root must NOT satisfy the \
         anchor — the check binds the committed state root, not just a count"
    );
}

/// REGRESSION — the N3 committee-restart hole is CLOSED by Fix B.
///
/// This reproduces the exact wedge and proves the fix, at the persistence
/// boundary a real restart crosses (`store_attested_root` → drop the store →
/// reopen → `latest_attested_root` → verify the anchor):
///
///   * PRE-FIX shape (the wedge): a full-mode root carrying only the local
///     node's single signature at `threshold = committee-size` CANNOT re-anchor
///     — neither the light-client `verify_signatures` nor the new
///     `verify_finalization_quorum` accepts it. This is the fail-close a
///     committee node hit after finalizing >=1 height.
///   * POST-FIX shape (Fix B): the same root, once the >=threshold committee
///     finalization-vote quorum has assembled into `finalization_quorum`,
///     survives the store/reload restart and `verify_finalization_quorum`
///     ACCEPTS it — the node re-anchors and keeps finalizing.
///   * SOUNDNESS held: a root whose `finalization_quorum` is a sub-threshold or
///     wrong-root set of signatures is still REFUSED after reload. No quorum,
///     no anchor.
#[test]
fn committee_node_restarts_cleanly_with_finalization_quorum() {
    use crate::federation::QuorumSignature;
    use dregg_federation::frost::MlDsaSigningKey;
    use dregg_types::{SigningKey, sign};

    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("committee_restart.redb");

    // A 3-member full-mode committee; threshold = supermajority(3) = 3.
    let sks: Vec<SigningKey> = (1u8..=3)
        .map(|s| SigningKey::from_bytes(&[s; 32]))
        .collect();
    let committee: Vec<PublicKey> = sks.iter().map(|k| k.public_key()).collect();
    // The committee's ML-DSA-65 keypairs, derived from the SAME seed bytes as
    // the ed25519 keys (exactly the production derivation) — the PQ half.
    let pqs: Vec<(dregg_federation::frost::MlDsaPublicKey, MlDsaSigningKey)> = (1u8..=3)
        .map(|s| MlDsaSigningKey::from_seed(&[s; 32]))
        .collect();
    // The genesis-ENROLLED ML-DSA roster, aligned index-for-index with `committee`.
    let ml_dsa_committee: Vec<dregg_federation::frost::MlDsaPublicKey> =
        pqs.iter().map(|(pk, _)| pk.clone()).collect();

    let block_id = [0xCD; 32];
    let merkle_root = [0xAB; 32];

    // The record the FIXED commit path persists once the vote quorum assembles:
    // the local single sig stays in `quorum_signatures` (light-client
    // attestation), and the >=threshold committee HYBRID finalization-vote
    // signatures over `(block_id, merkle_root)` fill `finalization_quorum` — each
    // carrying BOTH halves and the voter's ML-DSA pubkey (option (a)).
    let vote_msg = dregg_types::finalization_vote_signing_message(&block_id, &merkle_root);
    let hybrid_quorum = |msg: &[u8]| -> Vec<QuorumSignature> {
        sks.iter()
            .zip(pqs.iter())
            .map(|(k, (pq_pk, pq_sk))| QuorumSignature {
                voter: k.public_key(),
                signature: sign(k, msg),
                ml_dsa_pubkey: pq_pk.0.to_vec(),
                pq_signature: pq_sk.sign(msg).expect("ml-dsa signing"),
            })
            .collect()
    };
    let quorum: Vec<QuorumSignature> = hybrid_quorum(&vote_msg);

    let base = StoredAttestedRoot {
        merkle_root,
        note_tree_root: None,
        nullifier_set_root: None,
        height: 1,
        timestamp: 1_700_000_000,
        blocklace_block_id: Some(block_id),
        finality_round: Some(1),
        // The single LOCAL signature over the full `signing_message()` — this is
        // all a full-mode node holds synchronously (1 < threshold 3).
        quorum_signatures: vec![(
            committee[0],
            sign(
                &sks[0],
                &StoredAttestedRoot {
                    merkle_root,
                    note_tree_root: None,
                    nullifier_set_root: None,
                    height: 1,
                    timestamp: 1_700_000_000,
                    blocklace_block_id: Some(block_id),
                    finality_round: Some(1),
                    quorum_signatures: Vec::new(),
                    threshold_qc: None,
                    threshold: 3,
                    federation_id: dregg_types::FederationId::PLACEHOLDER,
                    receipt_stream_root: None,
                    finalization_quorum: Vec::new(),
                }
                .signing_message(),
            ),
        )],
        threshold_qc: None,
        threshold: 3,
        federation_id: dregg_types::FederationId::PLACEHOLDER,
        receipt_stream_root: None,
        finalization_quorum: Vec::new(),
    };

    // ── THE WEDGE (pre-fix persisted shape): only the lone local sig. ──
    // Neither anchor path can re-verify it → the node fail-closes.
    assert!(
        !base.verify_signatures(&committee),
        "lone local sig (1 < 3) must NOT satisfy the light-client anchor"
    );
    assert!(
        !base.verify_finalization_quorum(&committee, &ml_dsa_committee),
        "an empty finalization_quorum must NOT satisfy the restart anchor (the wedge)"
    );

    // ── FIX B (post-quorum-assembly persisted shape). ──
    let fixed = StoredAttestedRoot {
        finalization_quorum: quorum.clone(),
        ..base.clone()
    };

    // Persist it, then simulate a RESTART: drop the store, reopen from disk.
    {
        let store = PersistentStore::open(&path).unwrap();
        store.store_attested_root(&fixed).unwrap();
    }
    let reloaded = {
        let store = PersistentStore::open(&path).unwrap();
        store.latest_attested_root().unwrap().unwrap()
    };
    assert_eq!(reloaded.height, 1);
    assert!(
        reloaded.verify_finalization_quorum(&committee, &ml_dsa_committee),
        "after restart, a genuine >=threshold committee finalization-vote quorum \
         over the finalized root MUST re-anchor — the committee node restarts cleanly"
    );

    // ── SOUNDNESS: a sub-threshold quorum is still refused after reload. ──
    let sub_quorum = StoredAttestedRoot {
        finalization_quorum: quorum[..2].to_vec(), // 2 < 3
        ..base.clone()
    };
    assert!(
        !sub_quorum.verify_finalization_quorum(&committee, &ml_dsa_committee),
        "a sub-threshold finalization quorum must be refused — no weakening"
    );

    // ── SOUNDNESS: >=threshold signatures over a DIFFERENT root are refused. ──
    let wrong_msg = dregg_types::finalization_vote_signing_message(&block_id, &[0x00; 32]);
    let wrong_root_quorum = hybrid_quorum(&wrong_msg);
    let forged = StoredAttestedRoot {
        finalization_quorum: wrong_root_quorum,
        ..base.clone()
    };
    assert!(
        !forged.verify_finalization_quorum(&committee, &ml_dsa_committee),
        "three sigs over a DIFFERENT merkle_root must NOT anchor THIS root — the \
         quorum binds the committed state, not just a count"
    );

    // ── SOUNDNESS: corrupting the PQ half alone makes restart REFUSE. Every
    // ed25519 half is untouched (still valid), yet the hybrid anchor fails —
    // the post-quantum half is load-bearing, not decorative. ──
    let mut pq_corrupt = quorum.clone();
    pq_corrupt[0].pq_signature[0] ^= 0xFF;
    let pq_forged = StoredAttestedRoot {
        finalization_quorum: pq_corrupt,
        ..base.clone()
    };
    assert!(
        !pq_forged.verify_finalization_quorum(&committee, &ml_dsa_committee),
        "a corrupted ML-DSA half must refuse the restart anchor even though every \
         ed25519 half still verifies (classical ∧ pq)"
    );

    // ── SOUNDNESS: a MISSING PQ half (empty / wrong-length pubkey) is refused. ──
    let mut pq_missing = quorum.clone();
    pq_missing[0].pq_signature = Vec::new();
    let missing_sig = StoredAttestedRoot {
        finalization_quorum: pq_missing,
        ..base.clone()
    };
    assert!(
        !missing_sig.verify_finalization_quorum(&committee, &ml_dsa_committee),
        "an empty ML-DSA signature cannot satisfy the hybrid anchor"
    );
    let mut pq_badkey = quorum.clone();
    pq_badkey[0].ml_dsa_pubkey = vec![0u8; 10]; // wrong length → undecodable
    let bad_key = StoredAttestedRoot {
        finalization_quorum: pq_badkey,
        ..base.clone()
    };
    assert!(
        !bad_key.verify_finalization_quorum(&committee, &ml_dsa_committee),
        "an undecodable ML-DSA pubkey refuses the whole quorum — no silent skip"
    );

    // ── SOUNDNESS: an equivocating single voter cannot inflate the quorum. ──
    let inflated = StoredAttestedRoot {
        finalization_quorum: vec![quorum[0].clone(), quorum[0].clone(), quorum[0].clone()],
        ..base.clone()
    };
    assert!(
        !inflated.verify_finalization_quorum(&committee, &ml_dsa_committee),
        "one voter repeated 3x is 1 distinct signer < threshold 3 — refused"
    );
}

/// Build a 3-member committee, its ed25519+ML-DSA keys, and a persisted attested
/// root carrying a genuine HYBRID finalization-vote quorum. Returns
/// `(committee, ml_dsa_committee, root, block_id, merkle_root)` for restart tests
/// below — the ML-DSA roster is the genesis-ENROLLED one, aligned with `committee`.
#[cfg(test)]
fn hybrid_quorum_fixture() -> (
    Vec<PublicKey>,
    Vec<dregg_federation::frost::MlDsaPublicKey>,
    StoredAttestedRoot,
    [u8; 32],
    [u8; 32],
) {
    use crate::federation::QuorumSignature;
    use dregg_federation::frost::MlDsaSigningKey;
    use dregg_types::{SigningKey, sign};

    let sks: Vec<SigningKey> = (1u8..=3)
        .map(|s| SigningKey::from_bytes(&[s; 32]))
        .collect();
    let committee: Vec<PublicKey> = sks.iter().map(|k| k.public_key()).collect();
    let pqs: Vec<(dregg_federation::frost::MlDsaPublicKey, MlDsaSigningKey)> = (1u8..=3)
        .map(|s| MlDsaSigningKey::from_seed(&[s; 32]))
        .collect();
    let ml_dsa_committee: Vec<dregg_federation::frost::MlDsaPublicKey> =
        pqs.iter().map(|(pk, _)| pk.clone()).collect();

    let block_id = [0xCD; 32];
    let merkle_root = [0xAB; 32];
    let vote_msg = dregg_types::finalization_vote_signing_message(&block_id, &merkle_root);
    let quorum: Vec<QuorumSignature> = sks
        .iter()
        .zip(pqs.iter())
        .map(|(k, (pq_pk, pq_sk))| QuorumSignature {
            voter: k.public_key(),
            signature: sign(k, &vote_msg),
            ml_dsa_pubkey: pq_pk.0.to_vec(),
            pq_signature: pq_sk.sign(&vote_msg).expect("ml-dsa signing"),
        })
        .collect();

    let root = StoredAttestedRoot {
        merkle_root,
        note_tree_root: None,
        nullifier_set_root: None,
        height: 1,
        timestamp: 1_700_000_000,
        blocklace_block_id: Some(block_id),
        finality_round: Some(1),
        quorum_signatures: Vec::new(),
        threshold_qc: None,
        threshold: 3,
        federation_id: dregg_types::FederationId::PLACEHOLDER,
        receipt_stream_root: None,
        finalization_quorum: quorum,
    };
    (committee, ml_dsa_committee, root, block_id, merkle_root)
}

/// A persisted HYBRID quorum re-verifies after a store/reload restart iff BOTH
/// halves are intact: the reloaded root re-anchors, and every signer's ed25519
/// AND ML-DSA-65 half verifies over the finalized `(block_id, merkle_root)`.
#[test]
fn restart_reverifies_hybrid_quorum() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("hybrid_restart.redb");
    let (committee, ml_dsa_committee, root, _block_id, _merkle_root) = hybrid_quorum_fixture();

    {
        let store = PersistentStore::open(&path).unwrap();
        store.store_attested_root(&root).unwrap();
    }
    // RESTART: reopen from disk (postcard round-trip of the widened field).
    let reloaded = {
        let store = PersistentStore::open(&path).unwrap();
        store.latest_attested_root().unwrap().unwrap()
    };
    assert_eq!(
        reloaded, root,
        "the widened hybrid quorum round-trips postcard"
    );
    assert!(
        reloaded.verify_finalization_quorum(&committee, &ml_dsa_committee),
        "a persisted genuine hybrid quorum re-anchors on restart (classical ∧ pq)"
    );
}

/// Corrupting the POST-QUANTUM half of a persisted quorum makes restart REFUSE —
/// even though every ed25519 half is untouched. The persisted anchor now
/// re-verifies the FULL hybrid quorum, not just ed25519.
#[test]
fn restart_refuses_missing_pq_half() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("hybrid_restart_bad.redb");
    let (committee, ml_dsa_committee, mut root, _block_id, _merkle_root) = hybrid_quorum_fixture();

    // Corrupt one signer's ML-DSA signature; the ed25519 half stays valid.
    root.finalization_quorum[0].pq_signature[0] ^= 0xFF;

    {
        let store = PersistentStore::open(&path).unwrap();
        store.store_attested_root(&root).unwrap();
    }
    let reloaded = {
        let store = PersistentStore::open(&path).unwrap();
        store.latest_attested_root().unwrap().unwrap()
    };
    assert!(
        !reloaded.verify_finalization_quorum(&committee, &ml_dsa_committee),
        "a broken ML-DSA half must make the restart anchor REFUSE — the persisted \
         quorum is hybrid, not ed25519-only"
    );

    // And a fully DROPPED pq half (empty signature) is equally refused.
    let (committee2, ml_dsa_committee2, mut root2, _b, _m) = hybrid_quorum_fixture();
    root2.finalization_quorum[0].pq_signature = Vec::new();
    assert!(
        !root2.verify_finalization_quorum(&committee2, &ml_dsa_committee2),
        "an empty ML-DSA signature cannot satisfy the hybrid restart anchor"
    );
}

/// **THE QUANTUM-FORGERY ADVERSARIAL TEST (persist restart anchor).** The exact
/// attack the enrolled-roster pin closes: a quantum adversary breaks ed25519 for
/// enrolled member `P` (we reuse P's real ed25519 key to stand in for the forged
/// classical half), generates its OWN fresh ML-DSA-65 keypair, and signs the PQ
/// half with it — carrying that attacker key in `ml_dsa_pubkey`. Before the pin,
/// the PQ half was checked against the self-carried key, so BOTH halves passed
/// and the restart re-anchored a FORGED root. With the pin, the self-carried key
/// ≠ P's enrolled key, so `verify_finalization_quorum` REJECTS the whole quorum.
/// The honest enrolled-key quorum still re-anchors, and an unconfigured (empty)
/// enrolled roster fails closed rather than downgrade to ed25519-only.
#[test]
fn quantum_forged_pq_key_is_rejected() {
    use dregg_federation::frost::MlDsaSigningKey;

    let (committee, ml_dsa_committee, root, block_id, merkle_root) = hybrid_quorum_fixture();
    let vote_msg = dregg_types::finalization_vote_signing_message(&block_id, &merkle_root);

    // The HONEST persisted quorum re-anchors (baseline).
    assert!(
        root.verify_finalization_quorum(&committee, &ml_dsa_committee),
        "the honest enrolled-key quorum re-anchors on restart"
    );

    // THE ATTACK: replace every signer's ML-DSA key + signature with a FRESH
    // attacker keypair (a quantum adversary that broke ed25519 keeps the ed25519
    // halves valid). Each PQ half verifies under the attacker's own key.
    let mut forged = root.clone();
    for (i, qs) in forged.finalization_quorum.iter_mut().enumerate() {
        let attacker = MlDsaSigningKey::from_seed(&[0xA0 + i as u8; 32]);
        qs.ml_dsa_pubkey = attacker.0.0.to_vec();
        qs.pq_signature = attacker.1.sign(&vote_msg).expect("ml-dsa sign");
    }
    assert!(
        !forged.verify_finalization_quorum(&committee, &ml_dsa_committee),
        "a self-carried attacker ML-DSA key (not the enrolled key) must be REJECTED \
         even though every ed25519 half and every PQ half verifies on its own terms"
    );

    // NO SILENT DOWNGRADE: an empty (misaligned) enrolled roster fails closed even
    // for the honest signers — never an ed25519-only re-anchor.
    assert!(
        !root.verify_finalization_quorum(&committee, &[]),
        "an unconfigured (empty) enrolled roster must fail closed"
    );

    // And the hybrid tamper-floor leg agrees: the forged lone entry is not a
    // committee binding.
    let lone_forged = StoredAttestedRoot {
        finalization_quorum: forged.finalization_quorum[..1].to_vec(),
        quorum_signatures: Vec::new(),
        ..root.clone()
    };
    assert!(
        !lone_forged.has_any_valid_committee_signature(&committee, &ml_dsa_committee),
        "a forged-PQ-key lone vote is not a committee binding"
    );
}

/// The LONE-SIGNATURE tamper floor is HYBRID on the vote leg: a single
/// `finalization_quorum` entry counts toward `has_any_valid_committee_signature`
/// only when BOTH halves verify. A lone signature whose ML-DSA half is forged,
/// empty, or rides an undecodable pubkey no longer counts — even though its
/// ed25519 half is perfectly valid — so there is no classical-only acceptance
/// surface left over `QuorumSignature`s (consistent with
/// `verify_finalization_quorum`'s per-signer bar).
#[test]
fn lone_signature_tamper_floor_is_hybrid() {
    let (committee, ml_dsa_committee, root, _block_id, _merkle_root) = hybrid_quorum_fixture();

    // A single GENUINE hybrid vote entry satisfies the floor (it is a
    // lone-signature check, not a quorum).
    let lone = StoredAttestedRoot {
        finalization_quorum: root.finalization_quorum[..1].to_vec(),
        ..root.clone()
    };
    assert!(
        lone.has_any_valid_committee_signature(&committee, &ml_dsa_committee),
        "one genuine hybrid committee vote binds the root (the tamper floor)"
    );

    // Forge the PQ half ONLY: the ed25519 half stays valid, yet the lone
    // signature must NOT count any more (classical ∧ pq).
    let mut pq_forged = lone.clone();
    pq_forged.finalization_quorum[0].pq_signature[0] ^= 0xFF;
    assert!(
        !pq_forged.has_any_valid_committee_signature(&committee, &ml_dsa_committee),
        "a lone signature with a FORGED ML-DSA half must not count — no \
         classical-only acceptance surface"
    );

    // An EMPTY PQ half is equally refused.
    let mut pq_missing = lone.clone();
    pq_missing.finalization_quorum[0].pq_signature = Vec::new();
    assert!(
        !pq_missing.has_any_valid_committee_signature(&committee, &ml_dsa_committee),
        "an empty ML-DSA signature cannot satisfy the hybrid tamper floor"
    );

    // An undecodable (wrong-length) carried ML-DSA pubkey is refused.
    let mut pq_badkey = lone.clone();
    pq_badkey.finalization_quorum[0].ml_dsa_pubkey = vec![0u8; 10];
    assert!(
        !pq_badkey.has_any_valid_committee_signature(&committee, &ml_dsa_committee),
        "an undecodable ML-DSA pubkey is not a committee binding"
    );

    // A voter outside the committee never counts, hybrid-valid or not.
    assert!(
        !lone.has_any_valid_committee_signature(&committee[1..], &ml_dsa_committee[1..]),
        "a non-member's signature is not a committee binding"
    );

    // The quorum_signatures leg (the node's OWN light-client self-signature,
    // structurally classical) still provides the floor when the vote leg is
    // empty — the trailing-head tamper-check the lone local signature exists for.
    use dregg_types::{SigningKey, sign};
    let sk = SigningKey::from_bytes(&[1u8; 32]);
    let mut self_signed = StoredAttestedRoot {
        quorum_signatures: Vec::new(),
        finalization_quorum: Vec::new(),
        ..root.clone()
    };
    let msg = self_signed.signing_message();
    self_signed.quorum_signatures = vec![(sk.public_key(), sign(&sk, &msg))];
    assert!(
        self_signed.has_any_valid_committee_signature(&committee, &ml_dsa_committee),
        "the local light-client self-signature still provides the tamper floor"
    );
}

#[test]
fn attested_root_store_and_load() {
    let store = new_store();

    let root = sample_attested_root(1);
    store.store_attested_root(&root).unwrap();

    let loaded = store.latest_attested_root().unwrap();
    assert_eq!(loaded, Some(root));
}

#[test]
fn attested_root_latest_tracks_highest() {
    let store = new_store();

    store.store_attested_root(&sample_attested_root(1)).unwrap();
    store.store_attested_root(&sample_attested_root(5)).unwrap();
    store.store_attested_root(&sample_attested_root(3)).unwrap();

    // Latest should be height 5 (highest stored).
    let latest = store.latest_attested_root().unwrap().unwrap();
    assert_eq!(latest.height, 5);
}

#[test]
fn attested_root_by_height() {
    let store = new_store();

    let root3 = sample_attested_root(3);
    store.store_attested_root(&root3).unwrap();

    let loaded = store.attested_root_at_height(3).unwrap();
    assert_eq!(loaded, Some(root3));
    assert_eq!(store.attested_root_at_height(99).unwrap(), None);
}

#[test]
fn attested_root_empty() {
    let store = new_store();
    assert_eq!(store.latest_attested_root().unwrap(), None);
    assert_eq!(store.attested_root_count().unwrap(), 0);
}

#[test]
fn attested_root_count() {
    let store = new_store();

    store.store_attested_root(&sample_attested_root(1)).unwrap();
    store.store_attested_root(&sample_attested_root(2)).unwrap();
    store.store_attested_root(&sample_attested_root(3)).unwrap();
    assert_eq!(store.attested_root_count().unwrap(), 3);
}

#[test]
fn attested_root_all_ordered() {
    let store = new_store();

    store.store_attested_root(&sample_attested_root(3)).unwrap();
    store.store_attested_root(&sample_attested_root(1)).unwrap();
    store.store_attested_root(&sample_attested_root(2)).unwrap();

    let all = store.all_attested_roots().unwrap();
    assert_eq!(all.len(), 3);
    // Should be in height order (redb stores u64 keys in order).
    assert_eq!(all[0].height, 1);
    assert_eq!(all[1].height, 2);
    assert_eq!(all[2].height, 3);
}

#[test]
fn attested_root_validity() {
    let root = sample_attested_root(1);
    assert!(root.is_structurally_complete()); // 3 sigs >= threshold 2.

    let invalid = StoredAttestedRoot {
        threshold: 5,
        ..root
    };
    assert!(!invalid.is_structurally_complete()); // 3 sigs < threshold 5.
}

// =============================================================================
// Edge Cases
// =============================================================================

#[test]
fn many_revocations() {
    let store = new_store();

    let ids: Vec<String> = (0..1000).map(|i| format!("token-{i:05}")).collect();
    let refs: Vec<&str> = ids.iter().map(|s| s.as_str()).collect();
    store.store_revocations_batch(&refs).unwrap();

    assert_eq!(store.revocation_count().unwrap(), 1000);
    assert!(store.is_revoked("token-00500").unwrap());
    assert!(!store.is_revoked("token-01000").unwrap());
}

#[test]
fn store_root_hex() {
    let root = sample_attested_root(0xAB);
    // Height 0xAB = 171, so merkle_root = [171; 32].
    assert_eq!(root.root_hex(), "abababab");
}

// =============================================================================
// Note Tree & Nullifier Tests
// =============================================================================

#[test]
fn test_store_note_roundtrip() {
    use dregg_cell::note::Note;

    let store = new_store();

    // Create notes with deterministic randomness.
    let note1 = Note::with_randomness([1u8; 32], [1, 100, 0, 0, 0, 0, 0, 0], [10u8; 32]);
    let note2 = Note::with_randomness([2u8; 32], [1, 200, 0, 0, 0, 0, 0, 0], [20u8; 32]);
    let note3 = Note::with_randomness([3u8; 32], [2, 50, 0, 0, 0, 0, 0, 0], [30u8; 32]);

    let c1 = note1.commitment();
    let c2 = note2.commitment();
    let c3 = note3.commitment();

    // Store commitments.
    let pos1 = store.store_note_commitment(&c1).unwrap();
    let pos2 = store.store_note_commitment(&c2).unwrap();
    let pos3 = store.store_note_commitment(&c3).unwrap();

    assert_eq!(pos1, 0);
    assert_eq!(pos2, 1);
    assert_eq!(pos3, 2);
    assert_eq!(store.note_count().unwrap(), 3);

    // Recover and verify tree root matches.
    let commitments = store.load_all_note_commitments().unwrap();
    assert_eq!(commitments.len(), 3);
    assert_eq!(commitments[0], c1);
    assert_eq!(commitments[1], c2);
    assert_eq!(commitments[2], c3);

    // Rebuild tree and check root.
    let mut tree = crate::note_tree::NoteTree::from_commitments(commitments);
    let root = tree.root();
    let stored_root = store.note_tree_root().unwrap();
    assert_eq!(root, stored_root);
}

#[test]
fn test_nullifier_persistence() {
    use dregg_cell::note::{Note, Nullifier};

    let store = new_store();
    let note = Note::with_randomness([1u8; 32], [1, 100, 0, 0, 0, 0, 0, 0], [10u8; 32]);
    let spending_key = [0xBB; 32];
    let nullifier = note.nullifier(&spending_key);

    // Not spent initially.
    assert!(!store.is_nullifier_spent(&nullifier).unwrap());

    // Store it.
    store.store_nullifier(&nullifier).unwrap();

    // Now it's spent.
    assert!(store.is_nullifier_spent(&nullifier).unwrap());

    // Double-spend is rejected.
    let result = store.store_nullifier(&nullifier);
    assert!(matches!(result, Err(StoreError::Integrity(_))));

    // A different nullifier is not spent.
    let other_nullifier = Nullifier([0xFF; 32]);
    assert!(!store.is_nullifier_spent(&other_nullifier).unwrap());
}

#[test]
fn test_nullifier_persistence_across_restart() {
    use dregg_cell::note::Note;

    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("note_test.redb");
    let note = Note::with_randomness([1u8; 32], [1, 100, 0, 0, 0, 0, 0, 0], [10u8; 32]);
    let spending_key = [0xBB; 32];
    let nullifier = note.nullifier(&spending_key);

    // First session: store commitment and nullifier.
    {
        let store = PersistentStore::open(&path).unwrap();
        store.store_note_commitment(&note.commitment()).unwrap();
        store.store_nullifier(&nullifier).unwrap();
    }

    // Second session: verify persistence.
    {
        let store = PersistentStore::open(&path).unwrap();
        assert_eq!(store.note_count().unwrap(), 1);
        assert!(store.is_nullifier_spent(&nullifier).unwrap());

        let commitments = store.load_all_note_commitments().unwrap();
        assert_eq!(commitments[0], note.commitment());
    }
}

#[test]
fn test_spend_note_atomic() {
    use dregg_cell::note::Note;

    let store = new_store();

    let note1 = Note::with_randomness([1u8; 32], [1, 100, 0, 0, 0, 0, 0, 0], [10u8; 32]);
    let note2 = Note::with_randomness([2u8; 32], [1, 200, 0, 0, 0, 0, 0, 0], [20u8; 32]);
    let spending_key = [0xBB; 32];

    // First: store the original commitment for note1 (simulate issuance).
    store.store_note_commitment(&note1.commitment()).unwrap();
    assert_eq!(store.note_count().unwrap(), 1);

    // Spend note1 atomically: insert its nullifier + store the output commitment (note2).
    let nullifier1 = note1.nullifier(&spending_key);
    let pos = store
        .spend_note_atomic(&nullifier1, &note2.commitment())
        .unwrap();
    assert_eq!(pos, 1); // Second commitment is at position 1.

    // Verify both side effects occurred.
    assert!(store.is_nullifier_spent(&nullifier1).unwrap());
    assert_eq!(store.note_count().unwrap(), 2);

    // Double-spend is rejected atomically.
    let note3 = Note::with_randomness([3u8; 32], [2, 50, 0, 0, 0, 0, 0, 0], [30u8; 32]);
    let result = store.spend_note_atomic(&nullifier1, &note3.commitment());
    assert!(matches!(result, Err(StoreError::Integrity(_))));

    // The failed double-spend must not have added the commitment.
    assert_eq!(store.note_count().unwrap(), 2);
}

#[test]
fn test_spend_note_atomic_double_spend_no_side_effects() {
    use dregg_cell::note::Note;

    let store = new_store();

    let note1 = Note::with_randomness([1u8; 32], [1, 100, 0, 0, 0, 0, 0, 0], [10u8; 32]);
    let note2 = Note::with_randomness([2u8; 32], [1, 200, 0, 0, 0, 0, 0, 0], [20u8; 32]);
    let note3 = Note::with_randomness([3u8; 32], [2, 50, 0, 0, 0, 0, 0, 0], [30u8; 32]);
    let spending_key = [0xBB; 32];
    let nullifier1 = note1.nullifier(&spending_key);

    // Spend note1 successfully (creating note2 as output).
    let pos = store
        .spend_note_atomic(&nullifier1, &note2.commitment())
        .unwrap();
    assert_eq!(pos, 0);
    assert_eq!(store.note_count().unwrap(), 1);

    // Attempt double-spend: should fail AND not add note3's commitment.
    let result = store.spend_note_atomic(&nullifier1, &note3.commitment());
    assert!(result.is_err());
    assert_eq!(store.note_count().unwrap(), 1); // Still 1, not 2.
}

#[test]
fn test_attested_root_includes_note_tree() {
    use dregg_cell::note::Note;

    let store = new_store();

    // Add some notes.
    let note1 = Note::with_randomness([1u8; 32], [1, 100, 0, 0, 0, 0, 0, 0], [10u8; 32]);
    let note2 = Note::with_randomness([2u8; 32], [1, 200, 0, 0, 0, 0, 0, 0], [20u8; 32]);
    store.store_note_commitment(&note1.commitment()).unwrap();
    store.store_note_commitment(&note2.commitment()).unwrap();

    // Add a nullifier.
    let spending_key = [0xBB; 32];
    let nullifier = note1.nullifier(&spending_key);
    store.store_nullifier(&nullifier).unwrap();

    // Get the roots.
    let note_root = store.note_tree_root().unwrap();
    let nullifier_root = store.nullifier_set_root().unwrap();

    // Both should be non-zero (non-empty sets).
    assert_ne!(note_root, [0u8; 32]);
    assert_ne!(nullifier_root, [0u8; 32]);

    // Create an attested root that includes all three components.
    let attested = StoredAttestedRoot {
        merkle_root: [0xAB; 32], // Cell state root.
        note_tree_root: Some(note_root),
        nullifier_set_root: Some(nullifier_root),
        height: 1,
        timestamp: 1700000000,
        blocklace_block_id: None,
        finality_round: None,
        quorum_signatures: vec![(PublicKey([0x11; 32]), Signature([0x22; 64]))],
        threshold_qc: None,
        threshold: 1,
        federation_id: dregg_types::FederationId::PLACEHOLDER,
        receipt_stream_root: None,
        finalization_quorum: Vec::new(),
    };

    // Store and recover.
    store.store_attested_root(&attested).unwrap();
    let loaded = store.latest_attested_root().unwrap().unwrap();
    assert_eq!(loaded.note_tree_root, Some(note_root));
    assert_eq!(loaded.nullifier_set_root, Some(nullifier_root));
    assert_eq!(loaded.merkle_root, [0xAB; 32]);
}

// =============================================================================
// Forever-Digest Set Tests (restart-durable anti-replay carriers)
// =============================================================================

#[test]
fn forever_digests_survive_reopen() {
    use crate::tables::{NS_COURT_RESOLVED, NS_TRUSTLINE_DIGEST};

    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("forever.redb");

    let scope = [0x11; 32];
    let draw = [0x22; 32];
    let resolved = [0x33; 32];

    {
        let store = PersistentStore::open(&path).expect("open store");
        assert!(
            store
                .record_forever_digest(NS_TRUSTLINE_DIGEST, &scope, &draw)
                .unwrap(),
            "first burn is new"
        );
        assert!(
            !store
                .record_forever_digest(NS_TRUSTLINE_DIGEST, &scope, &draw)
                .unwrap(),
            "second burn is idempotent"
        );
        assert!(
            store
                .record_forever_digest(NS_COURT_RESOLVED, &[0u8; 32], &resolved)
                .unwrap()
        );
        // Drop: the simulated restart.
    }

    let store = PersistentStore::open(&path).expect("reopen store");
    assert!(
        store
            .forever_digest_seen(NS_TRUSTLINE_DIGEST, &scope, &draw)
            .unwrap(),
        "a burned draw digest survives the restart"
    );
    assert!(
        store
            .forever_digest_seen(NS_COURT_RESOLVED, &[0u8; 32], &resolved)
            .unwrap(),
        "a resolved-evidence digest survives the restart"
    );

    // Namespaces do not bleed: the same bytes under the other namespace are unseen.
    assert!(
        !store
            .forever_digest_seen(NS_COURT_RESOLVED, &scope, &draw)
            .unwrap()
    );
    assert!(
        !store
            .forever_digest_seen(NS_TRUSTLINE_DIGEST, &[0u8; 32], &resolved)
            .unwrap()
    );

    // Boot-time load returns exactly the namespace's pairs.
    let trustline_pairs = store.load_forever_digests(NS_TRUSTLINE_DIGEST).unwrap();
    assert_eq!(trustline_pairs, vec![(scope, draw)]);
    let court_pairs = store.load_forever_digests(NS_COURT_RESOLVED).unwrap();
    assert_eq!(court_pairs, vec![([0u8; 32], resolved)]);
}

#[test]
fn forever_digest_scopes_are_disjoint() {
    use crate::tables::NS_TRUSTLINE_DIGEST;

    let store = new_store();
    let digest = [0x77; 32];
    store
        .record_forever_digest(NS_TRUSTLINE_DIGEST, &[0xAA; 32], &digest)
        .unwrap();
    assert!(
        !store
            .forever_digest_seen(NS_TRUSTLINE_DIGEST, &[0xBB; 32], &digest)
            .unwrap(),
        "a digest burned against one trustline does not refuse another's"
    );
}

// =============================================================================
// Durable Channel Roster Tests (.docs-history-noclaude/PERSISTENCE.md §3, the roster caveat)
// =============================================================================

#[test]
fn channel_rosters_roundtrip_and_survive_reopen() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("rosters.redb");

    let channel_a = [0xA1; 32];
    let channel_b = [0xB2; 32];
    let roster_a = vec![1u8, 2, 3, 4];
    let roster_a2 = vec![9u8, 8, 7];
    let roster_b = vec![5u8, 6];

    {
        let store = PersistentStore::open(&path).expect("open store");
        store.store_channel_roster(&channel_a, &roster_a).unwrap();
        store.store_channel_roster(&channel_b, &roster_b).unwrap();
        // Upsert: a later epoch step overwrites.
        store.store_channel_roster(&channel_a, &roster_a2).unwrap();
        // Drop: the simulated restart.
    }

    let store = PersistentStore::open(&path).expect("reopen store");
    let mut loaded = store.load_channel_rosters().unwrap();
    loaded.sort();
    assert_eq!(
        loaded,
        vec![
            (channel_a, roster_a2.clone()),
            (channel_b, roster_b.clone())
        ]
    );

    // A stale roster's discard is durable.
    store.remove_channel_roster(&channel_a).unwrap();
    let loaded = store.load_channel_rosters().unwrap();
    assert_eq!(loaded, vec![(channel_b, roster_b)]);
}
