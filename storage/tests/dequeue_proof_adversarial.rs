//! Adversarial tests for the dequeue-proof verifier (board #173).
//!
//! The old verifier was a stub that accepted ANY proof whose roots differed.
//! These tests pin the real fail-closed semantics: a dequeue proof must show
//! the claimed entry was the HEAD of the queue committed by `old_root`, and
//! that `new_root` is exactly that queue with the head removed — recomputed
//! against the same commitment scheme `enqueue` uses (domain-tagged
//! `hash_entry` leaves under `blake3_binary_root`).

use dregg_storage::queue::{
    DequeueProof, MerkleQueue, QueueEntry, empty_queue_root, verify_dequeue_proof,
    verify_dequeue_proof_against,
};

fn make_entry(content: &[u8], sender: [u8; 32], deposit: u64) -> QueueEntry {
    QueueEntry {
        content_hash: *blake3::hash(content).as_bytes(),
        sender,
        deposit,
        enqueued_at: 42,
        size: content.len(),
    }
}

fn three_entry_queue() -> (MerkleQueue, Vec<QueueEntry>) {
    let mut q = MerkleQueue::new(10);
    let entries: Vec<QueueEntry> = (0u8..3)
        .map(|i| {
            make_entry(
                format!("msg-{i}").as_bytes(),
                [i + 1; 32],
                100 * (i as u64 + 1),
            )
        })
        .collect();
    for e in &entries {
        q.enqueue(e.clone()).unwrap();
    }
    (q, entries)
}

// ---------------------------------------------------------------------------
// (a) Legitimate proofs verify.
// ---------------------------------------------------------------------------

#[test]
fn legitimate_proof_verifies() {
    let (mut q, entries) = three_entry_queue();
    let pre_root = q.root();

    let (got, proof) = q.dequeue().unwrap();
    assert_eq!(got, entries[0]);
    assert!(
        verify_dequeue_proof(&proof),
        "real dequeue proof must verify"
    );
    assert!(
        verify_dequeue_proof_against(&proof, &pre_root),
        "real dequeue proof must verify against the live pre-root"
    );
    assert_eq!(proof.new_root, q.root(), "post-root matches live queue");
    assert_eq!(proof.remaining_leaves.len(), 2);
}

#[test]
fn legitimate_proof_chain_verifies_to_empty() {
    let (mut q, _) = three_entry_queue();
    let mut tracked_root = q.root();

    for step in 0..3 {
        let (_, proof) = q.dequeue().unwrap();
        assert!(
            verify_dequeue_proof_against(&proof, &tracked_root),
            "proof at step {step} must verify against the tracked root"
        );
        tracked_root = proof.new_root;
    }
    assert_eq!(
        tracked_root,
        empty_queue_root(),
        "chain ends at the empty root"
    );
}

#[test]
fn single_entry_dequeue_to_empty_verifies() {
    let mut q = MerkleQueue::new(4);
    q.enqueue(make_entry(b"solo", [7u8; 32], 5)).unwrap();
    let (_, proof) = q.dequeue().unwrap();
    assert!(verify_dequeue_proof(&proof));
    assert_eq!(proof.new_root, empty_queue_root());
    assert!(proof.remaining_leaves.is_empty());
}

// ---------------------------------------------------------------------------
// (b) Forged proofs with arbitrary differing roots REFUSE.
//     (This is exactly what the old stub accepted.)
// ---------------------------------------------------------------------------

#[test]
fn forged_arbitrary_roots_refused() {
    let forged = DequeueProof {
        entry: make_entry(b"phantom", [0xEE; 32], 1),
        old_root: [0xAA; 32],
        new_root: [0xBB; 32],
        position: 0,
        remaining_leaves: vec![],
    };
    assert!(
        !verify_dequeue_proof(&forged),
        "arbitrary differing roots must refuse (the old stub accepted this)"
    );
}

#[test]
fn forged_roots_with_garbage_witness_refused() {
    let forged = DequeueProof {
        entry: make_entry(b"phantom", [0xEE; 32], 1),
        old_root: [0xAA; 32],
        new_root: [0xBB; 32],
        position: 3,
        remaining_leaves: vec![[0x11; 32], [0x22; 32]],
    };
    assert!(!verify_dequeue_proof(&forged));
}

#[test]
fn tampered_old_root_refused() {
    let (mut q, _) = three_entry_queue();
    let (_, proof) = q.dequeue().unwrap();
    let mut t = proof.clone();
    t.old_root = [0xFF; 32];
    assert!(!verify_dequeue_proof(&t));
}

#[test]
fn tampered_new_root_refused() {
    let (mut q, _) = three_entry_queue();
    let (_, proof) = q.dequeue().unwrap();
    let mut t = proof.clone();
    t.new_root = [0xFF; 32];
    assert!(!verify_dequeue_proof(&t));
}

#[test]
fn equal_roots_refused() {
    let (mut q, _) = three_entry_queue();
    let (_, proof) = q.dequeue().unwrap();
    let mut t = proof.clone();
    t.new_root = t.old_root;
    assert!(
        !verify_dequeue_proof(&t),
        "old_root == new_root is never a dequeue"
    );
}

// ---------------------------------------------------------------------------
// (c) Wrong head message REFUSES.
// ---------------------------------------------------------------------------

#[test]
fn wrong_head_entry_refused() {
    let (mut q, entries) = three_entry_queue();
    let (_, proof) = q.dequeue().unwrap();

    // Claim the SECOND entry was dequeued instead of the real head.
    let mut t = proof.clone();
    t.entry = entries[1].clone();
    assert!(
        !verify_dequeue_proof(&t),
        "claiming a non-head entry must refuse"
    );
}

#[test]
fn fabricated_entry_refused() {
    let (mut q, _) = three_entry_queue();
    let (_, proof) = q.dequeue().unwrap();
    let mut t = proof.clone();
    t.entry = make_entry(b"never-enqueued", [0xDD; 32], 999);
    assert!(!verify_dequeue_proof(&t));
}

#[test]
fn tampered_entry_fields_refused() {
    let (mut q, _) = three_entry_queue();
    let (_, proof) = q.dequeue().unwrap();

    // Every field of the entry is bound by the leaf commitment.
    let mut t = proof.clone();
    t.entry.content_hash = [0xDE; 32];
    assert!(!verify_dequeue_proof(&t), "content_hash tamper must refuse");

    let mut t = proof.clone();
    t.entry.sender = [0xDE; 32];
    assert!(!verify_dequeue_proof(&t), "sender tamper must refuse");

    let mut t = proof.clone();
    t.entry.deposit += 1;
    assert!(!verify_dequeue_proof(&t), "deposit tamper must refuse");

    let mut t = proof.clone();
    t.entry.enqueued_at += 1;
    assert!(!verify_dequeue_proof(&t), "enqueued_at tamper must refuse");

    let mut t = proof.clone();
    t.entry.size += 1;
    assert!(!verify_dequeue_proof(&t), "size tamper must refuse");
}

// ---------------------------------------------------------------------------
// (d) Replayed old proof against a newer root REFUSES.
// ---------------------------------------------------------------------------

#[test]
fn replayed_proof_against_newer_root_refused() {
    let (mut q, _) = three_entry_queue();

    let (_, proof1) = q.dequeue().unwrap();
    assert!(verify_dequeue_proof(&proof1));

    // Queue advanced; proof1's pre-root is stale.
    let live_root = q.root();
    assert_ne!(proof1.old_root, live_root);
    assert!(
        !verify_dequeue_proof_against(&proof1, &live_root),
        "replaying an old proof against the newer live root must refuse"
    );

    // The fresh proof for the current state verifies against the live root.
    let (_, proof2) = q.dequeue().unwrap();
    assert!(verify_dequeue_proof_against(&proof2, &live_root));
    assert!(
        !verify_dequeue_proof_against(&proof2, &proof2.new_root),
        "a proof never verifies against its own post-root"
    );
}

// ---------------------------------------------------------------------------
// Malformed witnesses fail closed.
// ---------------------------------------------------------------------------

#[test]
fn dropped_remaining_leaf_refused() {
    let (mut q, _) = three_entry_queue();
    let (_, proof) = q.dequeue().unwrap();
    let mut t = proof.clone();
    t.remaining_leaves.pop();
    assert!(
        !verify_dequeue_proof(&t),
        "dropping a pending message must refuse"
    );
}

#[test]
fn injected_remaining_leaf_refused() {
    let (mut q, _) = three_entry_queue();
    let (_, proof) = q.dequeue().unwrap();
    let mut t = proof.clone();
    t.remaining_leaves.push([0x99; 32]);
    assert!(
        !verify_dequeue_proof(&t),
        "injecting a pending message must refuse"
    );
}

#[test]
fn reordered_remaining_leaves_refused() {
    let (mut q, _) = three_entry_queue();
    let (_, proof) = q.dequeue().unwrap();
    let mut t = proof.clone();
    assert_eq!(t.remaining_leaves.len(), 2);
    t.remaining_leaves.swap(0, 1);
    assert!(
        !verify_dequeue_proof(&t),
        "reordering pending messages must refuse"
    );
}

#[test]
fn empty_claim_from_empty_root_refused() {
    // "Dequeued from an already-empty queue" can never verify: the old window
    // always contains at least the head leaf, and no domain-tagged entry leaf
    // is the all-zeros empty sentinel.
    let forged = DequeueProof {
        entry: make_entry(b"ghost", [0x01; 32], 0),
        old_root: empty_queue_root(),
        new_root: empty_queue_root(),
        position: 0,
        remaining_leaves: vec![],
    };
    assert!(!verify_dequeue_proof(&forged));
}

#[test]
fn proof_for_one_queue_refused_on_another() {
    // Two different queues; a valid proof from queue A must not verify
    // against queue B's live root.
    let (mut qa, _) = three_entry_queue();
    let mut qb = MerkleQueue::new(10);
    qb.enqueue(make_entry(b"other", [0x42; 32], 7)).unwrap();

    let (_, proof_a) = qa.dequeue().unwrap();
    assert!(verify_dequeue_proof(&proof_a));
    assert!(!verify_dequeue_proof_against(&proof_a, &qb.root()));
}

/// Zero-padding alias hardening: a proof smuggling a zero leaf into
/// `remaining_leaves` must refuse, even though the pow2 padding alias
/// (`merkle_root([a,b,c]) == merkle_root([a,b,c,0])`) would otherwise let
/// the pre-root check pass while admitting a non-canonical post-root
/// (proved in Lean: QueueRoot.refRoot_pad_alias / verifyDequeueStrict).
#[test]
fn zero_leaf_in_remaining_refuses() {
    let (mut q, _) = three_entry_queue();
    let (_, proof) = q.dequeue().unwrap();
    assert!(verify_dequeue_proof(&proof), "honest proof verifies");

    let mut forged = proof.clone();
    forged.remaining_leaves.push([0u8; 32]);
    // Fail-closed on the zero leaf alone, regardless of what roots the
    // forger recomputes around the alias.
    assert!(
        !verify_dequeue_proof(&forged),
        "zero-leaf smuggling must refuse"
    );
    assert!(!verify_dequeue_proof_against(&forged, &forged.old_root));
}
