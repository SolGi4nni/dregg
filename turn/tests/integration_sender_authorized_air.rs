//! SenderAuthorized AIR teeth: real STARK-backed Merkle-membership enforcement.
//!
//! `StateConstraint::SenderAuthorized { AuthorizedSet::PublicRoot { .. } }`
//! dispatches through the witnessed-predicate registry. The default builtin is
//! fail-closed (`NotYetWiredVerifier`), so SenderAuthorized could never *pass*
//! and the membership relation was never algebraically enforced. This wires the
//! real gadget (`MerkleMembershipStarkVerifier`) and proves:
//!
//!   1. An authorized sender (a genuine leaf under the published root) passes.
//!   2. An UNAUTHORIZED sender — no Merkle path to the root — is rejected at the
//!      STARK level (the membership proof does not verify against the root).
//!   3. A tampered membership proof is rejected.
//!
//! These exercise both the verifier directly and the full
//! `StateConstraint::SenderAuthorized` evaluation path.

use dregg_cell::preconditions::EvalContext;
use dregg_cell::predicate::{PredicateInput, WitnessedPredicateKind, WitnessedPredicateVerifier};
use dregg_cell::program::{
    AuthorizedSet, CellProgram, StateConstraint, TransitionMeta, WitnessBlobView, WitnessBundle,
    WitnessKindTag,
};
use dregg_cell::state::CellState;
use dregg_circuit::dsl::membership::create_test_witness;
use dregg_circuit::membership_descriptor_4ary::{DIGEST_W, Digest8};
use dregg_turn::executor::membership_verifier::{
    MerkleMembershipStarkVerifier, authorized_set_root_bytes, authorized_set_root_digest,
    prove_sender_membership, registry_with_real_sender_membership,
};

/// THE canonical chip-native membership compress — the executor's leaf domain
/// (`dregg_commit::typed::compress_member`, the same function the in-AIR gate
/// `withMembershipPubkeyCompress` forces). Since the `node8` widening it returns ALL EIGHT
/// output lanes of the deployed arity-16 absorb, not lane 0.
fn compress(bytes: &[u8; 32]) -> Digest8 {
    dregg_commit::typed::compress_member(bytes)
}

/// Build a (siblings, positions) Merkle witness for a given sender pk leaf at
/// the test tree of `depth`. Every co-path node is a full 8-felt digest.
fn witness_for(sender: &[u8; 32], depth: usize) -> (Vec<[Digest8; 3]>, Vec<u8>) {
    let leaf = compress(sender);
    let (sibs, pos, _root) = create_test_witness(leaf, depth);
    (sibs, pos)
}

#[test]
fn authorized_sender_passes_membership_stark() {
    let sender = [0x11u8; 32];
    let (sibs, pos) = witness_for(&sender, 3);
    let proof = prove_sender_membership(&sender, &sibs, &pos).expect("prove membership");
    let root_bytes = authorized_set_root_bytes(&sender, &sibs, &pos);

    let v = MerkleMembershipStarkVerifier;
    let res = v.verify(&root_bytes, &PredicateInput::Sender(&sender), &proof);
    assert!(res.is_ok(), "authorized sender must verify: {res:?}");
}

#[test]
fn unauthorized_sender_rejected_at_stark_level() {
    // Honest tree built for `member`. The attacker `intruder` is NOT a leaf.
    let member = [0x11u8; 32];
    let (sibs, pos) = witness_for(&member, 3);
    let root_bytes = authorized_set_root_bytes(&member, &sibs, &pos);

    let intruder = [0x99u8; 32];
    // The intruder fabricates a membership proof for *their own* leaf using the
    // honest siblings/positions — but that yields a DIFFERENT root, so it can't
    // match the published one.
    let forged = prove_sender_membership(&intruder, &sibs, &pos).expect("prove");

    let v = MerkleMembershipStarkVerifier;
    let res = v.verify(&root_bytes, &PredicateInput::Sender(&intruder), &forged);
    assert!(
        res.is_err(),
        "unauthorized sender (no path to the published root) must be rejected at the STARK level"
    );
}

#[test]
fn intruder_cannot_reuse_members_proof() {
    // The attacker steals the member's valid proof but presents it under their
    // own identity. The leaf bound in the proof is the member's, not the
    // intruder's, so verification against `Sender(intruder)` fails.
    let member = [0x11u8; 32];
    let (sibs, pos) = witness_for(&member, 3);
    let members_proof = prove_sender_membership(&member, &sibs, &pos).expect("prove");
    let root_bytes = authorized_set_root_bytes(&member, &sibs, &pos);

    let intruder = [0x99u8; 32];
    let v = MerkleMembershipStarkVerifier;
    let res = v.verify(
        &root_bytes,
        &PredicateInput::Sender(&intruder),
        &members_proof,
    );
    assert!(
        res.is_err(),
        "a stolen membership proof must not verify under a different sender identity"
    );
}

#[test]
fn tampered_proof_rejected() {
    let sender = [0x11u8; 32];
    let (sibs, pos) = witness_for(&sender, 3);
    let mut proof = prove_sender_membership(&sender, &sibs, &pos).expect("prove");
    let root_bytes = authorized_set_root_bytes(&sender, &sibs, &pos);

    // Flip a byte in the serialized proof.
    proof[16] ^= 0xFF;

    let v = MerkleMembershipStarkVerifier;
    let res = v.verify(&root_bytes, &PredicateInput::Sender(&sender), &proof);
    assert!(res.is_err(), "tampered membership proof must be rejected");
}

#[test]
fn verifier_kind_is_merkle_membership() {
    let v = MerkleMembershipStarkVerifier;
    assert_eq!(v.kind(), WitnessedPredicateKind::MerkleMembership);
}

// --- Full StateConstraint::SenderAuthorized evaluation path ------------------

fn ctx_sender(sender: [u8; 32]) -> EvalContext {
    EvalContext {
        sender: Some(sender),
        ..Default::default()
    }
}

#[test]
fn sender_authorized_constraint_accepts_member() {
    let sender = [0x11u8; 32];
    let (sibs, pos) = witness_for(&sender, 3);
    let proof = prove_sender_membership(&sender, &sibs, &pos).expect("prove");
    let root_bytes = authorized_set_root_bytes(&sender, &sibs, &pos);

    let registry = registry_with_real_sender_membership();
    let blobs = [WitnessBlobView {
        kind: WitnessKindTag::MerklePath,
        bytes: &proof,
    }];
    let bundle = WitnessBundle {
        blobs: &blobs,
        registry: Some(&registry),
        finalized_roots: None,
    };

    // The cell publishes the root in slot 4.
    let mut state = CellState::new(0);
    state.fields[4] = root_bytes;

    let program = CellProgram::Predicate(vec![StateConstraint::SenderAuthorized {
        set: AuthorizedSet::PublicRoot { set_root_index: 4 },
    }]);
    let ctx = ctx_sender(sender);
    let res = program.evaluate_full(
        &state,
        None,
        Some(&ctx),
        &TransitionMeta::wildcard(),
        &bundle,
    );
    assert!(res.is_ok(), "member must pass SenderAuthorized: {res:?}");
}

#[test]
fn sender_authorized_constraint_rejects_non_member() {
    let member = [0x11u8; 32];
    let (sibs, pos) = witness_for(&member, 3);
    let root_bytes = authorized_set_root_bytes(&member, &sibs, &pos);

    // Intruder forges a proof for their own leaf with the same path shape; the
    // resulting root differs from the published root, so the STARK rejects.
    let intruder = [0x99u8; 32];
    let forged = prove_sender_membership(&intruder, &sibs, &pos).expect("prove");

    let registry = registry_with_real_sender_membership();
    let blobs = [WitnessBlobView {
        kind: WitnessKindTag::MerklePath,
        bytes: &forged,
    }];
    let bundle = WitnessBundle {
        blobs: &blobs,
        registry: Some(&registry),
        finalized_roots: None,
    };

    let mut state = CellState::new(0);
    state.fields[4] = root_bytes;

    let program = CellProgram::Predicate(vec![StateConstraint::SenderAuthorized {
        set: AuthorizedSet::PublicRoot { set_root_index: 4 },
    }]);
    let ctx = ctx_sender(intruder);
    let res = program.evaluate_full(
        &state,
        None,
        Some(&ctx),
        &TransitionMeta::wildcard(),
        &bundle,
    );
    assert!(
        res.is_err(),
        "non-member must be rejected by SenderAuthorized at the circuit level"
    );
}

/// THE SLOT ROUND-TRIP: the committed 32-byte root slot carries the WHOLE 8-felt digest —
/// eight canonical `u32` LE limbs filling all 32 bytes — and reads back lane-for-lane.
///
/// ⚑ This used to assert only that `bytes[0..4]` decoded to the root FELT, with 28 bytes
/// unread. That is the boundary re-narrowing the widening exists to close: a tree of 8-felt
/// nodes whose committed root is projected to 31 bits at the slot buys nothing. The negative
/// half is the non-vacuity: NO high lane may be zero-padded away, and two roots differing in
/// ANY lane must differ in the bytes.
#[test]
fn root_bytes_round_trip_carries_all_eight_lanes() {
    let sender = [0x11u8; 32];
    let (sibs, pos) = witness_for(&sender, 3);
    let digest = authorized_set_root_digest(&sender, &sibs, &pos);
    let bytes = authorized_set_root_bytes(&sender, &sibs, &pos);

    // Every lane round-trips through its own four bytes; the slot is used exactly.
    for (k, felt) in digest.iter().enumerate() {
        let recovered = u32::from_le_bytes([
            bytes[k * 4],
            bytes[k * 4 + 1],
            bytes[k * 4 + 2],
            bytes[k * 4 + 3],
        ]);
        assert_eq!(recovered, felt.as_u32(), "root lane {k} must round-trip");
    }
    // NON-VACUITY: the digest is genuinely eight lanes wide — the retired encoding would have
    // left bytes 4..32 zero, and a lane-0-only root has no eight distinct lanes to carry.
    assert_eq!(digest.len(), DIGEST_W);
    assert!(
        bytes[4..].iter().any(|&b| b != 0),
        "the high 28 bytes must carry root lanes 1..8 — all-zero is the retired one-felt slot"
    );
    // A DIFFERENT authorized set moves the bytes (the slot is not a constant).
    let (other_sibs, other_pos) = witness_for(&[0x99u8; 32], 3);
    assert_ne!(
        bytes,
        authorized_set_root_bytes(&[0x99u8; 32], &other_sibs, &other_pos),
        "a different authorized set must commit different root bytes"
    );
}
