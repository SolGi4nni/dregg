//! Regression: `Turn` (and the `Action`s in its call forest) MUST round-trip
//! through postcard.
//!
//! Postcard is a non-self-describing positional format. A
//! `#[serde(skip_serializing_if = "…")]` field is not written when the
//! predicate is true, but the deserializer still reads it positionally —
//! desyncing the byte stream and failing with "Found an Option discriminant
//! that wasn't 0 or 1" (or "expected more data"). That is exactly how the
//! gossip/blocklace finalized-turn path and `/api/turns/submit-signed` broke:
//! every turn with a defaulted optional field (the common case) was
//! undecodable, so turns never replicated.
//!
//! This test pins the fix: no `skip_serializing_if` may reappear on any field
//! that rides inside `Turn` over the wire.

use dregg_turn::action::{Action, Authorization, DelegationMode, Effect, symbol};
use dregg_turn::forest::CallForest;
use dregg_turn::turn::Turn;
use dregg_types::CellId;

fn minimal_action(target: CellId, effects: Vec<Effect>) -> Action {
    Action {
        target,
        method: symbol("submit"),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects,
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    }
}

fn turn_with(effects: Vec<Effect>) -> Turn {
    let agent = CellId::from_bytes([1u8; 32]);
    let mut forest = CallForest::new();
    forest.add_root(minimal_action(agent, effects));
    Turn {
        agent,
        nonce: 3,
        fee: 500,
        memo: Some("wire roundtrip".to_string()),
        valid_until: None,
        call_forest: forest,
        depends_on: vec![],
        previous_receipt_hash: None,
        conservation_proof: None,
        sovereign_witnesses: Default::default(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: vec![],
        cross_effect_dependencies: vec![],
        effect_witness_index_map: vec![],
    }
}

fn assert_roundtrips(turn: &Turn) {
    let bytes = postcard::to_stdvec(turn).expect("postcard serialize");
    let decoded: Turn = postcard::from_bytes(&bytes)
        .expect("postcard MUST round-trip Turn (no skip_serializing_if)");
    // Re-encode the decoded value; a positional desync would also corrupt this.
    let bytes2 = postcard::to_stdvec(&decoded).expect("re-serialize decoded turn");
    assert_eq!(bytes, bytes2, "postcard re-encode must be byte-stable");
    assert_eq!(turn.nonce, decoded.nonce);
    assert_eq!(turn.fee, decoded.fee);
    assert_eq!(turn.memo, decoded.memo);
    assert_eq!(
        turn.call_forest.action_count(),
        decoded.call_forest.action_count()
    );
}

#[test]
fn turn_with_defaulted_optionals_roundtrips() {
    // The common case: every optional/sidecar field at its default. This is the
    // exact shape that previously failed to deserialize.
    assert_roundtrips(&turn_with(vec![]));
}

#[test]
fn turn_with_transfer_effect_roundtrips() {
    let to = CellId::from_bytes([2u8; 32]);
    let from = CellId::from_bytes([1u8; 32]);
    assert_roundtrips(&turn_with(vec![Effect::Transfer {
        from,
        to,
        amount: 100,
    }]));
}

#[test]
fn turn_with_note_create_effect_roundtrips() {
    // NoteCreate carries the previously-skipped `value_commitment` / `range_proof`
    // optionals; exercise them at default (None) to pin the Effect-variant fix.
    use dregg_cell::NoteCommitment;
    assert_roundtrips(&turn_with(vec![Effect::NoteCreate {
        commitment: NoteCommitment([7u8; 32]),
        value: 42,
        asset_type: 0,
        encrypted_note: vec![],
        value_commitment: None,
        range_proof: None,
    }]));
}
