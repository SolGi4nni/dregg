//! End-to-end teeth for the LARGE COUNCIL — an arbitrary-N M-of-N proposal cell
//! whose member approvals live in the cell's EXECUTOR-REACHABLE user-field MAP
//! (`_RECORD-LAYER-UPGRADE.md`'s `fields_root`/`fields_map`) instead of the
//! fixed 16 register slots, on the REAL `TurnExecutor`.
//!
//! This is the record-layer upgrade's beachhead made end-to-end: the plain
//! `council` is hard-capped at `MAX_MEMBERS = 3` (its approval bits are fixed
//! slots 3..6); here a council holds **5 members past that cap**, each approval
//! a record at map keys `>= STATE_SLOTS`, and the threshold gate is the proven
//! distinctness-enforced `MOfNDistinct` over the map (`StateConstraint::
//! FieldsCollectionAggregate`). Every safety property is enforced by the cell
//! program the executor re-evaluates on every touching turn — NOT by SDK-side
//! checks: the negative tests hand the executor a well-signed, well-formed turn
//! and assert the EXECUTOR rejects it with `TurnError::ProgramViolation`.
//!
//! What is proven (both polarities):
//! * a 5-member, M-of-3 council with all approvals in the MAP commits its full
//!   lifecycle through the executor (propose → 3 distinct approvals → certify →
//!   execute), and the receipt's `post_state_hash` (which folds `fields_root`)
//!   binds the map-borne approvals;
//! * sub-quorum certification (2 distinct approvals) is REJECTED by the executor
//!   (the dynamic-N quorum gate bites on the flag-arming turn);
//! * a DUPLICATE-PADDED forge (one member's approval written under three map
//!   slots) is REJECTED — distinctness, not raw count, is load-bearing;
//! * ANTI-GHOST: tampering a 17th-field (map) approval flips the cell's
//!   canonical state commitment (the receipt binds the map, byte-for-byte).

use dregg_cell::program::field_from_u64;
use dregg_cell::{CellId, CellProgram};
use dregg_sdk::{AgentCipherclerk, AgentRuntime, Effect, SdkError};
use dregg_turn::{TurnError, TurnReceipt};
use starbridge_polis::STATE_SLOT;
use starbridge_polis::council::{
    APPROVED_FLAG_SLOT, MEMBERS_COMMIT_SLOT, PROPOSAL_HASH_SLOT, STATE_APPROVED, STATE_EXECUTED,
    STATE_PROPOSED,
};
use starbridge_polis::large_council::{
    LargeCouncilCharter, MEMBER_OFF, VOTE_OFF, large_council_cell_program,
};

// =============================================================================
// Harness — the agent's OWN cell becomes the large-council proposal cell, so
// every turn is a self-signed `execute` against it (no factory/adopt ceremony;
// the focus is the executor's per-cell program gate over the map).
// =============================================================================

/// A runtime whose agent cell carries the large-council program, plus the
/// charter. `members` are field-element identities (the distinctness keys).
fn harness(domain: &str, members: usize, threshold: u64) -> (AgentRuntime, CellId, LargeCouncilCharter) {
    let runtime = AgentRuntime::new_simple(AgentCipherclerk::new(), domain);
    let cell = runtime.cell_id();
    // Member identities: distinct nonzero field elements (1..=members).
    let charter = LargeCouncilCharter::new(
        (1..=members as u64).map(field_from_u64).collect(),
        threshold,
    );
    let program = large_council_cell_program(&charter).expect("valid large charter");
    // Install the full two-case program directly on the agent's own cell.
    install_program(&runtime, cell, program);
    (runtime, cell, charter)
}

fn install_program(runtime: &AgentRuntime, cell: CellId, program: CellProgram) {
    let mut ledger = runtime.ledger().lock().unwrap();
    let c = ledger.get_mut(&cell).expect("agent cell exists");
    c.program = program;
}

fn assert_program_violation(result: Result<TurnReceipt, SdkError>, what: &str) {
    match result {
        Err(SdkError::Turn(TurnError::ProgramViolation { .. })) => {}
        Err(other) => panic!("{what}: expected ProgramViolation, got {other:?}"),
        Ok(_) => panic!("{what}: expected the EXECUTOR to reject, but the turn committed"),
    }
}

/// Read a fixed register slot (0..16).
fn slot_of(runtime: &AgentRuntime, cell: CellId, slot: u8) -> [u8; 32] {
    runtime
        .ledger()
        .lock()
        .unwrap()
        .get(&cell)
        .expect("cell exists")
        .state
        .fields[slot as usize]
}

/// Read a map field (key >= 16) through the committed-map accessor.
fn map_field(runtime: &AgentRuntime, cell: CellId, key: u64) -> Option<[u8; 32]> {
    runtime
        .ledger()
        .lock()
        .unwrap()
        .get(&cell)
        .expect("cell exists")
        .state
        .get_field_ext(key)
}

/// The cell's canonical state commitment — the value the receipt's
/// `post_state_hash` carries (folds `fields_root`, so it binds the map).
fn state_commitment(runtime: &AgentRuntime, cell: CellId) -> [u8; 32] {
    let ledger = runtime.ledger().lock().unwrap();
    let c = ledger.get(&cell).expect("cell exists");
    dregg_cell::compute_canonical_state_commitment(c)
}

/// A `SetField` turn writing one map (or slot) key.
fn set_field(cell: CellId, key: u64, value: [u8; 32]) -> Vec<Effect> {
    vec![Effect::SetField {
        cell,
        index: key as usize,
        value,
    }]
}

/// Member `i` casts an approval (vote = 1) by writing their `(member_id, vote)`
/// element into the MAP (keys >= STATE_SLOTS). Two effects in one turn.
fn cast_approval(cell: CellId, charter: &LargeCouncilCharter, i: usize) -> Vec<Effect> {
    vec![
        Effect::SetField {
            cell,
            index: charter.member_id_key(i) as usize,
            value: charter.members[i],
        },
        Effect::SetField {
            cell,
            index: charter.member_vote_key(i) as usize,
            value: field_from_u64(1),
        },
    ]
}

/// Propose: stage the action hash, publish the membership commitment, step
/// DRAFT → PROPOSED — all in one turn (so `pin_term(MEMBERS_COMMIT)` is
/// satisfied as the cell leaves its birth state).
fn propose(cell: CellId, charter: &LargeCouncilCharter, action_hash: [u8; 32]) -> Vec<Effect> {
    vec![
        Effect::SetField {
            cell,
            index: PROPOSAL_HASH_SLOT as usize,
            value: action_hash,
        },
        Effect::SetField {
            cell,
            index: MEMBERS_COMMIT_SLOT as usize,
            value: charter.members_commitment(),
        },
        Effect::SetField {
            cell,
            index: STATE_SLOT as usize,
            value: field_from_u64(STATE_PROPOSED),
        },
    ]
}

/// Certify: arm the approved flag (0→1) and step PROPOSED → APPROVED in one
/// turn. The flag change fires the dynamic-N quorum gate (`SlotChanged`
/// case), so this commits ONLY when the distinct-M quorum is met in the map.
fn certify(cell: CellId) -> Vec<Effect> {
    vec![
        Effect::SetField {
            cell,
            index: APPROVED_FLAG_SLOT as usize,
            value: field_from_u64(1),
        },
        Effect::SetField {
            cell,
            index: STATE_SLOT as usize,
            value: field_from_u64(STATE_APPROVED),
        },
    ]
}

// =============================================================================
// Tests
// =============================================================================

/// THE BEACHHEAD: a 5-member, M-of-3 council whose member approvals live wholly
/// in the user-field MAP commits its full lifecycle through the REAL executor,
/// and the receipt binds the map-borne approvals.
#[test]
fn large_council_5_members_3of5_full_lifecycle_through_executor() {
    let (runtime, cell, charter) = harness("polis-large-council-happy", 5, 3);

    // Propose — DRAFT → PROPOSED, publish the membership commitment.
    let action_hash = *blake3::hash(b"fund the commons 500").as_bytes();
    runtime
        .execute(propose(cell, &charter, action_hash))
        .expect("propose must commit");
    assert_eq!(
        slot_of(&runtime, cell, STATE_SLOT),
        field_from_u64(STATE_PROPOSED),
        "cell is PROPOSED"
    );

    // Three DISTINCT members cast approvals into the MAP (keys >= STATE_SLOTS).
    for i in 0..3 {
        runtime
            .execute(cast_approval(cell, &charter, i))
            .unwrap_or_else(|e| panic!("member {i} approval must commit: {e:?}"));
        // The approval is genuinely in the committed map.
        assert_eq!(
            map_field(&runtime, cell, charter.member_id_key(i)),
            Some(charter.members[i]),
            "member {i} identity committed in the map"
        );
        assert_eq!(
            map_field(&runtime, cell, charter.member_vote_key(i)),
            Some(field_from_u64(1)),
            "member {i} YES vote committed in the map"
        );
    }

    // Certify — the dynamic-N quorum gate sees 3 distinct YES in the map ⇒ the
    // flag-arming turn COMMITS. The receipt's post_state_hash binds the map.
    let receipt = runtime.execute(certify(cell)).expect("certify must commit (3 >= 3)");
    assert_eq!(
        slot_of(&runtime, cell, STATE_SLOT),
        field_from_u64(STATE_APPROVED),
        "cell is APPROVED"
    );
    // The receipt attests the post-state the executor committed — which folds
    // `fields_root` over the map-borne approvals.
    assert_eq!(
        receipt.post_state_hash,
        state_commitment(&runtime, cell),
        "the receipt's post_state_hash is the canonical commitment (binds the map)"
    );

    // Execute — APPROVED → EXECUTED (terminal). Closes the lifecycle.
    runtime
        .execute(vec![Effect::SetField {
            cell,
            index: STATE_SLOT as usize,
            value: field_from_u64(STATE_EXECUTED),
        }])
        .expect("execute must commit");
    assert_eq!(
        slot_of(&runtime, cell, STATE_SLOT),
        field_from_u64(STATE_EXECUTED),
        "cell is EXECUTED"
    );
}

/// SUB-QUORUM TOOTH: with only 2 distinct approvals in the map, the executor
/// REJECTS certification (the dynamic-N quorum gate bites on the flag-arming
/// turn). The cell stays PROPOSED.
#[test]
fn large_council_subquorum_certify_rejected_by_executor() {
    let (runtime, cell, charter) = harness("polis-large-council-subquorum", 5, 3);
    runtime
        .execute(propose(cell, &charter, *blake3::hash(b"act").as_bytes()))
        .expect("propose");

    // Only TWO distinct members approve.
    runtime.execute(cast_approval(cell, &charter, 0)).expect("approve 0");
    runtime.execute(cast_approval(cell, &charter, 1)).expect("approve 1");

    // Certify with 2 < 3 distinct ⇒ the EXECUTOR rejects.
    assert_program_violation(runtime.execute(certify(cell)), "sub-quorum certify");
    assert_eq!(
        slot_of(&runtime, cell, STATE_SLOT),
        field_from_u64(STATE_PROPOSED),
        "the cell stays PROPOSED after the rejected certification"
    );

    // The third distinct approval then lets certification commit.
    runtime.execute(cast_approval(cell, &charter, 2)).expect("approve 2");
    runtime.execute(certify(cell)).expect("certify commits at 3 distinct");
    assert_eq!(
        slot_of(&runtime, cell, STATE_SLOT),
        field_from_u64(STATE_APPROVED),
        "the cell is APPROVED once the quorum is met"
    );
}

/// DUPLICATE-PADDED FORGE TOOTH: one member's approval written under THREE
/// distinct map slots raises the raw count to 3 but is ONE distinct identity;
/// the executor REJECTS certification. Distinctness — not raw count — is the
/// load-bearing gate (the `mOfNDistinct` keystone, now over the map).
#[test]
fn large_council_duplicate_padded_forge_rejected_by_executor() {
    let (runtime, cell, charter) = harness("polis-large-council-dupforge", 5, 3);
    runtime
        .execute(propose(cell, &charter, *blake3::hash(b"act").as_bytes()))
        .expect("propose");

    // Write member 0's identity + a YES vote into THREE element slots (0,1,2) —
    // raw satisfying-count 3, but ONE distinct identity.
    let forged_id = charter.members[0];
    for elem in 0..3u64 {
        let base = (starbridge_polis::large_council::APPROVAL_BASE)
            + elem * (starbridge_polis::large_council::STRIDE as u64);
        runtime
            .execute(set_field(cell, base + MEMBER_OFF as u64, forged_id))
            .expect("write forged identity");
        runtime
            .execute(set_field(cell, base + VOTE_OFF as u64, field_from_u64(1)))
            .expect("write forged vote");
    }

    // The duplicate-padded forge has raw count 3 but 1 distinct ⇒ REJECTED.
    assert_program_violation(
        runtime.execute(certify(cell)),
        "duplicate-padded forge certify",
    );
    assert_eq!(
        slot_of(&runtime, cell, STATE_SLOT),
        field_from_u64(STATE_PROPOSED),
        "the forged council stays PROPOSED",
    );
}

/// ANTI-GHOST TOOTH: a map (17th-field) approval is bound BYTE-FOR-BYTE by the
/// cell's canonical state commitment (which the receipt carries as
/// `post_state_hash`). Tampering ANY committed map approval flips the
/// commitment — the receipt cannot be reused for a tampered map.
#[test]
fn large_council_map_approval_is_bound_by_the_commitment_anti_ghost() {
    let (runtime, cell, charter) = harness("polis-large-council-antighost", 5, 3);
    runtime
        .execute(propose(cell, &charter, *blake3::hash(b"act").as_bytes()))
        .expect("propose");
    for i in 0..3 {
        runtime.execute(cast_approval(cell, &charter, i)).expect("approve");
    }
    let committed = runtime.execute(certify(cell)).expect("certify");
    let bound = committed.post_state_hash;
    assert_eq!(
        bound,
        state_commitment(&runtime, cell),
        "the receipt binds the committed (map-bearing) post-state"
    );

    // Now TAMPER a committed map approval directly in the ledger (a malicious
    // re-write of member 2's vote to a different value).
    {
        let mut ledger = runtime.ledger().lock().unwrap();
        let c = ledger.get_mut(&cell).expect("cell");
        assert!(c.state.set_field_ext(charter.member_vote_key(2), field_from_u64(7)));
    }
    let tampered = state_commitment(&runtime, cell);
    assert_ne!(
        bound, tampered,
        "tampering a 17th-field (map) approval MUST flip the canonical commitment \
         — the receipt's post_state_hash genuinely binds the map (anti-ghost)"
    );

    // And dropping the approval entirely also flips it (distinct maps ⇒ distinct
    // roots — the fields_root injectivity).
    {
        let mut ledger = runtime.ledger().lock().unwrap();
        let c = ledger.get_mut(&cell).expect("cell");
        c.state.fields_map.remove(&charter.member_vote_key(2));
        c.state.reseal_fields_root();
    }
    let dropped = state_commitment(&runtime, cell);
    assert_ne!(bound, dropped, "dropping a map approval flips the commitment too");
    assert_ne!(tampered, dropped, "tamper and drop are distinct commitments");
}
