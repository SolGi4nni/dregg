//! End-to-end teeth for the DISTINCT-COMMITTEE GOVERNANCE BOARD — a
//! governed-namespace cell whose committee votes live in the cell's
//! EXECUTOR-REACHABLE user-field MAP (`_RECORD-LAYER-UPGRADE.md`'s
//! `fields_root`/`fields_map`, keys `>= STATE_SLOTS`) instead of the 16 fixed
//! register slots, driven through the REAL `EmbeddedExecutor`.
//!
//! This is the SECOND maxed-out governance app on the record-layer upgrade
//! (the first is `sdk/tests/polis_large_council_e2e.rs`). The base
//! governed-namespace folds its committee votes into ONE register slot
//! (`PENDING_PROPOSAL_ROOT_SLOT`, a rolling BLAKE3 chain) — legible, but NOT a
//! distinctness-enforced count, and a committee larger than three cannot keep
//! one approval bit per member in the fixed slots. Here a committee of **5
//! members past that cap** casts its votes as records at map keys
//! `>= STATE_SLOTS` (well past the 8th/16th field), and the route-table-swap
//! gate is the proven distinctness-enforced `MOfNDistinct` over the map
//! (`StateConstraint::FieldsCollectionAggregate`, reused verbatim from the
//! polis large-council keystone). Every safety property is enforced by the cell
//! program the executor re-evaluates on every touching turn — the negative
//! tests hand the executor a well-signed, well-formed turn and assert it
//! REJECTS.
//!
//! What is proven (both polarities):
//! * a 5-member, 3-of-5 committee with all votes in the MAP commits the
//!   route-table swap through the executor (5 votes cast as map records → swap
//!   the table + bump version → the quorum gate sees ≥ 3 distinct approvers),
//!   and the receipt's `post_state_hash` (which folds `fields_root`) binds the
//!   map-borne votes;
//! * a sub-quorum swap (2 distinct votes) is REJECTED by the executor (the
//!   dynamic-N quorum gate bites on the version-bump turn);
//! * a DUPLICATE-PADDED forge (one member's vote written under three map slots)
//!   is REJECTED — distinctness, not raw count, is load-bearing;
//! * ANTI-GHOST: tampering a 17th-field (map) vote flips the cell's canonical
//!   state commitment (the receipt binds the map, byte-for-byte) — and tampering
//!   a 9th+ committed field cannot be reused under the bound receipt.

use dregg_app_framework::{AgentCipherclerk, AppCipherclerk, CellId, EmbeddedExecutor};
use dregg_cell::permissions::{AuthRequired, Permissions};
use dregg_cell::program::field_from_u64;
use dregg_cell::state::CellState;
use dregg_dfa::RouteTarget;
use starbridge_governed_namespace::committee_board::{
    MEMBER_OFF, VOTE_BASE, VOTE_OFF, VOTE_STRIDE, build_committee_commit_action,
    cast_committee_vote_effects, committee_board_program, member_id_key, member_vote_key,
};
use starbridge_governed_namespace::{
    DISPUTE_WINDOW_HEIGHT_SLOT, GOVERNANCE_COMMITTEE_ROOT_SLOT, PENDING_PROPOSAL_ROOT_SLOT,
    ROUTE_TABLE_ROOT_SLOT, THRESHOLD_SLOT, VERSION_SLOT, blake3_field, build_route_table,
    route_table_commitment, u64_field,
};

// =============================================================================
// Harness — the agent's OWN cell becomes the governance board, so every turn is
// a self-signed turn against it (the focus is the executor's per-cell program
// gate over the map, exactly as the polis large-council harness does).
// =============================================================================

const THRESHOLD: u64 = 3;
const MEMBERS: usize = 5;

fn make_cipherclerk(seed: u8) -> AppCipherclerk {
    AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32])
}

/// Stand up an executor whose agent cell IS the committee governance board: the
/// full two-case [`committee_board_program`] installed, the constitutional
/// fixed slots seeded (committee root, threshold, version=0, empty table), and
/// relaxed permissions so the self-signed turns commit. Returns the board cell.
fn seed_board(executor: &EmbeddedExecutor) -> CellId {
    let cell_id = executor.cell_id();
    let program = committee_board_program(THRESHOLD);
    executor.install_program(cell_id, program.clone());

    executor.with_ledger_mut(|ledger| {
        let cell = ledger.get_mut(&cell_id).expect("board cell exists");
        cell.program = program;
        cell.permissions = Permissions {
            send: AuthRequired::None,
            receive: AuthRequired::None,
            set_state: AuthRequired::None,
            set_permissions: AuthRequired::None,
            set_verification_key: AuthRequired::None,
            increment_nonce: AuthRequired::None,
            delegate: AuthRequired::None,
            access: AuthRequired::None,
        };
        let mut state = CellState::new(10_000_000);
        state.fields[ROUTE_TABLE_ROOT_SLOT as usize] = blake3_field(b"empty-table");
        state.fields[VERSION_SLOT as usize] = u64_field(0);
        state.fields[GOVERNANCE_COMMITTEE_ROOT_SLOT as usize] = blake3_field(b"committee-of-5");
        state.fields[THRESHOLD_SLOT as usize] = u64_field(THRESHOLD);
        state.fields[DISPUTE_WINDOW_HEIGHT_SLOT as usize] = u64_field(0);
        state.fields[PENDING_PROPOSAL_ROOT_SLOT as usize] = [0u8; 32];
        cell.state = state;
    });
    cell_id
}

/// The committee member identities (the distinctness keys): distinct nonzero
/// field elements `1..=MEMBERS`.
fn member_id(i: usize) -> [u8; 32] {
    field_from_u64((i + 1) as u64)
}

/// Cast committee member `i`'s APPROVE vote into the MAP (one self-signed turn:
/// two `SetField` effects writing `{member_id, vote=1}`).
fn cast_vote(executor: &EmbeddedExecutor, cipherclerk: &AppCipherclerk, board: CellId, i: usize) {
    let effects = cast_committee_vote_effects(board, i, member_id(i));
    let action = cipherclerk.make_action(board, "cast_committee_vote", effects);
    executor
        .submit_action(cipherclerk, action)
        .unwrap_or_else(|e| panic!("member {i} vote must commit: {e}"));
}

/// The new route table the swap installs.
fn target_table() -> dregg_dfa::RouteTable {
    build_route_table(&[
        ("/public/*", RouteTarget::handler("public")),
        ("/treasury/*", RouteTarget::handler("treasury")),
    ])
}

/// Read a map field through the committed-map accessor.
fn map_field(executor: &EmbeddedExecutor, board: CellId, key: u64) -> Option<[u8; 32]> {
    executor
        .cell_state(board)
        .and_then(|s| s.get_field_ext(key))
}

/// The board cell's canonical state commitment — the value the receipt's
/// `post_state_hash` carries (folds `fields_root`, so it binds the map).
fn state_commitment(executor: &EmbeddedExecutor, board: CellId) -> [u8; 32] {
    executor.with_ledger_mut(|ledger| {
        let cell = ledger.get(&board).expect("board cell");
        dregg_cell::compute_canonical_state_commitment(cell)
    })
}

fn assert_rejected(result: Result<dregg_turn::TurnReceipt, impl std::fmt::Display>, what: &str) {
    match result {
        Ok(_) => panic!("{what}: expected the EXECUTOR to reject, but the turn committed"),
        Err(e) => {
            let msg = e.to_string().to_lowercase();
            assert!(
                msg.contains("program")
                    || msg.contains("constraint")
                    || msg.contains("fieldscollectionaggregate")
                    || msg.contains("aggregate")
                    || msg.contains("refuse")
                    || msg.contains("quorum"),
                "{what}: rejection must cite the program/quorum gate, got: {msg}"
            );
        }
    }
}

// =============================================================================
// Tests
// =============================================================================

/// THE BEACHHEAD: a 5-member, 3-of-5 committee whose votes live wholly in the
/// user-field MAP commits the route-table swap through the REAL executor, and
/// the receipt binds the map-borne votes.
#[test]
fn committee_board_5_members_3of5_swaps_table_through_executor() {
    let cipherclerk = make_cipherclerk(0x01);
    let executor = EmbeddedExecutor::new(&cipherclerk, "default");
    let board = seed_board(&executor);

    // All five committee members cast APPROVE into the MAP (keys >= STATE_SLOTS).
    // These keys are well past the 8th/16th fixed field — this is the >8-field
    // end-to-end path.
    assert!(
        VOTE_BASE >= dregg_cell::state::STATE_SLOTS as u64,
        "the vote-board lives in the map tail (key >= STATE_SLOTS)"
    );
    for i in 0..MEMBERS {
        cast_vote(&executor, &cipherclerk, board, i);
        // The vote is genuinely in the committed map.
        assert_eq!(
            map_field(&executor, board, member_id_key(i)),
            Some(member_id(i)),
            "member {i} identity committed in the map"
        );
        assert_eq!(
            map_field(&executor, board, member_vote_key(i)),
            Some(field_from_u64(1)),
            "member {i} APPROVE committed in the map"
        );
    }
    // The highest committed map key is past 16 (5 members × stride 2 + base 16).
    assert!(
        member_vote_key(MEMBERS - 1) > 16,
        "the committee uses MORE than the 8/16 fixed fields (key {} > 16)",
        member_vote_key(MEMBERS - 1)
    );

    // Commit the swap — bumping `version` 0->1 fires the dynamic-N quorum gate,
    // which sees 5 >= 3 distinct approvers in the map ⇒ the swap COMMITS.
    let table = target_table();
    let commit = build_committee_commit_action(&cipherclerk, board, &table, 1);
    let receipt = executor
        .submit_action(&cipherclerk, commit)
        .expect("commit must swap the table (5 distinct >= 3)");

    // The route table swapped and the version bumped.
    let post = executor.cell_state(board).expect("board state");
    assert_eq!(
        post.fields[ROUTE_TABLE_ROOT_SLOT as usize],
        route_table_commitment(&table),
        "route_table_root swapped to the new table"
    );
    assert_eq!(
        post.fields[VERSION_SLOT as usize],
        u64_field(1),
        "version bumped to 1"
    );

    // The receipt attests the post-state the executor committed — which folds
    // `fields_root` over the map-borne committee votes.
    assert_eq!(
        receipt.post_state_hash,
        state_commitment(&executor, board),
        "the receipt's post_state_hash is the canonical commitment (binds the map)"
    );
}

/// SUB-QUORUM TOOTH: with only 2 distinct votes in the map, the executor
/// REJECTS the swap (the dynamic-N quorum gate bites on the version-bump turn).
/// The board's table + version stay put.
#[test]
fn committee_board_subquorum_swap_rejected_by_executor() {
    let cipherclerk = make_cipherclerk(0x02);
    let executor = EmbeddedExecutor::new(&cipherclerk, "default");
    let board = seed_board(&executor);

    // Only TWO distinct committee members vote.
    cast_vote(&executor, &cipherclerk, board, 0);
    cast_vote(&executor, &cipherclerk, board, 1);

    // Swap with 2 < 3 distinct ⇒ the EXECUTOR rejects.
    let table = target_table();
    let commit = build_committee_commit_action(&cipherclerk, board, &table, 1);
    assert_rejected(
        executor.submit_action(&cipherclerk, commit),
        "sub-quorum swap",
    );

    // The board is unchanged.
    let post = executor.cell_state(board).expect("board state");
    assert_eq!(
        post.fields[VERSION_SLOT as usize],
        u64_field(0),
        "version stays 0 after the rejected swap"
    );
    assert_eq!(
        post.fields[ROUTE_TABLE_ROOT_SLOT as usize],
        blake3_field(b"empty-table"),
        "route_table_root unchanged after the rejected swap"
    );

    // The third distinct vote then lets the swap commit.
    cast_vote(&executor, &cipherclerk, board, 2);
    let commit2 = build_committee_commit_action(&cipherclerk, board, &table, 1);
    executor
        .submit_action(&cipherclerk, commit2)
        .expect("swap commits at 3 distinct");
    let post2 = executor.cell_state(board).expect("board state");
    assert_eq!(
        post2.fields[VERSION_SLOT as usize],
        u64_field(1),
        "version bumps to 1 once the quorum is met"
    );
}

/// DUPLICATE-PADDED FORGE TOOTH: one member's vote written under THREE distinct
/// map slots raises the raw count to 3 but is ONE distinct identity; the
/// executor REJECTS the swap. Distinctness — not raw count — is the load-bearing
/// gate (the `mOfNDistinct` keystone, now over the governance committee's map).
#[test]
fn committee_board_duplicate_padded_forge_rejected_by_executor() {
    let cipherclerk = make_cipherclerk(0x03);
    let executor = EmbeddedExecutor::new(&cipherclerk, "default");
    let board = seed_board(&executor);

    // Write member 0's identity + an APPROVE vote into THREE element slots
    // (0,1,2) — raw satisfying-count 3, but ONE distinct identity.
    let forged_id = member_id(0);
    for elem in 0..3usize {
        let id_key = VOTE_BASE + (elem as u64) * (VOTE_STRIDE as u64) + MEMBER_OFF as u64;
        let vote_key = VOTE_BASE + (elem as u64) * (VOTE_STRIDE as u64) + VOTE_OFF as u64;
        let effects = vec![
            dregg_app_framework::Effect::SetField {
                cell: board,
                index: id_key as u64,
                value: forged_id,
            },
            dregg_app_framework::Effect::SetField {
                cell: board,
                index: vote_key as u64,
                value: field_from_u64(1),
            },
        ];
        let action = cipherclerk.make_action(board, "cast_committee_vote", effects);
        executor
            .submit_action(&cipherclerk, action)
            .expect("writing a forged vote record is itself allowed (invariants case)");
    }

    // The duplicate-padded forge has raw count 3 but 1 distinct ⇒ REJECTED.
    let table = target_table();
    let commit = build_committee_commit_action(&cipherclerk, board, &table, 1);
    assert_rejected(
        executor.submit_action(&cipherclerk, commit),
        "duplicate-padded forge swap",
    );
    let post = executor.cell_state(board).expect("board state");
    assert_eq!(
        post.fields[VERSION_SLOT as usize],
        u64_field(0),
        "the forged committee cannot swap the table",
    );
}

/// ANTI-GHOST TOOTH: a map (17th-field) committee vote is bound BYTE-FOR-BYTE by
/// the cell's canonical state commitment (which the receipt carries as
/// `post_state_hash`). Tampering ANY committed map vote flips the commitment —
/// the receipt cannot be reused for a tampered map.
#[test]
fn committee_board_map_vote_is_bound_by_the_commitment_anti_ghost() {
    let cipherclerk = make_cipherclerk(0x04);
    let executor = EmbeddedExecutor::new(&cipherclerk, "default");
    let board = seed_board(&executor);

    for i in 0..MEMBERS {
        cast_vote(&executor, &cipherclerk, board, i);
    }
    let table = target_table();
    let commit = build_committee_commit_action(&cipherclerk, board, &table, 1);
    let committed = executor
        .submit_action(&cipherclerk, commit)
        .expect("swap commits");
    let bound = committed.post_state_hash;
    assert_eq!(
        bound,
        state_commitment(&executor, board),
        "the receipt binds the committed (map-bearing) post-state"
    );

    // The tampered key is a 9th+ field (key 25 = member 4's vote, well past the
    // 8th/16th fixed field). Tamper member 4's committed vote directly in the
    // ledger (a malicious re-write to a different value).
    let tamper_key = member_vote_key(MEMBERS - 1);
    assert!(
        tamper_key > 16,
        "tampering a >16 (map) field, key {tamper_key}"
    );
    executor.with_ledger_mut(|ledger| {
        let cell = ledger.get_mut(&board).expect("board cell");
        assert!(cell.state.set_field_ext(tamper_key, field_from_u64(7)));
    });
    let tampered = state_commitment(&executor, board);
    assert_ne!(
        bound, tampered,
        "tampering a 17th-field (map) committee vote MUST flip the canonical commitment \
         — the receipt's post_state_hash genuinely binds the map (anti-ghost)"
    );

    // Dropping the vote entirely also flips it (distinct maps ⇒ distinct roots —
    // the fields_root injectivity).
    executor.with_ledger_mut(|ledger| {
        let cell = ledger.get_mut(&board).expect("board cell");
        cell.state.fields_map.remove(&tamper_key);
        cell.state.reseal_fields_root();
    });
    let dropped = state_commitment(&executor, board);
    assert_ne!(
        bound, dropped,
        "dropping a map vote flips the commitment too"
    );
    assert_ne!(
        tampered, dropped,
        "tamper and drop are distinct commitments"
    );
}
