//! `execute_pipeline` is the ONE pipeline entry, and it honors both of the properties
//! that used to be split across two.
//!
//! Until 2026-08-05 there were two near-identical batch executors:
//!
//! * `execute_pipeline` — the live one (used by `Script::run` and every test). It verified
//!   each turn's `depends_on` hashes against the set committed within the batch, and it
//!   **ignored `Pipeline::atomic` entirely**.
//! * `execute_pipeline_result` — **zero callers**. It honored `atomic` (snapshot the
//!   ledger, restore on any failure) and **omitted the `depends_on` verification**.
//!
//! So the flag `PipelineBuilder::atomic()` set was a no-op on every path anything called,
//! and the only function that implemented it silently dropped a check. Nothing in the tree
//! ever exercised `atomic` — the grep for `.atomic()` / `atomic: true` outside
//! `std::sync::atomic` returned nothing. The dead variant is deleted and both properties
//! live in the one entry; these tests are what makes that claim falsifiable.

use std::collections::HashMap;

use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, Pipeline,
    PipelineError, TurnExecutor, execute_pipeline, turn::Turn,
};

fn open_permissions() -> Permissions {
    Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

fn make_open_cell(seed: u8, balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37);
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell
}

fn turn_for(agent: CellId, nonce: u64, effects: Vec<Effect>) -> Turn {
    let mut forest = CallForest::new();
    forest.add_root(Action {
        target: agent,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects,
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    });
    Turn {
        agent,
        nonce,
        call_forest: forest,
        fee: 0,
        memo: None,
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    }
}

/// Two independent agents; the second turn is unexecutable (its agent does not exist), so
/// the batch has exactly one committing turn and one failing turn.
fn one_good_one_doomed() -> (Ledger, TurnExecutor, Turn, Turn, CellId) {
    let good = make_open_cell(41, 1_000);
    let good_id = good.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(good).unwrap();
    let executor = TurnExecutor::new(ComputronCosts::zero());

    let ok = turn_for(
        good_id,
        0,
        vec![Effect::SetField {
            cell: good_id,
            index: 0,
            value: [0xAB; 32],
        }],
    );
    // An agent that is not in the ledger: `CellNotFound`, refused before Phase 1.
    let doomed = turn_for(CellId::from_bytes([0x99; 32]), 0, vec![]);
    (ledger, executor, ok, doomed, good_id)
}

/// NON-ATOMIC (the default): a failure does NOT undo what already committed. This is the
/// baseline the atomic case must differ from — without it, the atomic test could pass for
/// the wrong reason.
#[test]
fn a_non_atomic_batch_keeps_what_committed() {
    let (mut ledger, executor, ok, doomed, agent) = one_good_one_doomed();
    let mut pipeline = Pipeline::new();
    pipeline.add_turn(ok);
    pipeline.add_turn(doomed);
    assert!(!pipeline.atomic);

    let results = execute_pipeline(pipeline, &mut ledger, &executor);
    assert!(results[0].is_ok(), "the good turn must commit: {results:?}");
    assert!(results[1].is_err(), "the doomed turn must fail");
    assert_eq!(
        ledger.get(&agent).unwrap().state.fields[0],
        [0xAB; 32],
        "a non-atomic batch leaves the committed write in place"
    );
}

/// ⚑ ATOMIC: the same batch with `atomic` set rolls the committed turn back and reports
/// every turn as failed. Before this landed, `execute_pipeline` ignored the flag entirely,
/// so this test's assertion would have been the non-atomic one above.
#[test]
fn an_atomic_batch_rolls_the_committed_turn_back() {
    let (mut ledger, executor, ok, doomed, agent) = one_good_one_doomed();
    let before = ledger.get(&agent).unwrap().state.fields[0];

    let mut pipeline = Pipeline::new();
    pipeline.add_turn(ok);
    pipeline.add_turn(doomed);
    pipeline.atomic = true;

    let results = execute_pipeline(pipeline, &mut ledger, &executor);
    assert!(
        results.iter().all(|r| r.is_err()),
        "an atomic batch with a failure must report NO successful turn: {results:?}"
    );
    assert_eq!(
        ledger.get(&agent).unwrap().state.fields[0],
        before,
        "the committed turn's write must be rolled back — this is the whole meaning of \
         `Pipeline::atomic`, and nothing honored it before 2026-08-05"
    );
    // The rolled-back turn is reported as such, not as a receipt naming a state that no
    // longer exists.
    assert!(
        matches!(
            &results[0],
            Err(PipelineError::TurnExecutionFailed { index: 0, reason }) if reason == "atomic rollback"
        ),
        "the rolled-back turn must say so: {:?}",
        results[0]
    );
}

/// An all-committing atomic batch is unaffected: the flag costs nothing when nothing fails.
#[test]
fn an_atomic_batch_that_all_commits_is_untouched() {
    let cell = make_open_cell(42, 1_000);
    let agent = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();
    let executor = TurnExecutor::new(ComputronCosts::zero());

    let mut pipeline = Pipeline::new();
    pipeline.add_turn(turn_for(
        agent,
        0,
        vec![Effect::SetField {
            cell: agent,
            index: 0,
            value: [0x11; 32],
        }],
    ));
    pipeline.atomic = true;

    let results = execute_pipeline(pipeline, &mut ledger, &executor);
    assert!(results[0].is_ok(), "the turn must commit: {results:?}");
    assert_eq!(
        ledger.get(&agent).unwrap().state.fields[0],
        [0x11; 32],
        "an atomic batch with no failure commits normally"
    );
}

/// The check the deleted variant dropped: a turn declaring a `depends_on` hash that no
/// turn in the batch committed is REFUSED. Pinned here because the surviving entry is now
/// the only one that carries it.
#[test]
fn an_unmet_depends_on_is_refused() {
    let cell = make_open_cell(43, 1_000);
    let agent = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();
    let executor = TurnExecutor::new(ComputronCosts::zero());

    let mut turn = turn_for(agent, 0, vec![Effect::IncrementNonce { cell: agent }]);
    // A dependency on a turn hash that is in no batch.
    turn.depends_on = vec![[0xDE; 32]];

    let mut pipeline = Pipeline::new();
    pipeline.add_turn(turn);
    let results = execute_pipeline(pipeline, &mut ledger, &executor);

    assert!(
        matches!(
            &results[0],
            Err(PipelineError::MissingDependency {
                turn_index: 0,
                missing_hash,
            }) if *missing_hash == [0xDE; 32]
        ),
        "an unmet depends_on must refuse the turn: {:?}",
        results[0]
    );
    assert_eq!(
        ledger.get(&agent).unwrap().state.nonce(),
        0,
        "the refused turn must not have executed"
    );
}
