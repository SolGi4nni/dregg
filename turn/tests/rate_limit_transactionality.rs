//! Executor-level adversarial tests for rate-limit consensus state.
//!
//! Rate limits are evaluated once per action, so a call forest must expose a
//! successful earlier action's staged debit to every later action in the same
//! forest.  The debit is committed only when the whole turn commits; a later
//! rejection must leave both the ledger and the counters at their pre-turn
//! state.

use std::collections::HashMap;

use dregg_cell::{
    AuthRequired, Cell, CellId, CellProgram, Ledger, Permissions, StateConstraint,
    program::{TransitionCase, TransitionGuard},
};
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, Turn, TurnExecutor,
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

fn program_cell(seed: u8, constraint: StateConstraint) -> Cell {
    let mut public_key = [0u8; 32];
    public_key[0] = seed;
    public_key[31] = seed.wrapping_mul(37);
    let mut cell = Cell::with_balance(public_key, [0u8; 32], 0);
    cell.permissions = open_permissions();
    cell.program = CellProgram::Predicate(vec![constraint]);
    cell
}

fn set_field_action(target: CellId, index: u64, value: [u8; 32]) -> Action {
    Action {
        target,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![Effect::SetField {
            cell: target,
            index,
            value,
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    }
}

fn turn(agent: CellId, nonce: u64, actions: Vec<Action>) -> Turn {
    let mut forest = CallForest::new();
    for action in actions {
        forest.add_root(action);
    }
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

fn field_u64(value: u64) -> [u8; 32] {
    let mut field = [0u8; 32];
    field[24..].copy_from_slice(&value.to_be_bytes());
    field
}

#[test]
fn count_limit_sees_an_earlier_action_in_the_same_turn() {
    let cell = program_cell(
        1,
        StateConstraint::RateLimit {
            max_per_epoch: 1,
            epoch_duration: 100,
        },
    );
    let cell_id = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let result = executor.execute(
        &turn(
            cell_id,
            0,
            vec![
                set_field_action(cell_id, 0, field_u64(1)),
                set_field_action(cell_id, 1, field_u64(1)),
            ],
        ),
        &mut ledger,
    );

    assert!(
        result.is_rejected(),
        "the second action exceeds max_per_epoch=1 and must reject the whole turn: {result:?}"
    );
    assert_eq!(ledger.get(&cell_id).unwrap().state.fields[0], [0u8; 32]);
    assert_eq!(ledger.get(&cell_id).unwrap().state.fields[1], [0u8; 32]);
    assert!(executor.rate_limit_counters.lock().unwrap().is_empty());
}

#[test]
fn sum_limit_sees_an_earlier_delta_in_the_same_turn() {
    let cell = program_cell(
        2,
        StateConstraint::RateLimitBySum {
            slot_index: 0,
            max_sum_per_epoch: 10,
            epoch_duration: 100,
        },
    );
    let cell_id = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let result = executor.execute(
        &turn(
            cell_id,
            0,
            vec![
                set_field_action(cell_id, 0, field_u64(6)),
                set_field_action(cell_id, 0, field_u64(12)),
            ],
        ),
        &mut ledger,
    );

    assert!(
        result.is_rejected(),
        "the second +6 delta raises the staged window sum to 12 and must reject: {result:?}"
    );
    assert_eq!(ledger.get(&cell_id).unwrap().state.fields[0], [0u8; 32]);
    assert!(executor.rate_limit_sum_counters.lock().unwrap().is_empty());
}

#[test]
fn a_later_failure_does_not_consume_a_rate_limit_debit() {
    let cell = program_cell(
        3,
        StateConstraint::RateLimit {
            max_per_epoch: 2,
            epoch_duration: 100,
        },
    );
    let cell_id = cell.id();
    let sender = *cell.public_key();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let mut invalid = set_field_action(cell_id, 1, field_u64(1));
    invalid.effects.push(Effect::SetField {
        cell: CellId::from_bytes([0xFF; 32]),
        index: 0,
        value: field_u64(1),
    });
    let rejected = executor.execute(
        &turn(
            cell_id,
            0,
            vec![set_field_action(cell_id, 0, field_u64(1)), invalid],
        ),
        &mut ledger,
    );
    assert!(
        rejected.is_rejected(),
        "setup turn must reject: {rejected:?}"
    );
    assert!(executor.rate_limit_counters.lock().unwrap().is_empty());

    let nonce = ledger.get(&cell_id).unwrap().state.nonce();
    let accepted = executor.execute(
        &turn(
            cell_id,
            nonce,
            vec![set_field_action(cell_id, 0, field_u64(2))],
        ),
        &mut ledger,
    );
    assert!(
        accepted.is_committed(),
        "the rejected turn must not consume the next action's debit: {accepted:?}"
    );
    assert_eq!(
        executor
            .rate_limit_counters
            .lock()
            .unwrap()
            .get(&(cell_id, sender, 0)),
        Some(&1)
    );
}

#[test]
fn cases_program_rate_limit_is_not_a_counter_bypass() {
    let mut cell = program_cell(
        4,
        StateConstraint::RateLimit {
            max_per_epoch: 99,
            epoch_duration: 100,
        },
    );
    cell.program = CellProgram::Cases(vec![TransitionCase {
        guard: TransitionGuard::Always,
        constraints: vec![StateConstraint::RateLimit {
            max_per_epoch: 1,
            epoch_duration: 100,
        }],
    }]);
    let cell_id = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let result = executor.execute(
        &turn(
            cell_id,
            0,
            vec![
                set_field_action(cell_id, 0, field_u64(1)),
                set_field_action(cell_id, 1, field_u64(1)),
            ],
        ),
        &mut ledger,
    );

    assert!(
        result.is_rejected(),
        "operation-scoped Cases must use the same authoritative staged counter: {result:?}"
    );
    assert!(executor.rate_limit_counters.lock().unwrap().is_empty());
}

#[test]
fn ambiguous_multiple_active_rate_windows_fail_closed() {
    let mut cell = program_cell(
        5,
        StateConstraint::RateLimit {
            max_per_epoch: 10,
            epoch_duration: 100,
        },
    );
    cell.program = CellProgram::Predicate(vec![
        StateConstraint::RateLimit {
            max_per_epoch: 10,
            epoch_duration: 100,
        },
        StateConstraint::RateLimit {
            max_per_epoch: 100,
            epoch_duration: 1_000,
        },
    ]);
    let cell_id = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let result = executor.execute(
        &turn(cell_id, 0, vec![set_field_action(cell_id, 0, field_u64(1))]),
        &mut ledger,
    );

    assert!(
        result.is_rejected(),
        "one scalar context cannot soundly represent two keyed windows: {result:?}"
    );
    assert!(executor.rate_limit_counters.lock().unwrap().is_empty());
}

#[test]
fn sum_limit_preserves_the_full_u64_prior() {
    let max = u64::from(u32::MAX) + 50;
    let cell = program_cell(
        6,
        StateConstraint::RateLimitBySum {
            slot_index: 0,
            max_sum_per_epoch: max,
            epoch_duration: 100,
        },
    );
    let cell_id = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero());
    executor
        .rate_limit_sum_counters
        .lock()
        .unwrap()
        .insert((cell_id, 0, 0), max + 1);
    let result = executor.execute(
        &turn(cell_id, 0, vec![set_field_action(cell_id, 0, field_u64(0))]),
        &mut ledger,
    );

    assert!(
        result.is_rejected(),
        "a prior above 2^32 must not be truncated below a u64 ceiling: {result:?}"
    );
    assert_eq!(
        executor
            .rate_limit_sum_counters
            .lock()
            .unwrap()
            .get(&(cell_id, 0, 0)),
        Some(&(max + 1))
    );
}
