//! `validate_without_apply` must not admit what `execute` refuses.
//!
//! # The divergence these pin (measured 2026-08-05, closed the same day)
//!
//! `TurnExecutor::validate_without_apply` documented itself as returning "the first error
//! that would be encountered" by `execute`. It ran SIX gates: empty forest, expiration,
//! agent existence, agent lifecycle, nonce, fee coverage (plus a cost estimate `execute`
//! does differently). `execute` runs five more before it can commit — the **freeze** gate
//! on the agent and the call-forest write set, the **receipt-chain** self-binding, the
//! **budget slice**, the **sovereign-witness** rules, and the **binding-proof sweep** —
//! and every one of those was missing here.
//!
//! The divergence ran in the dangerous direction: validate ACCEPTS what apply REFUSES.
//! And it is the function the mempool path calls
//! (`dregg_sdk::embed::EmbeddedRuntime::validate_turn`, and
//! `node::exact_fnsp_v3_execution_authority`'s charged-route preflight).
//!
//! ## What that cost
//!
//! Two of the five (sovereign witness, binding-proof sweep) run AFTER `execute`'s PHASE 1,
//! and **Phase 1 — the fee debit and the nonce increment — is never rolled back**. So a
//! turn the pre-filter admitted could be refused by the executor with the agent's fee
//! already spent and its nonce already advanced. `nonce_and_fee_are_spent_on_the_rejection`
//! below is that fact, executed.
//!
//! # How "before" is exhibited without breaking the shared tree
//!
//! Mutating `validate_without_apply` to its old body would leave a window in which every
//! concurrent lane compiles a disarmed gate. Instead each test re-executes the OLD
//! function's accept condition — the exact conjunction of the six gates it ran — against
//! the SAME turn and ledger, via [`old_validate_would_admit`]. That predicate is the old
//! body's `Ok(())` path; where it holds and `execute` rejects, the old function admitted a
//! turn the executor refuses.

use std::collections::HashMap;

use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, TurnError,
    TurnExecutor, TurnResult, turn::Turn,
};

// ---------------------------------------------------------------------------
// Harness
// ---------------------------------------------------------------------------

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

fn bare_turn(agent: CellId, nonce: u64, effects: Vec<Effect>) -> Turn {
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

/// **The pre-2026-08-05 `validate_without_apply` accept condition, re-executed.**
///
/// This is the old body's `Ok(())` path verbatim in structure: forest non-empty, not
/// expired, agent present, agent non-terminal, nonce equal, fee covered, estimated cost
/// within the fee. Nothing else. `true` here means the old function returned `Ok(())` for
/// this exact `(turn, ledger, executor)`.
fn old_validate_would_admit(executor: &TurnExecutor, turn: &Turn, ledger: &Ledger) -> bool {
    if turn.call_forest.is_empty() {
        return false;
    }
    if let Some(valid_until) = turn.valid_until {
        if executor.current_timestamp > valid_until {
            return false;
        }
    }
    let Some(agent_cell) = ledger.get(&turn.agent) else {
        return false;
    };
    if agent_cell.lifecycle.is_terminal() {
        return false;
    }
    if agent_cell.state.nonce() != turn.nonce {
        return false;
    }
    if agent_cell.state.balance() < 0 || (agent_cell.state.balance() as u64) < turn.fee {
        return false;
    }
    executor.estimate_cost(turn) <= turn.fee
}

// ---------------------------------------------------------------------------
// THE DIVERGENCE: receipt-chain self-binding
// ---------------------------------------------------------------------------

/// A turn whose claimed `previous_receipt_hash` does not match the executor's stored head
/// for that agent. `execute` refuses it (`ReceiptChainMismatch`) and always did; the old
/// `validate_without_apply` admitted it.
fn chain_mismatch_case() -> (TurnExecutor, Ledger, Turn) {
    let cell = make_open_cell(11, 1_000);
    let agent = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();
    let executor = TurnExecutor::new(ComputronCosts::zero());

    // The agent has no receipt history, so the only legal claim is `None`. Claim
    // something else.
    let mut turn = bare_turn(agent, 0, vec![Effect::IncrementNonce { cell: agent }]);
    turn.previous_receipt_hash = Some([0x5A; 32]);
    (executor, ledger, turn)
}

#[test]
fn before_the_old_gate_set_admits_a_turn_execute_refuses() {
    let (executor, mut ledger, turn) = chain_mismatch_case();

    // BEFORE: every gate the old `validate_without_apply` ran says yes.
    assert!(
        old_validate_would_admit(&executor, &turn, &ledger),
        "the pre-2026-08-05 gate set must ADMIT this turn — otherwise this test is not \
         exhibiting the divergence it claims"
    );

    // …and `execute` refuses it.
    let result = executor.execute(&turn, &mut ledger);
    match result {
        TurnResult::Rejected { reason, .. } => assert!(
            matches!(reason, TurnError::ReceiptChainMismatch { .. }),
            "expected ReceiptChainMismatch, got {reason:?}"
        ),
        other => panic!("execute must refuse a receipt-chain mismatch; got {other:?}"),
    }
}

#[test]
fn after_validate_refuses_it_with_the_same_error_execute_gives() {
    let (executor, mut ledger, turn) = chain_mismatch_case();

    let validate_err = executor
        .validate_without_apply(&turn, &ledger)
        .expect_err("validate_without_apply must now refuse what execute refuses");
    assert!(
        matches!(validate_err, TurnError::ReceiptChainMismatch { .. }),
        "expected ReceiptChainMismatch from validate, got {validate_err:?}"
    );

    // And it is the SAME refusal, not merely some refusal.
    let TurnResult::Rejected {
        reason: execute_err,
        ..
    } = executor.execute(&turn, &mut ledger)
    else {
        panic!("execute must refuse");
    };
    assert_eq!(
        format!("{validate_err}"),
        format!("{execute_err}"),
        "validate and execute must refuse for the same stated reason"
    );
}

/// ⚑ THE PRICE OF THE DIVERGENCE. The refusal above happens before Phase 1, so it costs
/// nothing. This one does not: a turn admitted by the pre-filter and refused by the
/// executor AFTER Phase 1 leaves the agent fee-debited and nonce-bumped. The gate that
/// catches it (the sovereign-witness rules) is one of the five that were missing.
#[test]
fn nonce_and_fee_are_spent_on_a_post_phase1_rejection() {
    let cell = make_open_cell(12, 1_000);
    let agent = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();
    let executor = TurnExecutor::new(ComputronCosts::zero());

    // A sovereign witness naming a cell that is not sovereign: witness rule 1. That rule
    // runs AFTER Phase 1 on the execute path.
    let ghost = CellId::from_bytes([0x77; 32]);
    let mut turn = bare_turn(agent, 0, vec![Effect::IncrementNonce { cell: agent }]);
    turn.fee = 100;
    turn.sovereign_witnesses.insert(
        ghost,
        dregg_turn::turn::SovereignCellWitness {
            cell_id: ghost,
            old_commitment: [0u8; 32],
            new_commitment: [1u8; 32],
            effects_hash: [0u8; 32],
            cell_state: make_open_cell(13, 0),
            signature: [0u8; 64],
            timestamp: 0,
            sequence: 1,
            transition_proof: None,
        },
    );

    // BEFORE: the old gate set admits it (fee is covered, nonce matches, agent is live).
    assert!(
        old_validate_would_admit(&executor, &turn, &ledger),
        "the old gate set must admit this turn for the exhibit to mean anything"
    );

    // AFTER: the widened validate refuses it, so the mempool never propagates it.
    assert!(
        executor.validate_without_apply(&turn, &ledger).is_err(),
        "validate_without_apply must refuse a witness for a non-sovereign cell"
    );

    // And this is what the old behaviour cost: execute refuses, but only after Phase 1.
    let before_balance = ledger.get(&agent).unwrap().state.balance();
    let before_nonce = ledger.get(&agent).unwrap().state.nonce();
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        !result.is_committed(),
        "the turn must be refused; got {result:?}"
    );
    let after = ledger.get(&agent).unwrap();
    assert_eq!(
        after.state.balance(),
        before_balance - 100,
        "PHASE 1 IS NOT ROLLED BACK: the fee is spent on a rejected turn"
    );
    assert_eq!(
        after.state.nonce(),
        before_nonce + 1,
        "PHASE 1 IS NOT ROLLED BACK: the nonce is bumped on a rejected turn"
    );
}

// ---------------------------------------------------------------------------
// THE DIVERGENCE: the freeze gate
// ---------------------------------------------------------------------------

/// The agent's cell frozen for migration. `execute` refuses (`CellFrozen`) before Phase 1;
/// the old `validate_without_apply` admitted.
#[test]
fn a_frozen_agent_is_refused_by_validate_and_by_execute() {
    let cell = make_open_cell(14, 1_000);
    let agent = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();
    let executor = TurnExecutor::new(ComputronCosts::zero());
    executor
        .cell_migrations
        .lock()
        .unwrap()
        .begin_migration(agent, [0xEE; 32], 0, 100)
        .expect("freeze the agent for migration");

    let turn = bare_turn(agent, 0, vec![Effect::IncrementNonce { cell: agent }]);

    assert!(
        old_validate_would_admit(&executor, &turn, &ledger),
        "the old gate set never looked at the freeze table"
    );

    let err = executor
        .validate_without_apply(&turn, &ledger)
        .expect_err("a frozen agent must be refused by validate");
    assert!(matches!(err, TurnError::CellFrozen { .. }), "{err:?}");

    let result = executor.execute(&turn, &mut ledger);
    assert!(
        matches!(
            &result,
            TurnResult::Rejected {
                reason: TurnError::CellFrozen { .. },
                ..
            }
        ),
        "execute must refuse a frozen agent; got {result:?}"
    );
}

// ---------------------------------------------------------------------------
// COMPLETENESS: honest turns still pass BOTH
// ---------------------------------------------------------------------------

/// An honest turn is admitted by `validate_without_apply` and commits through `execute`.
/// The widened gate set must refuse nothing legitimate — including on the second turn,
/// where the receipt-chain head is now non-`None` and the freshly added chain gate has to
/// agree with the head `execute` recorded.
#[test]
fn honest_turns_still_pass_validate_and_execute() {
    let cell = make_open_cell(15, 10_000);
    let agent = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();
    let executor = TurnExecutor::new(ComputronCosts::zero());

    let first = bare_turn(agent, 0, vec![Effect::IncrementNonce { cell: agent }]);
    executor
        .validate_without_apply(&first, &ledger)
        .expect("an honest first turn must validate");
    let result = executor.execute(&first, &mut ledger);
    assert!(result.is_committed(), "first turn must commit: {result:?}");

    // Second turn: nonce advanced, and the chain head is now set, so the turn must claim
    // it. This is the case the new receipt-chain gate could have broken.
    let head = executor
        .get_last_receipt_hash(&agent)
        .expect("the committed turn recorded a chain head");
    let mut second = bare_turn(
        agent,
        ledger.get(&agent).unwrap().state.nonce(),
        vec![Effect::IncrementNonce { cell: agent }],
    );
    second.previous_receipt_hash = Some(head);
    executor
        .validate_without_apply(&second, &ledger)
        .expect("an honest chained second turn must validate");
    let result = executor.execute(&second, &mut ledger);
    assert!(result.is_committed(), "second turn must commit: {result:?}");
}
