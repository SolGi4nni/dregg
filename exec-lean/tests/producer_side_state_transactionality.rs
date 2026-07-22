//! The verified producer's Rust cross-check is speculative as a whole. This
//! live-path test pins the commit half: the exact producer-returned receipt is
//! the chain head and committed resource side-state is retained. The inverse
//! is pinned without relying on a transient Rust/Lean divergence in
//! `turn/tests/producer_transactionality.rs`.

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_exec_lean::{
    lean_apply::{ProducerOutcome, produce_via_lean},
    lean_shadow,
};
use dregg_turn::{
    ActionBuilder, BudgetGate, BudgetSlice, ComputronCosts, Effect, TurnBuilder, TurnExecutor,
};

fn open_cell() -> Cell {
    let mut cell = Cell::with_balance([1; 32], [2; 32], 100);
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
    cell
}

#[test]
fn covered_commit_records_exact_receipt_head_and_budget_slice() {
    if !dregg_lean_ffi::demand_lean(
        dregg_lean_ffi::lean_available(),
        "Lean archive (verified producer transactionality)",
    ) {
        return;
    }

    // Burn is in the root-agreeing producer set, so this reaches the verified
    // authority branch rather than the Rust fallback. The formerly documented
    // no-cap divergence is now aligned: both producers commit this self-redeem.
    let agent = open_cell();
    let agent_id = agent.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent).unwrap();
    let pre_root = ledger.root();
    let executor = TurnExecutor::with_budget_gate(
        ComputronCosts::zero(),
        BudgetGate::new(17, BudgetSlice::new(100)),
    );
    let action = ActionBuilder::new_unchecked_for_tests(agent_id, "burn", agent_id)
        .effect(Effect::Burn {
            target: agent_id,
            slot: 0,
            amount: 10,
        })
        .build();
    let mut builder = TurnBuilder::new(agent_id, 0);
    builder.add_action(action);
    let turn = builder.fee(5).build();
    assert!(lean_shadow::forest_is_root_agreeing(&turn));

    let (result, outcome) = produce_via_lean(&executor, &turn, &mut ledger);
    assert!(result.is_committed(), "producer outcome: {outcome:?}");
    assert!(matches!(
        outcome,
        ProducerOutcome::LeanAuthoritative {
            committed: true,
            rust_committed: true,
            ..
        }
    ));
    assert_ne!(
        ledger.root(),
        pre_root,
        "the verified post-state is installed"
    );
    let receipt = match &result {
        dregg_turn::TurnResult::Committed { receipt, .. } => receipt,
        _ => unreachable!("asserted committed above"),
    };
    assert_eq!(
        executor.get_last_receipt_hash(&agent_id),
        Some(receipt.receipt_hash()),
        "the authority chain points at the exact receipt returned by the producer"
    );
    let gate = executor.budget_gate.as_ref().unwrap().lock().unwrap();
    assert_eq!(gate.slice.spent, 5, "the accepted debit remains committed");
    assert_eq!(gate.slice.debits.len(), 1);
    drop(gate);
    assert!(
        !executor.last_write_set().is_empty(),
        "the accepted reference run exposes its exact committed write-set"
    );
}
