use dregg_cell::CellId;
use dregg_turn::{BudgetGate, BudgetSlice, ComputronCosts, Finality, TurnExecutor, TurnReceipt};

#[test]
fn checkpoint_restores_receipt_budget_and_rate_side_state() {
    let executor = TurnExecutor::with_budget_gate(
        ComputronCosts::zero(),
        BudgetGate::new(7, BudgetSlice::new(100)),
    );
    let agent = CellId::from_bytes([1; 32]);
    executor.set_last_receipt_hash(agent, [2; 32]);

    let checkpoint = executor.checkpoint_producer_reference(agent);
    executor.record_authoritative_receipt_head(agent, [3; 32]);
    executor
        .rate_limit_counters
        .lock()
        .unwrap()
        .insert((agent, [4; 32], 5), 6);
    executor
        .budget_gate
        .as_ref()
        .unwrap()
        .lock()
        .unwrap()
        .try_debit(10, &[7; 32])
        .unwrap();
    executor.last_write_set.lock().unwrap().push(agent);

    executor.rollback_producer_reference(checkpoint);
    assert_eq!(executor.get_last_receipt_hash(&agent), Some([2; 32]));
    assert!(executor.rate_limit_state_snapshot().counts.is_empty());
    let gate = executor.budget_gate.as_ref().unwrap().lock().unwrap();
    assert_eq!(gate.slice.spent, 0);
    assert!(gate.slice.debits.is_empty());
    drop(gate);
    assert!(executor.last_write_set().is_empty());
}

#[test]
fn authoritative_restamp_records_the_post_restamp_hash() {
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let agent = CellId::from_bytes([9; 32]);
    let receipt = TurnReceipt {
        turn_hash: [1; 32],
        forest_hash: [2; 32],
        pre_state_hash: [3; 32],
        post_state_hash: [4; 32],
        timestamp: 5,
        effects_hash: [6; 32],
        computrons_used: 7,
        action_count: 1,
        previous_receipt_hash: None,
        agent,
        federation_id: [8; 32],
        routing_directives: vec![],
        introduction_exports: vec![],
        derivation_records: vec![],
        emitted_events: vec![],
        executor_signature: None,
        finality: Finality::Final,
        was_encrypted: false,
        was_burn: false,
        consumed_capabilities: vec![],
    };
    let speculative_hash = receipt.receipt_hash();
    executor.set_last_receipt_hash(agent, speculative_hash);

    let final_receipt = executor.restamp_authoritative_committed_receipt(receipt, [0xAA; 32]);
    let final_hash = final_receipt.receipt_hash();
    assert_ne!(final_hash, speculative_hash);
    assert_eq!(executor.get_last_receipt_hash(&agent), Some(final_hash));
    assert_eq!(final_receipt.post_state_hash, [0xAA; 32]);
}
