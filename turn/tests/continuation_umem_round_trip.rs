//! Continuations-as-umems over a REAL executor-produced trace.
//!
//! `crate::umem` re-reads a turn the LIVE executor committed as a Blum memory-op program
//! `(pre, ops, post)` whose `fold(pre, ops) == post` (the executor-state bridge). This test
//! takes such a GENUINE program, cuts it at every position, captures the prefix's state as a
//! passable `Continuation` (a umem), hands it across a serialization boundary, and resumes —
//! proving suspend→handoff→resume reaches the SAME post the executor reached, byte for byte.
//!
//! This is the continuation round-trip the revolution promises: the intermediate computation
//! state of a partial turn is a witnessed portable object, suspended and resumed — not a
//! bespoke re-run of the whole turn.
//!
//! The one structural seam (a mid-FOREST executor checkpoint, vs. this trace cut) is named in
//! `turn/src/continuation.rs`'s module docs ("THE SEAM — mid-forest checkpoint").

use std::sync::atomic::Ordering;

use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
use dregg_turn::continuation::Continuation;
use dregg_turn::umem::{UmemTurnWitness, fold};
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, TurnExecutor,
    turn::Turn,
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

fn multi_effect_turn(agent: CellId, target: CellId, nonce: u64, effects: Vec<Effect>) -> Turn {
    let mut forest = CallForest::new();
    let action = Action {
        target,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects,
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    };
    forest.add_root(action);
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
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    }
}

fn umem_executor() -> TurnExecutor {
    let executor = TurnExecutor::new(ComputronCosts::zero());
    executor.umem_witness_enabled.store(true, Ordering::Relaxed);
    executor
}

fn take_witness(executor: &TurnExecutor) -> UmemTurnWitness {
    executor
        .last_umem_witness
        .lock()
        .unwrap()
        .take()
        .expect("umem witness must be produced when the flag is set")
        .expect("umem witness emission must succeed")
}

/// Run a real multi-write turn, then cut its genuine Blum trace at EVERY position: each cut
/// captures a `Continuation` (a passable umem) whose resume — after a serialization hand-off —
/// reaches the exact post-state the executor reached.
#[test]
fn executor_trace_suspends_and_resumes_as_umem() {
    let agent = make_open_cell(8, 1000);
    let target = make_open_cell(9, 10);
    let (agent_id, target_id) = (agent.id(), target.id());

    let mut agent_with_cap = agent;
    let slot = agent_with_cap
        .capabilities
        .grant(target_id, AuthRequired::Either)
        .unwrap();
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent_with_cap).unwrap();
    ledger.insert_cell(target).unwrap();

    let executor = umem_executor();
    // Three verbs => several genuine memory-ops in journal order.
    let turn = multi_effect_turn(
        agent_id,
        agent_id,
        0,
        vec![
            Effect::Transfer {
                from: agent_id,
                to: target_id,
                amount: 7,
            },
            Effect::SetField {
                cell: agent_id,
                index: 0,
                value: [9u8; 32],
            },
            Effect::AttenuateCapability {
                cell: agent_id,
                slot,
                narrower_permissions: AuthRequired::Signature,
                narrower_effects: None,
                narrower_expiry: None,
            },
        ],
    );
    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed(), "turn must commit: {result:?}");

    let w = take_witness(&executor);
    // Sanity: the executor's own bridge square holds (this is a genuine program).
    assert_eq!(
        fold(&w.pre, &w.ops),
        w.post,
        "the executor-produced trace must fold pre -> post"
    );
    assert!(
        w.ops.len() >= 4,
        "expected several ops; got {}",
        w.ops.len()
    );

    // Cut the genuine trace at EVERY position. Each cut is a valid suspend point.
    for cut in 0..=w.ops.len() {
        let suspended = Continuation::suspend(&w.pre, &w.ops, cut);
        assert_eq!(
            suspended.consumed, cut,
            "the continuation records the cut position"
        );

        // Hand it off across a serialization boundary (pass the umem down the pipe).
        let wire = suspended.to_bytes();
        let landed = Continuation::from_bytes(&wire).expect("handed-off continuation decodes");
        assert_eq!(landed, suspended, "hand-off is byte-faithful at cut {cut}");

        // Resume from the captured umem.
        let resumed = landed
            .resume()
            .unwrap_or_else(|e| panic!("resume at cut {cut} must succeed: {e}"));
        assert_eq!(
            resumed, w.post,
            "suspend at cut {cut} -> handoff -> resume must reach the executor's post-state"
        );

        if cut == w.ops.len() {
            assert!(
                landed.is_complete(),
                "the final cut is a complete continuation"
            );
        }
    }
}
