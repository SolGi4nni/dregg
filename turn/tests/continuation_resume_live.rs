//! CONTINUATIONS-AS-PASSABLE-UMEMS, MADE LIVE — the third revolution end-to-end.
//!
//! `mid_forest_yield_point.rs` proves the executor captures a genuine mid-flight boundary
//! and that `Continuation::resume()` (checked against a witness) reaches the straight-through
//! post. But nothing in the running system DEPENDS on that resume — it is a witnessed
//! round-trip, not a load-bearing path.
//!
//! This file closes that: a real turn is SUSPENDED mid-forest into a `Continuation`, the
//! continuation is PARKED under the live promise vocabulary (`ResolutionCondition` /
//! `BrokenReason` from `pending`), HANDED OFF (serialized → deserialized — a different
//! party), and on resolution RESUMED to its post and REIFIED into a running ledger —
//! completing the turn WITHOUT re-executing its effects. The landed ledger is byte-identical
//! (root + every cell) to running the same turn straight through.
//!
//! This is the load-bearing claim: the suspended turn makes progress by resuming the
//! passable umem, not by re-running. `ResumableTurnRegistry` is the live consumer.

use std::sync::atomic::Ordering;

use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
use dregg_turn::continuation_resume::{ResumableTurnRegistry, ResumeFailure};
use dregg_turn::pending::ResolutionCondition;
use dregg_turn::umem::reify_ledger;
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

/// A fresh ledger holding (agent-with-cap-to-target, target), mirroring the mid-forest test
/// fixture so the suspended turn's effects are well-formed. Returns (agent_id, target_id, slot).
fn fixture(ledger: &mut Ledger) -> (CellId, CellId, u32) {
    let agent = make_open_cell(8, 1000);
    let target = make_open_cell(9, 10);
    let (agent_id, target_id) = (agent.id(), target.id());
    let mut agent_with_cap = agent;
    let slot = agent_with_cap
        .capabilities
        .grant(target_id, AuthRequired::Either)
        .unwrap();
    ledger.insert_cell(agent_with_cap).unwrap();
    ledger.insert_cell(target).unwrap();
    (agent_id, target_id, slot)
}

fn three_effect_turn(agent_id: CellId, target_id: CellId, slot: u32, amount: u64) -> Turn {
    let mut forest = CallForest::new();
    let action = Action {
        target: agent_id,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![
            Effect::Transfer {
                from: agent_id,
                to: target_id,
                amount,
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
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    };
    forest.add_root(action);
    Turn {
        agent: agent_id,
        nonce: 0,
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
    let e = TurnExecutor::new(ComputronCosts::zero());
    e.umem_witness_enabled.store(true, Ordering::Relaxed);
    e
}

/// THE KEYSTONE: a turn is SUSPENDED mid-forest, its continuation PARKED + HANDED OFF, and
/// on resolution RESUMED into a running ledger — completing the turn. The landed ledger is
/// byte-identical to running the same turn straight through.
#[test]
fn suspended_turn_resumes_into_a_byte_identical_ledger() {
    // --- STRAIGHT-THROUGH baseline: run the whole turn, no yield. ----------------------
    let straight_exec = umem_executor();
    let mut straight_ledger = Ledger::new();
    let (agent_id, target_id, slot) = fixture(&mut straight_ledger);
    let turn = three_effect_turn(agent_id, target_id, slot, 7);
    assert!(
        straight_exec
            .execute(&turn, &mut straight_ledger)
            .is_committed(),
        "straight-through turn must commit"
    );
    let straight_post = straight_exec
        .last_umem_witness
        .lock()
        .unwrap()
        .take()
        .expect("umem witness produced")
        .expect("umem witness ok")
        .post;
    let straight_root = straight_ledger.root();

    // --- LIVE suspend: run the same turn but arm a mid-forest yield (suspend the turn). -
    let suspend_exec = umem_executor();
    let mut suspend_ledger = Ledger::new();
    let (agent_id, target_id, slot) = fixture(&mut suspend_ledger);
    suspend_exec.set_umem_yield_at(Some(1)); // yield between the first and second effects
    let turn = three_effect_turn(agent_id, target_id, slot, 7);
    let turn_hash = turn.hash();
    assert!(
        suspend_exec
            .execute(&turn, &mut suspend_ledger)
            .is_committed(),
        "the suspended turn still commits as a whole (the yield is observation-only)"
    );

    // Capture the continuation = the passable umem of the suspended turn.
    let cont = suspend_exec
        .capture_yielded_continuation()
        .expect("a mid-forest yield must have produced a continuation");
    assert!(
        !cont.is_complete(),
        "a mid-forest suspension has remaining work to fold (it is a genuine middle)"
    );

    // --- PARK the continuation under the live promise vocabulary + HAND IT OFF. ---------
    let mut origin_reg = ResumableTurnRegistry::new();
    origin_reg.park(turn_hash, cont, ResolutionCondition::AwaitHeight(200), 1000);
    // Serialize the parked promise and ship it to a different party.
    let parked = origin_reg.get(&turn_hash).expect("parked").clone();
    let wire = serde_json::to_vec(&parked).expect("the parked continuation serializes");

    // --- THE RESOLVER (a different party) holds only the PRE-state ledger + the wire. ---
    let mut resolver_ledger = Ledger::new();
    let _ = fixture(&mut resolver_ledger); // resolver starts from the same pre-state
    let resolver_pre_root = resolver_ledger.root();
    assert_ne!(
        resolver_pre_root, straight_root,
        "the resolver's pre-state differs from the completed turn's state (work remains)"
    );

    let landed: dregg_turn::continuation_resume::ParkedContinuation =
        serde_json::from_slice(&wire).expect("the handed-off promise decodes");
    let mut resolver_reg = ResumableTurnRegistry::new();
    resolver_reg.park_entry(turn_hash, landed);

    // The promise's height condition is now met → resume into the running ledger.
    assert_eq!(
        resolver_reg.ready_by_height(200),
        vec![turn_hash],
        "the parked promise is ready once its height condition is met"
    );
    let resumed = resolver_reg
        .resume_into_ledger(turn_hash, &mut resolver_ledger)
        .expect("the suspended turn resumes into the ledger");
    assert!(
        resumed.resumed_ops > 0,
        "resume folded the remaining tail (it was NOT a no-op — real work was completed)"
    );
    assert!(resolver_reg.is_empty(), "the resumed promise is consumed");

    // --- THE GUARANTEE: completing-by-resume == running straight through. ---------------
    assert_eq!(
        resumed.post, straight_post,
        "the resumed post-state equals the straight-through post (resume reconstructs it exactly)"
    );
    assert_eq!(
        resolver_ledger.root(),
        straight_root,
        "the ledger completed by RESUMING the passable umem is byte-identical (root) to \
         running the turn straight through — the turn finished without re-executing"
    );

    // Cross-check: every present cell agrees, not just the root.
    let straight_again = reify_ledger(&straight_post).expect("straight post reifies");
    for (id, cell) in straight_again.iter() {
        let landed_cell = resolver_ledger
            .get(id)
            .expect("resumed ledger has every straight-through cell");
        assert_eq!(
            landed_cell.state.balance(),
            cell.state.balance(),
            "cell {id:?} balance matches after resume"
        );
        assert_eq!(
            landed_cell.state.fields, cell.state.fields,
            "cell {id:?} fields match after resume"
        );
    }
}

/// FAIL-CLOSED through the live path: a continuation handed off with a TAMPERED tail is
/// refused at resume, and the resolver's ledger is left untouched.
#[test]
fn tampered_handoff_refuses_and_leaves_ledger_untouched() {
    let suspend_exec = umem_executor();
    let mut suspend_ledger = Ledger::new();
    let (agent_id, target_id, slot) = fixture(&mut suspend_ledger);
    suspend_exec.set_umem_yield_at(Some(1));
    let turn = three_effect_turn(agent_id, target_id, slot, 11);
    let turn_hash = turn.hash();
    assert!(
        suspend_exec
            .execute(&turn, &mut suspend_ledger)
            .is_committed()
    );
    let mut cont = suspend_exec
        .capture_yielded_continuation()
        .expect("continuation captured");

    // Tamper the handed-off tail: forge the first remaining op's prev-claim.
    use dregg_turn::umem::{UKey, UVal, UmemKind};
    if let Some(op) = cont
        .remaining
        .iter_mut()
        .find(|o| o.kind == UmemKind::Write)
    {
        op.prev_val = Some(UVal::Int(123_456));
        // Use a key guaranteed present so it is the prev-claim, not the discipline, that bites.
        let _ = UKey::Balance(agent_id);
    }

    let mut reg = ResumableTurnRegistry::new();
    reg.park(turn_hash, cont, ResolutionCondition::AwaitHeight(0), 1000);

    let mut resolver_ledger = Ledger::new();
    let _ = fixture(&mut resolver_ledger);
    let pre_root = resolver_ledger.root();

    let err = reg
        .resume_into_ledger(turn_hash, &mut resolver_ledger)
        .expect_err("a tampered handed-off continuation must refuse");
    assert!(
        matches!(err, ResumeFailure::BadTail(_)),
        "the refusal is a bad-tail refusal, got {err:?}"
    );
    assert_eq!(
        resolver_ledger.root(),
        pre_root,
        "a refused resume leaves the ledger untouched (fail-closed)"
    );
}
