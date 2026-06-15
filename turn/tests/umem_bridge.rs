//! THE EXECUTOR-STATE BRIDGE round-trip: a REAL turn executed by the LIVE executor is
//! re-read as a Blum memory-op trace whose fold over the projected pre-state equals the
//! projected post-state — the Rust shadow of the Lean agreement keystones
//! (`metatheory/Dregg2/Exec/UniversalBridge.lean` `*_is_memory_program`).
//!
//! Covered verbs (the compressed kernel, `VerbCompression.compressed_kernel_three`):
//!   * move   — `Effect::Transfer` (the paired debit/credit balance writes);
//!   * gwrite — `Effect::SetField` (the record-field write) and
//!              `Effect::AttenuateCapability` (the caps-domain guarded write);
//!   * create — `Effect::CreateCell` (the multi-address bundle birth).
//!
//! Teeth: discipline holds, `synthesized == 0` (the journal NAMES every touched address
//! on these lanes), the specific cells moved to the expected values, and a tampered op
//! breaks the fold (the agreement check is not vacuous).

use std::sync::atomic::Ordering;

use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
use dregg_turn::umem::{UKey, UVal, UmemKind, UmemOp, UmemTurnWitness, disciplined, fold};
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

fn single_effect_turn(agent: CellId, target: CellId, nonce: u64, effect: Effect) -> Turn {
    multi_effect_turn(agent, target, nonce, vec![effect])
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

/// The shared teeth every witness must pass.
fn assert_bridge_square(w: &UmemTurnWitness) {
    assert_eq!(
        fold(&w.pre, &w.ops),
        w.post,
        "the fold of the emitted trace over the pre-projection must equal the \
         post-projection (the agreement square)"
    );
    assert!(disciplined(&w.ops), "the emitted trace must be disciplined");
    assert_eq!(
        w.synthesized, 0,
        "the journal must NAME every touched address on this lane (no synthesized ops)"
    );
    // every op's prev claim is the genuine fold-current value (re-walk independently).
    let mut current = w.pre.clone();
    for op in &w.ops {
        assert_eq!(
            op.prev_val,
            current.get(&op.key).cloned(),
            "op prev claim must match the running fold at {:?}",
            op.key
        );
        if let UmemKind::Write = op.kind {
            match &op.val {
                Some(v) => {
                    current.insert(op.key.clone(), v.clone());
                }
                None => {
                    current.remove(&op.key);
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// move: Effect::Transfer — paired debit/credit balance writes.
// ---------------------------------------------------------------------------
#[test]
fn umem_witness_transfer_round_trip() {
    let agent = make_open_cell(1, 1000);
    let target = make_open_cell(2, 50);
    let (agent_id, target_id) = (agent.id(), target.id());
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent).unwrap();
    ledger.insert_cell(target).unwrap();

    let executor = umem_executor();
    let turn = single_effect_turn(
        agent_id,
        agent_id,
        0,
        Effect::Transfer {
            from: agent_id,
            to: target_id,
            amount: 250,
        },
    );
    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed(), "transfer must commit: {result:?}");

    let w = take_witness(&executor);
    assert_bridge_square(&w);

    // the paired debit/credit writes, with genuine prevs and values.
    let debit = w
        .ops
        .iter()
        .find(|op| op.key == UKey::Balance(agent_id))
        .expect("debit write present");
    assert_eq!(debit.prev_val, Some(UVal::Int(1000)));
    assert_eq!(debit.val, Some(UVal::Int(750)));
    let credit = w
        .ops
        .iter()
        .find(|op| op.key == UKey::Balance(target_id))
        .expect("credit write present");
    assert_eq!(credit.prev_val, Some(UVal::Int(50)));
    assert_eq!(credit.val, Some(UVal::Int(300)));

    // TEETH: tampering one op's value breaks the agreement square.
    let mut tampered = w.ops.clone();
    let idx = tampered
        .iter()
        .position(|op| op.key == UKey::Balance(agent_id))
        .unwrap();
    tampered[idx].val = Some(UVal::Int(999));
    assert_ne!(
        fold(&w.pre, &tampered),
        w.post,
        "a tampered write must break the fold/post agreement"
    );
}

// ---------------------------------------------------------------------------
// gwrite: Effect::SetField — the record-field write.
// ---------------------------------------------------------------------------
#[test]
fn umem_witness_set_field_round_trip() {
    let agent = make_open_cell(3, 100);
    let target = make_open_cell(4, 0);
    let (agent_id, target_id) = (agent.id(), target.id());
    let mut agent_with_cap = agent;
    agent_with_cap
        .capabilities
        .grant(target_id, AuthRequired::None)
        .unwrap();
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent_with_cap).unwrap();
    ledger.insert_cell(target).unwrap();

    let executor = umem_executor();
    let value = [42u8; 32];
    let turn = single_effect_turn(
        agent_id,
        target_id,
        0,
        Effect::SetField {
            cell: target_id,
            index: 3,
            value,
        },
    );
    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed(), "set_field must commit: {result:?}");

    let w = take_witness(&executor);
    assert_bridge_square(&w);

    let write = w
        .ops
        .iter()
        .find(|op| {
            op.key
                == UKey::Field {
                    cell: target_id,
                    slot: 3,
                }
        })
        .expect("field write present");
    assert_eq!(write.prev_val, Some(UVal::Bytes32([0u8; 32])));
    assert_eq!(write.val, Some(UVal::Bytes32(value)));
}

// ---------------------------------------------------------------------------
// gwrite (heap domain): Effect::SetField with index >= STATE_SLOTS — the
// openable sorted-map spine (`CellState.fields_map`). This is the Rust executor
// half of the universal-map rotation: the live executor must admit heap keys
// so real collections (nameservice entries, council members, ...) can grow.
// ---------------------------------------------------------------------------
#[test]
fn umem_witness_set_heap_field_round_trip() {
    let agent = make_open_cell(10, 100);
    let target = make_open_cell(11, 0);
    let (agent_id, target_id) = (agent.id(), target.id());
    let mut agent_with_cap = agent;
    agent_with_cap
        .capabilities
        .grant(target_id, AuthRequired::None)
        .unwrap();
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent_with_cap).unwrap();
    ledger.insert_cell(target).unwrap();

    let executor = umem_executor();
    let slot: u64 = 42; // any key >= STATE_SLOTS (8) is a heap field.
    let value = [42u8; 32];
    let turn = single_effect_turn(
        agent_id,
        target_id,
        0,
        Effect::SetField {
            cell: target_id,
            index: slot as usize,
            value,
        },
    );
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        result.is_committed(),
        "set_field on heap slot must commit: {result:?}"
    );

    // The cell state actually grew into the heap map.
    let target_after = ledger.get(&target_id).expect("target present");
    assert_eq!(
        target_after.state.get_field_ext(slot),
        Some(value),
        "heap slot {slot} must hold the written value"
    );

    let w = take_witness(&executor);
    assert_bridge_square(&w);

    let write = w
        .ops
        .iter()
        .find(|op| {
            op.key
                == UKey::Field {
                    cell: target_id,
                    slot,
                }
        })
        .expect("heap field write present in umem trace");
    assert_eq!(
        write.prev_val, None,
        "fresh heap key was absent before the write"
    );
    assert_eq!(write.val, Some(UVal::Bytes32(value)));
}

// ---------------------------------------------------------------------------
// gwrite (caps domain): Effect::AttenuateCapability — the guarded narrow write.
// ---------------------------------------------------------------------------
#[test]
fn umem_witness_attenuate_capability_round_trip() {
    let actor = make_open_cell(5, 1000);
    let target = make_open_cell(6, 0);
    let (actor_id, target_id) = (actor.id(), target.id());

    let mut actor_with_cap = actor;
    let slot = actor_with_cap
        .capabilities
        .grant(target_id, AuthRequired::Either)
        .unwrap();
    let mut ledger = Ledger::new();
    ledger.insert_cell(actor_with_cap).unwrap();
    ledger.insert_cell(target).unwrap();

    let executor = umem_executor();
    let turn = single_effect_turn(
        actor_id,
        actor_id,
        0,
        Effect::AttenuateCapability {
            cell: actor_id,
            slot,
            narrower_permissions: AuthRequired::Signature,
            narrower_effects: None,
            narrower_expiry: None,
        },
    );
    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed(), "attenuation must commit: {result:?}");

    let w = take_witness(&executor);
    assert_bridge_square(&w);

    // the caps-domain write at the narrowed slot: prev present (the broad cap),
    // new present (the narrow cap), and they differ.
    let cap_write = w
        .ops
        .iter()
        .find(|op| {
            op.key
                == UKey::CapSlot {
                    cell: actor_id,
                    slot,
                }
        })
        .expect("cap-slot write present");
    assert!(cap_write.prev_val.is_some(), "the slot existed before");
    assert!(cap_write.val.is_some(), "the slot exists after");
    assert_ne!(
        cap_write.prev_val, cap_write.val,
        "attenuation genuinely narrowed the slot"
    );
}

// ---------------------------------------------------------------------------
// create: Effect::CreateCell — the multi-address bundle birth.
// ---------------------------------------------------------------------------
#[test]
fn umem_witness_create_cell_round_trip() {
    let agent = make_open_cell(7, 5000);
    let agent_id = agent.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent).unwrap();

    let executor = umem_executor();
    let mut new_pk = [0u8; 32];
    new_pk[0] = 99;
    let turn = single_effect_turn(
        agent_id,
        agent_id,
        0,
        Effect::CreateCell {
            public_key: new_pk,
            token_id: [0u8; 32],
            balance: 0,
        },
    );
    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed(), "create must commit: {result:?}");

    let w = take_witness(&executor);
    assert_bridge_square(&w);

    // the existence bit was born from absent (the freshness gate's trace shadow,
    // Lean `createTrace`'s `prevVal = none`).
    let exist = w
        .ops
        .iter()
        .find(|op| matches!(&op.key, UKey::Exist(c) if Some(*c) != Some(agent_id)))
        .expect("existence write for the born cell present");
    assert_eq!(exist.prev_val, None, "the born cell was fresh");
    assert_eq!(exist.val, Some(UVal::Present));
    // the bundle is multi-address (create separates by ARITY —
    // `create_birth_not_single_write`): existence + balance + the rest of the planes.
    let born = match &exist.key {
        UKey::Exist(c) => *c,
        _ => unreachable!(),
    };
    let born_ops: Vec<&UmemOp> = w
        .ops
        .iter()
        .filter(|op| op.key.cell() == Some(born))
        .collect();
    assert!(
        born_ops.len() > 2,
        "bundle birth initializes several addresses atomically (got {})",
        born_ops.len()
    );
    let born_balance = w
        .ops
        .iter()
        .find(|op| op.key == UKey::Balance(born))
        .expect("born balance write present");
    assert_eq!(born_balance.prev_val, None);
    assert_eq!(born_balance.val, Some(UVal::Int(0)));
}

// ---------------------------------------------------------------------------
// one turn, three verbs: the witness composes across effects in journal order.
// ---------------------------------------------------------------------------
#[test]
fn umem_witness_three_verb_turn_round_trip() {
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
    assert!(
        result.is_committed(),
        "three-verb turn must commit: {result:?}"
    );

    let w = take_witness(&executor);
    assert_bridge_square(&w);
    assert!(
        w.ops.len() >= 4,
        "transfer (2 writes) + set_field (1) + attenuate (1) at least; got {}",
        w.ops.len()
    );
}
