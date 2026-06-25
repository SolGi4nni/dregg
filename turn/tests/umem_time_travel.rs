//! TIME-TRAVEL VIA UMEM BOUNDARIES — the prototype.
//!
//! THE REVOLUTION: a snapshot of world/cell state IS a umem boundary
//! ([`UProjection`]), and rewinding IS restoring that boundary. The chronicle's
//! receipt-rewind, the desktop's time-scrub, and node-level world snapshots all
//! collapse to ONE operation — umem-boundary save/restore — witnessed by the SAME
//! Blum memory-checking algebra (`fold` / `disciplined`) that the executor-state
//! bridge already proves agreement under (`turn/src/umem.rs`, the Lean
//! `*_is_memory_program` keystones in `Dregg2/Exec/UniversalBridge.lean`).
//!
//! Why this is cheap and witnessed (no chip table, no O(history) replay):
//!   * a boundary is just `project_executor_state(...)` — a `BTreeMap<UKey,UVal>`;
//!   * advancing produces a NEW boundary;
//!   * REWINDING is the inverse Blum trace between the two boundaries, and the
//!     SAME `fold` that proves forward agreement proves the rewind reaches EXACTLY
//!     the height-H boundary. `disciplined` certifies the trace is a legal
//!     memcheck program. No history replay is needed: the boundary IS the state.
//!
//! This file PROVES: snapshot at height H → advance (real executor turns) → rewind
//! by restoring the umem boundary → state == the H snapshot, both
//!   (a) at the projection level (the boundary), and
//!   (b) via the umem op-trace (the inverse diff trace, folded, reaches H), with
//!       `disciplined` holding — i.e. the rewind is a legal, witnessable memory
//!       program, not an out-of-band poke.
//!
//! Why the snapshot BOUNDARY is now WITNESSABLE (the keystone, landed `99a8dc94`):
//! `boundary_init_root_derived` / `boundary_init_root_bound`
//! (`metatheory/Dregg2/Crypto/UniversalMemory.lean:463/475`, `#assert_axioms`-clean)
//! prove a boundary's INIT image is BOUND to the committed pre-state map root —
//! under the `Poseidon2SpongeCR` floor a boundary whose image differs from the
//! committed state produces a DIFFERENT sorted-Poseidon2 root, so the pin REFUSES.
//! This is exactly what time-travel needs: a snapshot's boundary is NOT
//! prover-chosen — it equals a committed root, so "rewind to height H" restores a
//! boundary the chain already attested. The rewind here is the in-Rust shadow; the
//! Lean binding makes the restored boundary trustworthy rather than free-witnessed.
//!
//! THE SEAM IS CLOSED (`reify_seam`): materializing a `UProjection` back into a
//! live byte-identical `Ledger` is now [`reify_cell`] / [`reify_ledger`] — the
//! inverse of `project_cell`. The projection deliberately DROPS derived
//! commitments (the ledger Merkle root, `fields_root`) and per-window metering —
//! documented non-cells in `turn/src/umem.rs` — and reify RE-DERIVES them from
//! the kept planes (it does not store them): `fields_root` from the
//! `Field { slot ≥ 16 }` plane, the ledger Merkle root lazily on the next
//! `root()`. The round-trip law `reify_ledger(project_ledger(L)) == L` is PROVEN
//! below over the faithful class (the class the projection is value-lossless on),
//! and the precise residual — four value planes the projection does not yet carry
//! (heap preimage, interfaces, cap tombstones, the post-revoke `next_slot` gap) —
//! is named by [`ReifyError`] and exercised by the refusal tests below: reify
//! REFUSES rather than round-trip a state the boundary cannot reconstruct.

use std::sync::atomic::Ordering;

use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
use dregg_turn::umem::{
    ReifyError, UKey, UProjection, UVal, UmemKind, UmemOp, disciplined, fold,
    project_executor_state, project_ledger, reify_cell, reify_ledger,
};
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
    let mut forest = CallForest::new();
    let action = Action {
        target,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![effect],
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

/// Take a umem BOUNDARY snapshot of the full executor state — THE snapshot
/// primitive. This is `project_executor_state`: ledger + nullifier sets + factory
/// registry, projected into the unified `(domain, collection, key) ↦ value` space.
fn snapshot_boundary(executor: &TurnExecutor, ledger: &Ledger) -> UProjection {
    project_executor_state(
        ledger,
        &executor.note_nullifiers.lock().unwrap(),
        &executor.bridged_nullifiers.lock().unwrap(),
        &executor.factory_registry.borrow(),
    )
}

/// THE REWIND PRIMITIVE — restore a target boundary by computing the inverse Blum
/// memory-op trace from `current` back to `target`, expressed in the SAME memcheck
/// algebra the executor bridge proves agreement under.
///
/// Every address whose value differs between `current` and `target` becomes one
/// WRITE op installing the target value (`None` = remove, the absent-cell
/// encoding). `fold(current, rewind_trace)` then yields EXACTLY `target` — this is
/// the witnessed restore. The trace is `disciplined` by construction (each address
/// is touched at most once, so `prev_serial = 0 < i+1`).
fn rewind_trace(current: &UProjection, target: &UProjection) -> Vec<UmemOp> {
    let mut ops = Vec::new();
    // addresses present in current but changed-or-absent in target.
    for (k, cur) in current.iter() {
        match target.get(k) {
            Some(t) if t == cur => {} // unchanged — no op.
            Some(t) => ops.push(UmemOp {
                kind: UmemKind::Write,
                key: k.clone(),
                val: Some(t.clone()),
                prev_val: Some(cur.clone()),
                prev_serial: 0,
            }),
            None => ops.push(UmemOp {
                kind: UmemKind::Write,
                key: k.clone(),
                val: None, // restore: this address was absent at the H boundary.
                prev_val: Some(cur.clone()),
                prev_serial: 0,
            }),
        }
    }
    // addresses present in target but absent in current (re-create at rewind).
    for (k, t) in target.iter() {
        if !current.contains_key(k) {
            ops.push(UmemOp {
                kind: UmemKind::Write,
                key: k.clone(),
                val: Some(t.clone()),
                prev_val: None,
                prev_serial: 0,
            });
        }
    }
    ops
}

// ===========================================================================
// THE PROTOTYPE: snapshot(H) → advance → rewind-via-umem → state == H.
// ===========================================================================
#[test]
fn time_travel_snapshot_advance_rewind_via_umem() {
    // --- world at height H: two cells. ---
    let agent = make_open_cell(1, 1000);
    let target = make_open_cell(2, 50);
    let (agent_id, target_id) = (agent.id(), target.id());
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent).unwrap();
    ledger.insert_cell(target).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero());
    executor.umem_witness_enabled.store(true, Ordering::Relaxed);

    // ============ 1. SNAPSHOT the umem boundary at height H. ============
    let boundary_h = snapshot_boundary(&executor, &ledger);
    // sanity: the boundary records the genesis balances.
    assert_eq!(
        boundary_h.get(&UKey::Balance(agent_id)),
        Some(&UVal::Int(1000))
    );
    assert_eq!(
        boundary_h.get(&UKey::Balance(target_id)),
        Some(&UVal::Int(50))
    );

    // ============ 2. ADVANCE: real executor turns past H. ============
    // turn A: transfer 250 agent → target.
    let turn_a = single_effect_turn(
        agent_id,
        agent_id,
        0,
        Effect::Transfer {
            from: agent_id,
            to: target_id,
            amount: 250,
        },
    );
    assert!(executor.execute(&turn_a, &mut ledger).is_committed());

    // turn B: a second transfer, chain-linked to turn A's receipt (the executor
    // enforces the per-agent receipt chain). Purely executor-driven so nonce/auth
    // stay coherent.
    let mut turn_b = single_effect_turn(
        agent_id,
        agent_id,
        1,
        Effect::Transfer {
            from: agent_id,
            to: target_id,
            amount: 40,
        },
    );
    turn_b.previous_receipt_hash = executor.get_last_receipt_hash(&agent_id);
    let rb = executor.execute(&turn_b, &mut ledger);
    assert!(rb.is_committed(), "turn B must commit: {rb:?}");

    // the world genuinely MOVED: a fresh boundary differs from H.
    let boundary_now = snapshot_boundary(&executor, &ledger);
    assert_ne!(
        boundary_now, boundary_h,
        "advancing must move the umem boundary"
    );
    assert_eq!(
        boundary_now.get(&UKey::Balance(agent_id)),
        Some(&UVal::Int(710)),
        "agent debited across two turns (1000 - 250 - 40)"
    );
    assert_eq!(
        boundary_now.get(&UKey::Balance(target_id)),
        Some(&UVal::Int(340)),
        "target credited across two turns (50 + 250 + 40)"
    );

    // ============ 3. REWIND: restore the umem boundary at H. ============
    let trace = rewind_trace(&boundary_now, &boundary_h);
    assert!(!trace.is_empty(), "rewinding a moved world is a real trace");
    // the rewind trace is a LEGAL memcheck program (the witness discipline).
    assert!(
        disciplined(&trace),
        "the rewind trace must satisfy the memcheck discipline"
    );

    // THE KEYSTONE EQUALITY: folding the rewind trace over the current boundary
    // yields EXACTLY the height-H boundary. This is the SAME `fold` the executor
    // bridge proves forward agreement under — run in the restore direction. No
    // history replay; the boundary IS the state.
    let restored = fold(&boundary_now, &trace);
    assert_eq!(
        restored, boundary_h,
        "rewinding via the umem boundary restores EXACTLY the height-H snapshot"
    );

    // every op's prev claim is the genuine current value (re-walk independently):
    // the rewind is witnessable, not an out-of-band state poke.
    let mut running = boundary_now.clone();
    for op in &trace {
        assert_eq!(
            op.prev_val,
            running.get(&op.key).cloned(),
            "rewind op prev claim must match the running boundary at {:?}",
            op.key
        );
        match &op.val {
            Some(v) => {
                running.insert(op.key.clone(), v.clone());
            }
            None => {
                running.remove(&op.key);
            }
        }
    }
    assert_eq!(running, boundary_h, "independent re-walk reaches H");
}

// ===========================================================================
// Round-trip law: snapshot → snapshot (no advance) → rewind is a NO-OP.
// A boundary restored to itself produces an empty trace and the identity fold.
// ===========================================================================
#[test]
fn rewind_to_self_is_a_noop() {
    let agent = make_open_cell(3, 500);
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent).unwrap();
    let executor = TurnExecutor::new(ComputronCosts::zero());

    let boundary = snapshot_boundary(&executor, &ledger);
    let trace = rewind_trace(&boundary, &boundary);
    assert!(
        trace.is_empty(),
        "rewinding to the same boundary is a no-op"
    );
    assert_eq!(fold(&boundary, &trace), boundary, "identity restore");
}

// ===========================================================================
// REIFY DIRECTION (the seam, CLOSED) — `reify_ledger` is the byte-identical
// inverse of `project_ledger`, re-deriving the dropped commitments from the
// kept planes.
// ===========================================================================

/// THE ROUND-TRIP LAW: `reify_ledger(project_ledger(L)) == L` over a populated
/// ledger in the faithful class (the planes the projection carries losslessly).
/// The dropped `fields_root` / heap_root / leaf caches / ledger Merkle root are
/// RE-DERIVED on reconstruction, not stored — and the rebuilt ledger is
/// `PartialEq`-equal to the original, cell-for-cell.
#[test]
fn reify_ledger_round_trips_a_populated_ledger() {
    // A ledger exercising the carried planes: balances, nonce, fixed fields,
    // overflow user-field map (slot ≥ 16 → fields_root re-derive), a granted
    // capability, custom permissions.
    let mut agent = make_open_cell(7, 1234);
    agent.state.set_field(0, [9u8; 32]);
    agent.state.set_field(3, [4u8; 32]);
    // overflow user-field MAP entries — these drive the dropped `fields_root`.
    agent.state.set_field_ext(16, [1u8; 32]);
    agent.state.set_field_ext(99, [2u8; 32]);
    let target = make_open_cell(8, 77);
    let (agent_id, target_id) = (agent.id(), target.id());
    // a live capability agent → target (contiguous slot 0 — faithful class).
    agent
        .capabilities
        .grant(target_id, dregg_cell::AuthRequired::None);

    let mut ledger = Ledger::new();
    ledger.insert_cell(agent).unwrap();
    ledger.insert_cell(target).unwrap();

    // PROJECT → REIFY → equal.
    let proj = project_ledger(&ledger);
    let mut reified = reify_ledger(&proj).expect("faithful-class ledger reifies");

    // Cell-for-cell byte identity (Cell: PartialEq excludes only the leaf cache,
    // which reify reconstructs dirty exactly as a fresh decode would).
    let orig_agent = ledger.get(&agent_id).unwrap();
    let new_agent = reified.get(&agent_id).unwrap();
    assert_eq!(
        new_agent, orig_agent,
        "reified agent cell is byte-identical (all carried planes + re-derived \
         fields_root)"
    );
    assert_eq!(
        reified.get(&target_id).unwrap(),
        ledger.get(&target_id).unwrap(),
        "reified target cell is byte-identical"
    );

    // The DROPPED fields_root was RE-DERIVED, not stored — it equals the original
    // (which the overflow map genuinely commits).
    assert_eq!(
        new_agent.state.fields_root, orig_agent.state.fields_root,
        "fields_root re-derived from the projected Field(slot≥16) plane"
    );
    assert_ne!(
        new_agent.state.fields_root,
        dregg_cell::state::empty_fields_root(),
        "the populated map's root is non-vacuous (genuinely re-derived)"
    );

    // The DROPPED ledger Merkle root re-materializes lazily and matches.
    assert_eq!(
        reified.root(),
        ledger.root(),
        "the ledger Merkle root re-derives on demand to the original"
    );

    // And the projection of the reified ledger equals the original projection —
    // the round-trip closes the loop at the boundary level too.
    assert_eq!(
        project_ledger(&reified),
        proj,
        "project(reify(project(L))) == project(L)"
    );
}

/// THE TIME-TRAVEL PAYOFF: snapshot(H) → advance (real executor turns) → REIFY
/// the H boundary into a live `Ledger` → it equals the height-H world. This is
/// `reify_cell` finishing the lane the rewind prototype above proved at the
/// projection level: the witnessed boundary lifts back to a byte-restored ledger.
#[test]
fn reify_restores_a_live_ledger_to_height_h() {
    let agent = make_open_cell(9, 500);
    let target = make_open_cell(10, 10);
    let (agent_id, target_id) = (agent.id(), target.id());
    let mut ledger_h = Ledger::new();
    ledger_h.insert_cell(agent).unwrap();
    ledger_h.insert_cell(target).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero());

    // SNAPSHOT the umem boundary at H.
    let boundary_h = snapshot_boundary(&executor, &ledger_h);

    // ADVANCE: a real transfer past H (mutate the live ledger).
    let mut ledger = ledger_h.clone();
    let turn = single_effect_turn(
        agent_id,
        agent_id,
        0,
        Effect::Transfer {
            from: agent_id,
            to: target_id,
            amount: 123,
        },
    );
    assert!(executor.execute(&turn, &mut ledger).is_committed());
    assert_eq!(ledger.get(&agent_id).unwrap().state.balance(), 377);

    // REIFY the H boundary back into a live ledger — the whole-ledger restore.
    let mut restored = reify_ledger(&boundary_h).expect("H boundary reifies");
    assert_eq!(
        restored.get(&agent_id).unwrap(),
        ledger_h.get(&agent_id).unwrap(),
        "reified agent cell == the height-H cell"
    );
    assert_eq!(
        restored.get(&target_id).unwrap(),
        ledger_h.get(&target_id).unwrap(),
        "reified target cell == the height-H cell"
    );
    assert_eq!(
        restored.root(),
        ledger_h.root(),
        "the restored ledger's Merkle root == the height-H root"
    );
}

/// THE HONEST RESIDUAL #1 — a non-empty HEAP is not carried by any `UKey`
/// plane (only its derived `heap_root` is, and its preimage is dropped). reify
/// REFUSES rather than fabricate an empty heap under a non-empty root.
#[test]
fn reify_refuses_heap_not_projected() {
    let mut cell = make_open_cell(11, 100);
    cell.state.set_heap(1, 2, [42u8; 32]); // non-empty heap → non-empty heap_root.
    let id = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();

    let proj = project_ledger(&ledger);
    let err = reify_cell(id, &proj).expect_err("a heap-bearing cell must refuse");
    assert_eq!(err, ReifyError::HeapNotProjected(id));
}

/// THE HONEST RESIDUAL #3/#4 — a REVOKED capability leaves a tombstone and a
/// `next_slot` gap that the live-only `CapSlot` plane drops. reify REFUSES
/// because the reconstructed cap set could not be byte-identical.
#[test]
fn reify_refuses_cap_revocation_gap() {
    let target = make_open_cell(13, 0);
    let target_id = target.id();
    let mut cell = make_open_cell(12, 100);
    // grant two caps (slots 0, 1) then revoke slot 0 → slot 0 tombstoned,
    // next_slot = 2, live caps = {slot 1}. The projection keeps only slot 1, so
    // a faithful reify cannot recover the slot-0 tombstone / next_slot=2.
    cell.capabilities
        .grant(target_id, dregg_cell::AuthRequired::None);
    cell.capabilities
        .grant(target_id, dregg_cell::AuthRequired::None);
    cell.capabilities.revoke(0);
    let id = cell.id();

    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();
    ledger.insert_cell(target).unwrap();

    let proj = project_ledger(&ledger);
    let err = reify_cell(id, &proj).expect_err("a revoked-cap cell must refuse");
    assert_eq!(err, ReifyError::CapNextSlotUnrecoverable(id));
}
