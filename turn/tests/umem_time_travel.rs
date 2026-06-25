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
//! THE NAMED SEAM (`reify_seam`): materializing a `UProjection` back into a live
//! byte-identical `Ledger` awaits a `reify_cell` inverse of `project_cell`, because
//! the projection deliberately DROPS derived commitments (the ledger Merkle root,
//! `fields_root`) and per-window metering — documented non-cells in
//! `turn/src/umem.rs`. Those are RECOMPUTED on reconstruction, so the seam is a
//! WIRE (re-derive the dropped commitments from the restored cell planes), not a
//! hole: the rewind GUARANTEE already lives complete at the projection+op-trace
//! level (proven here) and the boundary↔committed-root binding is proven in Lean.
//! `reify_cell` is the lane-finisher that lifts the witnessed boundary back to a
//! byte-restored `Ledger`. The test structure-prototypes reify for the planes the
//! projection carries (balances) and asserts the rewound boundary, naming the gap
//! precisely.

use std::sync::atomic::Ordering;

use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
use dregg_turn::umem::{
    UKey, UProjection, UVal, UmemKind, UmemOp, disciplined, fold, project_executor_state,
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
// REIFY DIRECTION (structure-prototype) — restore a boundary back into a live
// `Ledger` for the planes the projection carries losslessly (balances).
//
// THE NAMED SEAM (`reify_seam`): a full byte-identical `Ledger` restore from a
// `UProjection` alone awaits a `reify_cell` inverse of `project_cell`. The
// projection DROPS derived commitments (ledger Merkle root, `fields_root`) and
// per-window metering by design (see `turn/src/umem.rs` "Named exceptions"); those
// are RECOMPUTED on reconstruction, not stored in the boundary. So this prototype
// reifies the carried planes (balance) and asserts the live ledger matches the H
// boundary on them; the keystone closes the remaining planes.
// ===========================================================================
#[test]
fn reify_seam_balance_plane_restores_from_boundary() {
    let agent = make_open_cell(4, 800);
    let target = make_open_cell(5, 20);
    let (agent_id, target_id) = (agent.id(), target.id());
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent).unwrap();
    ledger.insert_cell(target).unwrap();
    let executor = TurnExecutor::new(ComputronCosts::zero());

    // snapshot H, advance, then reify the balance plane back from the H boundary.
    let boundary_h = snapshot_boundary(&executor, &ledger);
    let turn = single_effect_turn(
        agent_id,
        agent_id,
        0,
        Effect::Transfer {
            from: agent_id,
            to: target_id,
            amount: 100,
        },
    );
    assert!(executor.execute(&turn, &mut ledger).is_committed());
    assert_eq!(ledger.get(&agent_id).unwrap().state.balance(), 700);

    // REIFY the balance plane from the H boundary onto the live ledger.
    for (k, v) in boundary_h.iter() {
        if let (UKey::Balance(id), UVal::Int(bal)) = (k, v) {
            // restore the balance the boundary recorded at H.
            let mut c = ledger.get(id).cloned().unwrap();
            c.state.set_balance(*bal);
            ledger.remove(id);
            ledger.insert_cell(c).unwrap();
        }
    }
    // the live ledger's balance plane now matches the H boundary (the carried plane
    // round-trips). Full-cell reify (derived roots, all planes) is the seam.
    assert_eq!(
        ledger.get(&agent_id).unwrap().state.balance(),
        800,
        "agent balance reified back to the H boundary"
    );
    assert_eq!(
        ledger.get(&target_id).unwrap().state.balance(),
        20,
        "target balance reified back to the H boundary"
    );
}
