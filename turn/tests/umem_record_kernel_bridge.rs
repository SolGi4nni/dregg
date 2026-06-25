//! THE 3-VERB EXECUTOR BRIDGE — the authoritative `RecordKernelState` projection
//! agrees with the deployed per-map-table representation (the gauntlet anchor).
//!
//! `UNIVERSAL-MAP-ROTATION.md` §2.3: a 3-verb circuit proving against a 50-effect
//! executor has nothing to AGREE with — the differential gauntlets anchor on the
//! executor's shape, and that shape is the universal-map projection. This file is
//! that anchor's differential: a cell's `RecordKernelState` projects into the ONE
//! universal map, the per-domain BOUNDARY roots derived FROM that projection are
//! checked equal to the per-map-table roots the deployed commitment carries
//! (`fields_root` · `heap_root` · the canonical `cap_root`). On agreement the
//! projection IS the authoritative per-effect state representation; a tampered
//! projection moves a derived root and the agreement refuses (non-vacuity).
//!
//! VK-RISK-FREE: a pure projection + boundary derivation over a `Cell`; no
//! descriptor / wire / VK touch; the `umem_witness_enabled` gate is irrelevant
//! here (these are representation functions, not the prover witness).

use std::sync::atomic::Ordering;

use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
use dregg_turn::umem::{
    BoundaryDisagreement, RecordKernelBoundary, UKey, UVal, derive_record_kernel_boundary,
    project_record_kernel_state, record_kernel_boundary_agrees,
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

// ---------------------------------------------------------------------------
// The anchor: a cell exercising all three openable planes (overflow fields,
// heap, live caps) projects and its derived boundary EQUALS the per-map-table
// representation.
// ---------------------------------------------------------------------------
#[test]
fn record_kernel_boundary_agrees_over_all_planes() {
    let mut cell = make_open_cell(1, 1000);

    // FIELD plane (overflow, slot >= STATE_SLOTS=16): the openable fields_map.
    cell.state.set_field_ext(16, [7u8; 32]);
    cell.state.set_field_ext(99, [8u8; 32]);
    // HEAP plane.
    cell.state.set_heap(3, 5, [11u8; 32]);
    cell.state.set_heap(3, 9, [12u8; 32]);
    cell.state.set_heap(7, 1, [13u8; 32]);
    // CAPS plane (live, contiguous from slot 0 — no tombstones).
    let target = make_open_cell(2, 0).id();
    cell.capabilities.grant(target, AuthRequired::None).unwrap();
    cell.capabilities
        .grant(make_open_cell(3, 0).id(), AuthRequired::Signature)
        .unwrap();

    // THE AGREEMENT: the projection's derived boundary == the committed roots.
    let boundary = record_kernel_boundary_agrees(&cell)
        .expect("the RecordKernelState projection must reproduce the per-map-table roots");

    // Spell out the per-map-table representation it agrees with (no tautology:
    // the derivation never read these stored roots).
    assert_eq!(
        boundary.fields_root, cell.state.fields_root,
        "derived fields_root == committed fields_root"
    );
    assert_eq!(
        boundary.heap_root, cell.state.heap_root,
        "derived heap_root == committed heap_root"
    );
    assert_eq!(
        boundary.cap_root,
        dregg_cell::compute_canonical_capability_root_felt(&cell.capabilities),
        "derived cap_root == canonical capability root felt (the EffectVM cap_root column)"
    );
}

// ---------------------------------------------------------------------------
// The empty cell: every plane is empty, the derived boundary is the per-cell
// empty-root constants (the legacy-cell no-op the rotation rides).
// ---------------------------------------------------------------------------
#[test]
fn record_kernel_boundary_agrees_for_empty_cell() {
    let cell = make_open_cell(4, 0);
    let boundary = record_kernel_boundary_agrees(&cell).expect("empty cell agrees");
    assert_eq!(boundary.fields_root, cell.state.fields_root);
    assert_eq!(boundary.heap_root, cell.state.heap_root);
    assert_eq!(
        boundary.cap_root,
        dregg_cell::compute_canonical_capability_root_felt(&cell.capabilities)
    );
}

// ---------------------------------------------------------------------------
// NON-VACUITY: a tampered projection moves a derived root, so the boundary it
// reports no longer equals the committed root. (The agreement is a real check,
// not an `== self`.)
// ---------------------------------------------------------------------------
#[test]
fn tampered_projection_moves_the_derived_boundary() {
    let mut cell = make_open_cell(5, 100);
    cell.state.set_field_ext(20, [1u8; 32]);
    cell.state.set_heap(1, 1, [2u8; 32]);

    let honest = project_record_kernel_state(&cell);
    let honest_boundary = derive_record_kernel_boundary(&honest, cell.id());
    assert_eq!(honest_boundary.heap_root, cell.state.heap_root);
    assert_eq!(honest_boundary.fields_root, cell.state.fields_root);

    // Tamper the projected HEAP cell value: the derived heap_root must move and
    // no longer match the cell's committed heap_root.
    let mut tampered = honest.clone();
    let hk = UKey::Heap {
        cell: cell.id(),
        collection: 1,
        key: 1,
    };
    tampered.insert(hk, UVal::Bytes32([9u8; 32]));
    let tampered_boundary = derive_record_kernel_boundary(&tampered, cell.id());
    assert_ne!(
        tampered_boundary.heap_root, cell.state.heap_root,
        "a tampered Heap cell must move the derived heap_root off the committed root"
    );
    assert_ne!(
        tampered_boundary.heap_root, honest_boundary.heap_root,
        "the tamper genuinely moved the derived root"
    );

    // Tamper a projected overflow FIELD cell: the derived fields_root must move.
    let mut tampered_f = honest.clone();
    let fk = UKey::Field {
        cell: cell.id(),
        slot: 20,
    };
    tampered_f.insert(fk, UVal::Bytes32([0xAAu8; 32]));
    let tampered_f_boundary = derive_record_kernel_boundary(&tampered_f, cell.id());
    assert_ne!(
        tampered_f_boundary.fields_root, cell.state.fields_root,
        "a tampered Field(slot>=16) cell must move the derived fields_root"
    );
}

// ---------------------------------------------------------------------------
// The register-file fields (slot < STATE_SLOTS) are NOT part of fields_root:
// changing a fixed slot leaves the derived fields_root where the empty/overflow
// map puts it (the Field plane split at STATE_SLOTS is honored).
// ---------------------------------------------------------------------------
#[test]
fn fixed_slots_are_not_in_fields_root() {
    let mut cell = make_open_cell(6, 0);
    cell.state.set_field(0, [42u8; 32]);
    cell.state.set_field(15, [43u8; 32]);
    // no overflow entries → fields_root is the empty constant, and the bridge agrees.
    let boundary = record_kernel_boundary_agrees(&cell).expect("fixed-slot writes agree");
    assert_eq!(boundary.fields_root, dregg_cell::state::empty_fields_root());
    assert_eq!(boundary.fields_root, cell.state.fields_root);
}

// ---------------------------------------------------------------------------
// REVOKED CELLS ARE NOW FAITHFUL — a revoke leaves a ghost ZERO leaf in the
// deployed cap_root (the cap-crown reconciliation); the `CapTombstone` plane
// re-derives it, so the projection reproduces the committed root even after a
// revoke (the former reify residual #3, closed here for the boundary).
// ---------------------------------------------------------------------------
#[test]
fn record_kernel_boundary_agrees_over_revoked_cell() {
    let mut cell = make_open_cell(7, 500);
    let t0 = make_open_cell(70, 0).id();
    let t1 = make_open_cell(71, 0).id();
    let t2 = make_open_cell(72, 0).id();
    // grant three caps (slots 0,1,2), then revoke slot 1 → live {0,2}, ghost {1}.
    cell.capabilities.grant(t0, AuthRequired::None).unwrap();
    let slot1 = cell.capabilities.grant(t1, AuthRequired::None).unwrap();
    cell.capabilities.grant(t2, AuthRequired::None).unwrap();
    let root_before_revoke =
        dregg_cell::compute_canonical_capability_root_felt(&cell.capabilities);
    assert!(cell.capabilities.revoke(slot1), "the slot was live and is revoked");
    let committed = dregg_cell::compute_canonical_capability_root_felt(&cell.capabilities);

    // NON-VACUITY (the revoke MOVED cap_root): the ghost leaf changes the root.
    assert_ne!(
        committed, root_before_revoke,
        "a revoke moves the canonical cap_root (the ghost leaf is load-bearing)"
    );

    // THE AGREEMENT now covers the revoked cell: the projection's derived cap_root
    // (live `CapSlot` leaves PLUS the `CapTombstone` ghosts) reproduces the
    // committed root the deployed commitment carries.
    let boundary = record_kernel_boundary_agrees(&cell)
        .expect("a revoked cell's projection must now reproduce the deployed cap_root");
    assert_eq!(
        boundary.cap_root, committed,
        "derived cap_root == committed (the tombstone ghosts are folded in)"
    );

    // NON-VACUITY (the tombstone plane is LOAD-BEARING): drop the `CapTombstone`
    // cells from the projection and the derived cap_root no longer matches the
    // committed root — it falls back to the tombstone-free fold (the exact reify
    // residual-#3 gap this plane closes).
    let proj = project_record_kernel_state(&cell);
    assert!(
        proj.keys()
            .any(|k| matches!(k, UKey::CapTombstone { slot: 1, .. })),
        "the projection carries the revoked slot's tombstone cell"
    );
    let mut no_tombstones = proj.clone();
    no_tombstones.retain(|k, _| !matches!(k, UKey::CapTombstone { .. }));
    let derived_without = derive_record_kernel_boundary(&no_tombstones, cell.id());
    assert_ne!(
        derived_without.cap_root, committed,
        "without the tombstone plane the derived cap_root omits the ghost — the residual-#3 gap"
    );
    assert_ne!(
        derived_without.cap_root, boundary.cap_root,
        "the tombstone plane genuinely moved the derived root"
    );
}

// ===========================================================================
// THE LIVE-EXECUTOR ANCHOR — the bridge over a RecordKernelState the REAL
// executor produced (the gauntlet shape the 3-verb circuit agrees with).
// ===========================================================================

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

/// Assert every present cell of a ledger passes the bridge agreement (the
/// gauntlet anchor over the whole after-state).
fn assert_ledger_boundary_agrees(ledger: &Ledger) {
    for (id, cell) in ledger.iter() {
        let r: Result<RecordKernelBoundary, BoundaryDisagreement> =
            record_kernel_boundary_agrees(cell);
        assert!(
            r.is_ok(),
            "cell {id:?} RecordKernelState projection must agree with its per-map-table roots: {:?}",
            r.err()
        );
    }
}

#[test]
fn live_executor_after_state_agrees_three_verbs() {
    // agent grants a cap to target (caps plane), then a turn writes a heap
    // field + an overflow field + a transfer — the after-cells' RecordKernelState
    // projections must all agree with their per-map-table roots.
    let agent = make_open_cell(8, 1000);
    let target = make_open_cell(9, 10);
    let (agent_id, target_id) = (agent.id(), target.id());

    let mut agent_with_cap = agent;
    agent_with_cap
        .capabilities
        .grant(target_id, AuthRequired::None)
        .unwrap();
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent_with_cap).unwrap();
    ledger.insert_cell(target).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero());
    // The gate is irrelevant to the bridge (we read the committed after-cells),
    // but flip it on to prove the authoritative representation coexists with the
    // (recursion-gated-off) witness lane untouched.
    executor.umem_witness_enabled.store(true, Ordering::Relaxed);

    let turn = multi_effect_turn(
        agent_id,
        target_id,
        0,
        vec![
            Effect::Transfer {
                from: agent_id,
                to: target_id,
                amount: 7,
            },
            // an overflow field (slot >= 16 → fields_map / fields_root).
            Effect::SetField {
                cell: target_id,
                index: 42,
                value: [5u8; 32],
            },
            // a fixed field (slot < 16 → register file, not fields_root).
            Effect::SetField {
                cell: target_id,
                index: 2,
                value: [6u8; 32],
            },
        ],
    );
    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed(), "turn must commit: {result:?}");

    // The after-state the executor produced: every cell's RecordKernelState
    // projection reproduces its committed per-map-table roots.
    assert_ledger_boundary_agrees(&ledger);

    // And the specific overflow write moved the target's fields_root, which the
    // projection faithfully reproduces.
    let target_after = ledger.get(&target_id).expect("target present");
    assert_eq!(
        target_after.state.get_field_ext(42),
        Some([5u8; 32]),
        "overflow field landed in fields_map"
    );
    let boundary = record_kernel_boundary_agrees(target_after).expect("target agrees");
    assert_eq!(boundary.fields_root, target_after.state.fields_root);
}
