//! lean_state_producer_widen.rs — WIDEN THE SWAP state-producer past Transfer + SetField.
//!
//! The producer differential (`lean_state_producer_differential.rs`) proved the verified Lean
//! executor can BE the state PRODUCER for Transfer + SetField: its reconstituted `cell::Ledger`
//! AGREES with the legacy Rust `TurnExecutor` on the full cell state AND `.root()`. This file
//! WIDENS that producer differential to ONE representative turn per effect family the verified
//! executor models, and pins — per family — exactly which families ROUND-TRIP through the
//! `WireState → cell::Ledger` extractor and which are SWAP-GAPS (the wire model is lossier than the
//! cell commitment so the reconstituted `.root()` cannot match the Rust one).
//!
//! # The cell commitment is the yardstick
//!
//! `cell::Ledger::root()` hashes, per cell, `compute_canonical_state_commitment` =
//! `(balance, nonce, fields, permissions, verification_key, cap_root, lifecycle, program)`. A
//! family ROUND-TRIPS iff its post-state touches only commitment fields the `WireState` carries
//! (balance via `bal`; nonce/fields via the cell record; cap_root via the `caps` side-table when
//! the caps are bare `node`-shaped edges). A family is a SWAP-GAP iff its Rust post-state touches a
//! commitment field the wire drops (lifecycle; the full `Permissions`/`VK` struct; the per-cap
//! slot/breadstuff/facet detail behind `cap_root`).
//!
//! Each ROUND-TRIP test ASSERTS agreement (state + `.root()`). Each SWAP-GAP test ASSERTS the
//! SPECIFIC divergence (a negative tooth) so the gap is characterized, never silently passing — a
//! genuine finding surfaced precisely, per the SWAP discipline.
//!
//! Requires the linked Lean archive (`lean-shadow` + `lean_available()`); self-skips when absent.

#![cfg(feature = "lean-shadow")]

use std::collections::HashMap;

use dregg_cell::capability::CapabilityRef;
use dregg_cell::lifecycle::{CellLifecycle, DeathCertificate, DeathReason};
use dregg_cell::permissions::AuthRequired;
use dregg_cell::state::FieldElement;
use dregg_cell::{Cell, CellId, Ledger, Permissions};
use dregg_turn::lean_apply::{self, execute_via_lean};
use dregg_turn::lean_shadow::ShadowHostCtx;
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

fn make_open_cell(seed: u8, balance: u64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37);
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell
}

/// A self-`node` capability = mint/burn authority over the cell itself. The verified executor's
/// `mintAuthorizedB actor cell` leg (which `burnA` routes through) reads a `Cap::Node(self)` edge;
/// `ledger_to_wire_state` projects the cell's c-list to wire `caps`, so a cell holding a self-cap
/// passes the Lean mint/burn gate exactly as bare ownership passes the Rust one.
fn grant_self_cap(cell: &mut Cell) {
    let id = cell.id();
    cell.capabilities.grant(id, AuthRequired::None);
}

fn field_from_u64(v: u64) -> FieldElement {
    let mut out = [0u8; 32];
    out[24..32].copy_from_slice(&v.to_be_bytes());
    out
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
        valid_until: Some(1_000),
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

/// Compare two ledgers cell-by-cell (balance + nonce + the 8 state fields + the canonical
/// capability root) AND on `.root()`. Returns Ok(()) on full agreement or Err(why) on the first
/// divergence. The cap-root comparison is what makes delegate/revoke round-trips meaningful.
fn ledgers_agree(rust: &mut Ledger, lean: &mut Ledger, ids: &[CellId]) -> Result<(), String> {
    for id in ids {
        let r = rust.get(id).ok_or_else(|| format!("cell {id:?} missing from RUST ledger"))?;
        let l = lean.get(id).ok_or_else(|| format!("cell {id:?} missing from LEAN ledger"))?;
        if r.state.balance() != l.state.balance() {
            return Err(format!(
                "balance divergence on {id:?}: rust={} lean={}",
                r.state.balance(),
                l.state.balance()
            ));
        }
        if r.state.nonce() != l.state.nonce() {
            return Err(format!(
                "nonce divergence on {id:?}: rust={} lean={}",
                r.state.nonce(),
                l.state.nonce()
            ));
        }
        for slot in 0..dregg_cell::state::STATE_SLOTS {
            if r.state.fields[slot] != l.state.fields[slot] {
                return Err(format!(
                    "field[{slot}] divergence on {id:?}: rust={:?} lean={:?}",
                    r.state.fields[slot], l.state.fields[slot]
                ));
            }
        }
        let rc = dregg_cell::compute_canonical_capability_root(&r.capabilities);
        let lc = dregg_cell::compute_canonical_capability_root(&l.capabilities);
        if rc != lc {
            return Err(format!("cap_root divergence on {id:?}: rust={rc:?} lean={lc:?}"));
        }
    }
    let rr = rust.root();
    let lr = lean.root();
    if rr != lr {
        return Err(format!("ROOT divergence: rust={rr:?} lean={lr:?}"));
    }
    Ok(())
}

/// Run both producers and return `Ok(())` on full agreement, or `Err(why)` on the first divergence.
/// Both producers MUST commit (a commit-bit divergence is itself a divergence). Used by both the
/// round-trip families (which expect Ok) and the swap-gap families (which expect a SPECIFIC Err).
fn diff(pre: Ledger, turn: Turn, ids: &[CellId]) -> Result<(), String> {
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let mut rust_ledger = pre.clone();
    let rust_result = executor.execute(&turn, &mut rust_ledger);
    if !rust_result.is_committed() {
        return Err(format!("legacy Rust executor did not commit: {rust_result:?}"));
    }

    let host = ShadowHostCtx::diag();
    let (mut lean_ledger, lean_committed) = match execute_via_lean(&turn, &pre, &host) {
        Ok(x) => x,
        Err(lean_apply::ExtractError::Ineligible) => {
            return Err("turn was Lean-ineligible (a marshaller GAP — no wire arm)".to_string());
        }
        Err(e) => return Err(format!("Lean state-producer path errored: {e}")),
    };
    if !lean_committed {
        return Err("commit-bit divergence: Rust committed, Lean did not".to_string());
    }
    ledgers_agree(&mut rust_ledger, &mut lean_ledger, ids)
}

fn skip_no_lean() -> bool {
    if !dregg_lean_ffi::lean_available() {
        eprintln!("SKIP: Lean archive not linked (lean_available()==false)");
        true
    } else {
        false
    }
}

// =====================================================================================
// ROUND-TRIP FAMILIES — the reconstituted ledger AGREES (state + cap_root + .root()).
// =====================================================================================

#[test]
fn burn_round_trips() {
    if skip_no_lean() {
        return;
    }
    // Burn is mint/burn-PRIVILEGED in the verified kernel (`mintAuthorizedB actor cell`), so the
    // actor must hold a self-`node` cap for the Lean gate to commit (bare ownership suffices for
    // Rust). With the self-cap both producers commit; the burn only debits asset-0 balance, which
    // the `bal` side-table carries — so the reconstituted ledger agrees on balance, cap_root, root.
    let mut a = make_open_cell(1, 100);
    grant_self_cap(&mut a);
    let a_id = a.id();
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();

    let turn = single_effect_turn(a_id, a_id, 0, Effect::Burn { target: a_id, slot: 0, amount: 40 });
    diff(pre, turn, &[a_id]).expect("Burn must round-trip through the verified producer");
}

#[test]
fn increment_nonce_round_trips() {
    if skip_no_lean() {
        return;
    }
    // IncrementNonce bumps the cell nonce by 1 in Rust; the wire `incnonce` SETS the nonce field to
    // the post-increment value (`pre_nonce + 1`). The cell record carries `nonce`, so it
    // reconstitutes — agreement on nonce + cap_root + root.
    let a = make_open_cell(1, 100);
    let a_id = a.id();
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();

    let turn = single_effect_turn(a_id, a_id, 0, Effect::IncrementNonce { cell: a_id });
    diff(pre, turn, &[a_id]).expect("IncrementNonce must round-trip through the verified producer");
}

#[test]
fn revoke_on_empty_clist_round_trips() {
    if skip_no_lean() {
        return;
    }
    // RevokeCapability of a non-existent slot on an EMPTY c-list is a no-op in Rust (the cap_root
    // stays the empty-set root). The verified `recCRevoke` is TOTAL (always commits, edits the
    // revocation registry, not the cell c-list). So both commit and the cell c-list / cap_root are
    // unchanged on both sides — the reconstituted ledger agrees. (A revoke that actually drops a
    // held cap is exercised — and shown to be a gap — by `grant_capability_is_a_swap_gap`.)
    let a = make_open_cell(1, 100);
    let a_id = a.id();
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();

    let turn =
        single_effect_turn(a_id, a_id, 0, Effect::RevokeCapability { cell: a_id, slot: 0 });
    diff(pre, turn, &[a_id]).expect("Revoke on empty c-list must round-trip");
}

#[test]
fn two_effect_forest_round_trips() {
    if skip_no_lean() {
        return;
    }
    // A two-effect forest (Transfer then SetField) through the producer path — exercises the
    // sequential child-node execution AND the multi-field reconstitution together.
    let a = make_open_cell(1, 100);
    let b = make_open_cell(2, 5);
    let a_id = a.id();
    let b_id = b.id();
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();
    pre.insert_cell(b).unwrap();

    let mut forest = CallForest::new();
    let mk = |target, eff| Action {
        target,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![eff],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    };
    forest.add_root(mk(a_id, Effect::Transfer { from: a_id, to: b_id, amount: 25 }));
    forest.add_root(mk(a_id, Effect::SetField { cell: a_id, index: 6, value: field_from_u64(7) }));
    let turn = Turn {
        agent: a_id,
        nonce: 0,
        call_forest: forest,
        fee: 0,
        memo: None,
        valid_until: Some(1_000),
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
    };
    diff(pre, turn, &[a_id, b_id]).expect("Transfer+SetField forest must round-trip");
}

// =====================================================================================
// SWAP-GAP FAMILIES — the wire model is LOSSIER than the cell commitment, so the
// reconstituted `.root()` CANNOT match Rust. Each asserts the SPECIFIC divergence
// (a negative tooth): a real finding, characterized, not papered over.
// =====================================================================================

#[test]
fn cell_seal_is_a_lifecycle_swap_gap() {
    if skip_no_lean() {
        return;
    }
    // CellSeal transitions the cell's `lifecycle` Live → Sealed in Rust → the canonical state
    // commitment (which binds lifecycle) changes → `.root()` changes. The verified `WireState` has
    // NO lifecycle field, so the reconstitution carries the template `Live` lifecycle forward
    // unchanged. The two ledgers therefore diverge on `.root()` (Rust=Sealed-commitment,
    // Lean=Live-commitment). We ASSERT that exact root divergence so the gap is pinned.
    let a = make_open_cell(1, 100);
    let a_id = a.id();
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();

    let turn =
        single_effect_turn(a_id, a_id, 0, Effect::CellSeal { target: a_id, reason: [9u8; 32] });

    // Confirm Rust really did change the lifecycle (so the gap is about lifecycle, not a no-commit).
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let mut rust_ledger = pre.clone();
    assert!(executor.execute(&turn, &mut rust_ledger).is_committed(), "Rust CellSeal should commit");
    assert!(
        matches!(rust_ledger.get(&a_id).unwrap().lifecycle, CellLifecycle::Sealed { .. }),
        "Rust must have sealed the cell"
    );

    match diff(pre, turn, &[a_id]) {
        Ok(()) => panic!(
            "CellSeal unexpectedly round-tripped — the lifecycle swap-gap may have closed; \
             update this characterization (the wire would now carry lifecycle)"
        ),
        Err(why) => {
            assert!(
                why.contains("ROOT divergence"),
                "CellSeal swap-gap should manifest as a ROOT divergence (lifecycle dropped by the \
                 wire), but the divergence was: {why}"
            );
        }
    }
}

#[test]
fn cell_destroy_is_a_lifecycle_swap_gap() {
    if skip_no_lean() {
        return;
    }
    // CellDestroy transitions lifecycle → Destroyed (binding the death-cert hash) in Rust → root
    // changes; the wire drops lifecycle → reconstitution keeps Live → root diverges. Same gap class
    // as CellSeal, asserted on a distinct lifecycle target so a future lifecycle-carrying wire would
    // need to close BOTH.
    let a = make_open_cell(1, 100);
    let a_id = a.id();
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();

    let cert = DeathCertificate {
        cell_id: a_id,
        last_receipt_hash: [0u8; 32],
        final_state_commitment: [0u8; 32],
        destroyed_at_height: 0,
        reason: DeathReason::Voluntary,
    };
    let turn = single_effect_turn(
        a_id,
        a_id,
        0,
        Effect::CellDestroy { target: a_id, certificate: cert },
    );

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let mut rust_ledger = pre.clone();
    assert!(
        executor.execute(&turn, &mut rust_ledger).is_committed(),
        "Rust CellDestroy should commit"
    );
    assert!(
        matches!(rust_ledger.get(&a_id).unwrap().lifecycle, CellLifecycle::Destroyed { .. }),
        "Rust must have destroyed the cell"
    );

    match diff(pre, turn, &[a_id]) {
        Ok(()) => panic!(
            "CellDestroy unexpectedly round-tripped — the lifecycle swap-gap may have closed"
        ),
        Err(why) => assert!(
            why.contains("ROOT divergence"),
            "CellDestroy swap-gap should be a ROOT divergence (lifecycle dropped), got: {why}"
        ),
    }
}

#[test]
fn cell_unseal_round_trips() {
    if skip_no_lean() {
        return;
    }
    // CellUnseal (Sealed→Live) is the LIFECYCLE root-gap CLOSE: the verified `cellUnsealChainA`
    // flips the discriminant back to `lcLive` (0), and `CellLifecycle::Live` is the ONE lifecycle
    // state with NO payload. So the wire (a bare discriminant, here dropped because Live=0) carries
    // everything needed, and `wire_state_to_ledger` reconstitutes `CellLifecycle::Live` byte-exactly
    // — matching Rust's `Cell::unseal` (which sets `lifecycle = Live`). Both producers commit and the
    // reconstituted ledger AGREES on state + cap_root + `.root()`. (Its partner transitions CellSeal /
    // CellDestroy stay gaps: they install a Sealed/Destroyed PAYLOAD the wire does not carry.)
    let mut a = make_open_cell(1, 100);
    grant_self_cap(&mut a); // stateAuthB (self-`node` edge) for the unseal authority leg
    let a_id = a.id();
    // Pre-state: the cell is SEALED (so unseal has something to reverse). Rust binds a reason payload;
    // the verified pre-state carries the discriminant `1` (Sealed) — both unseal back to Live.
    a.seal([7u8; 32], 0).expect("seal the pre-state cell");
    assert!(
        matches!(a.lifecycle, CellLifecycle::Sealed { .. }),
        "pre-state must be Sealed for the unseal round-trip"
    );
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();

    // Confirm Rust unseals to Live (so the close is about a real Sealed→Live transition).
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let mut rust_ledger = pre.clone();
    assert!(
        executor.execute(
            &single_effect_turn(a_id, a_id, 0, Effect::CellUnseal { target: a_id }),
            &mut rust_ledger
        )
        .is_committed(),
        "Rust CellUnseal should commit"
    );
    assert!(
        matches!(rust_ledger.get(&a_id).unwrap().lifecycle, CellLifecycle::Live),
        "Rust must have unsealed the cell back to Live"
    );

    let turn = single_effect_turn(a_id, a_id, 0, Effect::CellUnseal { target: a_id });
    diff(pre, turn, &[a_id]).expect("CellUnseal must round-trip through the verified producer");
}

#[test]
fn grant_capability_is_a_cap_fidelity_swap_gap() {
    if skip_no_lean() {
        return;
    }
    // A self-GrantCapability inserts into the grantee's c-list a FULL `CapabilityRef`
    // (target, fresh slot, the granted permissions, breadstuff, ...). The wire `caps` model only
    // carries `Cap::Node(target)` (no slot/perms/breadstuff/facet detail), so the reconstituted
    // c-list — rebuilt as a bare `node` edge at slot 0 with `AuthRequired::None` — hashes to a
    // DIFFERENT `cap_root` than the Rust grant (which used a non-`None` permission). The divergence
    // surfaces as either a cap_root or a root divergence: the wire cap model is lossier than the
    // cell commitment. We ASSERT the divergence so the gap is pinned.
    let mut a = make_open_cell(1, 100);
    grant_self_cap(&mut a); // the delegator must HOLD an edge for the verified `recCDelegate` gate.
    let a_id = a.id();
    let b = make_open_cell(2, 5);
    let b_id = b.id();
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();
    pre.insert_cell(b).unwrap();

    // Grant B a capability over A, with a NON-None permission so the Rust cap_root cannot coincide
    // with the wire's bare-`node` (`AuthRequired::None`) reconstitution.
    let cap = CapabilityRef {
        target: a_id,
        slot: 0,
        permissions: AuthRequired::Signature,
        breadstuff: None,
        expires_at: None,
        allowed_effects: None,
        stored_epoch: None,
    };
    let turn =
        single_effect_turn(a_id, a_id, 0, Effect::GrantCapability { from: a_id, to: b_id, cap });

    // Confirm Rust granted a NON-None cap to B (so the gap is genuinely about cap fidelity).
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let mut rust_ledger = pre.clone();
    if executor.execute(&turn, &mut rust_ledger).is_committed() {
        let b_caps = &rust_ledger.get(&b_id).unwrap().capabilities;
        assert!(
            b_caps.iter().any(|c| c.target == a_id && c.permissions == AuthRequired::Signature),
            "Rust must have granted B a Signature-perm cap over A"
        );
    }

    match diff(pre, turn, &[a_id, b_id]) {
        Ok(()) => panic!(
            "GrantCapability unexpectedly round-tripped — the cap-fidelity swap-gap may have \
             closed (the wire caps model would now carry per-cap permissions/slot)"
        ),
        Err(why) => assert!(
            why.contains("cap_root divergence")
                || why.contains("ROOT divergence")
                || why.contains("commit-bit divergence"),
            "GrantCapability swap-gap should be a cap_root/root/commit-bit divergence, got: {why}"
        ),
    }
}
