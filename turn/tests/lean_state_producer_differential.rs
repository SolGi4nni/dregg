//! lean_state_producer_differential.rs — THE SWAP differential: prove the VERIFIED Lean executor
//! can BE the state PRODUCER.
//!
//! The headline gap (`marshal.rs`: "the biggest gap") was the missing `WireState → cell::Ledger`
//! extractor: the verified `dregg_exec_full_forest_auth` / `execFullForestG` produces a full
//! post-state, but the node threw it away and committed the LEGACY Rust `TurnExecutor`'s ledger
//! instead. `dregg_turn::lean_apply::wire_state_to_ledger` now reconstitutes a `cell::Ledger` from
//! the verified executor's produced `WireState`.
//!
//! This test runs a representative turn (a Transfer, then a SetField) through BOTH:
//!   * the verified Lean FFI executor → produced `WireState` → reconstituted `Ledger`
//!     (`lean_apply::execute_via_lean`), and
//!   * the legacy Rust `TurnExecutor::execute` → its `Ledger`,
//! and asserts the two ledgers AGREE — same balances, nonces, state fields, AND `.root()`. That
//! agreement is the differential proving the Lean executor can replace the Rust state producer.
//!
//! A divergence here is a REAL finding (a marshaller gap or a genuine semantic difference), surfaced
//! by the assertion — never papered over. Requires the linked Lean archive (`lean-shadow` feature +
//! `lean_available()`); when the archive is absent the test self-skips (it cannot compare).

#![cfg(feature = "lean-shadow")]

use std::collections::HashMap;

use dregg_cell::state::FieldElement;
use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
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
        // REQUIRED by the wire marshaller (the verified `admissible` clock leg checks it). The
        // diagnostic host clock is 0, so any future expiry admits.
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

/// Two open cells (A=balance 100, B=balance 5); A is the agent (sender).
fn two_cell_ledger() -> (Ledger, CellId, CellId) {
    let a = make_open_cell(1, 100);
    let b = make_open_cell(2, 5);
    let a_id = a.id();
    let b_id = b.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(a).unwrap();
    ledger.insert_cell(b).unwrap();
    (ledger, a_id, b_id)
}

/// Compare two ledgers cell-by-cell (balance + nonce + the 8 state fields) AND on `.root()`.
/// Returns Ok(()) on full agreement or Err(description) on the first divergence.
fn ledgers_agree(rust: &mut Ledger, lean: &mut Ledger, ids: &[CellId]) -> Result<(), String> {
    for id in ids {
        let r = rust
            .get(id)
            .ok_or_else(|| format!("cell {id:?} missing from RUST ledger"))?;
        let l = lean
            .get(id)
            .ok_or_else(|| format!("cell {id:?} missing from LEAN ledger"))?;
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
    }
    let rr = rust.root();
    let lr = lean.root();
    if rr != lr {
        return Err(format!("ROOT divergence: rust={rr:?} lean={lr:?}"));
    }
    Ok(())
}

/// The core differential: run `turn` through the legacy Rust executor and through the verified Lean
/// executor (reconstituting its produced post-state), and assert both ledgers agree.
fn run_differential(pre: Ledger, turn: Turn, ids: &[CellId]) {
    // (1) Legacy Rust producer.
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let mut rust_ledger = pre.clone();
    let rust_result = executor.execute(&turn, &mut rust_ledger);
    assert!(
        rust_result.is_committed(),
        "legacy Rust executor did not commit the turn: {rust_result:?}"
    );

    // (2) Verified Lean producer: install the post-state it produces.
    let host = ShadowHostCtx::diag();
    let (mut lean_ledger, lean_committed) = match execute_via_lean(&turn, &pre, &host) {
        Ok(x) => x,
        Err(lean_apply::ExtractError::Ineligible) => {
            // The forest had an effect with no wire arm — cannot compare (not a divergence, a GAP).
            panic!(
                "turn was Lean-ineligible (a marshaller gap); cannot run the state-producer differential"
            );
        }
        Err(e) => panic!("Lean state-producer path failed: {e}"),
    };

    assert!(
        lean_committed,
        "verified Lean executor did not commit a turn the Rust executor committed (commit-bit divergence)"
    );

    // (3) The two PRODUCERS must agree on the full post-state.
    match ledgers_agree(&mut rust_ledger, &mut lean_ledger, ids) {
        Ok(()) => {}
        Err(why) => {
            panic!("STATE-PRODUCER DIVERGENCE — Rust ledger ≠ Lean-reconstituted ledger: {why}")
        }
    }
}

#[test]
fn transfer_lean_produced_ledger_agrees_with_rust() {
    if !dregg_lean_ffi::lean_available() {
        eprintln!("SKIP: Lean archive not linked (lean_available()==false)");
        return;
    }
    let (pre, a_id, b_id) = two_cell_ledger();
    // Agent A (nonce 0) transfers 30 to B. Open permissions + Unchecked → authority by ownership.
    let turn = single_effect_turn(
        a_id,
        a_id,
        0,
        Effect::Transfer {
            from: a_id,
            to: b_id,
            amount: 30,
        },
    );
    run_differential(pre, turn, &[a_id, b_id]);
}

#[test]
fn setfield_lean_produced_ledger_agrees_with_rust() {
    if !dregg_lean_ffi::lean_available() {
        eprintln!("SKIP: Lean archive not linked (lean_available()==false)");
        return;
    }
    let (pre, a_id, b_id) = two_cell_ledger();
    // Agent A sets its own state slot 6 ("target") to 42 — a second effect TYPE through the
    // same producer path, exercising the field reconstitution (not just balance/nonce).
    let turn = single_effect_turn(
        a_id,
        a_id,
        0,
        Effect::SetField {
            cell: a_id,
            index: 6,
            value: field_from_u64(42),
        },
    );
    run_differential(pre, turn, &[a_id, b_id]);
}
