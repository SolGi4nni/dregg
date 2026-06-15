//! lean_producer_mode.rs — THE SWAP node-level producer-mode test.
//!
//! This is the NODE side of the authority inversion: the node's commit path
//! (`blocklace_sync::execute_finalized_turn`), when `lean_producer_enabled` is set
//! (`DREGG_LEAN_PRODUCER=1`), routes through `dregg_turn::lean_apply::produce_via_lean`, which makes
//! the VERIFIED Lean executor the authoritative state PRODUCER and demotes the Rust `TurnExecutor`
//! to a parallel differential cross-check.
//!
//! Here we drive the SAME helper the node commit site calls, on a representative turn (a Transfer),
//! and assert:
//!   1. the verified producer is AUTHORITATIVE (`ProducerOutcome::LeanAuthoritative`),
//!   2. the COMMITTED ledger (the one `produce_via_lean` installs) equals what the Rust reference
//!      independently produces — same balances/nonces/state-fields AND `.root()`, and
//!   3. the outcome reports `rust_agreed == true` (the demoted reference found no Rust bug).
//!
//! A surfaced Rust bug here is a REAL finding (the Lean verdict is what was committed) — never
//! gates on the linked Lean archive (`lean_available()`); when it is absent the test self-skips (it
//! cannot run the verified producer). No `#[ignore]`, no weakened asserts.

use std::collections::HashMap;

use dregg_cell::state::FieldElement;
use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
use dregg_turn::lean_apply::{self, ProducerOutcome};
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
    // signed-wells (ac01f9b7b): i64 balances
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

/// Compare two ledgers cell-by-cell (balance + nonce + all state fields) AND on `.root()`.
fn assert_ledgers_agree(committed: &mut Ledger, rust: &mut Ledger, ids: &[CellId]) {
    for id in ids {
        let c = committed
            .get(id)
            .unwrap_or_else(|| panic!("cell {id:?} missing from COMMITTED ledger"));
        let r = rust
            .get(id)
            .unwrap_or_else(|| panic!("cell {id:?} missing from RUST differential ledger"));
        assert_eq!(
            c.state.balance(),
            r.state.balance(),
            "balance divergence on {id:?}: committed(lean)={} rust={}",
            c.state.balance(),
            r.state.balance()
        );
        assert_eq!(
            c.state.nonce(),
            r.state.nonce(),
            "nonce divergence on {id:?}: committed(lean)={} rust={}",
            c.state.nonce(),
            r.state.nonce()
        );
        for slot in 0..dregg_cell::state::STATE_SLOTS {
            assert_eq!(
                c.state.fields[slot], r.state.fields[slot],
                "field[{slot}] divergence on {id:?}"
            );
        }
    }
    assert_eq!(
        committed.root(),
        rust.root(),
        "ROOT divergence between the COMMITTED (Lean-produced) ledger and the Rust differential"
    );
}

/// Drive `produce_via_lean` (the helper the node commit path calls under producer mode) and assert
/// the verified producer's installed state matches the Rust differential.
fn run_producer_mode(pre: Ledger, turn: Turn, expected_committed: bool, ids: &[CellId]) {
    // Independent Rust producer (the reference). Run it on its OWN executor + copy of the pre-state
    // — a SEPARATE executor so its committed receipt does not pollute the producer-mode executor's
    // receipt-chain head (which would make the verified ChainHead leg reject the producer turn).
    let ref_executor = TurnExecutor::new(ComputronCosts::zero());
    let mut rust_ledger = pre.clone();
    let rust_result = ref_executor.execute(&turn, &mut rust_ledger);
    assert_eq!(
        rust_result.is_committed(),
        expected_committed,
        "Rust reference did not match the expected commit decision: {rust_result:?}"
    );

    // PRODUCER MODE: `produce_via_lean` installs the VERIFIED Lean post-state into `ledger`. Use a
    // FRESH executor (matching the node, which builds one per finalized turn).
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let mut ledger = pre.clone();
    let (_rust_result_inner, outcome) = lean_apply::produce_via_lean(&executor, &turn, &mut ledger);

    match outcome {
        ProducerOutcome::LeanAuthoritative {
            committed,
            rust_agreed,
            lean_root,
            rust_root,
            rust_committed,
        } => {
            assert_eq!(
                committed, expected_committed,
                "verified Lean producer (AUTHORITATIVE) commit bit did not match expectation"
            );
            assert_eq!(
                rust_committed, expected_committed,
                "Rust reference commit bit did not match expectation"
            );
            assert!(
                rust_agreed,
                "RUST BUG SURFACED: the demoted Rust reference disagrees with the AUTHORITATIVE \
                 verified Lean verdict (lean_root={lean_root:?} rust_root={rust_root:?}) — the \
                 Lean verdict was committed; Rust did not override it"
            );
            // The installed (committed) ledger must equal the independent Rust reference (they
            // agree on this turn, so the authoritative Lean state == the Rust reference state).
            assert_ledgers_agree(&mut ledger, &mut rust_ledger, ids);
        }
        ProducerOutcome::Fallback { reason } => {
            panic!(
                "turn was NOT eligible for the verified producer (outside the swap-safe covered \
                 set): {reason}; cannot run the node producer-mode test on a covered effect"
            );
        }
    }
}

#[test]
fn producer_mode_transfer_commits_lean_state_matching_rust() {
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
    run_producer_mode(pre, turn, true, &[a_id, b_id]);
}

#[test]
fn producer_mode_setfield_commits_lean_state_matching_rust() {
    if !dregg_lean_ffi::lean_available() {
        eprintln!("SKIP: Lean archive not linked (lean_available()==false)");
        return;
    }
    let (pre, a_id, b_id) = two_cell_ledger();
    // A second effect type (field reconstitution, not just balance/nonce) through the producer path.
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
    run_producer_mode(pre, turn, true, &[a_id, b_id]);
}

#[test]
fn producer_mode_cell_unseal_commits_lean_state_matching_rust() {
    if !dregg_lean_ffi::lean_available() {
        eprintln!("SKIP: Lean archive not linked (lean_available()==false)");
        return;
    }
    // CellUnseal (Sealed->Live) — the LIFECYCLE root-gap CLOSE driven through the node commit
    // helper. The verified producer flips the lifecycle discriminant back to Live (the payload-free
    // state), `produce_via_lean` installs `CellLifecycle::Live`, and the committed (Lean-produced)
    // ledger AGREES with the Rust differential on state + `.root()` (the lifecycle commitment fold).
    // A self-`node` cap supplies the unseal authority leg; the pre-state cell is SEALED.
    let mut a = make_open_cell(1, 100);
    let a_id = a.id();
    a.capabilities.grant(a_id, AuthRequired::None); // stateAuthB self-edge for the unseal authority
    a.seal([7u8; 32], 0).expect("seal the pre-state cell");
    let b = make_open_cell(2, 5);
    let b_id = b.id();
    let mut pre = Ledger::new();
    pre.insert_cell(a).unwrap();
    pre.insert_cell(b).unwrap();

    let turn = single_effect_turn(a_id, a_id, 0, Effect::CellUnseal { target: a_id });
    run_producer_mode(pre, turn, true, &[a_id, b_id]);
}
