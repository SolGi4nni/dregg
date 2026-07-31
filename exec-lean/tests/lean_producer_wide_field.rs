//! lean_producer_wide_field.rs — **THE WIRE-CARRIER FALLBACK, CLOSED** (both poles, live FFI).
//!
//! # What used to happen
//!
//! `lean_shadow::field_fits_wire_carrier` required `field[0..24] == 0` because the wire projection
//! (`field_to_i128`) read only the low 8 bytes. So a turn writing a FULL 32-byte state field — a
//! digest, a `cell_tag`, an `ELECTORATE_ROOT`, an execution-lease `PROVIDER_SLOT` — was
//! `effect_is_mappable == false`, hence not marshallable, hence
//! `produce_via_lean → Fallback { Ineligible }`: the VERIFIED producer never ran and the unverified
//! Rust executor decided and committed the turn. The refusal was correct (truncating would have
//! been worse) but it was a live, daily-reachable hole in the verified path.
//!
//! # What happens now
//!
//! The carrier is `marshal::WideInt` — a 256-bit magnitude, exactly the width of a `FieldElement`,
//! and exactly the width the Lean `Int` on the far side always had. The projection is TOTAL, so the
//! turn is covered, the verified Lean executor DECIDES it, and its post-state is INSTALLED.
//!
//! # Anti-vacuity
//!
//! "It no longer falls back" is satisfiable by making the shadow accept everything, so every test
//! here asserts WHAT WAS INSTALLED, not merely that something committed:
//!   * the outcome is `LeanAuthoritative` (the Lean verdict is the authority), and
//!   * the committed ledger's root EQUALS the `lean_root` the outcome reports — i.e. the state in
//!     the ledger is the one the VERIFIED executor produced, not Rust's, and
//!   * the field itself is the full 32 bytes (the thing the old carrier could not carry).
//!
//! Requires the linked Lean archive; self-skips when absent (PANICS under `DREGG_TEST_REQUIRE_LEAN=1`).

use std::collections::HashMap;

use dregg_cell::permissions::AuthRequired;
use dregg_cell::state::FieldElement;
use dregg_cell::{Cell, CellId, Ledger, Permissions};
use dregg_exec_lean::lean_apply::{ProducerOutcome, produce_via_lean};
use dregg_exec_lean::lean_shadow;
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, TurnExecutor,
    turn::Turn,
};

/// The `fields[]` slot the wire names `"target"` — the execution-lease PROVIDER slot of
/// docs/FINDING-state-field-truncation.md.
const PROVIDER_SLOT: u64 = 6;

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

/// The FINDING's exact 32-byte provider cell id — high 24 bytes NON-ZERO, which is precisely the
/// predicate the deleted `field_fits_wire_carrier` refused on.
fn wide_field() -> FieldElement {
    [
        0x93, 0x4e, 0x47, 0xf2, 0x22, 0x21, 0x69, 0x76, 0xec, 0xab, 0xcd, 0x76, 0xf8, 0xbe, 0x42,
        0xed, 0x45, 0x9e, 0x23, 0xb1, 0x2e, 0x98, 0x8a, 0xb7, 0xad, 0x7a, 0x7d, 0xa3, 0x27, 0xd6,
        0x80, 0x64,
    ]
}

/// A self-targeted single-`SetField` turn writing `value` into `PROVIDER_SLOT`.
fn set_field_turn(agent: CellId, value: FieldElement) -> Turn {
    let mut forest = CallForest::new();
    forest.add_root(Action {
        target: agent,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![Effect::SetField {
            cell: agent,
            index: PROVIDER_SLOT,
            value,
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    });
    Turn {
        agent,
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
    }
}

fn skip_no_lean() -> bool {
    !dregg_lean_ffi::demand_lean(
        dregg_lean_ffi::lean_available(),
        "Lean archive (lean_available)",
    )
}

/// GATE POLE — the eligibility predicate itself. A full-width `SetField` is now marshallable AND
/// root-agreeing. Under the old carrier BOTH were `false` (the value guard sat inside
/// `effect_is_mappable`), so this is the precise statement of what moved.
#[test]
fn a_full_width_setfield_is_now_covered_by_the_verified_producer() {
    let agent = make_open_cell(1, 100);
    let turn = set_field_turn(agent.id(), wide_field());

    assert!(
        wide_field()[0..24].iter().any(|&b| b != 0),
        "the fixture must be the shape the old guard refused (high 24 bytes non-zero)"
    );
    assert!(
        lean_shadow::forest_is_marshallable(&turn),
        "a full-width SetField must have a wire projection — the carrier is 256 bits wide now"
    );
    assert!(
        lean_shadow::forest_is_root_agreeing(&turn),
        "…and be in the COVERED set, so the verified producer is authoritative for it"
    );
    assert!(
        lean_shadow::first_root_gap_kind(&turn).is_none(),
        "no root-gap kind blocks it"
    );
}

/// COMMIT POLE — the verified producer RUNS and its state is what lands.
#[test]
fn a_full_width_setfield_is_lean_executed_and_the_lean_state_is_installed() {
    if skip_no_lean() {
        return;
    }
    let agent = make_open_cell(1, 100);
    let agent_id = agent.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent).unwrap();

    let turn = set_field_turn(agent_id, wide_field());
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let (result, outcome) = produce_via_lean(&executor, &turn, &mut ledger);

    // (1) The VERIFIED executor decided it — not a fallback.
    let (committed, lean_root, rust_agreed) = match outcome {
        ProducerOutcome::LeanAuthoritative {
            committed,
            lean_root,
            rust_agreed,
            ..
        } => (committed, lean_root, rust_agreed),
        ProducerOutcome::Fallback { reason } => panic!(
            "the wire-carrier fallback is supposed to be CLOSED — the verified producer must run \
             for a full-width SetField, got Fallback {{ {reason} }}"
        ),
    };
    assert!(committed, "the verified executor committed the self-write");
    assert!(
        result.is_committed(),
        "…and the returned TurnResult reflects that verdict"
    );

    // (2) ANTI-VACUITY: what is IN the ledger is the VERIFIED executor's post-state. `lean_root` is
    // `executor.consensus_state_commitment(&lean_ledger, agent)` — computed from the Lean-produced
    // ledger BEFORE the Rust reference ran — so equality here says the installed state is that one.
    assert_eq!(
        executor.consensus_state_commitment(&ledger, &agent_id),
        lean_root,
        "the INSTALLED state must be the verified producer's post-state (anti-vacuity: a shadow \
         that accepted everything would still fail this)"
    );

    // (3) …and the field itself crossed WHOLE — the thing the old carrier could not do.
    let got = ledger.get(&agent_id).unwrap().state.fields[PROVIDER_SLOT as usize];
    assert_eq!(
        got,
        wide_field(),
        "the full 32-byte field must be installed; the low-8 projection would give 0000…d68064"
    );

    // (4) …and the demoted Rust reference reproduced it, so this is not a divergence dressed as a
    // win. (A `false` here would be a REAL finding, not a reason to distrust the install.)
    assert!(
        rust_agreed,
        "the Rust reference must reproduce the verified verdict AND root on this turn"
    );
}

/// NARROW POLE (no regression) — a low-64 field, which crossed before, still crosses.
#[test]
fn a_narrow_setfield_still_commits_through_the_verified_producer() {
    if skip_no_lean() {
        return;
    }
    let agent = make_open_cell(2, 100);
    let agent_id = agent.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent).unwrap();

    let mut narrow = [0u8; 32];
    narrow[24..32].copy_from_slice(&42u64.to_be_bytes());
    let turn = set_field_turn(agent_id, narrow);

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let (result, outcome) = produce_via_lean(&executor, &turn, &mut ledger);
    assert!(result.is_committed(), "the narrow write still commits");
    match outcome {
        ProducerOutcome::LeanAuthoritative { lean_root, .. } => assert_eq!(
            executor.consensus_state_commitment(&ledger, &agent_id),
            lean_root,
            "the installed state is still the verified producer's"
        ),
        ProducerOutcome::Fallback { reason } => {
            panic!("a narrow SetField must not regress into a fallback: {reason}")
        }
    }
    assert_eq!(
        ledger.get(&agent_id).unwrap().state.fields[PROVIDER_SLOT as usize],
        narrow,
        "the narrow value is installed unchanged"
    );
}

/// WIDE `EmitEvent` — the other effect the carrier guard gated (`Emit.topic`). A full-width topic is
/// now wire-carriable, so an `EmitEvent` turn stays on the verified path.
#[test]
fn a_full_width_event_topic_no_longer_fences_the_turn() {
    let agent = make_open_cell(3, 100);
    let agent_id = agent.id();

    let mut forest = CallForest::new();
    forest.add_root(Action {
        target: agent_id,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![Effect::EmitEvent {
            cell: agent_id,
            event: dregg_turn::action::Event {
                topic: wide_field(),
                data: vec![],
            },
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    });
    let mut turn = set_field_turn(agent_id, wide_field());
    turn.call_forest = forest;

    assert!(
        lean_shadow::forest_is_marshallable(&turn),
        "a full-width event topic must marshal — the topic shares the widened carrier"
    );
    assert!(
        lean_shadow::forest_is_root_agreeing(&turn),
        "…and stay in the covered set"
    );
}
