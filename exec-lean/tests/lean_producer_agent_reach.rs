//! lean_producer_agent_reach.rs — THE AGENT-REACH FENCE (issue #56).
//!
//! The deepest hole in the verified-producer swap: the wire model binds the acting principal as
//! `actor := action.target` (`lean_shadow::tree_to_wforest`), and the Lean authority gate
//! `stateAuthB` = `authorizedB { actor, src := target, dst := target }` SHORT-CIRCUITS on the owner
//! disjunct `actor = src`. So for a root whose `action.target` differs from `turn.agent`, the Lean
//! model authorizes the write as if the TARGET cell were self-writing — with NO capability edge.
//! But the DEPLOYED Rust executor enforces AGENT-REACH (`execute_tree.rs:451`): for a root, the
//! agent must OWN the target, hold a c-list edge, or carry a bearer proof — else `CapabilityNotHeld`.
//!
//! Without a fence, a turn where agent W targets a cell R it does not own and holds no edge to would
//! be REJECTED by Rust but COMMITTED by Lean, and the default-on producer (`produce_via_lean`) would
//! INSTALL that cross-cell write the authority model forbids — a soundness hole.
//!
//! TIER-1 FENCE (this file): `forest_is_root_agreeing` additionally requires every root to satisfy
//! `turn.agent == action.target` OR carry a bearer proof (`forest_agent_reaches_roots`). An
//! agent≠target non-bearer root is fenced OUT of the covered set onto the Rust producer, which
//! enforces agent-reach. This is a pure SAFETY-NET tightening — Rust already decides these; the
//! fence only stops the verified producer from LOOSENING past Rust.
//!
//! Teeth:
//!   * FALSIFIER (`hole_agent_targets_unreachable_cell_is_fenced`): the exact hole scenario — the
//!     producer must NOT commit it (falls to Rust → `CapabilityNotHeld`), matching Rust. Removing
//!     the fence flips the outcome to `LeanAuthoritative { committed: true }` — the canary fails RED.
//!   * LIVENESS-SELF (`legit_self_write_still_commits`): agent == target STILL commits under the
//!     verified producer (`LeanAuthoritative`) — the fence does not over-reject.
//!   * LIVENESS-EDGE (`legit_cross_cell_with_cap_edge_still_commits`): agent ≠ target but the agent
//!     HOLDS a c-list edge — Rust commits it, so the fenced-to-Rust turn STILL commits (no liveness
//!     regression; the fence routes it, it does not kill it).
//!
//! Requires the linked Lean archive; self-skips when absent (PANICS under `DREGG_TEST_REQUIRE_LEAN=1`).

use std::collections::HashMap;

use dregg_cell::permissions::AuthRequired;
use dregg_cell::state::FieldElement;
use dregg_cell::{Cell, CellId, Ledger, Permissions};
use dregg_exec_lean::lean_apply::{ExtractError, ProducerOutcome, produce_via_lean};
use dregg_exec_lean::lean_shadow;
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

fn field_from_u64(v: u64) -> FieldElement {
    let mut out = [0u8; 32];
    out[24..32].copy_from_slice(&v.to_be_bytes());
    out
}

/// A single-`SetField` turn: agent acts, root targets `target`, writes state slot 6.
fn set_field_turn(agent: CellId, target: CellId, field_cell: CellId) -> Turn {
    let mut forest = CallForest::new();
    let action = Action {
        target,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![Effect::SetField {
            cell: field_cell,
            index: 6,
            value: field_from_u64(42),
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    };
    forest.add_root(action);
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

/// FALSIFIER — the hole. Agent W targets cell R that W does NOT own and holds no cap edge to.
/// Rust REJECTS (`CapabilityNotHeld`). Without the fence the verified producer COMMITS (Lean models
/// R self-writing) and the producer INSTALLS it — the soundness hole. With the fence the turn is
/// FENCED onto the Rust path: NOT committed, `Fallback { AgentReach }`, ledger UNCHANGED. Matches
/// Rust. Removing the fence would flip the outcome to `LeanAuthoritative { committed: true }` and
/// mutate the ledger — every assertion below fails RED (the mutation canary).
#[test]
fn hole_agent_targets_unreachable_cell_is_fenced() {
    if skip_no_lean() {
        return;
    }

    let w = make_open_cell(1, 100); // the AGENT
    let w_id = w.id();
    let r = make_open_cell(2, 0); // the target — W does not own it, holds no edge to it
    let r_id = r.id();
    assert_ne!(w_id, r_id, "agent and target must be distinct cells");

    let mut pre = Ledger::new();
    pre.insert_cell(w).unwrap();
    pre.insert_cell(r).unwrap();

    let turn = set_field_turn(w_id, r_id, r_id);

    // The gate itself: the hole turn is FENCED OUT of the covered set.
    assert!(
        !lean_shadow::forest_is_root_agreeing(&turn),
        "agent≠target non-bearer root must NOT be root-agreeing (the agent-reach fence)"
    );

    // Rust reference alone: this is a genuine rejection (CapabilityNotHeld). Note `execute` mutates
    // its ledger in place even on the reject path (the producer snapshots pre-state precisely for
    // this reason), so we assert only the VERDICT here, not the reference ledger's root.
    let ref_exec = TurnExecutor::new(ComputronCosts::zero());
    let mut rust_only = pre.clone();
    assert!(
        !ref_exec.execute(&turn, &mut rust_only).is_committed(),
        "Rust rejects the cross-cell write (CapabilityNotHeld)"
    );
    let pre_root = pre.root();

    // The LIVE producer path: must NOT commit — fenced to Rust, matching the rejection.
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let mut ledger = pre.clone();
    let (result, outcome) = produce_via_lean(&executor, &turn, &mut ledger);

    assert!(
        !result.is_committed(),
        "PRODUCER must NOT commit the unreachable cross-cell write — the hole is closed"
    );
    match outcome {
        ProducerOutcome::Fallback {
            reason: ExtractError::AgentReach,
        } => {}
        other => panic!(
            "the hole turn must fence with Fallback {{ AgentReach }}, got {other:?} \
             (if this is LeanAuthoritative{{committed:true}}, the fence was removed — #56 reopened)"
        ),
    }
    // The verified producer no longer COMMITS this turn — the load-bearing soundness property. The
    // fence routes it onto the legacy Rust producer, so the resulting ledger is byte-identical to a
    // pure `executor.execute` (no verified Lean cross-cell write installed on top of Rust's verdict).
    let _ = pre_root;
    assert_eq!(
        ledger.root(),
        rust_only.root(),
        "the fenced turn rides the exact Rust path (no Lean-produced cross-cell write installed)"
    );
}

/// LIVENESS-SELF — the fence does not over-reject. Agent == target (a genuine self-write) is STILL
/// covered and STILL committed by the verified producer.
#[test]
fn legit_self_write_still_commits() {
    if skip_no_lean() {
        return;
    }

    let w = make_open_cell(3, 100);
    let w_id = w.id();
    let mut pre = Ledger::new();
    pre.insert_cell(w).unwrap();

    let turn = set_field_turn(w_id, w_id, w_id);

    assert!(
        lean_shadow::forest_is_root_agreeing(&turn),
        "a self-write (agent == target) must remain root-agreeing (no over-rejection)"
    );

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let mut ledger = pre.clone();
    let (result, outcome) = produce_via_lean(&executor, &turn, &mut ledger);

    assert!(
        result.is_committed(),
        "the legitimate self-write STILL commits under the verified producer"
    );
    match outcome {
        ProducerOutcome::LeanAuthoritative { committed, .. } => {
            assert!(
                committed,
                "the verified verdict for the self-write is COMMIT"
            );
        }
        other => panic!("a covered self-write must be LeanAuthoritative, got {other:?}"),
    }
    assert_ne!(
        ledger.root(),
        pre.root(),
        "the self-write actually mutated the ledger"
    );
}

/// LIVENESS-EDGE — no liveness regression for a LEGITIMATE cross-cell write. Agent W holds a real
/// c-list edge to R, so Rust ACCEPTS. The fence routes it to the Rust producer (agent ≠ target,
/// non-bearer), which commits it — the turn STILL commits. The fence routes; it does not kill.
#[test]
fn legit_cross_cell_with_cap_edge_still_commits() {
    if skip_no_lean() {
        return;
    }

    let mut w = make_open_cell(4, 100); // the AGENT
    let r = make_open_cell(5, 0); // the target
    let r_id = r.id();
    // Grant W a c-list edge to R: now Rust's agent-reach gate is satisfied.
    w.capabilities
        .grant(r_id, AuthRequired::None)
        .expect("granting a cap edge to R must succeed");
    let w_id = w.id();

    let mut pre = Ledger::new();
    pre.insert_cell(w).unwrap();
    pre.insert_cell(r).unwrap();

    let turn = set_field_turn(w_id, r_id, r_id);

    // Rust accepts this — the agent HOLDS the edge.
    let ref_exec = TurnExecutor::new(ComputronCosts::zero());
    let mut rust_only = pre.clone();
    assert!(
        ref_exec.execute(&turn, &mut rust_only).is_committed(),
        "Rust commits the cross-cell write when the agent holds the edge"
    );

    // The producer fences it to Rust (agent≠target non-bearer) — but it STILL commits.
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let mut ledger = pre.clone();
    let (result, outcome) = produce_via_lean(&executor, &turn, &mut ledger);

    assert!(
        result.is_committed(),
        "a legitimate cap-backed cross-cell write STILL commits (fenced to Rust, not killed)"
    );
    assert!(
        matches!(
            outcome,
            ProducerOutcome::Fallback {
                reason: ExtractError::AgentReach
            }
        ),
        "the cap-backed cross-cell write rides the Rust producer under the agent-reach fence"
    );
    assert_eq!(
        ledger.root(),
        rust_only.root(),
        "the fenced-to-Rust commit installs the same post-state Rust computes"
    );
}
