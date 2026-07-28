//! THE ARMED verified-rejection tooth — the verified Lean executor as the AUTHORITATIVE decision on
//! the commit path, through the mechanism that is actually turned on.
//!
//! ## What this replaces, and why
//!
//! `exec-lean/tests/lean_strict_veto.rs` used to pin the same divergence through
//! `DREGG_LEAN_SHADOW=1` + `DREGG_LEAN_SHADOW_STRICT=1` and the veto inside
//! `TurnExecutor::execute`. Both variables were set by NOTHING in the repo outside that test —
//! whole-tree sweep including `.github/`, `docker/`, `deploy/`, every `.service`/`.env`, every
//! `Dockerfile`/compose file, and every Rust `env::set_var` — so that gate decided nothing anywhere.
//! It was also DOMINATED: `lean_apply::produce_via_lean` (THE SWAP authority inversion, ON by
//! default on native via `DREGG_LEAN_PRODUCER`) installs the verified verdict in BOTH directions,
//! not merely as a one-way tightening.
//!
//! And it was BROKEN. Measured 2026-07-28 against the linked archive: the veto restored the ledger,
//! the factory registry and the FNSP admission slot, but NOT the agent's receipt-chain head, which
//! `execute_without_shadow` had already advanced. A vetoed turn therefore left the executor
//! expecting a `previous_receipt_hash` for a receipt that was never issued and can never be
//! produced, and the agent's next honest turn was refused
//! `ReceiptChainMismatch { expected: Some(d250…), got: None }` — permanently. That mechanism was
//! deleted; this file pins the same semantics on the path that runs, INCLUDING the receipt-head
//! restoration the deleted path got wrong.
//!
//! ## The tooth
//!
//! The divergence is the under-authorised `Burn`: dregg1's `apply.rs` commits a burn on an owned
//! open cell, while the verified `.burnA` requires an explicit mint/burn cap (`mintAuthorizedB`).
//!
//! Run (single-threaded not required — no env mutation):
//!   DREGG_TEST_REQUIRE_LEAN=1 cargo nextest run -p dregg-exec-lean \
//!       --test lean_producer_verified_rejection --test-threads=4

use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, TurnExecutor,
    turn::Turn,
};

/// The executor a native node builds: the verified-Lean observer injected, exactly as
/// `node::executor_setup::new_submit_executor` does.
fn node_shaped_executor() -> TurnExecutor {
    TurnExecutor::new(ComputronCosts::zero())
        .with_shadow_observer(dregg_exec_lean::LeanShadowObserver::arc())
}

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

fn one_cell_ledger(bal: i64) -> (Ledger, CellId) {
    // signed-wells (ac01f9b7b): i64 balances
    let mut pk = [0u8; 32];
    pk[0] = 1;
    pk[31] = 37;
    let mut cell = Cell::with_balance(pk, [0u8; 32], bal);
    cell.permissions = open_permissions();
    let id = cell.id();
    let mut l = Ledger::new();
    l.insert_cell(cell).unwrap();
    (l, id)
}

fn turn_with(agent: CellId, nonce: u64, prev: Option<[u8; 32]>, effects: Vec<Effect>) -> Turn {
    let mut forest = CallForest::new();
    forest.add_root(Action {
        target: agent,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects,
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    });
    Turn {
        agent,
        nonce,
        call_forest: forest,
        fee: 0,
        memo: None,
        valid_until: Some(1_000_000),
        previous_receipt_hash: prev,
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

fn burn_10(agent: CellId, prev: Option<[u8; 32]>) -> Turn {
    turn_with(
        agent,
        0,
        prev,
        vec![Effect::Burn {
            target: agent,
            slot: 0,
            amount: 10,
        }],
    )
}

/// The written value MUST fit the low-64 wire carrier (`lean_shadow::field_fits_wire_carrier`:
/// bytes 0..24 zero). A full 32-byte digest makes the whole turn `Ineligible` and FENCES it onto the
/// Rust producer — measured here, and the reason the honest pole below asserts on the value it does.
/// That is the standing `SetField` carrier residual, not a defect of this test.
const WIRE_CARRIABLE_FIELD: [u8; 32] = {
    let mut v = [0u8; 32];
    v[31] = 0xcd;
    v
};

fn set_field(agent: CellId, nonce: u64, prev: Option<[u8; 32]>) -> Turn {
    turn_with(
        agent,
        nonce,
        prev,
        vec![Effect::SetField {
            cell: agent,
            index: 3,
            value: WIRE_CARRIABLE_FIELD,
        }],
    )
}

fn require_lean() -> bool {
    dregg_lean_ffi::demand_lean(
        dregg_lean_ffi::lean_available(),
        "verified Turn executor archive (lean_available)",
    )
}

/// POLE 1 — AN HONEST TURN STILL COMMITS through the authoritative producer, and the state
/// actually moves. Without this the rejection pole below would be satisfied by a producer that
/// rejects everything.
#[test]
fn honest_turn_commits_through_the_authoritative_producer() {
    if !require_lean() {
        return;
    }
    let (mut ledger, agent) = one_cell_ledger(100);
    let executor = node_shaped_executor();

    let (result, outcome) =
        dregg_exec_lean::produce_via_lean(&executor, &set_field(agent, 0, None), &mut ledger);

    assert!(
        matches!(
            outcome,
            dregg_exec_lean::ProducerOutcome::LeanAuthoritative { .. }
        ),
        "an owned open-cell SetField must be in the COVERED set (the verified producer decides it), \
         got {outcome:?}"
    );
    assert!(
        !outcome.rust_bug_surfaced(),
        "the two executors must AGREE on an honest SetField; a disagreement here is a real finding: \
         {outcome:?}"
    );
    assert!(
        result.is_committed(),
        "the honest turn must COMMIT under the verified producer, got {result:?}"
    );
    assert_eq!(
        ledger
            .get(&agent)
            .and_then(|c| c.state.get_field(3).copied()),
        Some(WIRE_CARRIABLE_FIELD),
        "the committed write must be on the authoritative ledger, not merely accepted"
    );
}

/// POLE 2 — A GENUINE DIVERGENCE IS CAUGHT. The under-authorised burn is committed by the legacy
/// Rust executor and REJECTED by the verified `.burnA` (no mint/burn cap). The verified verdict is
/// authoritative: the turn is `Rejected`, the balance does not move, and the disagreement is
/// surfaced as a Rust bug rather than laundered into agreement.
#[test]
fn verified_rejection_overrides_the_rust_commit_and_surfaces_the_bug() {
    if !require_lean() {
        return;
    }

    // The demoted Rust reference on its own: apply.rs COMMITS this burn (100 -> 90). This is what
    // makes the pole below non-vacuous — the verified verdict is genuinely overriding an accept,
    // not agreeing with a rejection Rust would have made anyway.
    {
        let (mut ledger, agent) = one_cell_ledger(100);
        let rust_only = TurnExecutor::new(ComputronCosts::zero());
        let r = rust_only.execute(&burn_10(agent, None), &mut ledger);
        assert!(
            r.is_committed(),
            "PRECONDITION: the legacy Rust executor must COMMIT the under-authorised burn \
             (otherwise this test proves nothing), got {r:?}"
        );
        assert_eq!(
            ledger.get(&agent).map(|c| c.state.balance()),
            Some(90),
            "PRECONDITION: the Rust-committed burn debits 10"
        );
    }

    let (mut ledger, agent) = one_cell_ledger(100);
    let executor = node_shaped_executor();
    let (result, outcome) =
        dregg_exec_lean::produce_via_lean(&executor, &burn_10(agent, None), &mut ledger);

    assert!(
        !result.is_committed(),
        "the verified kernel REJECTED this burn, so the authoritative result must be a rejection, \
         got {result:?}"
    );
    assert_eq!(
        ledger.get(&agent).map(|c| c.state.balance()),
        Some(100),
        "a verified rejection is NO state edit — the balance must be the pre-state 100"
    );
    assert!(
        outcome.rust_bug_surfaced(),
        "the Rust reference COMMITTED what the verified kernel REJECTED; that disagreement must be \
         surfaced as a Rust bug, not reported as agreement. outcome = {outcome:?}"
    );
    // The rejection must be legible: the verified refusal names its gate when the wire carried an
    // admission reason, else the generic veto. Either way it must be one of the two verified-refusal
    // shapes and never a Rust-side error.
    match &result {
        dregg_turn::turn::TurnResult::Rejected { reason, .. } => assert!(
            matches!(
                reason,
                dregg_turn::TurnError::LeanShadowVeto
                    | dregg_turn::TurnError::AdmissionRefused { .. }
            ),
            "a verified override must report LeanShadowVeto or the named AdmissionRefused, got \
             {reason:?}"
        ),
        other => panic!("expected Rejected, got {other:?}"),
    }
}

/// POLE 2b — THE REGRESSION TOOTH for the defect that killed the deleted strict veto: a verified
/// rejection must leave the agent able to act.
///
/// The deleted `TurnExecutor::execute` veto restored the ledger but NOT the agent's receipt-chain
/// head, which the Rust reference had already advanced on its (now-overridden) commit. The agent's
/// next honest turn then failed `ReceiptChainMismatch { expected: Some(..), got: None }` forever,
/// because no receipt carrying that hash was ever issued. `produce_via_lean` rolls the reference's
/// side state back through `checkpoint_producer_reference` / `rollback_producer_reference`; this
/// pins that it actually does.
#[test]
fn verified_rejection_leaves_the_agent_able_to_take_its_next_turn() {
    if !require_lean() {
        return;
    }
    let (mut ledger, agent) = one_cell_ledger(100);
    let executor = node_shaped_executor();

    let (rejected, _) =
        dregg_exec_lean::produce_via_lean(&executor, &burn_10(agent, None), &mut ledger);
    assert!(
        !rejected.is_committed(),
        "precondition: the verified kernel rejects the under-authorised burn, got {rejected:?}"
    );

    assert_eq!(
        executor.get_last_receipt_hash(&agent),
        None,
        "A REJECTED TURN MUST NOT ADVANCE THE RECEIPT CHAIN. The Rust reference advanced it \
         speculatively; the verified rejection must roll it back, or the agent is left expecting a \
         receipt that was never issued and can never be produced. This is exactly the defect that \
         retired the DREGG_LEAN_SHADOW_STRICT veto."
    );

    // The agent's next honest turn correctly claims genesis (`prev = None`, since the previous turn
    // was rejected) and must COMMIT.
    let (next, outcome) =
        dregg_exec_lean::produce_via_lean(&executor, &set_field(agent, 0, None), &mut ledger);
    assert!(
        matches!(
            outcome,
            dregg_exec_lean::ProducerOutcome::LeanAuthoritative { .. }
        ),
        "the follow-up turn must also be COVERED (so this pole exercises the verified producer, \
         not the Rust fallback), got {outcome:?}"
    );
    assert!(
        next.is_committed(),
        "the agent must still be able to act after a verified rejection, got {next:?} \
         (outcome {outcome:?})"
    );
    assert_eq!(
        ledger
            .get(&agent)
            .and_then(|c| c.state.get_field(3).copied()),
        Some(WIRE_CARRIABLE_FIELD),
        "the follow-up write must land on the authoritative ledger"
    );
}
