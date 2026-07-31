//! THE PRODUCER DIFFERENTIAL IS NO LONGER ANCHOR-BLIND — and the blindness is measured, not
//! asserted from a docstring.
//!
//! ═══ WHAT WAS OPEN ═══════════════════════════════════════════════════════════════
//! `produce_via_lean` runs the verified Lean executor as the AUTHORITY and the legacy Rust
//! executor as a demoted REFERENCE, then reports whether the reference reproduced the verified
//! verdict. Until 2026-07-30 that comparison was exactly two values: the commit bit, and
//! `TurnExecutor::consensus_state_commitment`.
//!
//! **The anchor is a per-AGENT-cell commitment.** `state_commit::consensus_state_commitment`
//! commits the AGENT's cell under a `V9RotationContext` whose only whole-ledger component is
//! `rotation_witness::cells_root` — a tree whose leaves are EXISTENCE BITS (`BabyBear::ONE`), never
//! a cell's value. So two post-states that differ only in a transfer RECIPIENT's balance produce
//! byte-identical anchors, and the differential reported `rust_agreed: true` for them.
//!
//! A predicate that DID catch that existed — `lean_shadow::post_states_agree`, a cell-by-cell
//! comparison — but it was reachable only from `maybe_shadow_turn`, gated on `DREGG_LEAN_SHADOW=1`,
//! which was set by nothing in the tree outside one test; and its verdict was discarded at the
//! single call site (`let _ = …`). Two independent reasons it decided nothing. It was moved onto
//! this armed seam as [`ProducerDivergence::PostStateCell`] and the dark path was deleted.
//!
//! ⚠ The same blindness is true of the receipt's signed `post_state_hash`, which is that same
//! anchor value. That is a LARGER residual than this file closes and it is NOT closed here —
//! `turn/src/state_commit.rs` already labels it ("a per-cell commit, not the whole-ledger snapshot
//! the BLAKE3 root was"). What this file establishes is that the Lean↔Rust DIFFERENTIAL no longer
//! inherits it.
//!
//! ═══ THE POLES ═══════════════════════════════════════════════════════════════════
//! 1. `the_anchor_cannot_see_a_non_agent_cell` — the blindness itself, MEASURED against a real
//!    `TurnExecutor`. Without this the rest is a claim about a hypothetical.
//! 2. `a_non_agent_cell_divergence_is_caught_by_the_post_state_leg` — same two ledgers, and the
//!    differential returns `PostStateCell` naming the right cell. Poles 1+2 together are the
//!    strength: leg 2 passed, leg 3 refused.
//! 3. `agreeing_post_states_are_agreement` — the non-vacuity guard. A differential that returned
//!    `Some(..)` for everything would satisfy pole 2 and is refused here.
//! 4. `an_honest_turn_is_decided_as_agreement_and_the_lean_state_is_installed` (needs the archive)
//!    — the ADMIT pole through the real producer: `LeanAuthoritative { divergence: None }` by
//!    variant, AND the verified verdict was INSTALLED (the write is on the ledger and the receipt
//!    attests the Lean root), not merely computed.
//! 5. `a_verified_refusal_is_decided_as_a_commit_bit_divergence` (needs the archive) — the REFUSE
//!    pole through the real producer: `divergence == Some(CommitBit { lean: false, rust: true })`
//!    matched by VARIANT, the rejection reason matched by VARIANT, and the ledger back at the
//!    pre-state. Asserting the variant is what distinguishes "the differential ran and answered"
//!    from "something went wrong" — a `Fallback` outcome is a different variant and fails here.
//!
//! Run: `DREGG_TEST_REQUIRE_LEAN=1 cargo nextest run -p dregg-exec-lean \
//!        --test producer_differential_sees_non_agent_cells`

use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
use dregg_exec_lean::lean_apply::classify_divergence;
use dregg_exec_lean::{ProducerDivergence, ProducerOutcome, produce_via_lean};
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, TurnExecutor,
    turn::{Turn, TurnResult},
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

fn open_cell(seed: u8, balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37);
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell
}

fn ledger_of(cells: &[Cell]) -> Ledger {
    let mut l = Ledger::new();
    for c in cells {
        l.insert_cell(c.clone()).expect("distinct cell ids");
    }
    l
}

/// The two ledgers this file's strength poles turn on: identical but for the BYSTANDER's balance.
/// Returns `(agent_id, bystander_id, lean_side, rust_side)`.
fn ledgers_differing_only_in_a_non_agent_cell() -> (CellId, CellId, Ledger, Ledger) {
    let agent = open_cell(1, 100);
    // The exact shape the anchor cannot see: a recipient credited a different amount by the two
    // executors. Same cell id (`CellId::derive_raw` is over public key + token id, both fixed by
    // the seed), different value.
    let bystander_lean = open_cell(2, 50);
    let bystander_rust = open_cell(2, 51);
    assert_ne!(
        bystander_lean, bystander_rust,
        "fixture: the two bystander cells must actually differ"
    );
    assert_eq!(
        bystander_lean.id(),
        bystander_rust.id(),
        "fixture: the divergence must be a VALUE drift on ONE cell, not two different cells — a \
         different id would move `cells_root` and the anchor would (correctly) catch it"
    );
    let agent_id = agent.id();
    let bystander_id = bystander_lean.id();
    (
        agent_id,
        bystander_id,
        ledger_of(&[agent.clone(), bystander_lean]),
        ledger_of(&[agent, bystander_rust]),
    )
}

/// ⚑ POLE 1 — THE BLINDNESS, MEASURED. The consensus anchor for the AGENT is byte-identical across
/// two ledgers that differ in a non-agent cell's balance. This is the fact the whole file rests on,
/// and it is taken from a real `TurnExecutor`, not from a comment.
#[test]
fn the_anchor_cannot_see_a_non_agent_cell() {
    let (agent, bystander, lean_side, rust_side) = ledgers_differing_only_in_a_non_agent_cell();
    let executor = TurnExecutor::new(ComputronCosts::zero());

    assert_ne!(
        lean_side.get(&bystander),
        rust_side.get(&bystander),
        "precondition: the two ledgers really do differ at the bystander"
    );
    assert_eq!(
        executor.consensus_state_commitment(&lean_side, &agent),
        executor.consensus_state_commitment(&rust_side, &agent),
        "THE ANCHOR IS BLIND HERE, and that is the finding: `consensus_state_commitment` commits \
         the AGENT'S cell under a ctx whose only whole-ledger component is `cells_root`, whose \
         leaves are EXISTENCE BITS. A non-agent cell's VALUE is not in it. If this assertion ever \
         FAILS, the anchor got wider — delete this file's premise and re-derive it, do not weaken \
         the assertion."
    );
}

/// ⚑ POLE 2 — AND THE DIFFERENTIAL CATCHES IT ANYWAY. Same two ledgers, same commit bit, and (per
/// pole 1) the same anchor — so legs 1 and 2 both pass. Leg 3 refuses, and names the cell.
///
/// Before 2026-07-30 this input produced `rust_agreed: true`: a Lean↔Rust disagreement reported as
/// agreement, on the value-moving side of a transfer.
#[test]
fn a_non_agent_cell_divergence_is_caught_by_the_post_state_leg() {
    let (agent, bystander, lean_side, rust_side) = ledgers_differing_only_in_a_non_agent_cell();
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let lean_root = executor.consensus_state_commitment(&lean_side, &agent);
    let rust_root = executor.consensus_state_commitment(&rust_side, &agent);

    // ⚑ THE RED-PROOF, IN VALUE — no source is disarmed and no window is opened in the shared
    // tree. This is LITERALLY the predicate `produce_via_lean` used until 2026-07-30
    // (`rust_agreed = lean_committed == rust_committed && lean_root == rust_root`), evaluated on
    // this input. It says AGREED. So the assertion below is not merely true, it is a CHANGE: the
    // old differential returned the wrong answer here and this one returns the right answer.
    let (lean_committed, rust_committed) = (true, true);
    let pre_2026_07_30_rust_agreed = lean_committed == rust_committed && lean_root == rust_root;
    assert!(
        pre_2026_07_30_rust_agreed,
        "the two-leg differential this replaced must call these post-states AGREED — if it does \
         not, the anchor has changed and this file's whole premise needs re-deriving"
    );

    let divergence = classify_divergence(
        lean_committed,
        rust_committed,
        lean_root,
        rust_root,
        &lean_side,
        &rust_side,
    );

    assert_eq!(
        divergence,
        Some(ProducerDivergence::PostStateCell { cell: bystander }),
        "the two coarse legs agreed (same commit bit, same anchor — pole 1 measures that), so the \
         ONLY leg that can catch this is the cell-by-cell post-state comparison, and it must name \
         the bystander. `None` here means the differential is back to being anchor-blind; \
         `CommitBit`/`Anchor` means a leg fired for the wrong reason."
    );
}

/// NON-VACUITY. A differential that answered `Some(..)` unconditionally would pass pole 2. Two
/// identical post-states must be reported as agreement.
#[test]
fn agreeing_post_states_are_agreement() {
    let (agent, _bystander, lean_side, _rust_side) = ledgers_differing_only_in_a_non_agent_cell();
    let same = lean_side.clone();
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let root = executor.consensus_state_commitment(&lean_side, &agent);

    assert_eq!(
        classify_divergence(true, true, root, root, &lean_side, &same),
        None,
        "identical post-states, identical anchors and identical commit bits is AGREEMENT; a \
         differential that cannot say so is not a differential"
    );
}

/// The coarse legs still fire, and still take precedence — a commit-bit disagreement makes the
/// post-states incomparable, so reporting a cell there would be noise rather than a finding.
#[test]
fn the_coarse_legs_take_precedence_and_are_named() {
    let (agent, _b, lean_side, rust_side) = ledgers_differing_only_in_a_non_agent_cell();
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let lean_root = executor.consensus_state_commitment(&lean_side, &agent);

    assert_eq!(
        classify_divergence(false, true, lean_root, lean_root, &lean_side, &rust_side),
        Some(ProducerDivergence::CommitBit {
            lean: false,
            rust: true
        }),
        "a commit-bit disagreement must be reported as such, ahead of any cell difference"
    );
    let other = [0xABu8; 32];
    assert_eq!(
        classify_divergence(true, true, lean_root, other, &lean_side, &lean_side),
        Some(ProducerDivergence::Anchor {
            lean_root,
            rust_root: other
        }),
        "an anchor disagreement must be reported as such, ahead of any cell difference"
    );
}

// ───────────────────────────────────────────────────────────────────────────────────
// END-TO-END: the field is not merely computed, it is what `produce_via_lean` installs.
// ───────────────────────────────────────────────────────────────────────────────────

/// The written value MUST fit the low-64 wire carrier, or the turn is `Ineligible` and FENCED onto
/// the Rust producer — the standing `SetField` carrier residual, not a defect of this test.
const WIRE_CARRIABLE_FIELD: [u8; 32] = {
    let mut v = [0u8; 32];
    v[31] = 0xcd;
    v
};

fn node_shaped_executor() -> TurnExecutor {
    TurnExecutor::new(ComputronCosts::zero())
        .with_shadow_observer(dregg_exec_lean::LeanShadowObserver::arc())
}

fn turn_with(agent: CellId, effects: Vec<Effect>) -> Turn {
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
        nonce: 0,
        call_forest: forest,
        fee: 0,
        memo: None,
        valid_until: Some(1_000_000),
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

fn require_lean() -> bool {
    dregg_lean_ffi::demand_lean(
        dregg_lean_ffi::lean_available(),
        "verified Turn executor archive (lean_available)",
    )
}

/// ADMIT POLE, end to end. An honest self-write is decided by the verified producer, the
/// differential reports AGREEMENT **by variant** (`divergence: None`), and the verified verdict is
/// INSTALLED — the field is on the ledger and the receipt attests the Lean root. "Wired" that is
/// satisfied by a call that never fires would fail the installation assertions.
#[test]
fn an_honest_turn_is_decided_as_agreement_and_the_lean_state_is_installed() {
    if !require_lean() {
        return;
    }
    let agent = open_cell(1, 100);
    let agent_id = agent.id();
    let mut ledger = ledger_of(&[agent]);
    let executor = node_shaped_executor();

    let turn = turn_with(
        agent_id,
        vec![Effect::SetField {
            cell: agent_id,
            index: 3,
            value: WIRE_CARRIABLE_FIELD,
        }],
    );
    let (result, outcome) = produce_via_lean(&executor, &turn, &mut ledger);

    let (committed, divergence, lean_root) = match &outcome {
        ProducerOutcome::LeanAuthoritative {
            committed,
            divergence,
            lean_root,
            ..
        } => (*committed, divergence.clone(), *lean_root),
        ProducerOutcome::Fallback { reason } => panic!(
            "an owned open-cell SetField must be COVERED — the verified producer has to be the \
             thing that decided, or this pole asserts nothing. Fenced with: {reason:?}"
        ),
    };
    assert!(committed, "the verified kernel commits the self-write");
    assert_eq!(
        divergence, None,
        "the two executors must AGREE on an honest self-write, at ALL THREE legs. A `Some(..)` here \
         is a real finding about the Rust reference, not a test bug"
    );

    // …and the verdict was INSTALLED, not merely computed.
    assert_eq!(
        ledger
            .get(&agent_id)
            .and_then(|c| c.state.get_field(3).copied()),
        Some(WIRE_CARRIABLE_FIELD),
        "the committed write must be on the authoritative ledger"
    );
    match &result {
        TurnResult::Committed { receipt, .. } => assert_eq!(
            receipt.post_state_hash, lean_root,
            "the receipt must attest the AUTHORITATIVE (Lean) root — that is what makes the \
             verified producer the decider rather than a bystander that computed a number"
        ),
        other => panic!("expected Committed, got {other:?}"),
    }
}

/// REFUSE POLE, end to end, **by variant**. The under-authorised `Burn`: dregg1's `apply.rs` commits
/// it on an owned open cell, the verified `.burnA` requires an explicit mint/burn cap
/// (`mintAuthorizedB`). The verified refusal wins, and the differential names the leg that caught
/// the disagreement.
///
/// `rust_bug_surfaced()` — a bare bool — would also be `true` here. Matching the VARIANT is the
/// point: it says the commit-bit leg ran and answered, and it fails if the producer fell back or if
/// some other leg fired.
#[test]
fn a_verified_refusal_is_decided_as_a_commit_bit_divergence() {
    if !require_lean() {
        return;
    }
    let agent = open_cell(1, 100);
    let agent_id = agent.id();

    // PRECONDITION — the Rust reference really does commit this, so the pole is not satisfied by
    // both executors happening to refuse.
    {
        let mut ledger = ledger_of(&[agent.clone()]);
        let rust_only = TurnExecutor::new(ComputronCosts::zero());
        let r = rust_only.execute(
            &turn_with(
                agent_id,
                vec![Effect::Burn {
                    target: agent_id,
                    slot: 0,
                    amount: 10,
                }],
            ),
            &mut ledger,
        );
        assert!(
            r.is_committed(),
            "PRECONDITION: the legacy Rust executor must COMMIT the under-authorised burn, else \
             this pole proves nothing. Got {r:?}"
        );
    }

    let mut ledger = ledger_of(&[agent]);
    let executor = node_shaped_executor();
    let turn = turn_with(
        agent_id,
        vec![Effect::Burn {
            target: agent_id,
            slot: 0,
            amount: 10,
        }],
    );
    let (result, outcome) = produce_via_lean(&executor, &turn, &mut ledger);

    match &outcome {
        ProducerOutcome::LeanAuthoritative { divergence, .. } => assert_eq!(
            divergence.as_ref(),
            Some(&ProducerDivergence::CommitBit {
                lean: false,
                rust: true
            }),
            "the verified kernel REJECTED what the Rust reference COMMITTED — the commit-bit leg \
             must name that exactly. A different variant means a different leg answered; `None` \
             means the disagreement was laundered into agreement"
        ),
        ProducerOutcome::Fallback { reason } => panic!(
            "the burn must be COVERED so the verified producer decides it; fenced with {reason:?}"
        ),
    }

    match &result {
        TurnResult::Rejected { reason, .. } => assert!(
            matches!(
                reason,
                dregg_turn::TurnError::LeanShadowVeto
                    | dregg_turn::TurnError::AdmissionRefused { .. }
            ),
            "a verified override must report LeanShadowVeto or the named AdmissionRefused, never a \
             Rust-side error. Got {reason:?}"
        ),
        other => panic!("expected Rejected, got {other:?}"),
    }
    assert_eq!(
        ledger.get(&agent_id).map(|c| c.state.balance()),
        Some(100),
        "a verified rejection is NO state edit — the refusal must be INSTALLED, not just reported"
    );
}
