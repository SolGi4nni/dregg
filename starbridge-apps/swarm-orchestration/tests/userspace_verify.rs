//! Pre-submission assurance: the swarm's dispatch forest run through the
//! `dregg-userspace-verify` `analyze()` toolkit — "lint your turn before you
//! spend gas". A stranger pre-flights the swarm's plan and SEES it pass
//! (conservation + non-amplification + well-formedness) BEFORE any gas is spent,
//! and SEES the toolkit catch a deliberately-malformed plan (an amplifying grant
//! / a non-conserving move) with a precisely-located finding.
//!
//! This is the STATIC half of the assurance (read the artifact, never execute
//! it). The DYNAMIC half — whether the signer HELD the cap, whether balances
//! suffice — is the executor's job, exercised in `tests/factory_birth.rs`.

use dregg_app_framework::{AgentCipherclerk, AppCipherclerk, AuthRequired, CellId, Effect};
use dregg_cell::CapabilityRef;
use dregg_turn::forest::{CallForest, CallTree};
use starbridge_swarm_orchestration::{Worker, build_dispatch_action, build_open_board_action};

use dregg_userspace_verify::{RingLeg, analyze, check_no_amplification, check_ring_balance};

fn cclerk() -> AppCipherclerk {
    AppCipherclerk::new(AgentCipherclerk::new(), [0x71u8; 32])
}

fn board_cell() -> CellId {
    CellId::from_bytes([0xB0u8; 32])
}

fn worker_a_cell() -> CellId {
    CellId::from_bytes([0xA1u8; 32])
}

fn worker_b_cell() -> CellId {
    CellId::from_bytes([0xB2u8; 32])
}

/// Assemble a flat `CallForest` (one root per action) from a list of actions —
/// the shape `make_turn_with_actions` produces, built directly so the test does
/// not depend on the executor.
fn forest(actions: Vec<dregg_turn::action::Action>) -> CallForest {
    CallForest {
        roots: actions.into_iter().map(CallTree::new).collect(),
        forest_hash: [0u8; 32],
    }
}

/// THE SWARM'S DISPATCH PLAN PASSES THE PRE-FLIGHT. The honest open-board +
/// two-dispatch forest is conserving (no value moves — the dispatches are
/// `SetField` meters + `EmitEvent` wakes), non-amplifying (no grants), and
/// well-formed (real signatures, non-empty actions). `analyze()` returns a clean
/// verdict — the stranger sees GREEN before spending gas.
#[test]
fn the_honest_dispatch_plan_passes_userspace_verify() {
    let c = cclerk();
    let board = board_cell();
    let plan = forest(vec![
        build_open_board_action(&c, board, "lead-pk", 1000),
        build_dispatch_action(&c, board, Worker::A, worker_a_cell(), 0, 600, 1, "index"),
        build_dispatch_action(
            &c,
            board,
            Worker::B,
            worker_b_cell(),
            0,
            300,
            2,
            "summarize",
        ),
    ]);

    let assurance = analyze(&plan, false);
    assert!(
        assurance.pass(),
        "the honest dispatch plan must pass every static check; findings: {:?}",
        assurance.all_findings()
    );
    assert!(
        assurance.conservation.is_pass(),
        "no value moves ⇒ conserves"
    );
    assert!(
        assurance.no_amplification.is_pass(),
        "no grants ⇒ no amplification"
    );
    assert!(
        assurance.wellformed.is_pass(),
        "real signatures, non-empty actions"
    );
}

/// THE PAYOUT RING BALANCES. When the swarm settles worker payouts as a closed
/// ring (the coordinator pays each worker, the workers' contributions net), the
/// userspace ring-balance check certifies the cycle closes and conserves per
/// asset — the userspace twin of the Lean `settleRing_conserves`, checked on the
/// legs BEFORE the ring is lowered and submitted.
#[test]
fn a_balanced_payout_ring_passes_ring_balance() {
    let board = board_cell();
    let worker_a = worker_a_cell();
    let worker_b = worker_b_cell();
    // A closed 3-cycle: board -> a -> b -> board, 100 each. Every participant
    // nets to zero (gives 100, gets 100).
    let legs = vec![
        RingLeg {
            from: board,
            to: worker_a,
            asset: "computron".into(),
            amount: 100,
        },
        RingLeg {
            from: worker_a,
            to: worker_b,
            asset: "computron".into(),
            amount: 100,
        },
        RingLeg {
            from: worker_b,
            to: board,
            asset: "computron".into(),
            amount: 100,
        },
    ];
    let verdict = check_ring_balance(&legs);
    assert!(
        verdict.is_pass(),
        "a closed, conserving ring must pass: {:?}",
        verdict.findings()
    );

    // ...and an UN-balanced ring (a worker is a pure sink) is CAUGHT.
    let bad = vec![
        RingLeg {
            from: board,
            to: worker_a,
            asset: "computron".into(),
            amount: 100,
        },
        // worker_a never gives it back: a pure sink — the ring does not close.
    ];
    let verdict = check_ring_balance(&bad);
    assert!(!verdict.is_pass(), "an open ring must be caught");
    assert!(
        verdict.findings().iter().any(|f| f.guarantee == "ring"),
        "the finding must name the ring guarantee"
    );
}

/// THE OVER-GRANT (the static, in-artifact half of no-amplification) IS CAUGHT.
/// A forest where the coordinator delegates a worker a NARROW cap (restricted to
/// `EFFECT_SET_FIELD`) and the worker then re-grants a WIDER cap (adding
/// `EFFECT_TRANSFER`) for the same target is structurally amplifying — exactly
/// the over-grant the executor's non-amplification gate would reject, found here
/// FIRST, with a precise locus, before any gas is spent. The Lean
/// `worker_cannot_widen_reach` / `derive_no_amplify`, statically.
#[test]
fn an_amplifying_grant_is_caught_by_userspace_verify() {
    let c = cclerk();
    let board = board_cell();
    let worker = worker_a_cell();
    let resource = CellId::from_bytes([0xCC; 32]);

    // The coordinator delegates the worker a NARROW cap over `resource`:
    // SetField only (no Transfer).
    let narrow = CapabilityRef {
        target: resource,
        slot: 0,
        permissions: AuthRequired::Signature,
        breadstuff: None,
        expires_at: None,
        allowed_effects: Some(dregg_cell::facet::EFFECT_SET_FIELD),
        stored_epoch: None,
    };
    // The worker then tries to re-grant a WIDER cap over the SAME resource:
    // adding Transfer — an amplification of what it was handed.
    let wide = CapabilityRef {
        target: resource,
        slot: 0,
        permissions: AuthRequired::Signature,
        breadstuff: None,
        expires_at: None,
        allowed_effects: Some(
            dregg_cell::facet::EFFECT_SET_FIELD | dregg_cell::facet::EFFECT_TRANSFER,
        ),
        stored_epoch: None,
    };

    // Build the delegation chain as a real parent->child forest: the board's
    // root grants `narrow` to the worker; a CHILD node (the worker) grants `wide`
    // onward — the amplification is provable in-artifact.
    let board_grant = c.make_action(
        board,
        "delegate",
        vec![Effect::GrantCapability {
            from: board,
            to: worker,
            cap: narrow.clone(),
        }],
    );
    let worker_regrant = c.make_action(
        worker,
        "redelegate",
        vec![Effect::GrantCapability {
            from: worker,
            to: CellId::from_bytes([0xDD; 32]),
            cap: wide.clone(),
        }],
    );
    let mut root = CallTree::new(board_grant);
    root.add_child(worker_regrant);
    let amplifying = CallForest {
        roots: vec![root],
        forest_hash: [0u8; 32],
    };

    let verdict = check_no_amplification(&amplifying);
    assert!(
        !verdict.is_pass(),
        "the amplifying re-grant must be CAUGHT — the over-grant tooth (static)"
    );
    let findings = verdict.findings();
    assert!(
        findings
            .iter()
            .any(|f| f.guarantee.contains("non-amplification")),
        "the finding must name guarantee A (non-amplification); got {findings:?}"
    );
    assert!(
        findings.iter().any(|f| f.message.contains("amplifies")),
        "the finding must explain the amplification; got {findings:?}"
    );

    // The CONVERSE (non-vacuity): an ATTENUATING re-grant (the worker narrows
    // further — Transfer only, a SUBSET of the SetField+... it would need... here
    // we keep it within `narrow` by re-granting the SAME narrow cap) PASSES.
    let attenuating_regrant = c.make_action(
        worker,
        "redelegate",
        vec![Effect::GrantCapability {
            from: worker,
            to: CellId::from_bytes([0xDD; 32]),
            cap: narrow.clone(),
        }],
    );
    let mut root2 = CallTree::new(c.make_action(
        board,
        "delegate",
        vec![Effect::GrantCapability {
            from: board,
            to: worker,
            cap: narrow,
        }],
    ));
    root2.add_child(attenuating_regrant);
    let attenuating = CallForest {
        roots: vec![root2],
        forest_hash: [0u8; 32],
    };
    assert!(
        check_no_amplification(&attenuating).is_pass(),
        "an attenuating (subset) re-grant must PASS — the tooth is non-vacuous"
    );
}

/// A NON-CONSERVING MOVE IS CAUGHT. A forest whose `balance_change` deltas do
/// not net to zero (value conjured) is rejected by `check_conservation` with the
/// asset column and the net residue named — the cheap pre-flight catching what
/// the executor's conservation law would reject.
#[test]
fn a_non_conserving_move_is_caught_by_userspace_verify() {
    let c = cclerk();
    let board = board_cell();
    // An action that conjures +500 with no offsetting debit (a balance_change
    // delta with no counterpart) — does not conserve.
    let mut conjure = c.make_action(
        board,
        "conjure",
        vec![Effect::EmitEvent {
            cell: board,
            event: dregg_turn::action::Event::new(dregg_turn::action::symbol("conjure"), vec![]),
        }],
    );
    conjure.balance_change = Some(500);
    let bad = forest(vec![conjure]);

    let assurance = analyze(&bad, false);
    assert!(
        !assurance.conservation.is_pass(),
        "a non-conserving move must be CAUGHT by the conservation check"
    );
    assert!(
        assurance
            .conservation
            .findings()
            .iter()
            .any(|f| f.guarantee.contains("conservation")),
        "the finding must name guarantee B (conservation)"
    );
}

/// A structural sanity the userspace view depends on: a single dispatch forest
/// is well-formed (real signature + non-empty action), so the verifier's
/// well-formedness check passes it.
#[test]
fn dispatch_is_well_formed_for_the_verifier() {
    let c = cclerk();
    let board = board_cell();
    let plan = forest(vec![build_dispatch_action(
        &c,
        board,
        Worker::A,
        worker_a_cell(),
        0,
        100,
        2,
        "t",
    )]);
    // well-formedness: real signature + non-empty action.
    assert!(analyze(&plan, false).wellformed.is_pass());
}
