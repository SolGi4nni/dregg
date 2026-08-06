//! Stage 7-γ.2 Phase 1 — bilateral cross-cell PI AGREEMENT demo / integration test.
//!
//! ⚑ 2026-08-05: this file used to drive the `dregg-verifier bilateral-pair` SUBPROCESS
//! and assert `exit 0` + `"verified": true`. That subcommand is DELETED, because every
//! `WitnessedReceipt` it printed `verified: true` over carried `proof_bytes: []` — it
//! verified no proof and could not have. The demo now calls the library entry point,
//! which is named for what it does (`check_bilateral_pi_agreement`) and reports
//! `pi_agrees_with_schedule` alongside `entries_without_proof`.
//!
//! What it demonstrates, and the boundary:
//!
//!   1. Build a [`Turn`] with a Transfer(alice → bob).
//!   2. Fabricate per-cell PI-ONLY [`WitnessedReceipt`]s for alice + bob with the γ.2
//!      bilateral PI slots populated and NO proof bytes.
//!   3. The schedule reconstructed from the canonical `Turn` AGREES with those PI
//!      vectors, and the result says both things: it agrees, and 2 of 2 entries have
//!      nothing behind them.
//!   4. Tamper with the bundle (overwrite Alice's `OUTGOING_TRANSFER_ROOT` with
//!      garbage) and the agreement REFUSES.
//!   5. Ship only one half of a bilateral Transfer and the cross-side existence check
//!      REFUSES (§4.5 of STAGE-7-GAMMA-2-PI-DESIGN.md).
//!
//! Steps 4 and 5 are real refusals of the agreement algebra. Step 3's caveat is the
//! whole reason the CLI is gone: cross-cell agreement layers ON TOP of per-cell proof
//! soundness (`dregg_verifier::verify_rotated_leg` /
//! `dregg_sdk::verify_effect_vm_rotated_with_cutover`), it does not supply it.

use dregg_circuit::effect_vm::pi as p;
use dregg_turn::{ActionBuilder, Turn, TurnBuilder, TurnReceipt};
use dregg_types::CellId;
use dregg_verifier::{
    BilateralBundle, BilateralEntry, BilateralPiAgreement, check_bilateral_pi_agreement,
    fabricate_pi_only_witnessed_receipt,
};

fn cid(b: u8) -> CellId {
    CellId::from_bytes([b; 32])
}

fn dummy_receipt(agent: CellId) -> TurnReceipt {
    TurnReceipt {
        turn_hash: [0u8; 32],
        forest_hash: [0u8; 32],
        pre_state_hash: [0u8; 32],
        post_state_hash: [0u8; 32],
        timestamp: 0,
        effects_hash: [0u8; 32],
        computrons_used: 0,
        action_count: 0,
        previous_receipt_hash: None,
        agent,
        federation_id: [0u8; 32],
        routing_directives: vec![],
        introduction_exports: vec![],
        derivation_records: vec![],
        emitted_events: vec![],
        executor_signature: None,
        finality: Default::default(),
        was_encrypted: false,
        was_burn: false,
        consumed_capabilities: vec![],
    }
}

fn make_transfer_turn(alice: CellId, bob: CellId, amount: u64, nonce: u64) -> Turn {
    let mut builder = TurnBuilder::new(alice, nonce);
    let action = ActionBuilder::new_unchecked_for_tests(alice, "transfer", alice)
        .effect_transfer(alice, bob, amount)
        .build();
    builder.add_action(action);
    builder.fee(0).build()
}

/// Round-trip the bundle through its on-disk JSON shape (an auditor ships one file),
/// then run the agreement check on what came back out.
fn check_via_json(bundle: &BilateralBundle) -> BilateralPiAgreement {
    let json = serde_json::to_string_pretty(bundle).expect("serialize");
    let round_tripped: BilateralBundle = serde_json::from_str(&json).expect("deserialize");
    check_bilateral_pi_agreement(&round_tripped)
}

#[test]
fn bilateral_pair_demo_happy_path_then_tamper() {
    // ---- Step 1-3: build the honest bundle ----
    let alice = cid(0xA1);
    let bob = cid(0xB2);
    let turn = make_transfer_turn(alice, bob, 100, 1);
    let alice_wr = fabricate_pi_only_witnessed_receipt(&turn, &alice, dummy_receipt(alice));
    let bob_wr = fabricate_pi_only_witnessed_receipt(&turn, &bob, dummy_receipt(alice));

    let bundle = BilateralBundle {
        turn: turn.clone(),
        entries: vec![
            BilateralEntry {
                cell_id: alice,
                witnessed_receipt: alice_wr.clone(),
            },
            BilateralEntry {
                cell_id: bob,
                witnessed_receipt: bob_wr.clone(),
            },
        ],
        unilateral_attestations: std::collections::BTreeMap::new(),
    };
    // ---- Step 3: the schedule agrees, AND the scope is reported ----
    let verdict = check_via_json(&bundle);
    assert!(
        verdict.pi_agrees_with_schedule,
        "the honest bundle's PI must agree with the schedule: {verdict:?}"
    );
    assert_eq!(
        verdict.entries_without_proof, 2,
        "both entries are PI-only, and the result must SAY so rather than print \
         `verified: true` over them: {verdict:?}"
    );
    assert_eq!(verdict.entry_count, 2);
    assert_eq!(verdict.transfer_count, 1);
    assert_eq!(verdict.grant_count, 0);
    assert_eq!(verdict.introduce_count, 0);

    // ---- Step 6: tamper with Alice's OUTGOING_TRANSFER_ROOT ----
    let mut tampered_alice = alice_wr;
    tampered_alice.public_inputs[p::OUTGOING_TRANSFER_ROOT_BASE] = 0xDEAD_BEEF & 0x7FFF_FFFF;
    let tampered_bundle = BilateralBundle {
        turn,
        entries: vec![
            BilateralEntry {
                cell_id: alice,
                witnessed_receipt: tampered_alice,
            },
            BilateralEntry {
                cell_id: bob,
                witnessed_receipt: bob_wr,
            },
        ],
        unilateral_attestations: std::collections::BTreeMap::new(),
    };
    let verdict = check_via_json(&tampered_bundle);
    assert!(
        !verdict.pi_agrees_with_schedule,
        "tampered bundle must REFUSE: {verdict:?}"
    );
    assert!(
        verdict.reason.contains("root") || verdict.reason.contains("outgoing_transfer"),
        "expected root-mismatch reason, got: {}",
        verdict.reason
    );
}

#[test]
fn bilateral_pair_demo_missing_peer_rejects() {
    // Demo: a malicious prover who tries to ship only one half of a
    // bilateral Transfer (the sender's WR) and elide the receiver. The
    // agreement check rejects on the cross-side existence check
    // — this is the §4.5 "sender invents a transfer to a non-existent cell"
    // adversarial case from STAGE-7-GAMMA-2-PI-DESIGN.md.
    let alice = cid(0xA1);
    let bob = cid(0xB2);
    let turn = make_transfer_turn(alice, bob, 100, 1);
    let alice_wr = fabricate_pi_only_witnessed_receipt(&turn, &alice, dummy_receipt(alice));

    let bundle = BilateralBundle {
        turn,
        entries: vec![BilateralEntry {
            cell_id: alice,
            witnessed_receipt: alice_wr,
        }],
        unilateral_attestations: std::collections::BTreeMap::new(),
    };
    let verdict = check_via_json(&bundle);
    assert!(
        !verdict.pi_agrees_with_schedule,
        "missing-peer bundle must REFUSE: {verdict:?}"
    );
    assert!(
        verdict.reason.contains("missing peer") || verdict.reason.contains("Transfer"),
        "expected missing-peer reason, got: {}",
        verdict.reason
    );
}
