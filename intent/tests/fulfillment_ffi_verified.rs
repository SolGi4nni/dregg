//! The LIVE-FFI fulfillment test: a fulfilled intent IS settled through the REAL verified Lean
//! executor — not a Rust mirror.
//!
//! # What this closes (over `fulfillment_verified_turn.rs`)
//!
//! `fulfillment_verified_turn.rs` drives the live engine to a `SettlementOutput` and folds the
//! lowered legs through a *Rust re-implementation* of the Lean `settleRing` (a hand-mirror of
//! `recKExecAsset`). That pins the SEMANTICS agree, but the executor it runs is still Rust.
//!
//! This test routes the SAME live `finalize()` output through
//! [`dregg_intent::trustless::TrustlessIntentEngine::finalize_verified`], which folds each lowered
//! leg through the REAL Lean FFI (`@[export] dregg_record_kernel_step` over the PROVED
//! `Exec.recKExec`, per the Lean keystone `Dregg2.Intent.RingFFI.ffi_export_realises_settleRing_leg`)
//! over the leg's asset-projected column, AND cross-checks the in-process verified transition
//! against the export's verdict + post-column — failing closed on any drift. So here "an intent
//! fulfilled" literally executes through the linked verified kernel and conserves there.
//!
//! Gated on the `verified-settle` feature (links `libdregg_lean.a`). Run with:
//!   cargo test -p dregg-intent --features verified-settle --test fulfillment_ffi_verified

#![cfg(feature = "verified-settle")]

use dregg_federation::threshold_decrypt::{
    KeyShare, ThresholdEncryptionKey, generate_epoch_key, produce_decryption_share,
};
use dregg_intent::solver::{RingTrade, Settlement};
use dregg_intent::trustless::{
    BatchState, DEFAULT_MIN_SOLVER_BOND, EncryptedIntent, SolverSubmission, TrustlessIntentEngine,
    WitnessedProofVerifier,
};
use dregg_intent::verified_settle::touched_assets;
use dregg_intent::{CommitmentId, Intent, IntentId, IntentKind, MatchSpec};

use dregg_cell::predicate::{InputRef, WitnessedPredicate, WitnessedPredicateKind};

fn make_keys(threshold: u8, n: u8) -> (ThresholdEncryptionKey, Vec<KeyShare>) {
    generate_epoch_key([0xBBu8; 32], threshold, n)
}

fn make_intent(seed: u8) -> Intent {
    let spec = MatchSpec {
        actions: vec![],
        constraints: vec![],
        min_budget: None,
        resource_pattern: None,
        compound: None,
        predicate_requirements: vec![],
        strict_resource_matching: false,
    };
    Intent::new(
        IntentKind::Offer,
        spec,
        CommitmentId([seed; 32]),
        99999,
        None,
    )
}

fn encrypt(intent: &Intent, key: &ThresholdEncryptionKey) -> EncryptedIntent {
    let bytes = postcard::to_allocvec(intent).unwrap();
    let ct = dregg_federation::threshold_decrypt::threshold_encrypt(&bytes, key).unwrap();
    EncryptedIntent {
        ciphertext: ct,
        creator_commitment: intent.creator,
        submitted_at: 1,
    }
}

fn drive_to_solving(
    engine: &mut TrustlessIntentEngine,
    key: &ThresholdEncryptionKey,
    shares: &[KeyShare],
    intents: &[Intent],
) {
    for b in 0u8..=255 {
        engine.deposit_bond(&[b; 32], DEFAULT_MIN_SOLVER_BOND * 20);
    }
    let mut encs = Vec::new();
    for intent in intents {
        let enc = encrypt(intent, key);
        engine.submit_encrypted(enc.clone()).unwrap();
        encs.push(enc);
    }
    engine.close_batch(10).unwrap();
    for enc in &encs {
        for ks in shares.iter().take(engine.decrypt_threshold) {
            engine
                .contribute_decrypt_share(produce_decryption_share(&enc.ciphertext, ks))
                .unwrap();
        }
    }
    assert_eq!(engine.batch_state(), BatchState::Solving);
}

/// A closed, conserving ring over the given intents: leg `i` sends asset `i` from creator[i] to
/// creator[i+1] (a chained cycle). The shape `validate_ring` emits / `check_settlement_conservation`
/// accepts.
fn closed_ring_submission(solver_byte: u8, intents: &[Intent], amount: u64) -> SolverSubmission {
    let participants: Vec<IntentId> = intents.iter().map(|i| i.id).collect();
    let settlements: Vec<Settlement> = intents
        .iter()
        .enumerate()
        .map(|(i, it)| Settlement {
            from: it.creator,
            to: intents[(i + 1) % intents.len()].creator,
            asset: {
                let mut a = [0u8; 32];
                a[0] = 0xA0 + i as u8;
                a
            },
            amount,
        })
        .collect();
    let score = intents.len() as f64;
    let commitment = WitnessedProofVerifier::compute_batch_binding(intents);
    SolverSubmission {
        solver_id: [solver_byte; 32],
        solution: vec![RingTrade {
            participants,
            settlements,
            score,
        }],
        total_score: score,
        validity_proof: vec![0x01, 0x02, 0x03],
        witnessed_predicate: Some(WitnessedPredicate {
            kind: WitnessedPredicateKind::MerkleMembership,
            commitment,
            input_ref: InputRef::PublicInput { pi_index: 0 },
            proof_witness_index: 0,
        }),
        bond: DEFAULT_MIN_SOLVER_BOND,
        submitted_at: 11,
    }
}

/// Drive a closed ring all the way to `finalize_verified`, asserting the verified Lean executor
/// settles it AND conserves every asset (the post-ledger equals the funded pre-ledger per asset).
fn run_ffi_verified(n: u8, amount: u64) {
    let (key, shares) = make_keys(2, 3);
    let mut engine = TrustlessIntentEngine::with_stub_verifier(2, 3);
    let intents: Vec<Intent> = (0..n).map(|b| make_intent(0x10 + b)).collect();
    drive_to_solving(&mut engine, &key, &shares, &intents);

    engine.advance_height(1);
    let sub = closed_ring_submission(0xAA, &intents, amount);
    engine
        .submit_solution(sub.clone())
        .expect("closed conserving ring accepted by the live engine");

    engine.advance_height(20);

    // THE LIVE FFI PATH: finalize + settle through the REAL verified Lean executor.
    let (output, k0, k1) = engine
        .finalize_verified()
        .expect("finalize_verified: the lowered fulfillment must settle on the verified executor");

    assert!(!output.sealed.turn.call_forest.roots.is_empty());

    // The verified executor conserved every touched asset (the Lean `settleRing_conserves`,
    // witnessed through the REAL FFI, not a mirror).
    let legs =
        dregg_intent::verified_settle::extract_legs(&output.sealed, &sub.solution[0].settlements)
            .expect("legs extract");
    for a in touched_assets(&legs) {
        assert_eq!(
            k1.total_asset(&a),
            k0.total_asset(&a),
            "verified Lean executor leaked value in asset {:02x}.. — NOT a conserving verified turn",
            a[0]
        );
    }
}

#[test]
fn live_fulfillment_2ring_is_verified_by_the_lean_ffi() {
    run_ffi_verified(2, 50);
}

#[test]
fn live_fulfillment_3ring_is_verified_by_the_lean_ffi() {
    run_ffi_verified(3, 30);
}

#[test]
fn live_fulfillment_corpus_verified_by_the_lean_ffi() {
    for n in 2u8..=5 {
        for amt in [1u64, 7, 100, 9999] {
            run_ffi_verified(n, amt);
        }
    }
}
