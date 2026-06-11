//! Beachhead: the LIVE fulfillment Turn IS a verified, conserving turn.
//!
//! # The gap this closes
//!
//! The existing `ring_settlement_differential.rs` pins the Rust *conservation decision*
//! (`trustless::ring_conservation_decision` = `check_settlement_conservation`) against a mirror of
//! the verified Lean `settleRing` fold. But the running engine does NOT settle by that decision —
//! it FULFILLS by lowering the winning solution to a `dregg_turn::Turn` inside
//! `TrustlessIntentEngine::finalize` (`intent/src/trustless.rs:1554` → `lowering::lower` →
//! `lowering::seal_plan_uniform`, `intent/src/lowering.rs:268 lower_settlement_leg`). NOTHING pinned
//! that the lowered fulfillment Turn moves the SAME value the verified executor would move. So a
//! drift between "what the engine ships to the executor" and "what the verified `settleRing` keystone
//! is proved over" was undetected.
//!
//! # What this test does (routes the fulfillment through the verified semantics)
//!
//! It drives the ACTUAL live engine end-to-end — encrypted submit → threshold decrypt → solver
//! submission → challenge window → `finalize()` — to obtain the real `SettlementOutput.sealed`
//! (`SealedTurn`). It then:
//!
//!   1. EXTRACTS the `Effect::Transfer { from, to, amount }` legs from the lowered `SealedTurn`'s
//!      `call_forest` (the exact Turn the executor would run).
//!   2. Reconstructs the verified-executor `Ring` from those legs and folds them through a faithful
//!      mirror of Lean `Dregg2.Intent.Ring.settleRing` (the `recKExecAsset` per-asset gate the
//!      keystones `settleRing_conserves` / `settleRing_atomic` are PROVED over).
//!   3. ASSERTS: the lowered legs are EXACTLY the solver's settlement rows (the Lean `loweredLeg`
//!      data-preservation: same from/to/asset/amount), AND the verified executor settles the funded
//!      ring fully AND conserves every touched asset.
//!
//! So "an intent fulfilled" (the lowered Turn `finalize` ships) literally settles + conserves on the
//! verified executor semantics — the Lean `lowered_fulfillment_conserves` keystone, witnessed on the
//! live path. A divergence (the lowering dropping/garbling a leg, or shipping a non-conserving Turn)
//! is caught here.

use std::collections::{BTreeMap, BTreeSet};

use dregg_cell::predicate::{InputRef, WitnessedPredicate, WitnessedPredicateKind};
use dregg_federation::threshold_decrypt::{
    KeyShare, ThresholdEncryptionKey, generate_epoch_key, produce_decryption_share,
    threshold_encrypt,
};
use dregg_intent::solver::{RingTrade, Settlement};
use dregg_intent::trustless::{
    BatchState, DEFAULT_MIN_SOLVER_BOND, EncryptedIntent, SettlementOutput, SolverSubmission,
    TrustlessIntentEngine, WitnessedProofVerifier,
};
use dregg_intent::{CommitmentId, Intent, IntentId, IntentKind, MatchSpec};

use dregg_turn::action::Effect;

// ============================================================================
// VERIFIED-EXECUTOR REFERENCE — faithful mirror of Lean `settleRing` / `recKExecAsset`.
// (Shares the per-asset-ledger contract with `ring_settlement_differential.rs`.)
// ============================================================================

/// A single extracted transfer leg: the `Effect::Transfer` data the lowered Turn carries, indexed
/// to a cell byte + 32-byte asset (the verified ledger key). Mirrors the Lean `RingLeg`.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Leg {
    from: u8,
    to: u8,
    asset: [u8; 32],
    amount: i128,
}

#[derive(Clone, Debug)]
struct Ledger {
    bal: BTreeMap<(u8, [u8; 32]), i128>,
    accounts: BTreeSet<u8>,
}

impl Ledger {
    fn get(&self, cell: u8, a: &[u8; 32]) -> i128 {
        *self.bal.get(&(cell, *a)).unwrap_or(&0)
    }
    fn set(&mut self, cell: u8, a: &[u8; 32], v: i128) {
        self.bal.insert((cell, *a), v);
    }
    fn total_asset(&self, a: &[u8; 32]) -> i128 {
        self.accounts.iter().map(|c| self.get(*c, a)).sum()
    }
}

/// `recKExecAsset` for one leg — the verified per-asset transition. `None` on a failed gate
/// (authorised: actor==src here / non-negative amount / available / distinct endpoints / both live).
fn rec_exec_asset(k: &Ledger, l: &Leg) -> Option<Ledger> {
    let src_bal = k.get(l.from, &l.asset);
    let ok = l.amount >= 0
        && l.amount <= src_bal
        && l.from != l.to
        && k.accounts.contains(&l.from)
        && k.accounts.contains(&l.to);
    if !ok {
        return None;
    }
    let mut ns = k.clone();
    ns.set(l.from, &l.asset, src_bal - l.amount);
    ns.set(l.to, &l.asset, k.get(l.to, &l.asset) + l.amount);
    Some(ns)
}

/// `settleRing` — atomic fold of the legs through the verified executor. `None` if ANY leg fails.
fn settle_ring(k0: &Ledger, legs: &[Leg]) -> Option<Ledger> {
    let mut k = k0.clone();
    for l in legs {
        match rec_exec_asset(&k, l) {
            Some(nk) => k = nk,
            None => return None,
        }
    }
    Some(k)
}

/// Fund every sender for its leg (so the availability gate passes), with all touched cells live.
fn funded_ledger(legs: &[Leg]) -> Ledger {
    let mut bal: BTreeMap<(u8, [u8; 32]), i128> = BTreeMap::new();
    let mut accounts: BTreeSet<u8> = BTreeSet::new();
    for l in legs {
        accounts.insert(l.from);
        accounts.insert(l.to);
        *bal.entry((l.from, l.asset)).or_insert(0) += l.amount;
    }
    Ledger { bal, accounts }
}

// ============================================================================
// EXTRACT the lowered fulfillment legs from the live `SealedTurn`.
// ============================================================================

/// Walk the lowered `SealedTurn`'s call forest and pull every `Effect::Transfer` leg, in order.
/// This is the EXACT set of value moves the executor would run for the fulfillment — the Lean
/// `loweredRing` the keystone `lowered_fulfillment_conserves` is stated over.
fn extract_transfer_legs(output: &SettlementOutput) -> Vec<Leg> {
    let mut legs = Vec::new();
    for root in &output.sealed.turn.call_forest.roots {
        for effect in &root.action.effects {
            if let Effect::Transfer { from, to, amount } = effect {
                legs.push(Leg {
                    from: from.as_bytes()[0],
                    to: to.as_bytes()[0],
                    // The lowering carries only from/to/amount on `Effect::Transfer` (the asset
                    // column is the settlement's; the executable per-asset move is per ring leg).
                    // We bind the asset back from the originating settlement below, so here we use
                    // a placeholder that `pair_with_settlements` overwrites.
                    asset: [0u8; 32],
                    amount: *amount as i128,
                });
            }
        }
    }
    legs
}

/// The lowering drops the per-leg `asset` onto a bare `Effect::Transfer { from, to, amount }`
/// (the executable bilateral primitive). To run the PER-ASSET verified executor we re-pair each
/// lowered leg with the asset of the settlement row it came from — matching by (from, to, amount)
/// in order. This asserts the lowering is data-preserving leg-by-leg (Lean `loweredLeg`: same
/// from/to/amount, only the authorising actor differs).
fn pair_with_settlements(legs: &mut [Leg], settlements: &[Settlement]) {
    assert_eq!(
        legs.len(),
        settlements.len(),
        "the lowered Turn must carry exactly one Transfer per settlement leg \
         (lowering must not drop or duplicate a leg)"
    );
    for (leg, s) in legs.iter_mut().zip(settlements.iter()) {
        // Data-preservation: the lowered leg's from/to/amount must equal the settlement's.
        assert_eq!(
            leg.from, s.from.0[0],
            "lowered leg `from` diverges from the settlement row"
        );
        assert_eq!(
            leg.to, s.to.0[0],
            "lowered leg `to` diverges from the settlement row"
        );
        assert_eq!(
            leg.amount, s.amount as i128,
            "lowered leg `amount` diverges from the settlement row"
        );
        leg.asset = s.asset;
    }
}

// ============================================================================
// Engine driving harness (mirrors integration_batch_lifecycle.rs).
// ============================================================================

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
    let ct = threshold_encrypt(&bytes, key).unwrap();
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

/// Build a CLOSED, conserving ring submission over the given intents: leg `i` sends asset `i` of
/// `amount` from creator[i] to creator[i+1] (a chained cycle — every cell sends and receives, each
/// asset balanced). This is the shape `RingSolver::validate_ring` emits and that
/// `check_settlement_conservation` accepts.
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

/// Drive a closed ring over `n` intents all the way to a settled `SettlementOutput`, then PIN the
/// lowered fulfillment Turn against the verified executor.
fn run_fulfillment_and_pin(n: u8, amount: u64) {
    let (key, shares) = make_keys(2, 3);
    // Stub verifier: the proof algebra is out of scope here (the lifecycle integration tests do the
    // same); what we PIN is the lowered-Turn ⟺ verified-executor coherence, which is independent of
    // the proof backend. The batch-binding gate and structural ring check still run.
    let mut engine = TrustlessIntentEngine::with_stub_verifier(2, 3);
    let intents: Vec<Intent> = (0..n).map(|b| make_intent(0x10 + b)).collect();
    drive_to_solving(&mut engine, &key, &shares, &intents);

    engine.advance_height(1);
    let sub = closed_ring_submission(0xAA, &intents, amount);
    engine
        .submit_solution(sub.clone())
        .expect("closed conserving ring must be accepted by the live engine");

    // Past the challenge window, finalize → real lowered SealedTurn.
    engine.advance_height(20);
    let output = engine
        .finalize()
        .expect("finalize must produce a settlement");

    // Extract the lowered fulfillment legs and re-pair them with the solver's settlement assets.
    let mut legs = extract_transfer_legs(&output);
    let settlements = &sub.solution[0].settlements;
    pair_with_settlements(&mut legs, settlements);

    // ROUTE THE FULFILLMENT THROUGH THE VERIFIED EXECUTOR: fold the lowered legs through the mirror
    // of Lean `settleRing` over a funded ledger; assert it settles fully AND conserves every asset.
    let k0 = funded_ledger(&legs);
    let settled = settle_ring(&k0, &legs)
        .expect("the lowered fulfillment ring must settle on the verified executor");

    let touched: BTreeSet<[u8; 32]> = legs.iter().map(|l| l.asset).collect();
    for a in touched {
        assert_eq!(
            settled.total_asset(&a),
            k0.total_asset(&a),
            "the lowered fulfillment Turn LEAKED value in asset {:02x}.. — \
             it is NOT a conserving verified turn",
            a[0]
        );
    }
}

// ============================================================================
// The beachhead tests.
// ============================================================================

#[test]
fn live_fulfillment_2ring_is_a_verified_conserving_turn() {
    run_fulfillment_and_pin(2, 50);
}

#[test]
fn live_fulfillment_3ring_is_a_verified_conserving_turn() {
    run_fulfillment_and_pin(3, 30);
}

#[test]
fn live_fulfillment_5ring_is_a_verified_conserving_turn() {
    run_fulfillment_and_pin(5, 17);
}

/// Vary the amount across a small corpus: every closed-ring fulfillment the live engine settles
/// must move exactly the lowered legs and conserve on the verified executor.
#[test]
fn live_fulfillment_corpus_conserves() {
    for n in 2u8..=6 {
        for amt in [1u64, 7, 100, 9999] {
            run_fulfillment_and_pin(n, amt);
        }
    }
}
