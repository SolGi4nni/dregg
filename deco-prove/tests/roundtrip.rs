//! **End-to-end: the DECO prover → the REAL bridge verifier → a conserved mint.**
//!
//! Round-trips through the ACTUAL `dregg_bridge::stripe_deco` verifier (not a mock):
//! the prover produces an attestation, the bridge verifier accepts honest facts and
//! mints the conserved amount, and any forged fact is REFUSED
//! (`DecoCommitmentMismatch`) — no mint. The genuine-STARK path is the SLOW
//! `#[ignore]` test (real recursion, ~seconds+, the codebase convention for the
//! recursion prover); the fast test exercises the full verifier + mint pipeline.

use dregg_bridge::{
    DecoPaymentAttestation, MoneyIn, StripeMirrorConfig, StripeMirrorError, StripeMirrorState,
};
use dregg_circuit::field::BabyBear;
use dregg_deco_prove::prover::StripePaymentFacts;
use dregg_deco_prove::{
    NotaryKeypair, prove_stripe_deco, verify_notary_attestation, verify_stripe_deco_stark,
};
use dregg_types::CellId;

const MIRROR_ASSET: [u8; 32] = [0xCDu8; 32];

fn config() -> StripeMirrorConfig {
    StripeMirrorConfig {
        asset: MIRROR_ASSET,
        webhook_secret: b"whsec_unused_on_the_deco_path".to_vec(),
        currency: "usd".to_string(),
        min_cents: 50,
        max_cents: 1_000_000_00,
    }
}

fn facts(intent: &str, amount: u64, rcpt: u8) -> StripePaymentFacts {
    StripePaymentFacts {
        payment_intent_id: intent.to_string(),
        amount_cents: amount,
        currency: "usd".to_string(),
        recipient: CellId::from_bytes([rcpt; 32]),
    }
}

/// FAST: the prover's fact projection round-trips through the REAL bridge verifier and
/// mints the conserved amount; a forged (post-hoc bumped) fact is refused. No heavy
/// STARK — this pins the verifier + mint + conservation pipeline; the genuine-proof
/// carrier is exercised by [`deco_prover_full_stark_roundtrip_mints`] (SLOW).
#[test]
fn deco_prover_facts_roundtrip_through_real_verifier_and_mints() {
    let mut mirror = StripeMirrorState::new(config());
    let f = facts("pi_rt_honest", 2500, 1);

    // The prover's canonical attestation (STARK carrier omitted for the fast path —
    // the same felt identity the full prover commits).
    let att = DecoPaymentAttestation::attest(
        f.payment_intent_id.clone(),
        f.amount_cents,
        f.currency.clone(),
        f.recipient,
        None,
    );
    assert_eq!(att.payment_hash, f.payment_hash());

    // The REAL bridge verifier accepts + mints the conserved amount.
    let minted = mirror
        .mint_against_deco(&att)
        .expect("honest DECO attestation mints through the real verifier");
    assert_eq!(minted.amount, 2500);
    assert_eq!(minted.recipient, f.recipient);
    assert_eq!(mirror.live_supply, 2500);
    assert_eq!(mirror.total_verified_payments, 2500);
    assert!(mirror.invariant_holds());

    // A forged fact (bumped amount, stale committed identity) is REFUSED — no mint.
    let mut forged = att.clone();
    forged.amount_cents = 9_999_999;
    assert_eq!(
        mirror.verify_deco_payment(&forged).unwrap_err(),
        StripeMirrorError::DecoCommitmentMismatch
    );
    // And through the single production entry.
    assert_eq!(
        mirror.verify_money_in(MoneyIn::Deco(&forged)).unwrap_err(),
        StripeMirrorError::DecoCommitmentMismatch
    );
    assert_eq!(mirror.live_supply, 2500, "no forgery minted");
}

/// FAST: the notary (interim MPC-TLS capture) layer binds the SAME disclosed facts the
/// prover attests — the origin attestation and the identity commitment agree, and a
/// forged fact breaks the notary commitment too. (Named trust boundary: semi-honest
/// notary observed a real Stripe session; see docs/deos/DECO-PROVER-STATUS.md.)
#[test]
fn notary_attestation_binds_the_same_disclosed_facts() {
    let kp = NotaryKeypair::from_seed(&[9u8; 32]);
    let salt = BabyBear::new(0x1234);
    let f = facts("pi_rt_notary", 4200, 3);

    let notary_att = kp.attest(&f, salt);
    assert_eq!(notary_att.commitment.payment_hash, f.payment_hash());
    assert_eq!(
        verify_notary_attestation(&notary_att, &kp.public_key(), &f, salt),
        Ok(())
    );

    // A bumped amount no longer opens the notarized commitment.
    let mut forged = f.clone();
    forged.amount_cents = 9_999;
    assert!(verify_notary_attestation(&notary_att, &kp.public_key(), &forged, salt).is_err());
}

/// SLOW (real recursion, ~seconds+): the FULL prover core — produce an attestation with
/// a GENUINE STARK proof over the deployed DECO leaf AIR, re-verify the carried proof
/// binds the facts, round-trip through the REAL bridge verifier, and mint the conserved
/// amount. Then tamper the facts: BOTH the STARK re-verify (`ProofFactsMismatch`) and
/// the bridge felt-commitment binding (`DecoCommitmentMismatch`) refuse it — the prover
/// cannot forge a passing attestation.
#[test]
#[ignore = "SLOW: real recursion leaf prove (~seconds+); run with --ignored"]
fn deco_prover_full_stark_roundtrip_mints() {
    let mut mirror = StripeMirrorState::new(config());
    let f = facts("pi_full_stark", 2500, 1);
    let salt = BabyBear::new(0x55);

    // Produce a genuine STARK-carrying attestation.
    let att = prove_stripe_deco(&f, salt).expect("the honest DECO prover emits an attestation");
    assert!(
        att.zk_tls_proof.is_some(),
        "the attestation carries a genuine STARK proof"
    );
    assert_eq!(att.payment_hash, f.payment_hash());

    // The carried STARK proof re-verifies (structural + exposed-claim binding to facts).
    verify_stripe_deco_stark(&att).expect("the carried STARK proof binds the disclosed facts");

    // The REAL bridge verifier accepts + mints the conserved amount.
    let minted = mirror
        .mint_against_deco(&att)
        .expect("the STARK-carrying attestation mints through the real verifier");
    assert_eq!(minted.amount, 2500);
    assert_eq!(mirror.live_supply, 2500);
    assert!(mirror.invariant_holds());

    // Tamper the facts on the produced attestation (the DecoBackingAttack shape).
    let mut forged = att.clone();
    forged.amount_cents = 9_999_999;
    // (1) the STARK's exposed identity no longer binds the bumped amount.
    assert_eq!(
        verify_stripe_deco_stark(&forged).unwrap_err(),
        dregg_deco_prove::DecoProveError::ProofFactsMismatch
    );
    // (2) the bridge felt-commitment binding refuses it too — no mint.
    assert_eq!(
        mirror.verify_deco_payment(&forged).unwrap_err(),
        StripeMirrorError::DecoCommitmentMismatch
    );
    assert_eq!(mirror.live_supply, 2500, "no forgery minted");
}
