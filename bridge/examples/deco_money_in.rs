//! `deco_money_in` — the audited DECO/zkTLS money-in, run for real (test-mode fixture).
//!
//! The runnable spine of `docs/WALKTHROUGH.md` §Earn. It exercises the PROVEN,
//! trustless Stripe money-in ([`dregg_bridge::stripe_deco`]): mint dregg USD-credit
//! ONLY against a DECO attestation that a settled Stripe payment occurred, and let
//! the reader RE-VERIFY the binding themselves.
//!
//! ## Honest label — read this first
//!
//! This example carries a **test-mode fixture attestation** (`zk_tls_proof: None`),
//! so it MUST be built with the `test-utils` feature:
//!
//!   cargo run -p dregg-bridge --example deco_money_in --features test-utils
//!
//! That is not a convenience — it is compiler-enforced honesty. A PRODUCTION build
//! (`DECO_REQUIRES_STARK_PROOF = cfg!(not(any(test, feature = "test-utils")))`)
//! REFUSES a `None`-carrier attestation with `DecoProofMissing`. The live prover
//! that turns a real Stripe TLS session into a genuine DECO leaf STARK lives in the
//! `dregg-deco-prove` crate (`prove_stripe_deco`, MPC-TLS/notary capture). So this
//! run proves the VERIFICATION teeth (range + felt-commitment binding + conserved
//! mint) over a fixture; it does NOT claim a live Stripe session occurred.

use dregg_bridge::stripe_deco::MoneyIn;
use dregg_bridge::{
    DecoPaymentAttestation, StripeMirrorConfig, StripeMirrorError, StripeMirrorState,
};
use dregg_cell::CellId;
use dregg_circuit::dsl::deco_payment::stripe_payment_hash_felt;
use dregg_turn::action::Effect;

fn cid(b: u8) -> CellId {
    CellId::from_bytes([b; 32])
}

fn config() -> StripeMirrorConfig {
    StripeMirrorConfig {
        // The USD-credit mirror asset (1 unit = 1 cent).
        asset: [0xCDu8; 32],
        // Unused on the DECO path (the HMAC fallback's verifying key).
        webhook_secret: b"whsec_unused_on_the_deco_path".to_vec(),
        currency: "usd".to_string(),
        min_cents: 50,
        max_cents: 1_000_000_00,
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("== the audited DECO/zkTLS money-in (test-mode fixture) ==\n");

    // The recipient is the agent cell that EARNS the credit — the same cell a grain
    // owner would fund. Tie it to your grain's owner cell in a real run.
    let recipient = cid(1);
    let amount_cents = 2500; // $25.00 cleared at Stripe

    // ── 1. THE ATTESTATION (fixture) ────────────────────────────────────────────
    // `attest` decomposes the disclosed facts to the committed felt identity via the
    // ONE canonical encoder the in-AIR DECO leaf recomputes. `zk_tls_proof: None`
    // marks this a fixture (see the honest label above).
    let att =
        DecoPaymentAttestation::attest("pi_walkthrough_001", amount_cents, "usd", recipient, None);
    println!("[deco ] attestation: payment_intent=pi_walkthrough_001 amount={amount_cents}c usd");
    println!("        recipient={:?}", recipient.0[0]);
    println!(
        "        committed payment_hash (felt): {:?}\n",
        att.payment_hash
    );

    // ── 2. VERIFY the money-in — the production entry, dispatched to the DECO path ─
    let mirror0 = StripeMirrorState::new(config());
    let verified = mirror0.verify_money_in(MoneyIn::Deco(&att))?;
    println!("[verify] DECO teeth passed: amount={}c", verified.amount);
    println!("         gate-5 range ✓ · felt-commitment binding ✓ · currency/bounds ✓");
    println!("         consume-once nullifier bound (double-mint gate)\n");

    // ── 3. MINT — draw the conserved credit ─────────────────────────────────────
    // mint_against_deco records the verified backing and draws the mint against it,
    // so `live_supply <= total_verified_payments` BITES exactly as on the HMAC path.
    let mut mirror = StripeMirrorState::new(config());
    let minted = mirror.mint_against_deco(&att)?;
    match minted.effect {
        Effect::Mint {
            target,
            slot,
            amount,
        } => {
            println!(
                "[mint ] Effect::Mint target={:?} slot={slot} amount={amount}",
                target.0[0]
            );
        }
        ref other => println!("[mint ] unexpected effect: {other:?}"),
    }
    println!(
        "         conservation: live_supply={} total_verified={} invariant_holds={}\n",
        mirror.live_supply,
        mirror.total_verified_payments,
        mirror.invariant_holds()
    );
    assert!(mirror.invariant_holds());
    assert_eq!(mirror.live_supply, amount_cents);

    // ── 4. SELF-VERIFY — recompute the commitment YOURSELF, trusting no oracle ────
    // The reader recomputes the canonical felt over the disclosed facts through the
    // SAME encoder the executor, the deployed producer, and the in-AIR leaf all use.
    // A forged-facts attestation cannot reproduce it.
    let recomputed =
        stripe_payment_hash_felt(amount_cents, "usd", &recipient.0, "pi_walkthrough_001");
    assert_eq!(
        recomputed, att.payment_hash,
        "the disclosed facts recompute to the committed identity"
    );
    assert_eq!(
        recomputed, verified.payment_hash,
        "the executor minted against the SAME felt identity"
    );
    println!("[self ] recomputed the felt commitment independently — it MATCHES the mint.\n");

    // ── 5. THE ANTI-VACUITY TOOTH — a forged-facts attestation is REFUSED ────────
    // Bump the amount after the identity was committed: the felt-commitment binding
    // fails, no mint. (This is why the recompute above is meaningful, not vacuous.)
    let mut forged = DecoPaymentAttestation::attest("pi_forge", 2500, "usd", recipient, None);
    forged.amount_cents = 999_999; // tamper: claim more than the committed identity backs
    match StripeMirrorState::new(config()).verify_money_in(MoneyIn::Deco(&forged)) {
        Err(StripeMirrorError::DecoCommitmentMismatch) => {
            println!(
                "[tooth] a FORGED-FACTS attestation is REFUSED (DecoCommitmentMismatch) — no mint.\n"
            );
        }
        other => panic!("a forged attestation must be refused, got {other:?}"),
    }

    println!("== GREEN: money-in verified + conserved-minted from a DECO attestation,");
    println!("   re-verifiable by hand; a forgery is refused. (fixture — live prover =");
    println!("   dregg-deco-prove; production requires the STARK carrier.) ==");
    Ok(())
}
