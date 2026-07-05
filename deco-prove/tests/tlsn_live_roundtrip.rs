//! **The REAL local MPC-TLS roundtrip → DECO mint** (feature-gated `tlsn-live`).
//!
//! A genuine `tlsn` Prover + a real local Notary run the MPC-TLS 2PC handshake against a
//! test HTTPS server returning a Stripe-payment-shaped JSON, the Prover selectively
//! discloses the payment facts (hiding the `Authorization` secret), signs a real
//! `Attestation`, builds a real `Presentation`, and `presentation.verify()` yields a real
//! `PresentationOutput`. The extracted facts drive a conserved mint through the REAL
//! `dregg_bridge::stripe_deco` verifier. A tampered presentation fails the real `verify()`.
//!
//! Run with: `cargo test -p dregg-deco-prove --features tlsn-live --test tlsn_live_roundtrip`.
#![cfg(feature = "tlsn-live")]

use dregg_bridge::{DecoPaymentAttestation, StripeMirrorConfig, StripeMirrorState};
use dregg_deco_prove::tlsn_live::{
    LivePayment, run_local_roundtrip_blocking, verify_stripe_presentation,
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

/// THE DELIVERABLE — the whole chain runs on REAL tlsn, not a fixture:
///   real MPC-TLS 2PC roundtrip → real Attestation → real Presentation →
///   real presentation.verify() → extracted facts → DECO mint (conserved).
/// Plus: the Authorization secret is hidden (selective disclosure), and a tampered
/// presentation is refused by the REAL verify().
#[test]
fn real_local_mpc_tls_roundtrip_mints_and_tamper_is_refused() {
    let recipient = CellId::from_bytes([5u8; 32]);
    let payment = LivePayment::settled("pi_3RealMpcTls", 2500, recipient);

    // ── Run the genuine local MPC-TLS roundtrip (server + notary + prover in-process).
    let roundtrip =
        run_local_roundtrip_blocking(&payment).expect("real MPC-TLS roundtrip + verify");

    // The verified, extracted facts came out of the AUTHENTICATED transcript.
    let v = &roundtrip.verified;
    assert_eq!(v.facts.payment_intent_id, "pi_3RealMpcTls");
    assert_eq!(v.facts.amount_cents, 2500);
    assert_eq!(v.facts.currency, "usd");
    assert_eq!(v.facts.recipient, recipient);
    assert_eq!(v.server_name, roundtrip.pinned_server);

    // Selective disclosure: the Authorization secret was NOT authenticated (it is redacted
    // in the delivered sent transcript) — prove the payment without revealing the key.
    assert!(
        v.authorization_hidden(),
        "the Authorization secret must be hidden by selective disclosure"
    );

    // ── Feed the REAL extracted facts into the origin-agnostic DECO Layer → mint through
    // the REAL bridge verifier, conserved.
    let att = DecoPaymentAttestation::attest(
        v.facts.payment_intent_id.clone(),
        v.facts.amount_cents,
        v.facts.currency.clone(),
        v.facts.recipient,
        None,
    );
    assert_eq!(att.payment_hash, v.facts.payment_hash());

    let mut mirror = StripeMirrorState::new(config());
    let minted = mirror
        .mint_against_deco(&att)
        .expect("the tlsn-origin attestation mints through the real verifier");
    assert_eq!(minted.amount, 2500);
    assert_eq!(minted.recipient, recipient);
    assert_eq!(mirror.live_supply, 2500);
    assert_eq!(mirror.total_verified_payments, 2500);
    assert!(mirror.invariant_holds());

    // ── The honest presentation re-verifies through the standalone verifier too.
    verify_stripe_presentation(&roundtrip.presentation_bytes, &roundtrip.pinned_server)
        .expect("the honest presentation verifies");

    // ── TAMPER the real Presentation bytes → the REAL verify() refuses it. No fact is
    // trusted, no mint.
    let mut tampered = roundtrip.presentation_bytes.clone();
    // Flip bytes across a spread of the presentation so we hit authenticated material
    // regardless of layout — the real cryptographic verify must reject.
    let n = tampered.len();
    for i in [n / 3, n / 2, (2 * n) / 3] {
        tampered[i] ^= 0xFF;
    }
    assert!(
        verify_stripe_presentation(&tampered, &roundtrip.pinned_server).is_err(),
        "a tampered presentation MUST fail the real verify()"
    );
    assert_eq!(mirror.live_supply, 2500, "no tampered-origin mint");

    // A presentation verified against the WRONG pinned server is refused.
    assert!(
        verify_stripe_presentation(&roundtrip.presentation_bytes, "evil.example.com").is_err(),
        "server pinning must refuse a non-pinned host"
    );
}
