//! **The ORACLE WELD — zkTLS lane, end-to-end.**
//!
//! The real composition the graded-mark doc names: this crate's zkTLS price producer
//! (`endpoints::price`) verifies a genuine Coinbase spot attestation with the full 3-leg
//! `verify_zkoracle` (authentic ∧ well-formed ∧ cross-leg-bound), yielding an `AttestedPrice`
//! `{ asset, amount, time, attestation }`; that VERIFIED amount + origin + the zkoracle
//! `content_commitment` bind into a `dregg_tee_verify::GradedMark` — the graded input the
//! lending/solvency logic consumes (`metatheory/Market/OracleWeld.lean`).
//!
//! Both polarities:
//! - POSITIVE — a genuine attested price mints a graded mark carrying the exact amount, ATTESTED
//!   grade, and the named origin (`api.coinbase.com`);
//! - NEGATIVE — a tampered price never yields an `AttestedPrice` (the notary signature breaks), so
//!   NO graded mark can be built from it: an unattested price is unconstructable through this lane.

use std::collections::HashMap;

use dregg_tee_verify::{Grade, GradedMark, MarkError, MarkPrice, MarkProvenance, TrustGrade};
use dregg_zkoracle_prove::attestation::{FieldSpan, ZkOracleAttestation, content_commitment};
use dregg_zkoracle_prove::authentic::{EndpointConfig, FixtureNotary, build_endpoint_fixture};
use dregg_zkoracle_prove::cfg::prove_cfg_compact;
use dregg_zkoracle_prove::endpoints::price::{
    AttestedPrice, COINBASE_SERVER_NAME, CoinbaseSpotOracle, PriceError, PriceOracle,
    coinbase_spot_body, coinbase_spot_path, coinbase_spot_spec, verify_coinbase_spot,
};

/// Serialize the zkoracle content commitment (a BabyBear felt) to bytes — the fold's connect
/// target the graded mark carries. The exact bytes are opaque to the mark, which only binds
/// provenance to a non-empty, real zkoracle commitment.
fn commit_bytes(att: &ZkOracleAttestation) -> Vec<u8> {
    bincode::serialize(&att.content_commit).expect("BabyBear content commitment serializes")
}

/// Build a graded mark from a VERIFIED zkTLS price — the sanctioned composition. The authenticity
/// of `amount`/`origin` was established by `verify_coinbase_spot` (a full `verify_zkoracle`) that
/// produced `attested`; this only binds that verified amount into the mark.
fn graded_mark_from_verified_price(attested: &AttestedPrice) -> Result<GradedMark, MarkError> {
    GradedMark::from_zktls_price(
        COINBASE_SERVER_NAME,
        &attested.amount,
        commit_bytes(&attested.attestation),
    )
}

fn book() -> HashMap<String, String> {
    HashMap::from([("BTC-USD".to_string(), "64250.37".to_string())])
}

#[test]
fn a_genuine_zktls_price_mints_a_graded_mark() {
    // The zkTLS producer: a real Coinbase spot attestation, verified 3-leg → an AttestedPrice.
    let notary = FixtureNotary::from_seed(&[91u8; 32]);
    let oracle = CoinbaseSpotOracle::new(notary, book(), 1_700_000_500);
    let quote = oracle.price("BTC-USD").expect("a genuine BTC-USD quote");
    // Re-verify trustlessly (the downstream contract) before binding.
    let reverified =
        verify_coinbase_spot(&quote.attestation, oracle.config()).expect("re-verifies 3-leg");
    assert_eq!(reverified.amount, "64250.37");

    // The weld: the verified amount binds into a graded mark.
    let mark = graded_mark_from_verified_price(&reverified).expect("verified price binds");
    assert_eq!(
        mark.price(),
        MarkPrice {
            num: 6_425_037,
            den: 100
        }
    );
    assert_eq!(mark.grade(), TrustGrade::Attested);
    match mark.provenance() {
        MarkProvenance::ZkTlsProvenance {
            origin,
            content_commit,
        } => {
            assert_eq!(origin, COINBASE_SERVER_NAME);
            assert!(
                !content_commit.is_empty(),
                "carries the zkoracle content commitment"
            );
        }
        other => panic!("expected zkTLS provenance, got {other:?}"),
    }
    // The honest grade: consuming this in PROVED lending logic is an ATTESTED composite, not PROVED.
    assert_eq!(mark.lending_composite_grade(), Grade::Attested);
    assert_ne!(mark.lending_composite_grade(), Grade::Proved);
}

#[test]
fn a_tampered_price_never_becomes_a_graded_mark() {
    // NEGATIVE POLE: flip a byte in the authenticated amount → the notary signature breaks →
    // verify_coinbase_spot refuses → there is no AttestedPrice → no graded mark can be built.
    let notary = FixtureNotary::from_seed(&[92u8; 32]);
    let spec = coinbase_spot_spec();
    let config = EndpointConfig::new(spec.clone(), notary.verifying_key());
    let body = coinbase_spot_body("BTC-USD", "64250.37");
    let path = coinbase_spot_path("BTC-USD");
    let mut pres = build_endpoint_fixture(&notary, &spec, &path, &body, 1);
    let amt_pos = pres
        .recv
        .windows(5)
        .position(|w| w == b"64250")
        .expect("amount present");
    pres.recv[amt_pos] ^= 0xFF;
    // Present the tampered session as an attestation (the honest legs over the untampered body,
    // the tampered presentation) — exactly the splice a forger would attempt.
    let att = ZkOracleAttestation {
        presentation: pres,
        cfg_cert: prove_cfg_compact(body.as_bytes()).unwrap(),
        field_span: FieldSpan { offset: 0, len: 0 },
        content_commit: content_commitment(body.as_bytes()),
        zk_injection: None,
        tlsn_presentation: None,
    };

    // The verifier refuses the tampered price — the notary signature breaks — so there is no
    // AttestedPrice, so no graded mark can be built from it.
    let verdict = verify_coinbase_spot(&att, &config);
    assert!(
        matches!(verdict, Err(PriceError::NotVerified(_))),
        "a tampered amount must be refused by the zkTLS verifier, got {verdict:?}"
    );
}
