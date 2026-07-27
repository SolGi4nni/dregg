//! **THE DM's NARRATION PROVENANCE, DRIVEN** — the authentic leg of a DM narration is a
//! real MPC-TLS presentation, and a self-signed fixture is refused on the live path.
//!
//! The DM's pitch is that a narration "provably came from a real model". On every path the
//! game actually used, that rested on a `FixtureNotary`: this process built the transcript
//! and signed it with a key it holds itself. Worse, `attest_narration_live` ran a GENUINE
//! MPC-TLS 2PC roundtrip and then **threw the presentation away** — it returned a pure
//! fixture attestation, so the real session was unobservable downstream.
//!
//! These tests drive the fused path:
//!   1. `attest_narration_live` fuses the REAL presentation into the authentic leg, and a
//!      `RequireMpcTls` verifier authenticates the narration by genuine
//!      `presentation.verify()`;
//!   2. the default (fixture) narration is REFUSED on that same live path — non-vacuous;
//!   3. the receipt id fingerprints the real presentation, so a live narration and a
//!      fixture narration over the same prose cannot share a receipt.
//!
//! Run:
//! ```text
//! cargo test -p attested-dm --features tlsn-live --test dm_model_provenance
//! ```
#![cfg(feature = "tlsn-live")]

use attested_dm::{
    attestation_commitment, authentic_provenance, verify_zkoracle_with_policy, AuthenticPolicy,
    AuthenticProvenance, DmAttestationCarrier,
};
use dregg_zkoracle_live::TlsnLeg;
use dregg_zkoracle_prove::authentic::{EndpointConfig, EndpointSpec, SecretHeader};
use dregg_zkoracle_prove::{verify_zkoracle, ZkOracleError};

/// The local MPC-TLS fixture server presents the `tlsn-server-fixture` cert for this domain.
const LIVE_SERVER: &str = "test-server.io";

const NARRATION: &str = "The Warden turns its lantern-eye upon you and does not blink.";

/// The config a live DM narration is verified under: pin the server the REAL 2PC session
/// authenticated. (The notary anchor is only read on the fixture path.)
fn live_config(carrier: &DmAttestationCarrier) -> EndpointConfig {
    EndpointConfig::new(
        EndpointSpec {
            id: "anthropic-messages-live".to_string(),
            server_name: LIVE_SERVER.to_string(),
            method: "POST".to_string(),
            secret_header: Some(SecretHeader {
                name: "x-api-key".to_string(),
                placeholder: "sk-ant-MERCHANT-API-KEY-PLACEHOLDER".to_string(),
                marker: "MERCHANT-API-KEY".to_string(),
            }),
        },
        carrier.config().expected_notary.clone(),
    )
}

/// **(1) THE DM's LIVE NARRATION CARRIES REAL TRANSPORT PROVENANCE.** `attest_narration_live`
/// no longer discards the presentation: the real MPC-TLS session IS the authentic leg, and a
/// `RequireMpcTls` verifier accepts it on the strength of genuine `presentation.verify()`.
#[test]
fn dm_live_narration_fuses_the_real_presentation_into_the_authentic_leg() {
    let carrier = DmAttestationCarrier::default();
    let att = carrier
        .attest_narration_live("The party enters the flooded vault.", NARRATION)
        .expect("a real MPC-TLS 2PC roundtrip attests the narration");

    // The narration claims — and carries — real MPC-TLS provenance.
    assert_eq!(authentic_provenance(&att), AuthenticProvenance::MpcTls);

    let out = verify_zkoracle_with_policy(
        &att,
        &live_config(&carrier),
        AuthenticPolicy::RequireMpcTls,
        &TlsnLeg,
    )
    .expect("the real presentation authenticates the DM narration");
    assert_eq!(out.provenance, AuthenticProvenance::MpcTls);
    assert_eq!(out.session.server_name, LIVE_SERVER);
    // The DM's actual words are in the body the REAL session delivered.
    let body = String::from_utf8(out.session.response_body.clone()).expect("utf-8");
    assert!(
        body.contains(NARRATION),
        "the narration is the authenticated content"
    );

    // The in-circuit prose tooth rides along.
    assert!(
        att.zk_injection.is_some(),
        "the DM live path attaches the in-circuit STARK injection leg"
    );
}

/// **(2) THE DEFAULT (FIXTURE) NARRATION IS REFUSED ON THE LIVE PATH.** Non-vacuous in both
/// directions: the default narration verifies perfectly well on the fixture-admitting path
/// — that is exactly how the DM's "provably from a real model" was satisfied by a
/// transcript it signed itself — and is refused the moment real provenance is demanded.
#[test]
fn default_fixture_narration_is_refused_on_the_live_path() {
    let carrier = DmAttestationCarrier::default();
    let (att, _field) = carrier
        .attest_narration(NARRATION)
        .expect("the default narration attests");

    assert_eq!(
        authentic_provenance(&att),
        AuthenticProvenance::SelfSignedFixture
    );

    // REGRESSION DIRECTION — the legacy path ACCEPTS it. It looks exactly as green as a
    // really-authenticated narration.
    let out = verify_zkoracle(&att, carrier.config()).expect("the fixture path accepts");
    assert_eq!(out.provenance, AuthenticProvenance::SelfSignedFixture);

    // THE GATE — the live path refuses it outright. Nothing vouches for its origin.
    assert_eq!(
        verify_zkoracle_with_policy(
            &att,
            &live_config(&carrier),
            AuthenticPolicy::RequireMpcTls,
            &TlsnLeg
        ),
        Err(ZkOracleError::FixtureOnLivePath),
        "a self-signed narration must not pass as provably-from-the-model"
    );
}

/// **(3) THE RECEIPT ID FINGERPRINTS THE REAL SESSION.** A live narration and a fixture
/// narration of the SAME prose must not share a receipt — otherwise a landed turn's
/// provenance claim could be swapped without changing its on-ledger id.
#[test]
fn the_receipt_id_distinguishes_a_live_narration_from_a_fixture_one() {
    let carrier = DmAttestationCarrier::default();
    let live = carrier
        .attest_narration_live("The party enters the flooded vault.", NARRATION)
        .expect("live narration");
    let (fixture, _f) = carrier
        .attest_narration(NARRATION)
        .expect("fixture narration");

    assert_ne!(
        attestation_commitment(&live),
        attestation_commitment(&fixture),
        "the receipt id must bind WHAT vouched for the narration, not just its text"
    );

    // And stripping the real presentation off the live narration changes its receipt — the
    // live leg cannot be silently removed from a landed turn.
    let mut stripped = live.clone();
    stripped.tlsn_presentation = None;
    assert_ne!(
        attestation_commitment(&stripped),
        attestation_commitment(&live),
        "the receipt id fingerprints the real MPC-TLS presentation"
    );
}
