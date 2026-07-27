//! **THE PROVENANCE GATE, with NO MPC-TLS backend** — the verifier holds
//! [`NoMpcTlsBackend`], so it cannot run `presentation.verify()` at all.
//!
//! The gate's cheap half is a structural question answerable without any crypto: *does this
//! attestation carry a real MPC-TLS presentation at all, or only a transcript the prover
//! signed itself?* That question is what makes a self-signed fixture refusable on a live path
//! before a single leg runs.
//!
//! The other half is fail-closure. A verifier with no backend CANNOT run
//! `presentation.verify()`, so it must never accept a live leg — and, crucially, must never
//! "fall back" onto the fixture carrier that is sitting right there and would verify
//! happily. Falling back would be precisely the laundering the gate exists to stop: an
//! attestation would claim MPC-TLS provenance and be accepted on the strength of a
//! self-signed signature.
//!
//! Both halves are now unconditional. They used to be `#[cfg(not(feature = "tlsn-live"))]`,
//! and `--workspace` unified that feature ON, so the fail-closure pole did not exist in the
//! configuration CI ran. The real-backend counterpart is
//! `dregg-zkoracle-live/tests/model_provenance_fused.rs`.
//!
//! ```text
//! cargo test -p dregg-zkoracle-prove --test provenance_gate
//! ```

use dregg_zkoracle_prove::attestation::{
    AuthenticPolicy, AuthenticProvenance, NoMpcTlsBackend, ZkOracleAttestation, ZkOracleError,
    authentic_provenance, verify_zkoracle, verify_zkoracle_with_policy,
};
use dregg_zkoracle_prove::authentic::{AnthropicConfig, FixtureNotary, build_anthropic_fixture};
use dregg_zkoracle_prove::prove_zkoracle;

const REPLY: &str = "Paris.";
const BODY: &str = r#"{"id":"msg_01","type":"message","role":"assistant","content":[{"type":"text","text":"Paris."}]}"#;

fn fixture_attestation(seed: u8) -> (ZkOracleAttestation, AnthropicConfig) {
    let notary = FixtureNotary::from_seed(&[seed; 32]);
    let config = AnthropicConfig::new(notary.verifying_key());
    let pres = build_anthropic_fixture(&notary, BODY, 1_700_000_000);
    let att = prove_zkoracle(pres, REPLY.as_bytes().to_vec(), &config).expect("fixture attests");
    (att, config)
}

/// A fixture attestation self-describes as a self-signed test double — the type no longer
/// lets "authentic" hide which of two utterly different things vouched for the body.
#[test]
fn a_fixture_attestation_self_describes_as_a_test_double() {
    let (att, config) = fixture_attestation(1);
    assert_eq!(
        authentic_provenance(&att),
        AuthenticProvenance::SelfSignedFixture
    );
    // The legacy path accepts it and REPORTS what vouched, so an accept can no longer be
    // read as provenance without looking.
    let out = verify_zkoracle(&att, &config).expect("the fixture path accepts");
    assert_eq!(out.provenance, AuthenticProvenance::SelfSignedFixture);
}

/// **THE GATE.** A self-signed fixture is refused on the live path — in the light build,
/// with no crypto backend needed. This is the check that stops a test double being consumed
/// as a live proof of model provenance.
#[test]
fn fixture_only_attestation_is_refused_on_the_live_path() {
    let (att, config) = fixture_attestation(2);
    // The very same attestation the legacy path accepts...
    assert!(verify_zkoracle(&att, &config).is_ok());
    // ...is refused the moment real provenance is demanded.
    assert_eq!(
        verify_zkoracle_with_policy(
            &att,
            &config,
            AuthenticPolicy::RequireMpcTls,
            &NoMpcTlsBackend
        ),
        Err(ZkOracleError::FixtureOnLivePath)
    );
}

/// **FAIL-CLOSED, NOT FALL-BACK.** An attestation claiming a live leg, verified by a party
/// holding [`NoMpcTlsBackend`], is REFUSED — even though a perfectly valid fixture carrier
/// sits right there and the old code would have read it. Accepting here (on the fixture's
/// strength) would be the exact laundering the gate exists to prevent.
///
/// ⚑ THIS TEST USED TO CARRY `#[cfg(not(feature = "tlsn-live"))]`, which means it DID NOT
/// EXIST in the configuration CI actually ran: `cargo test --workspace` unified `tlsn-live`
/// on (via `dregg-oracle`'s `default`), so the pole proving "never fall back onto the
/// fixture" was compiled out of every whole-workspace run. The backend is a VALUE now, so
/// both poles are spellable in one build and this one always runs.
#[test]
fn a_live_leg_is_refused_fail_closed_without_the_backend() {
    let (mut att, config) = fixture_attestation(3);
    // Claim MPC-TLS provenance with bytes this build cannot check.
    att.tlsn_presentation = Some(b"not a presentation this build can verify".to_vec());
    assert_eq!(authentic_provenance(&att), AuthenticProvenance::MpcTls);

    // The fixture carrier is still valid — so a fall-back WOULD accept. It must not.
    assert_eq!(
        verify_zkoracle_with_policy(
            &att,
            &config,
            AuthenticPolicy::RequireMpcTls,
            &NoMpcTlsBackend
        ),
        Err(ZkOracleError::LiveBackendUnavailable),
        "an uncheckable live leg must refuse, never fall back onto the self-signed fixture"
    );

    // Belt and braces: the fixture carrier really would have verified.
    att.tlsn_presentation = None;
    assert!(verify_zkoracle(&att, &config).is_ok());
}

/// The policy's admission rule, stated directly.
#[test]
fn policy_admits_exactly_what_it_says() {
    assert!(AuthenticPolicy::AllowFixture.admits(AuthenticProvenance::SelfSignedFixture));
    assert!(AuthenticPolicy::AllowFixture.admits(AuthenticProvenance::MpcTls));
    assert!(!AuthenticPolicy::RequireMpcTls.admits(AuthenticProvenance::SelfSignedFixture));
    assert!(AuthenticPolicy::RequireMpcTls.admits(AuthenticProvenance::MpcTls));
}
