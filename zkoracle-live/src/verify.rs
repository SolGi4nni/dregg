//! **The REAL authentic leg** — leg 1 of the zkOracle attestation, adjudicated by genuine
//! `tlsn` `presentation.verify()` rather than the modeled ed25519 fixture carrier.
//!
//! [`TlsnLeg`] and [`TlsnHostLeg`] are the two implementations of
//! [`dregg_zkoracle_prove::attestation::MpcTlsLeg`] this crate exists to supply. Handing one
//! of them to `verify_zkoracle_with_policy(.., AuthenticPolicy::RequireMpcTls, leg)` is what
//! turns the provenance gate from "refuse everything live" into real MPC-TLS verification.
//!
//! ⚑ The choice is a VALUE, not a `#[cfg]`. A verifier that holds
//! [`dregg_zkoracle_prove::NoMpcTlsBackend`] refuses a live leg; one that holds a `TlsnLeg`
//! checks it. Both are spellable in the same build, and the call site says which is in use —
//! whereas the `#[cfg(feature = "tlsn-live")]` this replaced made that a property of which
//! OTHER packages cargo had been asked about.

use dregg_zkoracle_prove::attestation::{
    AuthenticProvenance, MpcTlsLeg, VerifiedZkOracle, ZkOracleAttestation, ZkOracleError,
    verify_legs_over_session,
};
use dregg_zkoracle_prove::authentic::{AuthenticError, AuthenticSession};

use crate::tlsn_live::{
    VerifiedResponse, verify_coinbase_presentation, verify_messages_presentation,
};

/// **The Anthropic-shaped MPC-TLS leg.** Authenticates the presentation against
/// `expected_server` using the test-fixture root store, and enforces the killer property that
/// survives a real session: the `x-api-key` was REDACTED, never authenticated.
#[derive(Clone, Copy, Debug, Default)]
pub struct TlsnLeg;

impl MpcTlsLeg for TlsnLeg {
    fn authenticate(
        &self,
        presentation_bytes: &[u8],
        expected_server: &str,
    ) -> Result<AuthenticSession, ZkOracleError> {
        let vr = verify_messages_presentation(presentation_bytes, expected_server)
            .map_err(|e| ZkOracleError::NotAuthenticLive(e.to_string()))?;
        // The killer property survives the real session: the x-api-key was redacted.
        if !vr.api_key_hidden() {
            return Err(ZkOracleError::NotAuthentic(AuthenticError::ApiKeyDisclosed));
        }
        Ok(session_of(vr))
    }
}

/// **The real-host MPC-TLS leg**, pinning BOTH the host's genuine TLS cert chain
/// (Mozilla/webpki roots) and the separate hosted notary's verifying key — the trust anchor a
/// verifier holds out-of-band. A tampered/forged presentation, a wrong host, or a wrong or
/// unpinned notary is refused by the genuine crypto.
///
/// No api-key check: these are PUBLIC read-only endpoints (`api.coinbase.com`,
/// `api.github.com`) with no secret request header to redact.
#[derive(Clone, Copy, Debug)]
pub struct TlsnHostLeg<'a> {
    /// The notary verifying key the verifier pins out-of-band.
    pub expected_notary_key: &'a tlsn::attestation::signing::VerifyingKey,
}

impl MpcTlsLeg for TlsnHostLeg<'_> {
    fn authenticate(
        &self,
        presentation_bytes: &[u8],
        expected_server: &str,
    ) -> Result<AuthenticSession, ZkOracleError> {
        let vr = verify_coinbase_presentation(
            presentation_bytes,
            expected_server,
            self.expected_notary_key,
        )
        .map_err(|e| ZkOracleError::NotAuthenticLive(e.to_string()))?;
        Ok(session_of(vr))
    }
}

fn session_of(vr: VerifiedResponse) -> AuthenticSession {
    AuthenticSession {
        server_name: vr.server_name,
        connection_time: vr.connection_time,
        response_body: vr.response_body,
    }
}

/// **VERIFY a zkOracle attestation with the LIVE authentic leg.**
///
/// Identical to `dregg_zkoracle_prove::verify_zkoracle` EXCEPT leg 1 is authenticated by the
/// REAL `tlsn` `presentation.verify()` over the attestation's `tlsn_presentation` — a
/// trustless MPC-TLS 2PC notary (it co-derived the session keys and saw no plaintext), NOT the
/// modeled ed25519 carrier. The authenticated body drives the SAME cross-leg weld +
/// well-formed + injection legs. A tampered/forged presentation is refused by the real crypto
/// ([`ZkOracleError::NotAuthenticLive`]); an un-redacted api-key still fails the killer
/// property ([`AuthenticError::ApiKeyDisclosed`]).
pub fn verify_zkoracle_live(
    att: &ZkOracleAttestation,
    expected_server: &str,
) -> Result<VerifiedZkOracle, ZkOracleError> {
    let bytes = att.tlsn_presentation.as_ref().ok_or_else(|| {
        ZkOracleError::NotAuthenticLive("attestation carries no tlsn presentation".to_string())
    })?;
    let session = TlsnLeg.authenticate(bytes, expected_server)?;
    verify_legs_over_session(att, session, AuthenticProvenance::MpcTls)
}

/// **VERIFY a zkOracle attestation with the LIVE authentic leg against a REAL host.**
///
/// Like [`verify_zkoracle_live`] but leg 1 authenticates against the host's GENUINE cert chain
/// and PINS `expected_notary_key` ([`TlsnHostLeg`]). The authenticated body drives the SAME
/// downstream legs, so the splice refusal is identical on every path.
pub fn verify_zkoracle_live_host(
    att: &ZkOracleAttestation,
    expected_server: &str,
    expected_notary_key: &tlsn::attestation::signing::VerifyingKey,
) -> Result<VerifiedZkOracle, ZkOracleError> {
    let bytes = att.tlsn_presentation.as_ref().ok_or_else(|| {
        ZkOracleError::NotAuthenticLive("attestation carries no tlsn presentation".to_string())
    })?;
    let session = TlsnHostLeg {
        expected_notary_key,
    }
    .authenticate(bytes, expected_server)?;
    verify_legs_over_session(att, session, AuthenticProvenance::MpcTls)
}
