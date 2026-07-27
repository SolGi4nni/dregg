//! **The LIVE GitHub commit oracle** — a genuine MPC-TLS 2PC session with the real
//! `api.github.com` (no auth needed; the endpoint is public and read-only).
//!
//! The fixture-backed sibling (spec, schema, and the request/response `sha` cross-check) is
//! [`dregg_zkoracle_prove::endpoints::github`]; this module supplies leg 1 from a real session
//! and reaches the SAME extractor, so both paths cross-check identically.

use dregg_zkoracle_prove::attestation::{
    ZkOracleAttestation, ZkOracleError, attestation_over_authenticated_body,
};
use dregg_zkoracle_prove::endpoints::github::{
    GITHUB_SERVER_NAME, GithubCommitFact, GithubError, commit_fact_over_session,
};

use crate::tlsn_live::{run_github_roundtrip_blocking, verify_coinbase_presentation};
use crate::verify::verify_zkoracle_live_host;

/// **Prove a live `api.github.com` commit** — a genuine MPC-TLS 2PC roundtrip against the real
/// GitHub API, bound through the authentic ∧ well-formed legs.
pub fn prove_github_live(
    owner: &str,
    repo: &str,
    sha: &str,
) -> Result<
    (
        ZkOracleAttestation,
        tlsn::attestation::signing::VerifyingKey,
    ),
    ZkOracleError,
> {
    let rt = run_github_roundtrip_blocking(owner, repo, sha)
        .map_err(|e| ZkOracleError::NotAuthenticLive(e.to_string()))?;
    let att = attestation_over_authenticated_body(
        rt.notary_pin.verifying_key.alg.to_string().as_str(),
        &rt.notary_pin.verifying_key.data,
        &rt.verified.server_name,
        rt.verified.connection_time,
        &rt.verified.sent_redacted,
        &rt.verified.response_body,
        rt.presentation_bytes,
    )?;
    Ok((att, rt.notary_pin.verifying_key))
}

/// Verify a live-carrier GitHub attestation and extract the commit fact — leg 1 by the real
/// `presentation.verify()` under the pinned host + notary key, then the SHARED
/// [`commit_fact_over_session`] cross-check.
pub fn verify_github_live(
    att: &ZkOracleAttestation,
    expected_notary_key: &tlsn::attestation::signing::VerifyingKey,
) -> Result<GithubCommitFact, GithubError> {
    let verified = verify_zkoracle_live_host(att, GITHUB_SERVER_NAME, expected_notary_key)
        .map_err(GithubError::NotVerified)?;
    commit_fact_over_session(att, &verified)
}

/// Portable prove: `(tlsn presentation bytes, bincode notary key)`.
pub fn prove_github_portable(
    owner: &str,
    repo: &str,
    sha: &str,
) -> Result<(Vec<u8>, Vec<u8>), GithubError> {
    let (att, key) = prove_github_live(owner, repo, sha).map_err(GithubError::NotVerified)?;
    let pres = att.tlsn_presentation.ok_or_else(|| {
        GithubError::NotVerified(ZkOracleError::NotAuthenticLive(
            "prover produced no tlsn presentation".to_string(),
        ))
    })?;
    let key_bytes = bincode::serialize(&key).map_err(|e| {
        GithubError::NotVerified(ZkOracleError::NotAuthenticLive(format!(
            "notary key serialize: {e}"
        )))
    })?;
    Ok((pres, key_bytes))
}

/// Portable verify from raw bytes — rebuilds the attestation from the authenticated body.
pub fn verify_github_portable_bytes(
    presentation_bytes: &[u8],
    notary_key_bytes: &[u8],
) -> Result<GithubCommitFact, GithubError> {
    let key: tlsn::attestation::signing::VerifyingKey = bincode::deserialize(notary_key_bytes)
        .map_err(|e| {
            GithubError::NotVerified(ZkOracleError::NotAuthenticLive(format!(
                "notary key decode: {e}"
            )))
        })?;
    let vr = verify_coinbase_presentation(presentation_bytes, GITHUB_SERVER_NAME, &key).map_err(
        |e| {
            GithubError::NotVerified(ZkOracleError::NotAuthenticLive(format!(
                "presentation: {e}"
            )))
        },
    )?;
    let att = attestation_over_authenticated_body(
        key.alg.to_string().as_str(),
        &key.data,
        &vr.server_name,
        vr.connection_time,
        &vr.sent_redacted,
        &vr.response_body,
        presentation_bytes.to_vec(),
    )
    .map_err(GithubError::NotVerified)?;
    verify_github_live(&att, &key)
}
