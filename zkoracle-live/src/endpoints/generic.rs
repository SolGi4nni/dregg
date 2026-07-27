//! **The generic web-fact endpoint** — prove ANY public HTTPS JSON `GET` and disclose the
//! whole (authenticated, well-formed) body. The caller extracts the field they care about.
//!
//! Unlike the coinbase/github endpoints there is no fixture sibling for this one: every path
//! it has runs a real MPC-TLS session, which is why the whole module lives in this crate.

use dregg_zkoracle_prove::attestation::{
    ZkOracleAttestation, ZkOracleError, attestation_over_authenticated_body,
};

use crate::tlsn_live::{run_url_roundtrip_blocking, verify_coinbase_presentation};

/// Prove a live `GET https://{host}{path}` — a genuine MPC-TLS 2PC, the body disclosed whole
/// and bound through the authentic + well-formed legs.
pub fn prove_url_live(
    host: &str,
    path: &str,
) -> Result<
    (
        ZkOracleAttestation,
        tlsn::attestation::signing::VerifyingKey,
    ),
    ZkOracleError,
> {
    let rt = run_url_roundtrip_blocking(host, path)
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

/// Portable prove: `(tlsn presentation bytes, bincode notary key)`.
pub fn prove_url_portable(host: &str, path: &str) -> Result<(Vec<u8>, Vec<u8>), ZkOracleError> {
    let (att, key) = prove_url_live(host, path)?;
    let pres = att
        .tlsn_presentation
        .ok_or_else(|| ZkOracleError::NotAuthenticLive("no tlsn presentation".to_string()))?;
    let key_bytes = bincode::serialize(&key)
        .map_err(|e| ZkOracleError::NotAuthenticLive(format!("key serialize: {e}")))?;
    Ok((pres, key_bytes))
}

/// Portable verify — authenticate the presentation against `host` and return the whole
/// verified response body (UTF-8). The caller extracts the field they need.
pub fn verify_url_body_portable_bytes(
    presentation_bytes: &[u8],
    notary_key_bytes: &[u8],
    host: &str,
) -> Result<String, ZkOracleError> {
    let key: tlsn::attestation::signing::VerifyingKey = bincode::deserialize(notary_key_bytes)
        .map_err(|e| ZkOracleError::NotAuthenticLive(format!("notary key decode: {e}")))?;
    let vr = verify_coinbase_presentation(presentation_bytes, host, &key)
        .map_err(|e| ZkOracleError::NotAuthenticLive(format!("presentation: {e}")))?;
    String::from_utf8(vr.response_body.clone())
        .map_err(|e| ZkOracleError::NotAuthenticLive(format!("body not utf8: {e}")))
}
