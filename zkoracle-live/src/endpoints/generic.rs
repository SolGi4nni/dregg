//! Generic web-fact endpoint — prove ANY public HTTPS JSON `GET` and disclose the
//! whole (authenticated, well-formed) body. The caller extracts the field they care
//! about from the returned body.

use crate::attestation::{ZkOracleAttestation, ZkOracleError};

/// Prove a live `GET https://{host}{path}` — a genuine MPC-TLS 2PC, the body disclosed
/// whole and bound through the authentic + well-formed legs.
#[cfg(feature = "tlsn-live")]
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
    use crate::attestation::{FieldSpan, content_commitment};
    use crate::authentic::{EndpointPresentation, TlsnVerifyingKey};
    use crate::cfg::prove_cfg_compact;

    let rt = crate::tlsn_live::run_url_roundtrip_blocking(host, path)
        .map_err(|e| ZkOracleError::NotAuthenticLive(e.to_string()))?;
    let body = rt.verified.response_body.clone();
    let cfg_cert = prove_cfg_compact(&body).map_err(ZkOracleError::NotWellFormed)?;
    let content_commit = content_commitment(&body);
    let recv = {
        let mut v = b"HTTP/1.1 200 OK\r\ncontent-type: application/json\r\n\r\n".to_vec();
        v.extend_from_slice(&body);
        v
    };
    let presentation = EndpointPresentation {
        verifying_key: TlsnVerifyingKey {
            alg: rt.notary_pin.verifying_key.alg.to_string(),
            data: rt.notary_pin.verifying_key.data.clone(),
        },
        server_name: rt.verified.server_name.clone(),
        connection_time: rt.verified.connection_time,
        sent: rt.verified.sent_redacted.clone(),
        recv,
        notary_sig: [0u8; 64],
    };
    let att = ZkOracleAttestation {
        presentation,
        cfg_cert,
        field_span: FieldSpan { offset: 0, len: 0 },
        content_commit,
        zk_injection: None,
        tlsn_presentation: Some(rt.presentation_bytes),
    };
    Ok((att, rt.notary_pin.verifying_key))
}

/// Portable prove: `(tlsn presentation bytes, bincode notary key)`.
#[cfg(feature = "tlsn-live")]
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
#[cfg(feature = "tlsn-live")]
pub fn verify_url_body_portable_bytes(
    presentation_bytes: &[u8],
    notary_key_bytes: &[u8],
    host: &str,
) -> Result<String, ZkOracleError> {
    let key: tlsn::attestation::signing::VerifyingKey = bincode::deserialize(notary_key_bytes)
        .map_err(|e| ZkOracleError::NotAuthenticLive(format!("notary key decode: {e}")))?;
    let vr = crate::tlsn_live::verify_coinbase_presentation(presentation_bytes, host, &key)
        .map_err(|e| ZkOracleError::NotAuthenticLive(format!("presentation: {e}")))?;
    String::from_utf8(vr.response_body.clone())
        .map_err(|e| ZkOracleError::NotAuthenticLive(format!("body not utf8: {e}")))
}
