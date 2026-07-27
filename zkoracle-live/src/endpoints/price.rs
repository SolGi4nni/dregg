//! **The LIVE Coinbase spot-price oracle** — a genuine MPC-TLS 2PC session with the real
//! `api.coinbase.com`, verified trustlessly by a third party from a portable proof file.
//!
//! The fixture-backed sibling (spec, schema, and the asset cross-check) is
//! [`dregg_zkoracle_prove::endpoints::price`]; this module supplies leg 1 from a real session
//! and reaches the SAME extractor, so both paths cross-check identically.

use dregg_zkoracle_prove::attestation::{
    VerifiedZkOracle, ZkOracleAttestation, ZkOracleError, attestation_over_authenticated_body,
};
use dregg_zkoracle_prove::endpoints::price::{
    AttestedPrice, COINBASE_SERVER_NAME, PriceError, price_fact_over_session,
};

use crate::tlsn_live::{run_coinbase_roundtrip_blocking, verify_coinbase_presentation};
use crate::verify::verify_zkoracle_live_host;

/// **PRODUCE a Coinbase spot attestation from a LIVE MPC-TLS session** against the real
/// `api.coinbase.com`.
///
/// Runs the genuine 2PC roundtrip ([`run_coinbase_roundtrip_blocking`]) — a SEPARATE hosted
/// notary co-derives the session keys and sees no plaintext — then binds legs 2–4 over the
/// AUTHENTICATED body. Leg 1's real evidence is
/// [`ZkOracleAttestation::tlsn_presentation`], verified trustlessly by
/// [`verify_coinbase_live`]; the modeled `presentation` carrier is an UNSIGNED envelope
/// carrying the authenticated request line so the asset is recoverable. A verifier MUST use
/// [`verify_coinbase_live`], NOT the modeled
/// [`dregg_zkoracle_prove::endpoints::price::verify_coinbase_spot`], on a live attestation.
///
/// Returns the portable attestation + the notary's `tlsn` verifying key: the ephemeral notary
/// mints a fresh key per run, so that key is the out-of-band trust anchor the honest prover
/// PUBLISHES alongside the proof for a third party to pin.
pub fn prove_coinbase_live(
    asset: &str,
) -> Result<
    (
        ZkOracleAttestation,
        tlsn::attestation::signing::VerifyingKey,
    ),
    ZkOracleError,
> {
    let rt = run_coinbase_roundtrip_blocking(asset)
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

/// **VERIFY a LIVE Coinbase spot attestation** → the [`AttestedPrice`].
///
/// Leg 1 is authenticated by the REAL `tlsn` `presentation.verify()` against the genuine
/// `api.coinbase.com` cert chain (Mozilla roots), pinning both the host
/// ([`COINBASE_SERVER_NAME`]) and `expected_notary_key`; legs 2–4 run over the SAME
/// authenticated body, and the asset cross-check is the shared
/// [`price_fact_over_session`].
pub fn verify_coinbase_live(
    att: &ZkOracleAttestation,
    expected_notary_key: &tlsn::attestation::signing::VerifyingKey,
) -> Result<AttestedPrice, PriceError> {
    let verified: VerifiedZkOracle =
        verify_zkoracle_live_host(att, COINBASE_SERVER_NAME, expected_notary_key)
            .map_err(PriceError::NotVerified)?;
    price_fact_over_session(att, &verified)
}

/// Verify a PORTABLE coinbase proof — the bincode `tlsn` `Presentation` bytes + the pinned
/// notary key. Re-derives the full zkOracle attestation from the AUTHENTICATED response body
/// and runs the genuine verifier, so a stranger verifies a proof file trusting only
/// api.coinbase.com's genuine cert chain + the pinned notary key.
pub fn verify_coinbase_portable(
    presentation_bytes: &[u8],
    notary_key: &tlsn::attestation::signing::VerifyingKey,
) -> Result<AttestedPrice, PriceError> {
    // 1. Authenticate the real tlsn presentation -> the verified response body.
    let vr = verify_coinbase_presentation(presentation_bytes, COINBASE_SERVER_NAME, notary_key)
        .map_err(|e| {
            PriceError::NotVerified(ZkOracleError::NotAuthenticLive(format!(
                "presentation: {e}"
            )))
        })?;
    // 2. Rebuild the attestation over that authenticated body.
    let att = attestation_over_authenticated_body(
        notary_key.alg.to_string().as_str(),
        &notary_key.data,
        &vr.server_name,
        vr.connection_time,
        &vr.sent_redacted,
        &vr.response_body,
        presentation_bytes.to_vec(),
    )
    .map_err(PriceError::NotVerified)?;
    // 3. The genuine verifier (fail-closed).
    verify_coinbase_live(&att, notary_key)
}

/// Produce a PORTABLE coinbase proof as raw bytes: `(tlsn_presentation_bytes,
/// bincode(notary VerifyingKey))`. A caller serializes these into any container; a stranger
/// re-verifies with [`verify_coinbase_portable_bytes`].
pub fn prove_coinbase_portable(asset: &str) -> Result<(Vec<u8>, Vec<u8>), PriceError> {
    let (att, key) = prove_coinbase_live(asset).map_err(PriceError::NotVerified)?;
    let pres = att.tlsn_presentation.ok_or_else(|| {
        PriceError::NotVerified(ZkOracleError::NotAuthenticLive(
            "prover produced no tlsn presentation".to_string(),
        ))
    })?;
    let key_bytes = bincode::serialize(&key).map_err(|e| {
        PriceError::NotVerified(ZkOracleError::NotAuthenticLive(format!(
            "notary key serialize: {e}"
        )))
    })?;
    Ok((pres, key_bytes))
}

/// Verify a PORTABLE coinbase proof from raw bytes (no tlsn types in the caller).
pub fn verify_coinbase_portable_bytes(
    presentation_bytes: &[u8],
    notary_key_bytes: &[u8],
) -> Result<AttestedPrice, PriceError> {
    let key: tlsn::attestation::signing::VerifyingKey = bincode::deserialize(notary_key_bytes)
        .map_err(|e| {
            PriceError::NotVerified(ZkOracleError::NotAuthenticLive(format!(
                "notary key decode: {e}"
            )))
        })?;
    verify_coinbase_portable(presentation_bytes, &key)
}
