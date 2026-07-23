//! The top-level attested client: `model + openai_request + cpk + VerifierConfig` →
//! `(openai_response, AttestationRecord)`, doing discover → **attest (fail-closed)** →
//! encrypt-to-attested-key → invoke → decrypt. Non-streaming.
//!
//! Header/route contract confirmed against the reference `scripts/test_e2e_client.py` and
//! `chutes_e2ee/transport.py`:
//! `POST {api_base}/e2e/invoke`, body = blob (`Content-Type: application/octet-stream`),
//! headers `Authorization: Bearer cpk`, `X-Chute-Id`, `X-Instance-Id` (the ATTESTED
//! instance), `X-E2E-Nonce` (an opaque single-use invocation token from discovery, echoed
//! verbatim), `X-E2E-Stream: false`, `X-E2E-Path: /v1/chat/completions`.
//!
//! The round trip is deliberately split in two, because the two halves have VERY different
//! costs and lifetimes: attestation (discovery + evidence + DCAP collateral + verify) takes
//! seconds and is valid for the whole lifetime of an instance's `e2e_pubkey`, while the
//! per-request half ([`invoke_encrypted`]) is ML-KEM encapsulate + ChaCha20-Poly1305 and takes
//! microseconds. [`crate::session`] caches the first so a narrator pays it once, not per turn.

use std::time::Duration;

use crate::attest::{attest_chute, AttestationRecord, AttestedInstance, VerifierConfig};
use crate::crypto::{build_e2ee_request, decrypt_response};
use crate::discovery::{discover, resolve_chute_id, InstanceInfo, Instances};
use crate::error::ClientError;

/// The OpenAI request path Chutes routes E2EE calls to.
pub const E2E_PATH: &str = "/v1/chat/completions";

/// The default HTTP timeout for the attested client (seconds).
pub const DEFAULT_TIMEOUT_SECS: u64 = 120;

/// A blocking HTTP client with the default timeout.
pub fn http_client() -> Result<reqwest::blocking::Client, ClientError> {
    http_client_with_timeout(DEFAULT_TIMEOUT_SECS)
}

/// A blocking HTTP client with an explicit timeout (seconds).
pub fn http_client_with_timeout(secs: u64) -> Result<reqwest::blocking::Client, ClientError> {
    reqwest::blocking::Client::builder()
        .timeout(Duration::from_secs(secs))
        .build()
        .map_err(ClientError::Http)
}

/// Full attested, end-to-end-encrypted chat completion.
///
/// Fail-closed: if NO instance of the resolved chute attests (DCAP crypto + fresh-nonce
/// report_data binding + registry measurement match + accepted TCB), this returns `Err`
/// BEFORE any request body is sent. On success, the returned [`AttestationRecord`] is the
/// receipt for the exact enclave (`instance_id`) that served the response.
///
/// This is the ONE-SHOT path: it re-attests on every call (~12.5s live). A caller that makes
/// repeated requests (a narrator) should hold a [`crate::session::SessionCache`] instead, which
/// runs this same attestation once per instance-lifetime and then only [`invoke_encrypted`].
pub fn attested_chat_completion(
    model: &str,
    openai_request: &serde_json::Value,
    cpk: &str,
    cfg: &VerifierConfig,
) -> Result<(serde_json::Value, AttestationRecord), ClientError> {
    let http = http_client()?;

    // 1. model -> chute_id.
    let chute_id = resolve_chute_id(&http, &cfg.models_base, model, cpk)?;

    // 2. discover instances (e2e_pubkey + invocation nonces per instance).
    let mut discovered = discover(&http, &cfg.api_base, &chute_id, cpk)?;

    // 3. ATTEST (fail-closed). Only instances that attested may be encrypted to.
    let attested = attest_chute(&http, cfg, &chute_id, cpk, &discovered)?;

    // 4. pick an attested instance that also has a usable invocation nonce.
    let (chosen, mut nonce) =
        pick_instance_with_nonce(&attested, &discovered).ok_or(ClientError::NoUsableInstance)?;
    let instance_id = chosen.instance_id.clone();
    let e2e_pubkey_b64 = chosen.e2e_pubkey_b64.clone();
    let record = AttestationRecord::from(chosen);

    // 5-7. encrypt to the ATTESTED pubkey, invoke, decrypt — with one retry on a stale
    //      invocation nonce (refetching the nonce does NOT require re-attesting: the instance
    //      and the pubkey it bound into the quote are unchanged).
    let response = match invoke_encrypted(
        &http,
        cfg,
        &chute_id,
        &instance_id,
        &e2e_pubkey_b64,
        &nonce,
        openai_request,
        cpk,
    ) {
        Ok(v) => v,
        Err(InvokeError::StaleNonce(_)) => {
            // Refetch discovery once for a fresh invocation nonce on the SAME attested
            // instance, then retry. (We do NOT switch instances: only `instance_id` attested.)
            discovered = discover(&http, &cfg.api_base, &chute_id, cpk)?;
            nonce = discovered
                .by_id(&instance_id)
                .and_then(|i| i.nonces.first().cloned())
                .ok_or_else(|| {
                    ClientError::Invoke(
                        "stale invocation nonce and no fresh nonce for the attested instance on refetch".into(),
                    )
                })?;
            invoke_encrypted(
                &http,
                cfg,
                &chute_id,
                &instance_id,
                &e2e_pubkey_b64,
                &nonce,
                openai_request,
                cpk,
            )
            .map_err(|e| match e {
                InvokeError::StaleNonce(m) => {
                    ClientError::Invoke(format!("stale nonce again after refetch: {m}"))
                }
                InvokeError::Other(e) => e,
            })?
        }
        Err(InvokeError::Other(e)) => return Err(e),
    };

    Ok((response, record))
}

/// Pick the first attested instance that also has an unused invocation nonce in discovery.
fn pick_instance_with_nonce<'a>(
    attested: &'a [AttestedInstance],
    discovered: &Instances,
) -> Option<(&'a AttestedInstance, String)> {
    for a in attested {
        if let Some(InstanceInfo { nonces, .. }) = discovered.by_id(&a.instance_id) {
            if let Some(n) = nonces.first() {
                return Some((a, n.clone()));
            }
        }
    }
    None
}

/// Why a single encrypted invocation failed. `StaleNonce` is called out separately because it is
/// the ONE failure a caller may retry WITHOUT re-attesting — the single-use invocation token
/// expired, but the instance and the `e2e_pubkey` its quote bound are unchanged.
#[derive(Debug)]
pub enum InvokeError {
    /// The invocation nonce was rejected as stale (403 mentioning "nonce"). Refetch nonces and retry.
    StaleNonce(String),
    /// Anything else — transport, HTTP status, crypto, malformed reply.
    Other(ClientError),
}

impl From<InvokeError> for ClientError {
    fn from(e: InvokeError) -> ClientError {
        match e {
            InvokeError::StaleNonce(m) => {
                ClientError::Invoke(format!("stale invocation nonce: {m}"))
            }
            InvokeError::Other(e) => e,
        }
    }
}

/// The PER-REQUEST half of the round trip: encrypt `openai_request` to `e2e_pubkey_b64`, POST it
/// pinned to `instance_id`, decrypt the reply. Microseconds of crypto plus one HTTP round trip.
///
/// **This function performs NO attestation.** It is sound only when `e2e_pubkey_b64` and
/// `instance_id` came from an instance that ALREADY passed [`crate::attest::attest_chute`] — the
/// pubkey is what makes the ciphertext readable by an enclave and nothing else, so handing an
/// unverified pubkey here throws the whole guarantee away. [`crate::session::SessionCache`] is the
/// supported way to reuse a verified pair; the fresh ephemeral response keypair generated inside
/// [`build_e2ee_request`] keeps every reuse forward-secret per request.
#[allow(clippy::too_many_arguments)]
pub fn invoke_encrypted(
    http: &reqwest::blocking::Client,
    cfg: &VerifierConfig,
    chute_id: &str,
    instance_id: &str,
    e2e_pubkey_b64: &str,
    invocation_nonce: &str,
    openai_request: &serde_json::Value,
    cpk: &str,
) -> Result<serde_json::Value, InvokeError> {
    let built = build_e2ee_request(e2e_pubkey_b64, openai_request)
        .map_err(|e| InvokeError::Other(e.into()))?;
    let body = invoke(
        http,
        cfg,
        chute_id,
        instance_id,
        invocation_nonce,
        &built.blob,
        cpk,
    )?;
    decrypt_response(&body, &built.response_sk).map_err(|e| InvokeError::Other(e.into()))
}

/// `POST {api_base}/e2e/invoke` (non-stream). Returns the raw encrypted response body on 200,
/// [`InvokeError::StaleNonce`] on a 403 whose body mentions "nonce", else an error.
fn invoke(
    http: &reqwest::blocking::Client,
    cfg: &VerifierConfig,
    chute_id: &str,
    instance_id: &str,
    nonce: &str,
    blob: &[u8],
    cpk: &str,
) -> Result<Vec<u8>, InvokeError> {
    let url = format!("{}/e2e/invoke", cfg.api_base.trim_end_matches('/'));
    let resp = http
        .post(&url)
        .bearer_auth(cpk)
        .header("X-Chute-Id", chute_id)
        .header("X-Instance-Id", instance_id)
        .header("X-E2E-Nonce", nonce)
        .header("X-E2E-Stream", "false")
        .header("X-E2E-Path", E2E_PATH)
        .header(reqwest::header::CONTENT_TYPE, "application/octet-stream")
        .body(blob.to_vec())
        .send()
        .map_err(|e| InvokeError::Other(ClientError::Http(e)))?;

    let status = resp.status();
    if status.is_success() {
        return resp
            .bytes()
            .map(|b| b.to_vec())
            .map_err(|e| InvokeError::Other(ClientError::Http(e)));
    }
    let body = resp.text().unwrap_or_default();
    if status.as_u16() == 403 && body.to_lowercase().contains("nonce") {
        return Err(InvokeError::StaleNonce(body));
    }
    Err(InvokeError::Other(ClientError::Invoke(format!(
        "POST {url} -> {status}: {body}"
    ))))
}
