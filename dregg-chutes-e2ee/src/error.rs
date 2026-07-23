//! Client error type. Every attestation/transport failure is fail-closed: the top-level
//! [`crate::attested_chat_completion`] returns `Err` and sends NO request when attestation
//! does not pass.

use crate::crypto::CryptoError;

#[derive(Debug, thiserror::Error)]
pub enum ClientError {
    #[error("crypto: {0}")]
    Crypto(#[from] CryptoError),
    #[error("HTTP: {0}")]
    Http(#[from] reqwest::Error),
    #[error("discovery failed: {0}")]
    Discovery(String),
    #[error("model {0:?} not found in /v1/models")]
    ModelNotFound(String),
    #[error("evidence fetch failed: {0}")]
    Evidence(String),
    #[error("ATTESTATION REFUSED (no request sent): {0}")]
    AttestationRefused(String),
    #[error("no attested instance also had a usable invocation nonce")]
    NoUsableInstance,
    #[error("invoke failed: {0}")]
    Invoke(String),
    #[error("config: {0}")]
    Config(String),
}
