//! Token error types.

/// Errors that can occur during token operations.
#[derive(Debug, thiserror::Error)]
pub enum TokenError {
    /// Token signature or HMAC verification failed.
    #[error("token verification failed: {0}")]
    VerificationFailed(String),

    /// Token format is malformed or unrecognized.
    #[error("malformed token: {0}")]
    Malformed(String),

    /// Authorization denied — a check or caveat was not satisfied.
    #[error("authorization denied: {0}")]
    Denied(String),

    /// Token has expired.
    #[error("token expired")]
    Expired,

    /// Unsupported token format for this operation.
    #[error("unsupported token format: {0}")]
    UnsupportedFormat(String),

    /// Encoding/decoding error.
    #[error("encoding error: {0}")]
    Encoding(String),

    /// Cryptographic error.
    #[error("crypto error: {0}")]
    Crypto(String),

    /// A caveat could not be decoded (malformed wire encoding).
    #[error("malformed caveat: {0}")]
    MalformedCaveat(String),

    /// Datalog evaluation error (Biscuit-specific).
    #[error("datalog error: {0}")]
    Datalog(String),

    /// Missing discharge macaroon (Macaroon-specific).
    #[error("missing discharge: {0}")]
    MissingDischarge(String),

    /// Key material error.
    #[error("key error: {0}")]
    KeyError(String),

    /// Binary data does not match any known token format.
    #[error("unrecognized token format: data does not match Macaroon or Biscuit patterns")]
    UnrecognizedFormat,
}
