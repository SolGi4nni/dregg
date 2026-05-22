//! Axum extractor for verifying pyana presentation proofs from request headers.
//!
//! Extracts and verifies the `X-Pyana-Proof` header using
//! `PyanaEngine::verify_presentation_bytes()`.
//!
//! # Usage
//!
//! ```ignore
//! use axum::{Router, routing::get};
//! use pyana_app_framework::middleware::VerifiedPresentation;
//!
//! async fn protected(proof: VerifiedPresentation) -> &'static str {
//!     if proof.verified {
//!         "access granted"
//!     } else {
//!         "access denied"
//!     }
//! }
//!
//! let app = Router::new()
//!     .route("/protected", get(protected))
//!     .with_state(engine_state);
//! ```

use std::sync::Arc;

use axum::extract::FromRequestParts;
use axum::http::StatusCode;
use axum::http::request::Parts;
use tokio::sync::RwLock;

use pyana_sdk::embed::PyanaEngine;

/// The result of extracting and verifying a pyana presentation proof.
///
/// This is an axum extractor: declare it as a handler argument and it will
/// automatically parse the `X-Pyana-Proof` header, decode the base64 payload,
/// and run STARK verification against the engine's federation root.
#[derive(Clone, Debug)]
pub struct VerifiedPresentation {
    /// The action field from the proof (BLAKE3 hash of action string).
    pub action: [u8; 32],
    /// The resource field from the proof (BLAKE3 hash of resource string).
    pub resource: [u8; 32],
    /// The federation root the proof was verified against.
    pub federation_root: [u8; 32],
    /// Whether the proof cryptographically verified.
    pub verified: bool,
}

/// Shared engine state that the extractor reads from.
///
/// Wrap your `PyanaEngine` in this type and pass it as axum state:
///
/// ```ignore
/// let state = EngineState(Arc::new(RwLock::new(engine)));
/// Router::new().with_state(state);
/// ```
#[derive(Clone)]
pub struct EngineState(pub Arc<RwLock<PyanaEngine>>);

/// Header name for the base64-encoded presentation proof.
pub const PROOF_HEADER: &str = "x-pyana-proof";

/// Header name for the action being authorized (optional, for binding check).
pub const ACTION_HEADER: &str = "x-pyana-action";

/// Header name for the resource being accessed (optional, for binding check).
pub const RESOURCE_HEADER: &str = "x-pyana-resource";

impl FromRequestParts<EngineState> for VerifiedPresentation {
    type Rejection = (StatusCode, &'static str);

    async fn from_request_parts(
        parts: &mut Parts,
        state: &EngineState,
    ) -> Result<Self, Self::Rejection> {
        // Extract the proof header.
        let proof_header = parts
            .headers
            .get(PROOF_HEADER)
            .ok_or((StatusCode::UNAUTHORIZED, "missing X-Pyana-Proof header"))?;

        let proof_b64 = proof_header.to_str().map_err(|_| {
            (
                StatusCode::BAD_REQUEST,
                "X-Pyana-Proof header is not valid UTF-8",
            )
        })?;

        // Decode base64.
        use base64::Engine as _;
        let proof_bytes = base64::engine::general_purpose::STANDARD
            .decode(proof_b64)
            .map_err(|_| (StatusCode::BAD_REQUEST, "X-Pyana-Proof is not valid base64"))?;

        // Extract action/resource from headers (hashed for binding).
        let action = extract_hash_header(&parts.headers, ACTION_HEADER);
        let resource = extract_hash_header(&parts.headers, RESOURCE_HEADER);

        // Verify against the engine.
        let engine = state.0.read().await;
        let federation_root = engine.federation_root();
        let verified = engine.verify_presentation_bytes(&proof_bytes);

        Ok(VerifiedPresentation {
            action,
            resource,
            federation_root,
            verified,
        })
    }
}

/// Extract a header value and hash it to 32 bytes, or return zeroes if absent.
fn extract_hash_header(headers: &axum::http::HeaderMap, name: &str) -> [u8; 32] {
    headers
        .get(name)
        .and_then(|v| v.to_str().ok())
        .map(|s| *blake3::hash(s.as_bytes()).as_bytes())
        .unwrap_or([0u8; 32])
}

/// Rejection helper: create a 403 Forbidden response when verification fails.
///
/// Use this in handlers that want to hard-reject unverified proofs:
///
/// ```ignore
/// async fn handler(proof: VerifiedPresentation) -> Result<String, (StatusCode, &'static str)> {
///     require_verified(&proof)?;
///     Ok("access granted".into())
/// }
/// ```
pub fn require_verified(proof: &VerifiedPresentation) -> Result<(), (StatusCode, &'static str)> {
    if proof.verified {
        Ok(())
    } else {
        Err((
            StatusCode::FORBIDDEN,
            "presentation proof verification failed",
        ))
    }
}
