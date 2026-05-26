//! Shared admin bearer token authentication for dregg apps.
//!
//! Reads `DREGG_ADMIN_TOKEN` from the environment at startup. Any route guarded
//! by the [`AdminAuth`] extractor requires an `Authorization: Bearer <token>` header
//! matching this value.
//!
//! If `DREGG_ADMIN_TOKEN` is not set, the behavior depends on the [`AdminMode`]:
//! - [`AdminMode::Disabled`]: admin endpoints return 503 (production default)
//! - [`AdminMode::Open`]: admin endpoints are unprotected (devnet/testing)
//!
//! # Usage
//!
//! ```ignore
//! use dregg_app_framework::auth::{AdminAuth, AdminToken};
//!
//! async fn protected_handler(_auth: AdminAuth) -> &'static str {
//!     "admin access granted"
//! }
//! ```

use axum::extract::FromRequestParts;
use axum::http::StatusCode;
use axum::http::request::Parts;
use axum::response::{IntoResponse, Response};
use serde_json::json;
use std::sync::Arc;

// =============================================================================
// AdminToken
// =============================================================================

/// The admin token configuration, read from `DREGG_ADMIN_TOKEN` at startup.
///
/// Stored in your app state and referenced by the [`AdminAuth`] extractor.
#[derive(Clone, Debug)]
pub struct AdminToken {
    inner: Option<Arc<String>>,
    mode: AdminMode,
}

/// What to do when `DREGG_ADMIN_TOKEN` is not configured.
#[derive(Clone, Debug, Copy, PartialEq, Eq)]
pub enum AdminMode {
    /// Admin endpoints return 503 when no token is configured (safe default).
    Disabled,
    /// Admin endpoints are open when no token is configured (devnet/testing).
    Open,
}

impl AdminToken {
    /// Read the admin token from `DREGG_ADMIN_TOKEN` environment variable.
    ///
    /// Uses [`AdminMode::Disabled`] as the default when the variable is unset.
    pub fn from_env() -> Self {
        Self::from_env_with_mode(AdminMode::Disabled)
    }

    /// Read the admin token from `DREGG_ADMIN_TOKEN` with a specified fallback mode.
    pub fn from_env_with_mode(mode: AdminMode) -> Self {
        Self {
            inner: std::env::var("DREGG_ADMIN_TOKEN").ok().map(|s| Arc::new(s)),
            mode,
        }
    }

    /// Create an admin token from a known value (for testing).
    pub fn from_value(token: impl Into<String>) -> Self {
        Self {
            inner: Some(Arc::new(token.into())),
            mode: AdminMode::Disabled,
        }
    }

    /// Create an unset token with open mode (for devnet).
    pub fn open() -> Self {
        Self {
            inner: None,
            mode: AdminMode::Open,
        }
    }

    /// Check if a token value is configured.
    pub fn is_configured(&self) -> bool {
        self.inner.is_some()
    }

    /// Validate a provided bearer token against the configured token.
    ///
    /// Returns:
    /// - `Ok(())` if the token matches or if no token is configured and mode is Open
    /// - `Err(rejection)` otherwise
    pub fn validate(&self, provided: Option<&str>) -> Result<(), AdminAuthRejection> {
        match &self.inner {
            Some(expected) => {
                let provided = provided.ok_or(AdminAuthRejection::MissingHeader)?;
                let bearer = provided
                    .strip_prefix("Bearer ")
                    .ok_or(AdminAuthRejection::InvalidToken)?;
                if !constant_time_eq(bearer.as_bytes(), expected.as_bytes()) {
                    return Err(AdminAuthRejection::InvalidToken);
                }
                Ok(())
            }
            None => match self.mode {
                AdminMode::Open => Ok(()),
                AdminMode::Disabled => Err(AdminAuthRejection::NotConfigured),
            },
        }
    }
}

// =============================================================================
// AdminAuth extractor
// =============================================================================

/// Axum extractor that validates the admin bearer token.
///
/// Add `_auth: AdminAuth` as a parameter to any handler that should be
/// admin-protected. The extractor reads the `AdminToken` from app state
/// via the [`HasAdminToken`] trait.
///
/// Returns:
/// - 503 if `DREGG_ADMIN_TOKEN` is not configured and mode is Disabled
/// - 401 if the `Authorization` header is missing or invalid
pub struct AdminAuth;

/// Rejection type for admin auth failures.
#[derive(Debug)]
pub enum AdminAuthRejection {
    /// Admin token not configured in environment (and mode is Disabled).
    NotConfigured,
    /// Authorization header missing.
    MissingHeader,
    /// Token does not match.
    InvalidToken,
}

impl IntoResponse for AdminAuthRejection {
    fn into_response(self) -> Response {
        let (status, msg) = match self {
            Self::NotConfigured => (
                StatusCode::SERVICE_UNAVAILABLE,
                "admin endpoints disabled: DREGG_ADMIN_TOKEN not configured",
            ),
            Self::MissingHeader => (StatusCode::UNAUTHORIZED, "missing Authorization header"),
            Self::InvalidToken => (StatusCode::UNAUTHORIZED, "invalid admin token"),
        };
        (status, axum::Json(json!({"error": msg}))).into_response()
    }
}

/// Trait for app states that contain an [`AdminToken`].
///
/// Implement this on your AppState so the [`AdminAuth`] extractor can find the token.
pub trait HasAdminToken {
    fn admin_token(&self) -> &AdminToken;
}

impl<S> FromRequestParts<S> for AdminAuth
where
    S: HasAdminToken + Send + Sync,
{
    type Rejection = AdminAuthRejection;

    async fn from_request_parts(parts: &mut Parts, state: &S) -> Result<Self, Self::Rejection> {
        let token = state.admin_token();
        let auth_value = parts
            .headers
            .get(axum::http::header::AUTHORIZATION)
            .and_then(|v| v.to_str().ok());
        token.validate(auth_value)?;
        Ok(AdminAuth)
    }
}

// =============================================================================
// Helpers
// =============================================================================

/// Constant-time byte comparison (prevents timing side-channels on token comparison).
fn constant_time_eq(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut acc = 0u8;
    for (x, y) in a.iter().zip(b.iter()) {
        acc |= x ^ y;
    }
    acc == 0
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn constant_time_eq_works() {
        assert!(constant_time_eq(b"hello", b"hello"));
        assert!(!constant_time_eq(b"hello", b"world"));
        assert!(!constant_time_eq(b"hello", b"hell"));
        assert!(!constant_time_eq(b"", b"x"));
        assert!(constant_time_eq(b"", b""));
    }

    #[test]
    fn validate_with_configured_token() {
        let token = AdminToken::from_value("secret123");
        assert!(token.validate(Some("Bearer secret123")).is_ok());
        assert!(token.validate(Some("Bearer wrong")).is_err());
        assert!(token.validate(None).is_err());
        assert!(token.validate(Some("Basic secret123")).is_err());
    }

    #[test]
    fn validate_disabled_mode() {
        let token = AdminToken {
            inner: None,
            mode: AdminMode::Disabled,
        };
        assert!(matches!(
            token.validate(None),
            Err(AdminAuthRejection::NotConfigured)
        ));
    }

    #[test]
    fn validate_open_mode() {
        let token = AdminToken::open();
        assert!(token.validate(None).is_ok());
        assert!(token.validate(Some("Bearer anything")).is_ok());
    }
}
