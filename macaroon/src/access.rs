//! Access trait — the request being authorized against caveats.
//!
//! Consumers implement `Access` for their domain-specific request types.
//! The macaroon library is generic over access — it only requires that
//! caveats can check `prohibits(&dyn Access)`.

use std::any::Any;

/// Represents a request that caveats are checked against.
///
/// Domain-specific implementations (e.g., `DreggAccess`) provide the
/// actual fields. Caveats downcast to the concrete type they understand.
///
/// This is intentionally minimal — the macaroon library doesn't prescribe
/// what an "access" looks like. That's the consumer's domain.
pub trait Access: Any + Send + Sync {
    /// Return self as `Any` for downcasting by caveat implementations.
    fn as_any(&self) -> &dyn Any;

    /// Current timestamp (Unix seconds) for validity window checks.
    /// Returns 0 if time-based checks are not applicable.
    fn now(&self) -> i64;
}
