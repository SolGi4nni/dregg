//! Sealed-bid auction using commit-reveal to prevent front-running.
//!
//! Orders use a two-phase protocol:
//! 1. **Commit**: Consumer submits a blinded commitment (hash of order details + secret).
//!    Other participants see "someone committed" but not the order details.
//! 2. **Reveal**: After the commit window elapses, the consumer reveals details +
//!    secret, proving they committed first, and the order becomes eligible for matching.
//!
//! This prevents MEV-style attacks where a watcher sees an incoming order and races
//! to consume the same offering first.

use pyana_app_framework::compute_commitment_hash;
use serde::{Deserialize, Serialize};

// =============================================================================
// Types
// =============================================================================

/// A commitment to an order, hiding details during the commit phase.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct OrderCommitment {
    /// The order ID this commitment is for.
    pub order_id: [u8; 32],
    /// The blinded commitment hash: BLAKE3(order_id || secret || epoch).
    pub commitment_hash: [u8; 32],
    /// When this commitment was created (Unix seconds).
    pub committed_at: u64,
}

/// Parameters for the commit phase of an order.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CommitParams {
    /// The consumer's secret used for the commitment.
    /// In production this would be generated client-side; here it's provided for testing.
    pub secret: [u8; 32],
}

/// Parameters for the reveal phase of an order.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RevealParams {
    /// The secret that was used in the commit phase.
    pub secret: [u8; 32],
}

// =============================================================================
// Commitment computation
// =============================================================================

/// Compute the commitment hash for an order.
///
/// Uses the same scheme as the intent layer's commit-reveal:
/// `BLAKE3(order_id || secret || epoch)` where epoch is currently 0 (single-epoch mode).
pub fn compute_order_commitment(order_id: &[u8; 32], secret: &[u8; 32]) -> [u8; 32] {
    // Use epoch 0 for the exchange (we use our own time-based reveal window).
    compute_commitment_hash(order_id, secret, 0)
}

/// Verify that a revealed secret matches a previously-registered commitment hash.
pub fn verify_commitment(order_id: &[u8; 32], secret: &[u8; 32], expected_hash: &[u8; 32]) -> bool {
    let computed = compute_order_commitment(order_id, secret);
    computed == *expected_hash
}

/// The minimum time (seconds) between commit and reveal.
/// Orders cannot be revealed before this window elapses.
pub const COMMIT_REVEAL_WINDOW_SECS: u64 = 5;

/// The maximum time (seconds) a commitment remains valid.
/// After this, the commitment expires and the order slot reopens.
pub const COMMITMENT_EXPIRY_SECS: u64 = 60;
