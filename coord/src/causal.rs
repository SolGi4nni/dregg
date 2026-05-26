//! Layer 1: Causal Chaining.
//!
//! Every turn a node produces includes hash-pointers to the latest turns it has seen.
//! This creates a DAG of happened-before relationships. Any node can verify
//! "turn T2 happened after turn T1" by following the hash links.
//!
//! No global ordering needed — just local causal consistency.
//!
//! Production nodes use `dregg_types::CausalDag` directly (re-exported below).
//! `CausalTurn`, `CausalLedger`, and `CausalTurnBuilder` have been deleted —
//! they were not used outside of tests. See Block 4 of the 2026-05-24 cleanup.

use crate::error::CoordError;

// Re-export the shared CausalDag from dregg-types.
pub use dregg_types::CausalDag;

// ─── CoordError conversion ────────────────────────────────────────────────────

/// Convert a `dregg_types::CausalError` into a `CoordError`.
impl From<dregg_types::CausalError> for CoordError {
    fn from(err: dregg_types::CausalError) -> Self {
        match err {
            dregg_types::CausalError::MissingDeps { turn_hash, missing } => {
                CoordError::MissingDependency {
                    turn_hash,
                    dep_hash: missing.into_iter().next().unwrap_or([0; 32]),
                }
            }
            dregg_types::CausalError::Duplicate(hash) => CoordError::DuplicateTurn { hash },
        }
    }
}
