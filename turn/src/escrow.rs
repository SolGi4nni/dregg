//! Escrow primitives: conditional settlement with timeout-based refund.
//!
//! An escrow locks value from a sender, releasing it to a recipient IF a condition
//! is satisfied, or returning it to the sender after a timeout. This enables
//! trustless exchange patterns like compute-for-payment.

use pyana_cell::CellId;
use serde::{Deserialize, Serialize};

/// The condition that must be satisfied to release an escrow.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum EscrowCondition {
    /// Recipient must present a ZK proof verified against this key.
    ProofPresented {
        /// The verification key that the proof must validate against.
        verification_key: [u8; 32],
    },
    /// Requires signatures from ALL listed parties.
    SignedByAll {
        /// The Ed25519 public keys of all required signers.
        signers: Vec<[u8; 32]>,
    },
    /// A predicate (identified by hash) evaluates to true against state.
    PredicateSatisfied {
        /// The BLAKE3 hash identifying the predicate.
        predicate_hash: [u8; 32],
    },
}

/// A record of an active escrow tracked by the executor.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct EscrowRecord {
    /// The escrow creator (who locked the funds).
    pub creator: CellId,
    /// The intended recipient (who receives funds on release).
    pub recipient: CellId,
    /// The locked amount.
    pub amount: u64,
    /// The condition required for release.
    pub condition: EscrowCondition,
    /// Block height after which refund is allowed.
    pub timeout_height: u64,
    /// Whether this escrow has been resolved (released or refunded).
    pub resolved: bool,
}
