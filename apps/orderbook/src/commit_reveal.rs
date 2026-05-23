//! Commit-reveal protocol for order submission.
//!
//! Prevents frontrunning by the matcher: users first commit a blinded hash of
//! their order, then reveal after the commitment window closes. The matcher
//! cannot see the order parameters until the reveal phase, at which point it
//! must process ALL revealed orders from that batch fairly.
//!
//! ## Protocol
//!
//! 1. **Commit phase**: User broadcasts `commitment = blake3(order_bytes || secret)`.
//!    The matcher records the commitment and the block height.
//!
//! 2. **Reveal phase**: After `COMMIT_WINDOW_BLOCKS` pass, the user reveals
//!    `(order, secret)`. The matcher verifies `blake3(order_bytes || secret) == commitment`.
//!    If valid, the order enters the matching queue.
//!
//! 3. **Batch matching**: All orders revealed in the same batch are sorted by
//!    commitment timestamp (first-committed = first-matched), preventing the
//!    matcher from reordering them.
//!
//! ## MEV Protection
//!
//! - The matcher cannot see order parameters during the commit window.
//! - The commitment timestamp determines priority (attestable via federation block inclusion).
//! - A matcher who delays reveals or reorders them is detectable (proofs reference
//!   the commitment sequence in the state commitment).

use crate::order::Order;
use serde::{Deserialize, Serialize};

/// Number of blocks between commit and allowed reveal.
/// During this window, the order content is hidden from the matcher.
pub const COMMIT_WINDOW_BLOCKS: u64 = 2;

/// Maximum blocks after the commit window opens for reveal before the commitment expires.
/// This prevents griefing by committing without revealing.
pub const REVEAL_DEADLINE_BLOCKS: u64 = 10;

/// A blinded order commitment (submitted in the commit phase).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OrderCommitment {
    /// The blinded hash: `blake3("pyana-orderbook-commit-v1" || order_bytes || secret)`.
    pub hash: [u8; 32],
    /// The block height at which this commitment was included in the federation.
    pub committed_at: u64,
    /// The trader's cell ID (public, so we can attribute the commitment).
    pub trader: pyana_types::CellId,
}

/// The reveal payload (submitted in the reveal phase).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct OrderReveal {
    /// The full order being revealed.
    pub order: Order,
    /// The secret used in the commitment.
    pub secret: [u8; 32],
    /// The commitment hash this reveal corresponds to.
    pub commitment_hash: [u8; 32],
}

/// Registry tracking pending commitments and their lifecycle.
#[derive(Clone, Debug, Default)]
pub struct CommitRevealRegistry {
    /// Pending commitments awaiting reveal, keyed by commitment hash.
    pending: std::collections::HashMap<[u8; 32], OrderCommitment>,
    /// Revealed orders ready for batch matching, in commitment-time order.
    revealed: Vec<(Order, u64)>, // (order, committed_at)
    /// Current batch sequence number.
    pub batch_sequence: u64,
}

/// Errors from the commit-reveal protocol.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CommitRevealError {
    /// The commitment hash is already registered.
    DuplicateCommitment,
    /// No matching commitment found for this reveal.
    CommitmentNotFound,
    /// The reveal came too early (commit window has not elapsed).
    RevealTooEarly { blocks_remaining: u64 },
    /// The commitment has expired (reveal deadline passed).
    CommitmentExpired,
    /// The revealed order does not match the commitment hash.
    HashMismatch,
    /// The reveal trader does not match the commitment trader.
    TraderMismatch,
}

impl std::fmt::Display for CommitRevealError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::DuplicateCommitment => write!(f, "commitment already registered"),
            Self::CommitmentNotFound => write!(f, "no matching commitment found"),
            Self::RevealTooEarly { blocks_remaining } => {
                write!(f, "reveal too early, {} blocks remaining", blocks_remaining)
            }
            Self::CommitmentExpired => write!(f, "commitment expired"),
            Self::HashMismatch => write!(f, "order does not match commitment hash"),
            Self::TraderMismatch => write!(f, "reveal trader != commitment trader"),
        }
    }
}

/// Compute the commitment hash for an order.
pub fn compute_order_commitment(order: &Order, secret: &[u8; 32]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-orderbook-commit-v1");
    let order_bytes = postcard::to_allocvec(order).unwrap_or_default();
    hasher.update(&order_bytes);
    hasher.update(secret);
    *hasher.finalize().as_bytes()
}

impl CommitRevealRegistry {
    /// Create a new empty registry.
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a commitment (commit phase).
    pub fn commit(&mut self, commitment: OrderCommitment) -> Result<(), CommitRevealError> {
        if self.pending.contains_key(&commitment.hash) {
            return Err(CommitRevealError::DuplicateCommitment);
        }
        self.pending.insert(commitment.hash, commitment);
        Ok(())
    }

    /// Reveal an order (reveal phase). Validates the commitment and queues for matching.
    pub fn reveal(
        &mut self,
        reveal: OrderReveal,
        current_height: u64,
    ) -> Result<(), CommitRevealError> {
        let commitment = self
            .pending
            .get(&reveal.commitment_hash)
            .ok_or(CommitRevealError::CommitmentNotFound)?;

        // Check commit window has elapsed.
        let earliest_reveal = commitment.committed_at + COMMIT_WINDOW_BLOCKS;
        if current_height < earliest_reveal {
            return Err(CommitRevealError::RevealTooEarly {
                blocks_remaining: earliest_reveal - current_height,
            });
        }

        // Check reveal deadline has not passed.
        let deadline = commitment.committed_at + COMMIT_WINDOW_BLOCKS + REVEAL_DEADLINE_BLOCKS;
        if current_height > deadline {
            self.pending.remove(&reveal.commitment_hash);
            return Err(CommitRevealError::CommitmentExpired);
        }

        // Verify trader matches.
        if reveal.order.trader != commitment.trader {
            return Err(CommitRevealError::TraderMismatch);
        }

        // Verify hash matches.
        let expected_hash = compute_order_commitment(&reveal.order, &reveal.secret);
        if expected_hash != reveal.commitment_hash {
            return Err(CommitRevealError::HashMismatch);
        }

        let committed_at = commitment.committed_at;
        self.pending.remove(&reveal.commitment_hash);
        self.revealed.push((reveal.order, committed_at));
        Ok(())
    }

    /// Drain all revealed orders for batch matching, sorted by commitment timestamp.
    /// Returns orders in first-committed-first-matched order.
    pub fn drain_batch(&mut self) -> Vec<Order> {
        self.revealed.sort_by_key(|(_, committed_at)| *committed_at);
        let orders: Vec<Order> = self.revealed.drain(..).map(|(order, _)| order).collect();
        if !orders.is_empty() {
            self.batch_sequence += 1;
        }
        orders
    }

    /// Expire stale commitments that passed their reveal deadline.
    pub fn expire_stale(&mut self, current_height: u64) -> usize {
        let deadline = COMMIT_WINDOW_BLOCKS + REVEAL_DEADLINE_BLOCKS;
        let before = self.pending.len();
        self.pending
            .retain(|_, c| current_height <= c.committed_at + deadline);
        before - self.pending.len()
    }

    /// Number of pending (unrevealed) commitments.
    pub fn pending_count(&self) -> usize {
        self.pending.len()
    }

    /// Number of revealed orders awaiting batch matching.
    pub fn revealed_count(&self) -> usize {
        self.revealed.len()
    }
}
