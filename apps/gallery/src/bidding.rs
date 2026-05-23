//! Commit-reveal bidding protocol.
//!
//! Bidding uses a two-phase commit-reveal scheme to prevent sniping:
//!
//! 1. **Commit phase**: Bidders submit BLAKE3(bidder_cell || amount || nonce).
//!    The amount is hidden; only the commitment hash is public.
//!
//! 2. **Reveal phase**: Bidders reveal their (amount, nonce) pair. The server
//!    verifies the reveal matches the commitment. Bids that aren't revealed
//!    before the deadline forfeit their escrow deposit.
//!
//! This ensures no bidder can react to others' bid amounts during the auction.

use pyana_app_framework::CellId;

use crate::{BidCommitment, RevealedBid, verify_bid_reveal};

/// Errors from bidding operations.
#[derive(Debug, Clone)]
pub enum BiddingError {
    /// Auction is not in the bidding phase.
    NotInBiddingPhase,
    /// Auction is not in the reveal phase.
    NotInRevealPhase,
    /// Duplicate commitment (same bidder already committed).
    DuplicateCommitment,
    /// Commitment not found during reveal.
    CommitmentNotFound,
    /// Reveal does not match commitment hash.
    RevealMismatch,
    /// Bid amount is below the reserve price.
    BelowReserve { amount: u64, reserve: u64 },
    /// Bidder already revealed.
    AlreadyRevealed,
    /// Escrow amount does not cover the bid.
    InsufficientEscrow { escrowed: u64, bid: u64 },
}

impl std::fmt::Display for BiddingError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotInBiddingPhase => write!(f, "auction is not in bidding phase"),
            Self::NotInRevealPhase => write!(f, "auction is not in reveal phase"),
            Self::DuplicateCommitment => write!(f, "duplicate bid commitment from this bidder"),
            Self::CommitmentNotFound => write!(f, "commitment not found"),
            Self::RevealMismatch => write!(f, "reveal does not match commitment"),
            Self::BelowReserve { amount, reserve } => {
                write!(f, "bid {amount} is below reserve price {reserve}")
            }
            Self::AlreadyRevealed => write!(f, "bid already revealed"),
            Self::InsufficientEscrow { escrowed, bid } => {
                write!(f, "escrowed {escrowed} but bid {bid}")
            }
        }
    }
}

impl std::error::Error for BiddingError {}

/// The commit-reveal bidding engine.
///
/// Manages bid commitments and reveals for a single auction.
pub struct CommitRevealBidding {
    /// All bid commitments received.
    pub commitments: Vec<BidCommitment>,
    /// All revealed bids (populated during reveal phase).
    pub revealed: Vec<RevealedBid>,
    /// Reserve price for this auction.
    pub reserve_price: u64,
}

impl CommitRevealBidding {
    /// Create a new bidding engine with the given reserve price.
    pub fn new(reserve_price: u64) -> Self {
        Self {
            commitments: Vec::new(),
            revealed: Vec::new(),
            reserve_price,
        }
    }

    /// Reconstruct from existing state.
    pub fn from_state(
        commitments: Vec<BidCommitment>,
        revealed: Vec<RevealedBid>,
        reserve_price: u64,
    ) -> Self {
        Self {
            commitments,
            revealed,
            reserve_price,
        }
    }

    /// Submit a bid commitment during the bidding phase.
    ///
    /// The commitment is BLAKE3(bidder_cell || amount || nonce). The caller
    /// must also create an escrow for the bid amount separately.
    pub fn submit_commitment(
        &mut self,
        commitment: [u8; 32],
        bidder: CellId,
        escrow_id: [u8; 32],
        current_height: u64,
    ) -> Result<(), BiddingError> {
        // Check for duplicate commitment from the same bidder.
        if self
            .commitments
            .iter()
            .any(|c| c.bidder.as_bytes() == bidder.as_bytes())
        {
            return Err(BiddingError::DuplicateCommitment);
        }

        self.commitments.push(BidCommitment {
            commitment,
            bidder,
            escrow_id,
            submitted_at: current_height,
        });

        Ok(())
    }

    /// Reveal a bid during the reveal phase.
    ///
    /// Verifies that BLAKE3(bidder_cell || amount || nonce) == commitment.
    pub fn reveal_bid(
        &mut self,
        commitment: [u8; 32],
        bidder: CellId,
        amount: u64,
        nonce: [u8; 32],
    ) -> Result<(), BiddingError> {
        // Find the matching commitment.
        let bid_commitment = self
            .commitments
            .iter()
            .find(|c| c.commitment == commitment && c.bidder.as_bytes() == bidder.as_bytes())
            .ok_or(BiddingError::CommitmentNotFound)?;

        // Check not already revealed.
        if self.revealed.iter().any(|r| r.commitment == commitment) {
            return Err(BiddingError::AlreadyRevealed);
        }

        // Verify the reveal matches the commitment.
        if !verify_bid_reveal(&commitment, &bidder, amount, &nonce) {
            return Err(BiddingError::RevealMismatch);
        }

        // Check amount meets reserve.
        if amount < self.reserve_price {
            return Err(BiddingError::BelowReserve {
                amount,
                reserve: self.reserve_price,
            });
        }

        // Check escrow covers the bid (we stored escrow_id; the actual check
        // is done by the engine, but we can validate the intent here).
        let _ = bid_commitment;

        self.revealed.push(RevealedBid {
            commitment,
            bidder,
            amount,
            nonce,
        });

        Ok(())
    }

    /// Get the winning bid (highest revealed bid).
    pub fn determine_winner(&self) -> Option<&RevealedBid> {
        self.revealed.iter().max_by_key(|r| r.amount)
    }

    /// Get all losing bids (for refund processing).
    pub fn losing_bids(&self) -> Vec<&RevealedBid> {
        let winner = self.determine_winner();
        self.revealed
            .iter()
            .filter(|r| winner.map(|w| w.commitment != r.commitment).unwrap_or(true))
            .collect()
    }

    /// Get unrevealed commitments (bidders who didn't reveal — forfeit escrow deposit).
    pub fn unrevealed_commitments(&self) -> Vec<&BidCommitment> {
        self.commitments
            .iter()
            .filter(|c| !self.revealed.iter().any(|r| r.commitment == c.commitment))
            .collect()
    }

    /// Total number of commitments.
    pub fn commitment_count(&self) -> usize {
        self.commitments.len()
    }

    /// Total number of reveals.
    pub fn reveal_count(&self) -> usize {
        self.revealed.len()
    }

    /// Get the highest revealed bid amount.
    pub fn highest_bid(&self) -> Option<u64> {
        self.revealed.iter().map(|r| r.amount).max()
    }
}
