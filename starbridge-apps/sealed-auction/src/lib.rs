//! # Sealed-intent multi-agent coordination (Starbridge usecase app #2)
//!
//! Several agents COMPETE for a single award — a compute slot, a task assignment, a contract — by
//! submitting *sealed* bids during a COMMIT phase, then REVEALING them, after which the winning bid
//! SETTLES atomically through the verified per-asset executor. Because the commit is a hash binding
//! `(bidder, value, nonce)`, no agent can peek at, copy, or front-run another's bid before the
//! reveal: the sealed commitment hides the value (and the nonce blinds even low-entropy values) and
//! binds the bidder to exactly one bid.
//!
//! This is the executable surface of the Lean development
//! `metatheory/Dregg2/Intent/SealedAuction.lean`, which PROVES the guarantees this crate enforces:
//!
//! | Lean keystone                       | What it guarantees                                   |
//! |-------------------------------------|------------------------------------------------------|
//! | `reveal_binds_committed`            | a sealed commitment opens to EXACTLY its bid (CR) —  |
//! |                                     | no peeking-then-switching.                           |
//! | `reveal_requires_reveal_phase`      | no reveal binds before the commit phase closes.      |
//! | `uncommitted_cannot_open`/`_win`    | a non-committed party can never reveal, hence settle.|
//! | `settle_atomic`                     | the award is all-or-nothing (a leg failure aborts).  |
//! | `settle_conserves`                  | the award is value-neutral (no mint/burn).           |
//! | `winner_was_committed`              | the award binds back to a real prior commitment.     |
//!
//! ## Routing through the VERIFIED executor
//!
//! Settlement does NOT re-implement ledger arithmetic. It builds the award ring — leg 1: the winner
//! pays its bid to the seller; leg 2: the seller's slot cell delivers the task-token to the winner —
//! and folds it through [`dregg_intent::verified_settle::settle_ring_verified`], the Rust mirror of
//! the Lean `Ring.settleRing`/`SealedAuction.settle`. That fold runs the verified per-asset
//! transition `recKExecAsset` for every leg (and, under the intent crate's `verified-settle`
//! feature, cross-checks each leg against the REAL Lean FFI export). A leg that fails its gate aborts
//! the whole award (atomicity); a committed award provably conserves every asset (conservation). The
//! coordination is therefore settled by the verified executor, not by a Rust-only shadow.
//!
//! ## The sealed commitment
//!
//! `seal(bid) = BLAKE3_derive_key("dregg-sealed-auction bid v1", bidder || value || nonce)` — the
//! same construction as the running `intent::commit_reveal_fulfillment::compute_commitment_hash`,
//! and the Rust image of the Lean `SealedAuction.sealOf` (`Blake3Kernel.hash [bidder, sign, |value|,
//! nonce]`). Collision-resistance is the assumption the binding rests on (proved non-vacuously in
//! Lean against the reference `Blake3Kernel` carrier).

use std::collections::BTreeMap;

use dregg_intent::verified_settle::{
    settle_ring_verified, VerifiedLeg, VerifiedLedger, VerifiedSettleError,
};

/// A cell id, restricted to the low byte the verified per-asset ledger indexes by (the Rust view of
/// the Lean `CellId`). Agents, the seller, and the award slot are all cells.
pub type CellId = u8;

/// A 32-byte asset id (the verified ledger's asset column).
pub type AssetId = [u8; 32];

/// A 32-byte sealed commitment.
pub type Seal = [u8; 32];

// ---------------------------------------------------------------------------
// The sealed bid and its commitment
// ---------------------------------------------------------------------------

/// A sealed bid: the bidder's cell, the offered `value` (the price it will pay for the award), and a
/// private `nonce` that blinds the commitment. `value` and `nonce` are secret until reveal; only
/// [`Bid::seal`] is public during the commit phase.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Bid {
    /// The agent placing the bid (pays the bid, receives the award).
    pub bidder: CellId,
    /// The bid value — the price offered for the award (sealed-bid first-price).
    pub value: i128,
    /// The blinding nonce — secret; gives the commitment hiding even for a low-entropy value.
    pub nonce: u64,
}

impl Bid {
    /// Construct a bid.
    pub fn new(bidder: CellId, value: i128, nonce: u64) -> Self {
        Self { bidder, value, nonce }
    }

    /// The sealed commitment of this bid — `BLAKE3(bidder || value || nonce)`. Binding (under CR a
    /// commitment opens to exactly its bid) and hiding (the nonce blinds the value). This is the Rust
    /// image of the Lean `SealedAuction.sealOf`.
    pub fn seal(&self) -> Seal {
        let mut hasher = blake3::Hasher::new_derive_key("dregg-sealed-auction bid v1");
        hasher.update(&[self.bidder]);
        // sign tag + magnitude, mirroring the Lean preimage `[bidder, sign, |value|, nonce]`.
        hasher.update(&[if self.value >= 0 { 0u8 } else { 1u8 }]);
        hasher.update(&self.value.unsigned_abs().to_le_bytes());
        hasher.update(&self.nonce.to_le_bytes());
        *hasher.finalize().as_bytes()
    }
}

// ---------------------------------------------------------------------------
// The auction phase + state machine
// ---------------------------------------------------------------------------

/// The auction phase. Reveals bind only in `Reveal`; settlement fires only in `Reveal`; `Settled` is
/// terminal. The `Commit → Reveal → Settled` ordering is the protocol's phase gate (the Lean
/// `Phase`), not a comment: it makes "no reveal before the commit phase closes" enforced.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Phase {
    /// Collecting sealed commitments; reveals are rejected.
    Commit,
    /// Commit phase closed; reveals accepted, settlement may fire.
    Reveal,
    /// The award has been settled; terminal.
    Settled,
}

/// Errors from the sealed-auction protocol.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AuctionError {
    /// A commit was attempted outside the commit phase (fail-closed: no late commitments).
    NotCommitPhase,
    /// A reveal/settle was attempted while still committing (no reveal before the commit closes).
    NotRevealPhase,
    /// The auction is already settled (terminal).
    AlreadySettled,
    /// The revealed bid's seal is not among the committed seals — a non-committed party, or a
    /// peeking-then-switching attempt whose changed bid no longer matches its commitment.
    NotCommitted,
    /// No valid reveals were collected, so there is no winner to award.
    NoWinner,
    /// The award failed to settle through the verified executor (e.g. the winner cannot pay, or the
    /// slot is empty); the whole award aborted (atomicity).
    SettlementRejected(VerifiedSettleError),
}

impl std::fmt::Display for AuctionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotCommitPhase => write!(f, "commit attempted outside the commit phase"),
            Self::NotRevealPhase => write!(f, "reveal/settle attempted before the commit phase closed"),
            Self::AlreadySettled => write!(f, "the auction is already settled"),
            Self::NotCommitted => write!(f, "the revealed bid was not among the committed seals"),
            Self::NoWinner => write!(f, "no valid reveals collected; no winner to award"),
            Self::SettlementRejected(e) => write!(f, "award settlement rejected by the verified executor: {e}"),
        }
    }
}

impl std::error::Error for AuctionError {}

/// A sealed-bid auction. The public coordination state: who awards (`seller`), the payment `asset`,
/// the award `slot` cell whose `slot_asset` column delivers the task-token to the winner, the
/// collected sealed `commitments`, the `phase`, and the `revealed` bids (gathered in the reveal
/// phase). The secret `(value, nonce)` of an unrevealed bid is NOT here — only its seal.
#[derive(Clone, Debug)]
pub struct Auction {
    /// The agent awarding the slot (receives the winner's payment).
    pub seller: CellId,
    /// The cell holding the award token; delivers `slot_asset` to the winner.
    pub slot: CellId,
    /// The payment asset (bids are denominated in this).
    pub asset: AssetId,
    /// The asset the award slot delivers to the winner (the task-token column).
    pub slot_asset: AssetId,
    /// The sealed commitments collected during the commit phase, in commit order.
    pub commitments: Vec<Seal>,
    /// The current phase.
    pub phase: Phase,
    /// The validly-revealed bids (collected during the reveal phase), keyed by seal so a seal can be
    /// revealed at most once.
    revealed: BTreeMap<Seal, Bid>,
}

impl Auction {
    /// Open a fresh auction in the commit phase.
    pub fn new(seller: CellId, slot: CellId, asset: AssetId, slot_asset: AssetId) -> Self {
        Self {
            seller,
            slot,
            asset,
            slot_asset,
            commitments: Vec::new(),
            phase: Phase::Commit,
            revealed: BTreeMap::new(),
        }
    }

    /// **Commit phase** — append a sealed commitment. Legal ONLY in the commit phase (fail-closed:
    /// no late commitments after the phase seals). Mirrors the Lean `SealedAuction.commit`.
    pub fn commit(&mut self, seal: Seal) -> Result<(), AuctionError> {
        if self.phase != Phase::Commit {
            return Err(AuctionError::NotCommitPhase);
        }
        self.commitments.push(seal);
        Ok(())
    }

    /// Close the commit phase, opening reveals (`Commit → Reveal`). Mirrors `SealedAuction.sealAuction`.
    pub fn seal_commit_phase(&mut self) {
        if self.phase == Phase::Commit {
            self.phase = Phase::Reveal;
        }
    }

    /// Whether a bid's reveal would be valid: the auction is in the reveal phase AND the bid's seal
    /// is among the committed seals. The Rust image of the Lean `SealedAuction.validReveal` — the
    /// two teeth (phase gate + membership gate).
    pub fn valid_reveal(&self, bid: &Bid) -> bool {
        self.phase == Phase::Reveal && self.commitments.contains(&bid.seal())
    }

    /// **Reveal phase** — open a bid. Accepted iff [`Auction::valid_reveal`] holds: the auction must
    /// be in the reveal phase and the bid's seal must be among the commitments. A non-committed party
    /// (or a peeker who changed its bid so the seal no longer matches) is rejected with
    /// [`AuctionError::NotCommitted`]. On success the bid joins the revealed set.
    ///
    /// This is the executable witness of:
    ///   - `reveal_requires_reveal_phase` (rejected while committing),
    ///   - `uncommitted_cannot_open` (a non-committed seal is rejected), and
    ///   - `reveal_binds_committed` (only the exact committed bid opens its commitment, since a
    ///     different bid hashes to a different seal that is not in `commitments`).
    pub fn reveal(&mut self, bid: Bid) -> Result<(), AuctionError> {
        match self.phase {
            Phase::Commit => return Err(AuctionError::NotRevealPhase),
            Phase::Settled => return Err(AuctionError::AlreadySettled),
            Phase::Reveal => {}
        }
        let seal = bid.seal();
        if !self.commitments.contains(&seal) {
            return Err(AuctionError::NotCommitted);
        }
        self.revealed.insert(seal, bid);
        Ok(())
    }

    /// The current winner among the validly-revealed bids — the bid with the maximal `value`
    /// (sealed-bid first-price). `None` if no valid reveals were collected. Mirrors the Lean
    /// `SealedAuction.winnerOf`.
    pub fn winner(&self) -> Option<Bid> {
        self.revealed
            .values()
            .copied()
            .max_by_key(|b| b.value)
    }

    /// The award ring — the two balanced legs settled atomically. Leg 1: the winner pays its bid of
    /// the payment asset to the seller (the winner authorises its own debit). Leg 2: the slot cell
    /// delivers the same amount of the task-token (`slot_asset`) to the winner. Mirrors the Lean
    /// `SealedAuction.awardRing`.
    pub fn award_ring(&self, winner: &Bid) -> Vec<VerifiedLeg> {
        vec![
            VerifiedLeg {
                from: winner.bidder,
                to: self.seller,
                asset: self.asset,
                amount: winner.value,
            },
            VerifiedLeg {
                from: self.slot,
                to: winner.bidder,
                asset: self.slot_asset,
                amount: winner.value,
            },
        ]
    }

    /// **Settle the award** — pick the winner (top revealed bid) and fold the award ring through the
    /// VERIFIED executor ([`settle_ring_verified`]). Returns the verified post-ledger and the winning
    /// bid on success, marking the auction `Settled`.
    ///
    /// Fails (and leaves the ledger untouched — atomicity) if:
    ///   - the commit phase has not closed (`NotRevealPhase`),
    ///   - no valid reveals were collected (`NoWinner`), or
    ///   - any award leg is rejected by the verified executor (`SettlementRejected`, e.g. the winner
    ///     cannot pay or the slot is empty).
    ///
    /// This is the executable witness of `settle_atomic` (a rejected leg aborts the whole award) and
    /// `settle_conserves` (the verified fold checks every asset's total supply is preserved). The
    /// returned `(ledger, winner)` provably has the winner among the committed parties
    /// (`winner_was_committed`) because only validly-revealed (hence committed) bids enter `revealed`.
    pub fn settle(&mut self, ledger: &VerifiedLedger) -> Result<(VerifiedLedger, Bid), AuctionError> {
        if self.phase != Phase::Reveal {
            return Err(AuctionError::NotRevealPhase);
        }
        let winner = self.winner().ok_or(AuctionError::NoWinner)?;
        let ring = self.award_ring(&winner);
        let post = settle_ring_verified(ledger, &ring)
            .map_err(AuctionError::SettlementRejected)?;
        self.phase = Phase::Settled;
        Ok((post, winner))
    }
}

// ---------------------------------------------------------------------------
// A convenience ledger builder for demos / drivers.
// ---------------------------------------------------------------------------

/// Build a verified ledger funding a set of `(cell, asset, balance)` rows, with every named cell live.
/// A convenience for drivers and the demo; the auction itself only reads the ledger.
pub fn fund_ledger(rows: &[(CellId, AssetId, i128)]) -> VerifiedLedger {
    let mut k = VerifiedLedger::new();
    for (cell, asset, bal) in rows {
        k.add_account(*cell);
        k.set(*cell, asset, *bal);
    }
    k
}

#[cfg(test)]
mod tests;
