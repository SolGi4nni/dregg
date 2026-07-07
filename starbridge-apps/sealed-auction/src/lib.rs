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
//! transition `recKExecAsset` for every leg (and, when the host has registered the Lean intent gate
//! — `dregg-exec-lean::register_distributed_gates()`, as a native node does at startup — cross-checks
//! each leg against the REAL Lean FFI export; unregistered, no FFI cross-check runs). A leg that
//! fails its gate aborts
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
//!
//! ## The commit phase is now ON-LEDGER (the deos floor)
//!
//! The original commit phase was an in-process `BTreeMap` of seals — the anti-front-running
//! guarantee lived in a Rust check, not in the executor. The deos floor LIFTS the commit board
//! ON-LEDGER: an auction is a **factory-born sovereign cell** ([`auction_factory_descriptor`])
//! whose installed [`CellProgram`] ([`auction_cell_program`]) IS the auction policy, re-checked
//! by the verified executor on every turn that touches it:
//!
//!   * [`PHASE_SLOT`] — the lifecycle phase code (`COMMIT=0 → REVEAL=1 → RESOLVED=2`).
//!     `StrictMonotonic` (scoped to the phase-advancing methods `close_commit` / `resolve`) — the
//!     phase only ADVANCES, never rewinds, and never re-fires (the anti-replay / anti-rollback
//!     tooth: even a no-advance bites, because `StrictMonotonic` is strict).
//!   * `COMMIT_BASE + i` — the i-th bidder's sealed commitment. Each `WriteOnce` — a sealed bid
//!     is FROZEN the instant it is committed: you cannot overwrite a committed bid (the
//!     anti-front-running tooth, now an EXECUTOR REFUSAL, not a `BTreeMap` membership check). The
//!     [`Bid::seal`] digest is the value written.
//!   * [`SELLER_SLOT`] — the awarding party (`WriteOnce`, bound at seed). [`WINNER_SLOT`] /
//!     [`HIGH_BID_SLOT`] — written at resolve (`WriteOnce` — the result freezes once announced).
//!
//! The in-process [`Auction`] / [`Bid`] commit-reveal state machine below is PRESERVED (it is the
//! executable witness of the commit-reveal CRYPTO — `seal` binding, the phase gate, settlement
//! through the verified executor); the on-ledger cell is the ADDITIVE deos floor that makes
//! "you cannot overwrite a committed bid" a real executor refusal.

use std::collections::{BTreeMap, HashSet};

use dregg_app_framework::CellId as DeosCellId;
use dregg_app_framework::{
    AppCipherclerk, AuthRequired, CapTarget, CapTemplate, CellAffordance, CellMode, CellProgram,
    ChildVkStrategy, ConstantsModule, DeosApp, DeosCell, Effect, EmbeddedExecutor, Event,
    FactoryDescriptor, FieldElement, FireExecuteError, GatedAffordance, InspectorDescriptor,
    StarbridgeAppContext, StateConstraint, TransitionCase, TransitionGuard, TurnReceipt,
    canonical_program_vk, field_from_bytes, field_from_u64, hex_encode_32, symbol,
};

use dregg_intent::verified_settle::{
    VerifiedLedger, VerifiedLeg, VerifiedSettleError, settle_ring_verified,
};

/// The deos-view CARD: the app's UI as a renderer-independent `deos.ui.*` view-tree.
pub mod card;
/// The CELLS-AS-SERVICE-OBJECTS face: a typed `InterfaceDescriptor` + `invoke()`
/// method dispatch over the auction lifecycle.
pub mod service;

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
        Self {
            bidder,
            value,
            nonce,
        }
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
            Self::NotRevealPhase => {
                write!(f, "reveal/settle attempted before the commit phase closed")
            }
            Self::AlreadySettled => write!(f, "the auction is already settled"),
            Self::NotCommitted => write!(f, "the revealed bid was not among the committed seals"),
            Self::NoWinner => write!(f, "no valid reveals collected; no winner to award"),
            Self::SettlementRejected(e) => {
                write!(f, "award settlement rejected by the verified executor: {e}")
            }
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
    /// The sealed commitments collected during the commit phase (a set — membership
    /// is the only query, so a `HashSet` makes the reveal-time check O(1)).
    pub commitments: HashSet<Seal>,
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
            commitments: HashSet::new(),
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
        self.commitments.insert(seal);
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
        self.revealed.values().copied().max_by_key(|b| b.value)
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
    pub fn settle(
        &mut self,
        ledger: &VerifiedLedger,
    ) -> Result<(VerifiedLedger, Bid), AuctionError> {
        if self.phase != Phase::Reveal {
            return Err(AuctionError::NotRevealPhase);
        }
        let winner = self.winner().ok_or(AuctionError::NoWinner)?;
        let ring = self.award_ring(&winner);
        let post = settle_ring_verified(ledger, &ring).map_err(AuctionError::SettlementRejected)?;
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

// =============================================================================
// THE ON-LEDGER FLOOR — the auction as a factory-born sovereign cell.
// =============================================================================
//
// `docs/deos/APPS-DEOS-INTEGRATION-CENSUS.md`: the census payoff for sealed-auction
// is to put the COMMIT PHASE ON-LEDGER. The original commit board was an in-process
// `BTreeMap<Seal>` — the anti-front-running tooth lived in a Rust membership check.
// Here the auction is a factory-born cell whose installed `CellProgram` IS the
// auction policy, re-checked by the verified executor on EVERY touching turn — so
// "you cannot overwrite a committed bid" becomes an EXECUTOR REFUSAL (`WriteOnce`),
// and "the phase only advances" becomes an EXECUTOR REFUSAL (`StrictMonotonic`).

/// Slot 0 — `PHASE`. The auction lifecycle phase code (`COMMIT=0 → REVEAL=1 →
/// RESOLVED=2`). `StrictMonotonic`, scoped to the phase-advancing methods
/// (`close_commit` / `resolve`) — the phase only ADVANCES, never rewinds, never
/// re-fires (the anti-replay / anti-rollback tooth; strict, so even a no-advance
/// bites). The on-ledger image of the in-process [`Phase`].
pub const PHASE_SLOT: usize = 0;

/// Slot 1 — `SELLER`. The awarding party's identity scalar. `WriteOnce` — bound at
/// seed, frozen for the life of the auction (the on-ledger image of [`Auction::seller`]).
pub const SELLER_SLOT: usize = 1;

/// Slot 2 — `HIGH_BID`. The winning bid's value, written at resolve. `WriteOnce` —
/// the result freezes once announced (no re-resolution).
pub const HIGH_BID_SLOT: usize = 2;

/// Slot 3 — `WINNER`. The winning bidder's identity scalar, written at resolve.
/// `WriteOnce` — the result freezes once announced.
pub const WINNER_SLOT: usize = 3;

/// The first commit-board slot. Bidder `i`'s sealed commitment lives at
/// `COMMIT_BASE + i`, each carrying a `WriteOnce` caveat — a committed sealed bid is
/// FROZEN forever (the anti-front-running tooth: you cannot overwrite a committed
/// bid). The [`Bid::seal`] digest is the value written.
pub const COMMIT_BASE: usize = 4;

/// How many sealed-commitment slots fit on a single auction cell. A dregg cell
/// carries exactly [`dregg_cell::state::STATE_SLOTS`] field slots; after reserving
/// PHASE / SELLER / HIGH_BID / WINNER, the commit board occupies
/// `COMMIT_BASE..STATE_SLOTS`.
pub const COMMIT_CAPACITY: usize = dregg_cell::state::STATE_SLOTS - COMMIT_BASE;

/// The slot index of bidder `i`'s sealed commitment.
pub fn commit_slot(i: usize) -> usize {
    COMMIT_BASE + i
}

/// `PHASE` codes — strictly increasing, so the auction lifecycle is one-way.
pub const PHASE_COMMIT: u64 = 0;
pub const PHASE_REVEAL: u64 = 1;
pub const PHASE_RESOLVED: u64 = 2;

/// Factory VK we publish for the sealed-auction factory.
pub const AUCTION_FACTORY_VK: [u8; 32] = *b"starbridge-sealed-auction-factry";

/// The perpetual auction invariants (the `Always` case) — also flattened into the
/// descriptor's `state_constraints` for constructor transparency (so the
/// FACTORY-BORN cell carries them, the executor re-checking them on every touching
/// turn). These hold on EVERY touching turn, in EVERY phase:
///
///   * the **anti-front-running** board: each commit slot is `WriteOnce` — a sealed
///     bid is frozen the instant it is committed (overwriting a committed bid is
///     REFUSED, the headline tooth);
///   * `SELLER` / `HIGH_BID` / `WINNER` are `WriteOnce` — the seller is bound once at
///     seed; the result freezes once announced;
///   * the **anti-rollback** phase floor: `Monotonic(PHASE)` — the phase may never
///     REWIND (`REVEAL → COMMIT` is REFUSED) on ANY method, so the lifecycle is
///     one-way even on the factory-born cell (whose installed program is exactly this
///     flat `state_constraints` predicate). This is the NON-strict floor: a method
///     that legitimately leaves PHASE unchanged (every `commit_bid` during COMMIT)
///     still passes (`new >= old`). The STRICTLY-increasing advance — even a
///     no-advance bites — is the phase-advancing methods' extra clause
///     (`StrictMonotonic(PHASE)` in the `close_commit` / `resolve` cases of
///     [`auction_cell_program`]); it cannot live here because it would refuse the
///     PHASE-unchanged `commit_bid`.
fn auction_invariants() -> Vec<StateConstraint> {
    let mut cs = Vec::with_capacity(4 + COMMIT_CAPACITY);
    cs.push(StateConstraint::WriteOnce {
        index: SELLER_SLOT as u8,
    });
    cs.push(StateConstraint::WriteOnce {
        index: HIGH_BID_SLOT as u8,
    });
    cs.push(StateConstraint::WriteOnce {
        index: WINNER_SLOT as u8,
    });
    // the anti-rollback phase floor — the phase may never rewind (non-strict, so a
    // PHASE-unchanged commit_bid still passes). The strict no-advance bite lives in
    // the phase-advancing method cases.
    cs.push(StateConstraint::Monotonic {
        index: PHASE_SLOT as u8,
    });
    // the anti-front-running commit board — every commit slot is write-once.
    for i in 0..COMMIT_CAPACITY {
        cs.push(StateConstraint::WriteOnce {
            index: commit_slot(i) as u8,
        });
    }
    cs
}

/// The `CellProgram` installed on every auction cell — a method-dispatched `Cases`
/// program whose `Always` case carries the perpetual invariants ([`auction_invariants`]:
/// the `WriteOnce` commit board + result registers) and whose phase-advancing cases
/// bind the `StrictMonotonic(PHASE)` lifecycle tooth:
///
///   * **`Always`**: the anti-front-running board (`WriteOnce(COMMIT_BASE + i)`) + the
///     result registers (`WriteOnce(SELLER/HIGH_BID/WINNER)`) — on EVERY touching turn.
///   * **`commit_bid`**: no extra clause — a commit writes a fresh commit slot, which
///     the `Always` `WriteOnce` governs (a re-commit to a taken slot is REFUSED). The
///     phase is NOT advanced (many bidders commit in COMMIT), so PHASE is deliberately
///     NOT under `StrictMonotonic` here.
///   * **`close_commit`**: `StrictMonotonic(PHASE)` — advance `COMMIT → REVEAL` (a
///     rewind or no-advance is REFUSED).
///   * **`reveal_bid`**: no extra clause — a reveal in the REVEAL phase records its
///     value; the phase is not advanced.
///   * **`resolve`**: `StrictMonotonic(PHASE)` — advance `REVEAL → RESOLVED`, writing
///     `WINNER` / `HIGH_BID` (frozen by the `Always` `WriteOnce`).
///
/// The program is method-dispatching, so an unknown method is default-denied
/// (`NoTransitionCaseMatched`). `StrictMonotonic(PHASE)` is scoped to the
/// phase-advancing methods because it is STRICT and unconditional within a case — a
/// `commit_bid` that (correctly) leaves PHASE unchanged would otherwise be refused.
pub fn auction_cell_program() -> CellProgram {
    CellProgram::Cases(vec![
        // ── invariants: every transition, every method ──────────────────
        TransitionCase {
            guard: TransitionGuard::Always,
            constraints: auction_invariants(),
        },
        // ── commit_bid: write a fresh commit slot (Always WriteOnce governs it) ─
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol("commit_bid"),
            },
            constraints: vec![],
        },
        // ── close_commit: advance COMMIT → REVEAL (StrictMonotonic) ──────
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol("close_commit"),
            },
            constraints: vec![StateConstraint::StrictMonotonic {
                index: PHASE_SLOT as u8,
            }],
        },
        // ── reveal_bid: record a revealed value (no phase change) ────────
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol("reveal_bid"),
            },
            constraints: vec![],
        },
        // ── resolve: advance REVEAL → RESOLVED (StrictMonotonic) ─────────
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol("resolve"),
            },
            constraints: vec![StateConstraint::StrictMonotonic {
                index: PHASE_SLOT as u8,
            }],
        },
    ])
}

/// The descriptor's flat `state_constraints` — exactly the predicate the executor
/// installs as the born cell's `CellProgram` and re-checks **unconditionally** on
/// every turn (`apply.rs::apply_create_cell_from_factory` installs
/// `CellProgram::Predicate(state_constraints)`). These are the `Always`-true
/// invariants only — the `WriteOnce` commit board + result registers (the
/// anti-front-running tooth). The phase-scoped `StrictMonotonic(PHASE)` is
/// method-scoped (it would be false on a `commit_bid` that leaves PHASE unchanged),
/// so it lives in the `close_commit` / `resolve` cases of [`auction_cell_program`]
/// (the canonical `child_program_vk` recipe).
fn auction_state_constraints() -> Vec<StateConstraint> {
    auction_invariants()
}

/// Canonical child-program VK for auction cells.
pub fn auction_child_program_vk() -> [u8; 32] {
    canonical_program_vk(&auction_cell_program())
}

/// Build the sealed-auction-cell [`FactoryDescriptor`]. The cell is born empty; the
/// seed turn binds `SELLER` and sets `PHASE = COMMIT`; bidders then commit sealed bids
/// into the `WriteOnce` board, the auctioneer closes the commit phase, bidders reveal,
/// and the auctioneer resolves — every step gated by the auction policy installed here
/// FOR LIFE.
pub fn auction_factory_descriptor() -> FactoryDescriptor {
    FactoryDescriptor {
        factory_vk: AUCTION_FACTORY_VK,
        child_program_vk: Some(auction_child_program_vk()),
        child_vk_strategy: Some(ChildVkStrategy::Fixed(Some(auction_child_program_vk()))),
        allowed_cap_templates: vec![CapTemplate {
            target: CapTarget::SelfCell,
            max_permissions: AuthRequired::Signature,
            attenuatable: true,
        }],
        field_constraints: vec![],
        state_constraints: auction_state_constraints(),
        default_mode: CellMode::Sovereign,
        creation_budget: Some(1_000_000),
    }
}

/// All factory descriptors this starbridge-app contributes.
pub fn factory_descriptors() -> Vec<FactoryDescriptor> {
    vec![auction_factory_descriptor()]
}

// =============================================================================
// The deos-native surface — the AUCTION as a composed `DeosApp`.
// =============================================================================
//
// The lifecycle operations are ONE [`DeosApp`] ([`auction_app`] below); the framework
// wires the rest — per-viewer projection, web-of-cells publish (the AUCTION cell IS a
// `dregg://` sturdyref), per-viewer rehydration, the generated
// `<dregg-affordance-surface>` component, and the manifest.
//
// **The seam is closed** — a TWO-TEMPO fire (mirror escrow-market / supply-chain).
// The state-mutating operations (`commit_bid`, `close_commit`, `reveal_bid`, `resolve`)
// are [`GatedAffordance`]s carrying a live-state PHASE PRECONDITION; the FULL auction
// program ([`auction_cell_program`]: the `WriteOnce` commit board + the
// `StrictMonotonic(PHASE)` lifecycle) is INSTALLED on the seeded auction cell
// ([`seed_auction`]) and RE-ENFORCED by the executor on every touching turn:
//
//   1. the deos PRECONDITION gate (the cap-gate `is_attenuation` AND the live-state
//      PHASE precondition `CellProgram::evaluate`) decides the button's verdict IN-BAND
//      — nothing submitted on a miss (anti-ghost; the htmx reactivity rides this);
//   2. [`fire_commit_bid`] / [`fire_close_commit`] / [`fire_reveal_bid`] / [`fire_resolve`]
//      submit the FULL multi-effect turn (built from the cell's LIVE state), and the
//      executor RE-ENFORCES the installed program — so OVERWRITING a committed bid
//      (`WriteOnce`) and a PHASE that rewinds / does-not-advance (`StrictMonotonic`) are
//      REAL executor refusals in the SUBMISSION path (see `tests/deos_seam.rs`).

/// The sealed-auction rights tiers, ON THE REAL ATTENUATION LATTICE:
///
///   - an OBSERVER (the public / an auditor watching the sale) holds
///     [`AuthRequired::Signature`] — the narrow read tier: `view_auction` and nothing
///     else;
///   - a BIDDER (an agent competing for the award) holds [`AuthRequired::Either`] — it
///     can `commit_bid` (seal a bid) and `reveal_bid` (open it) AND view;
///   - the AUCTIONEER (the party running the sale) holds [`AuthRequired::None`]/root — it
///     can `close_commit` (seal the commit phase) and `resolve` (announce the winner) on
///     top of everything a bidder can do.
///
/// So `Signature ⊂ Either ⊂ None` IS the observer ⊂ bidder ⊂ auctioneer ladder.
pub const OBSERVER_RIGHTS: AuthRequired = AuthRequired::Signature;
/// The bidder rights tier (sig-or-proof — commit + reveal + view). See [`OBSERVER_RIGHTS`].
pub const BIDDER_RIGHTS: AuthRequired = AuthRequired::Either;
/// The auctioneer rights tier (root — close + resolve + all). See [`OBSERVER_RIGHTS`].
pub const AUCTIONEER_RIGHTS: AuthRequired = AuthRequired::None;

/// The **life-of-cell auction program** the executor re-enforces on every touching turn
/// — the canonical method-dispatched [`auction_cell_program`]. This is the SAME program a
/// factory-born auction cell carries FOR LIFE (the one `tests/factory_birth.rs` proves
/// bites on the executor); installed by [`seed_auction`] so the gated fires re-enforce it.
pub fn auction_program() -> CellProgram {
    auction_cell_program()
}

/// A live-state precondition: the auction is in `phase`. A real [`CellProgram`] read
/// against the cell's current state, so a button is DARK in the wrong phase and LIT in
/// the right one (the htmx tooth). This gates "may this op fire now"; the auction
/// INVARIANT (the `WriteOnce` board + `StrictMonotonic(PHASE)`) is the installed
/// [`auction_program`] the executor re-enforces on the produced transition.
fn phase_precondition(phase: u64) -> CellProgram {
    CellProgram::Predicate(vec![StateConstraint::FieldEquals {
        index: PHASE_SLOT as u8,
        value: field_from_u64(phase),
    }])
}

/// The `commit_bid` precondition — the auction is in COMMIT (`PHASE == COMMIT`).
pub fn commit_precondition() -> CellProgram {
    phase_precondition(PHASE_COMMIT)
}

/// The `reveal_bid` precondition — the auction is in REVEAL (`PHASE == REVEAL`).
pub fn reveal_precondition() -> CellProgram {
    phase_precondition(PHASE_REVEAL)
}

/// The auctioneer's `close_commit` precondition — the auction is in COMMIT.
pub fn close_commit_precondition() -> CellProgram {
    phase_precondition(PHASE_COMMIT)
}

/// The auctioneer's `resolve` precondition — the auction is in REVEAL.
pub fn resolve_precondition() -> CellProgram {
    phase_precondition(PHASE_REVEAL)
}

/// **The AUCTION as a composed [`DeosApp`]** — the whole interaction surface, on the
/// deos bones. The auction cell is the agent's OWN cell (`cipherclerk.cell_id()`) so
/// fires execute against the seeded embedded ledger.
///
/// Five operations on the AUCTION cell, on the observer ⊂ bidder ⊂ auctioneer rights
/// ladder:
///
///   - `view_auction` — a cap-only affordance (an OBSERVER reads the board): `Signature`,
///     an `EmitEvent`;
///   - `commit_bid` — a [`GatedAffordance`] (a BIDDER seals a bid): `Either`, a COMMIT
///     precondition; the real fire ([`fire_commit_bid`]) writes a fresh `WriteOnce` commit
///     slot, re-enforced by the executor (overwriting a committed bid is REFUSED — the
///     anti-front-running tooth);
///   - `close_commit` — a [`GatedAffordance`] (the AUCTIONEER seals the commit phase):
///     `None`, a COMMIT precondition; advances `PHASE → REVEAL` (`StrictMonotonic`);
///   - `reveal_bid` — a [`GatedAffordance`] (a BIDDER opens its bid): `Either`, a REVEAL
///     precondition; records the revealed value;
///   - `resolve` — a [`GatedAffordance`] (the AUCTIONEER announces the winner): `None`, a
///     REVEAL precondition; advances `PHASE → RESOLVED` and writes `WINNER` / `HIGH_BID`.
///
/// The auction cell is published into the web-of-cells at the observer tier and is
/// discoverable under `auction` / `sealed-bid`.
///
/// Seed the cell's program + COMMIT state with [`seed_auction`] so the gated fires have a
/// live state and the executor re-enforces the program.
pub fn auction_app(cipherclerk: &AppCipherclerk, executor: &EmbeddedExecutor) -> DeosApp {
    let cell = cipherclerk.cell_id();

    // `view_auction` — an observer reads the board. Cap-only.
    let view = CellAffordance::new(
        "view_auction",
        OBSERVER_RIGHTS,
        Effect::EmitEvent {
            cell,
            event: Event::new(symbol("auction-read"), vec![]),
        },
    );
    // `commit_bid` — a BIDDER seals a bid. The GatedAffordance carries a DECISIVE effect
    // (a representative commit-slot write) AND the COMMIT precondition — so the button is
    // lit only in COMMIT, and the cap∧state gate decides its verdict in-band. The actual
    // fire ([`fire_commit_bid`]) writes the next free commit slot (read from live state),
    // which the executor re-enforces the `WriteOnce` board on (overwriting a committed bid
    // is REFUSED).
    let commit = GatedAffordance::new(
        CellAffordance::new(
            "commit_bid",
            BIDDER_RIGHTS,
            Effect::SetField {
                cell,
                index: commit_slot(0),
                value: field_from_u64(0),
            },
        ),
        commit_precondition(),
    );
    // `close_commit` — the AUCTIONEER seals the commit phase. The decisive effect advances
    // PHASE → REVEAL; gated on the COMMIT precondition. The executor re-enforces the
    // installed `StrictMonotonic(PHASE)` (a rewind / no-advance is refused).
    let close_commit = GatedAffordance::new(
        CellAffordance::new(
            "close_commit",
            AUCTIONEER_RIGHTS,
            Effect::SetField {
                cell,
                index: PHASE_SLOT,
                value: field_from_u64(PHASE_REVEAL),
            },
        ),
        close_commit_precondition(),
    );
    // `reveal_bid` — a BIDDER opens its bid. The decisive effect emits the revealed value;
    // gated on the REVEAL precondition.
    let reveal = GatedAffordance::new(
        CellAffordance::new(
            "reveal_bid",
            BIDDER_RIGHTS,
            Effect::EmitEvent {
                cell,
                event: Event::new(symbol("auction-reveal"), vec![]),
            },
        ),
        reveal_precondition(),
    );
    // `resolve` — the AUCTIONEER announces the winner. The decisive effect advances PHASE →
    // RESOLVED; gated on the REVEAL precondition. The executor re-enforces
    // `StrictMonotonic(PHASE)` + the `WriteOnce(WINNER/HIGH_BID)` result registers.
    let resolve = GatedAffordance::new(
        CellAffordance::new(
            "resolve",
            AUCTIONEER_RIGHTS,
            Effect::SetField {
                cell,
                index: PHASE_SLOT,
                value: field_from_u64(PHASE_RESOLVED),
            },
        ),
        resolve_precondition(),
    );

    DeosApp::builder("sealed-auction", cipherclerk.clone(), executor.clone())
        .discoverable(vec!["auction".into(), "sealed-bid".into()])
        .cell(
            DeosCell::new(cell, "auction")
                .affordance(view)
                .gated(commit)
                .gated(close_commit)
                .gated(reveal)
                .gated(resolve)
                .publish(OBSERVER_RIGHTS),
        )
        .build()
}

/// **Seed the AUCTION cell** so the gated fires have live state + the program bites:
/// install the full auction [`auction_program`] on the seeded auction cell (so the
/// executor re-enforces it on every touching turn), then bind the genesis state directly
/// into the embedded ledger — bind `SELLER` (`WriteOnce`, frozen after) and set
/// `PHASE = COMMIT` (commit slots empty).
///
/// After seeding, the auction is in COMMIT with a bound seller — a real `(old, new)`
/// baseline against which `commit_bid` writes the board. Returns the seeded seller scalar.
pub fn seed_auction(executor: &EmbeddedExecutor, seller: &str) -> FieldElement {
    let cell = executor.cell_id();
    executor.install_program(cell, auction_program());
    let seller_f = field_from_bytes(seller.as_bytes());
    executor.with_ledger_mut(|ledger| {
        if let Some(c) = ledger.get_mut(&cell) {
            c.state.set_field(SELLER_SLOT, seller_f);
            c.state.set_field(PHASE_SLOT, field_from_u64(PHASE_COMMIT));
        }
    });
    seller_f
}

/// **`commit_bid` effects** — write the sealed commitment `seal` into the next free commit
/// slot. The ONE coherent transition the installed invariants admit (a fresh `WriteOnce`
/// slot, the phase unchanged). The deos `commit_bid` gated affordance is the cap∧state
/// PRECONDITION face; THIS is the turn [`fire_commit_bid`] submits.
pub fn commit_bid_effects(cell: DeosCellId, slot: usize, seal: &Seal) -> Vec<Effect> {
    vec![
        Effect::SetField {
            cell,
            index: slot,
            value: *seal,
        },
        Effect::EmitEvent {
            cell,
            event: Event::new(symbol("auction-commit"), vec![*seal]),
        },
    ]
}

/// **`close_commit` effects** — advance `PHASE → REVEAL`, emitting `auction-closed`. THIS
/// is the turn [`fire_close_commit`] submits; the executor re-enforces `StrictMonotonic(PHASE)`.
pub fn close_commit_effects(cell: DeosCellId) -> Vec<Effect> {
    vec![
        Effect::SetField {
            cell,
            index: PHASE_SLOT,
            value: field_from_u64(PHASE_REVEAL),
        },
        Effect::EmitEvent {
            cell,
            event: Event::new(symbol("auction-closed"), vec![]),
        },
    ]
}

/// **`reveal_bid` effects** — record the revealed `(bidder, value)` of an opened bid (the
/// phase is not advanced). THIS is the turn [`fire_reveal_bid`] submits.
pub fn reveal_bid_effects(cell: DeosCellId, bidder: FieldElement, value: u64) -> Vec<Effect> {
    vec![Effect::EmitEvent {
        cell,
        event: Event::new(
            symbol("auction-reveal"),
            vec![bidder, field_from_u64(value)],
        ),
    }]
}

/// **`resolve` effects** — advance `PHASE → RESOLVED`, write `WINNER` / `HIGH_BID` (frozen
/// by the `Always` `WriteOnce`), and emit `auction-resolved`. THIS is the turn
/// [`fire_resolve`] submits; the executor re-enforces `StrictMonotonic(PHASE)` +
/// `WriteOnce(WINNER/HIGH_BID)`.
pub fn resolve_effects(cell: DeosCellId, winner: FieldElement, high_bid: u64) -> Vec<Effect> {
    let high_f = field_from_u64(high_bid);
    vec![
        Effect::SetField {
            cell,
            index: WINNER_SLOT,
            value: winner,
        },
        Effect::SetField {
            cell,
            index: HIGH_BID_SLOT,
            value: high_f,
        },
        Effect::SetField {
            cell,
            index: PHASE_SLOT,
            value: field_from_u64(PHASE_RESOLVED),
        },
        Effect::EmitEvent {
            cell,
            event: Event::new(symbol("auction-resolved"), vec![winner, high_f]),
        },
    ]
}

/// The next free commit slot on the auction cell's live `state` — the lowest
/// `COMMIT_BASE + i` whose value is still zero (unwritten). `None` if the board is full.
/// The honest [`fire_commit_bid`] picks this so each commit lands on a fresh `WriteOnce`
/// slot.
pub fn next_free_commit_slot(state: &dregg_cell::state::CellState) -> Option<usize> {
    (0..COMMIT_CAPACITY)
        .map(commit_slot)
        .find(|&slot| state.fields[slot] == [0u8; 32])
}

/// **Fire `commit_bid`** — the deos cap∧state PRECONDITION gate (cap ⊇ Either AND the
/// auction is in COMMIT), then the FULL commit turn ([`commit_bid_effects`]) the executor
/// re-enforces the auction program on. The fire reads the cell's LIVE state to pick the
/// next free commit slot, so two bidders never collide on a slot; the `WriteOnce` board
/// then FREEZES the committed bid (a later overwrite is REFUSED — the anti-front-running
/// tooth). Anti-ghost both ways: a precondition miss never submits; a program violation is
/// a real executor refusal. Use [`seed_auction`] first.
pub fn fire_commit_bid(
    app: &DeosApp,
    held: &AuthRequired,
    seal: Seal,
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
) -> Result<TurnReceipt, FireExecuteError> {
    let cell = &app.cells()[0];
    let target = cell.cell();
    cell.fire_gated_through_executor_with("commit_bid", held, cipherclerk, executor, move |live| {
        let slot = next_free_commit_slot(live).unwrap_or_else(|| commit_slot(0));
        commit_bid_effects(target, slot, &seal)
    })
}

/// **Fire `close_commit`** — the deos cap∧state PRECONDITION gate (cap ⊇ None AND the
/// auction is in COMMIT), then the FULL close turn ([`close_commit_effects`]). The executor
/// re-enforces `StrictMonotonic(PHASE)` (COMMIT → REVEAL). Use after the commits.
pub fn fire_close_commit(
    app: &DeosApp,
    held: &AuthRequired,
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
) -> Result<TurnReceipt, FireExecuteError> {
    let cell = &app.cells()[0];
    let target = cell.cell();
    cell.fire_gated_through_executor_with(
        "close_commit",
        held,
        cipherclerk,
        executor,
        move |_live| close_commit_effects(target),
    )
}

/// **Fire `reveal_bid`** — the deos cap∧state PRECONDITION gate (cap ⊇ Either AND the
/// auction is in REVEAL), then the FULL reveal turn ([`reveal_bid_effects`]) recording the
/// opened bid. Use after a successful [`fire_close_commit`].
pub fn fire_reveal_bid(
    app: &DeosApp,
    held: &AuthRequired,
    bidder: FieldElement,
    value: u64,
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
) -> Result<TurnReceipt, FireExecuteError> {
    let cell = &app.cells()[0];
    let target = cell.cell();
    cell.fire_gated_through_executor_with("reveal_bid", held, cipherclerk, executor, move |_live| {
        reveal_bid_effects(target, bidder, value)
    })
}

/// **Fire `resolve`** — the deos cap∧state PRECONDITION gate (cap ⊇ None AND the auction is
/// in REVEAL), then the FULL resolve turn ([`resolve_effects`]) the executor re-enforces the
/// auction program on. Advances `PHASE → RESOLVED` and writes the `WINNER` / `HIGH_BID`
/// (frozen by `WriteOnce`). `StrictMonotonic(PHASE)` re-enforces the one-way advance. Use
/// after the reveals.
pub fn fire_resolve(
    app: &DeosApp,
    held: &AuthRequired,
    winner: FieldElement,
    high_bid: u64,
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
) -> Result<TurnReceipt, FireExecuteError> {
    let cell = &app.cells()[0];
    let target = cell.cell();
    cell.fire_gated_through_executor_with("resolve", held, cipherclerk, executor, move |_live| {
        resolve_effects(target, winner, high_bid)
    })
}

/// Read a `u64` from the last 8 big-endian bytes of a field element (the inverse of
/// [`field_from_u64`] for the phase / bid-value registers the auction stores).
pub fn field_to_u64(f: &FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&f[24..32]);
    u64::from_be_bytes(b)
}

// =============================================================================
// StarbridgeAppContext mount.
// =============================================================================

/// Web-constants module (single source of truth for the JS surface).
pub fn web_constants() -> ConstantsModule {
    ConstantsModule::new("sealed-auction")
        .slot("PHASE_SLOT", PHASE_SLOT as u64)
        .slot("SELLER_SLOT", SELLER_SLOT as u64)
        .slot("HIGH_BID_SLOT", HIGH_BID_SLOT as u64)
        .slot("WINNER_SLOT", WINNER_SLOT as u64)
        .slot("COMMIT_BASE", COMMIT_BASE as u64)
        .slot("COMMIT_CAPACITY", COMMIT_CAPACITY as u64)
        .string("FACTORY_VK_HEX", hex_encode_32(&AUCTION_FACTORY_VK))
        .topic("COMMIT", "auction-commit")
        .topic("CLOSED", "auction-closed")
        .topic("REVEAL", "auction-reveal")
        .topic("RESOLVED", "auction-resolved")
}

/// **Register the sealed-auction starbridge-app** on a shared context — the FLOOR (the
/// executor-truth layer: the factory descriptor whose `state_constraints` ARE the
/// auction policy, installed on every born auction cell, with the on-ledger `WriteOnce`
/// commit board) AND the deos-native composition surface (the [`DeosApp`], folded into
/// the context's affordance registry). The factory + inspector are where SOUNDNESS lives
/// (overwriting a committed bid / rewinding the phase is a real executor refusal on the
/// born cell); the deos surface is the composition skin. Returns the factory VK.
pub fn register(ctx: &StarbridgeAppContext) -> [u8; 32] {
    let factory_vk = ctx.register_factory(auction_factory_descriptor());

    ctx.register_inspector(InspectorDescriptor {
        kind: "auction".into(),
        descriptor: serde_json::json!({
            "component": "dregg-auction",
            "module": "/starbridge-apps/sealed-auction/inspectors.js",
            "uri_prefix": "dregg://cell/",
            "summary_fields": ["phase", "seller", "high_bid", "winner", "commits"],
            "slot_layout": {
                "phase":      PHASE_SLOT,
                "seller":     SELLER_SLOT,
                "high_bid":   HIGH_BID_SLOT,
                "winner":     WINNER_SLOT,
                "commit_base": COMMIT_BASE,
                "capacity":   COMMIT_CAPACITY,
            },
            "phase_codes": {
                "commit":   PHASE_COMMIT,
                "reveal":   PHASE_REVEAL,
                "resolved": PHASE_RESOLVED,
            },
            "factory_vk_hex": hex_encode_32(&factory_vk),
            "child_program_vk_hex": hex_encode_32(&auction_child_program_vk()),
            "methods": ["commit_bid", "close_commit", "reveal_bid", "resolve"],
        }),
    });

    // Mount the deos-native composition surface (the `DeosApp`) on the SAME context.
    register_deos(ctx);

    factory_vk
}

/// **Mount the deos-native surface** ([`auction_app`]) on a shared context: build the
/// composed [`DeosApp`] from the context's cipherclerk + executor, seed the auction cell's
/// program + COMMIT state (so the gated fires bite), and fold the app into the context's
/// affordance registry ([`DeosApp::register`]). Returns the live [`DeosApp`] (so a host can
/// also [`DeosApp::mount`] its axum router / [`DeosApp::publish_all`] into the
/// web-of-cells).
pub fn register_deos(ctx: &StarbridgeAppContext) -> DeosApp {
    let app = auction_app(ctx.cipherclerk(), ctx.executor());
    // Seed the auction cell so the gated fires have a live `(old, new)` and the full
    // auction program (installed here) is re-enforced by the executor on every turn.
    seed_auction(ctx.executor(), "auctioneer");
    app.register(ctx);
    app
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod floor_tests {
    use super::*;
    use dregg_app_framework::{AgentCipherclerk, EmbeddedExecutor};
    use dregg_cell::program::TransitionMeta;
    use dregg_cell::state::CellState;

    fn test_cipherclerk() -> AppCipherclerk {
        AppCipherclerk::new(AgentCipherclerk::new(), [0x5au8; 32])
    }

    fn test_context() -> StarbridgeAppContext {
        let cipherclerk = test_cipherclerk();
        let executor = EmbeddedExecutor::new(&cipherclerk, "default");
        StarbridgeAppContext::new(cipherclerk, executor)
    }

    /// Evaluate the `Cases` program for a specific method (the program is
    /// method-dispatching, so a bare `evaluate` would default-deny).
    fn eval_for(
        program: &CellProgram,
        method: &str,
        new: &CellState,
        old: Option<&CellState>,
    ) -> Result<(), dregg_cell::ProgramError> {
        program.evaluate_with_meta(new, old, None, &TransitionMeta::new(symbol(method), 0))
    }

    fn empty() -> CellState {
        CellState::new(0)
    }

    fn committing() -> CellState {
        let mut s = empty();
        s.fields[SELLER_SLOT] = field_from_bytes(b"auctioneer");
        s.fields[PHASE_SLOT] = field_from_u64(PHASE_COMMIT);
        s
    }

    #[test]
    fn descriptor_is_deterministic() {
        assert_eq!(
            auction_factory_descriptor().hash(),
            auction_factory_descriptor().hash()
        );
    }

    #[test]
    fn child_program_vk_is_canonical_recipe() {
        let expected = canonical_program_vk(&auction_cell_program());
        assert_eq!(auction_child_program_vk(), expected);
        assert_eq!(
            auction_factory_descriptor().child_program_vk,
            Some(expected)
        );
    }

    #[test]
    fn factory_bakes_the_commit_board_and_result_caveats() {
        let d = auction_factory_descriptor();
        // the anti-front-running board: every commit slot is WriteOnce.
        for i in 0..COMMIT_CAPACITY {
            let idx = commit_slot(i) as u8;
            assert!(
                d.state_constraints.iter().any(|c| matches!(
                    c, StateConstraint::WriteOnce { index } if *index == idx
                )),
                "expected WriteOnce on commit slot {idx}"
            );
        }
        // the result registers freeze once written.
        for idx in [SELLER_SLOT as u8, HIGH_BID_SLOT as u8, WINNER_SLOT as u8] {
            assert!(
                d.state_constraints.iter().any(|c| matches!(
                    c, StateConstraint::WriteOnce { index } if *index == idx
                )),
                "expected WriteOnce on result slot {idx}"
            );
        }
        // the StrictMonotonic(PHASE) lifecycle lives in the close_commit / resolve cases.
        let phase_strict = match auction_cell_program() {
            CellProgram::Cases(cases) => cases.iter().any(|case| {
                matches!(case.guard, TransitionGuard::MethodIs { method } if method == symbol("resolve"))
                    && case.constraints.iter().any(|c| matches!(
                        c, StateConstraint::StrictMonotonic { index } if *index == PHASE_SLOT as u8
                    ))
            }),
            _ => false,
        };
        assert!(
            phase_strict,
            "StrictMonotonic(PHASE) missing from the resolve case"
        );
    }

    #[test]
    fn a_committed_bid_cannot_be_overwritten_the_anti_front_running_tooth() {
        // A committed sealed bid; a turn tries to OVERWRITE it → WriteOnce rejects.
        let program = auction_cell_program();
        let bid = Bid::new(7, 50, 9);
        let mut old = committing();
        old.fields[commit_slot(0)] = bid.seal();
        old.set_nonce(1);
        let mut overwrite = old.clone();
        overwrite.fields[commit_slot(0)] = Bid::new(7, 70, 9).seal(); // a different, higher bid
        let err = eval_for(&program, "commit_bid", &overwrite, Some(&old)).expect_err(
            "overwriting a committed sealed bid must be rejected — the anti-front-running tooth",
        );
        assert!(
            matches!(err, dregg_cell::ProgramError::ConstraintViolated {
                constraint: StateConstraint::WriteOnce { index }, ..
            } if index == commit_slot(0) as u8),
            "expected WriteOnce violation on the commit slot, got {err:?}"
        );
    }

    #[test]
    fn a_fresh_commit_to_an_empty_slot_is_accepted() {
        let program = auction_cell_program();
        let old = committing();
        let mut new = old.clone();
        new.fields[commit_slot(0)] = Bid::new(7, 50, 9).seal();
        assert!(eval_for(&program, "commit_bid", &new, Some(&old)).is_ok());
    }

    #[test]
    fn the_phase_cannot_rewind_or_stall_on_resolve_strictmonotonic() {
        let program = auction_cell_program();
        let mut old = committing();
        old.fields[PHASE_SLOT] = field_from_u64(PHASE_REVEAL);
        old.set_nonce(2);
        // a resolve that REWINDS the phase (REVEAL → COMMIT) is refused — the rewind
        // trips the universal `Monotonic(PHASE)` floor (evaluated first) AND, were that
        // absent, the resolve case's `StrictMonotonic(PHASE)`; either citing PHASE is a
        // valid anti-rollback refusal.
        let mut rewind = old.clone();
        rewind.fields[PHASE_SLOT] = field_from_u64(PHASE_COMMIT);
        let err = eval_for(&program, "resolve", &rewind, Some(&old))
            .expect_err("rewinding the phase must be rejected — the anti-rollback tooth");
        assert!(matches!(
            err,
            dregg_cell::ProgramError::ConstraintViolated {
                constraint: StateConstraint::StrictMonotonic { index }
                    | StateConstraint::Monotonic { index }, ..
            } if index == PHASE_SLOT as u8
        ));
        // a resolve that does NOT advance (REVEAL → REVEAL) is also refused (strict). The
        // non-strict `Monotonic` floor ADMITS the equal phase, so this bite is uniquely
        // the resolve case's `StrictMonotonic(PHASE)`.
        let stall = old.clone();
        let err = eval_for(&program, "resolve", &stall, Some(&old))
            .expect_err("a no-advance phase must be rejected — StrictMonotonic is strict");
        assert!(matches!(
            err,
            dregg_cell::ProgramError::ConstraintViolated {
                constraint: StateConstraint::StrictMonotonic { .. },
                ..
            }
        ));
    }

    #[test]
    fn unknown_method_is_default_denied() {
        let program = auction_cell_program();
        let err = eval_for(&program, "rig_auction", &committing(), Some(&empty()))
            .expect_err("an unknown method must be default-denied");
        assert!(matches!(
            err,
            dregg_cell::ProgramError::NoTransitionCaseMatched
        ));
    }

    #[test]
    fn register_installs_factory_and_inspector() {
        let ctx = test_context();
        let vk = register(&ctx);
        assert_eq!(vk, AUCTION_FACTORY_VK);
        assert_eq!(ctx.factory_registry().len(), 1);
        assert!(ctx.inspector_registry().get("auction").is_some());
    }
}
