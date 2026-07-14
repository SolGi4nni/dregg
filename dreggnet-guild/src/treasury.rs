//! # `treasury` — an escrow-custodied guild bank; no officer can abscond
//!
//! A guild treasury is not a balance an officer holds — it is value locked into the
//! protocol-proven `SealedEscrow` capacity ([`starbridge_escrow_market::SealedEscrowMarket`]).
//! [`GuildTreasury`] drives that capacity for a guild:
//!
//! * [`contribute`](GuildTreasury::contribute) — a member locks a conforming leg; the
//!   value LEAVES their wallet into custody (conserved, and the escrow commitment
//!   moves, so a light client witnesses it enter). A non-conforming leg, or a wallet
//!   that cannot cover it, is refused before any value moves.
//! * [`attempt_abscond`](GuildTreasury::attempt_abscond) — the anti-abscond tooth. The
//!   capacity permits a reclaim ONLY to the leg's original depositor; an officer (any
//!   non-depositor) pulling a member's contribution is a real refusal
//!   (`EscrowError::NotYourLeg`). **No officer can walk off with the bank.**
//! * [`reclaim`](GuildTreasury::reclaim) — the rightful depositor pulls their own
//!   contribution back before settlement and is made whole (the non-vacuous contrast:
//!   the SAME operation succeeds for the leg's owner).
//! * [`settle`](GuildTreasury::settle) — the escrow closes atomically, crossing each
//!   leg to its counterparty per the SEALED terms (fixed at open — an officer cannot
//!   re-point where value goes).
//!
//! The escrow custodian holds value only *in transit* and is never a party to the
//! trade (`starbridge_escrow_market::ESCROW_CUSTODIAN_PK`).

use dregg_cell::Cell;
use dregg_types::CellId;

pub use starbridge_escrow_market::{
    EscrowError, EscrowState, EscrowTerms, Leg, LegRequirement, MarketError, SealedEscrowMarket,
    Side,
};

/// A treasury operation refusal — the sealed-escrow capacity's forge-rejecting check
/// biting (a non-conforming leg, a non-depositor reclaim, an over-claim, …), or a
/// wallet that cannot cover / mismatches the leg's asset.
pub type TreasuryError = MarketError;

/// **An escrow-custodied guild treasury.** Wraps a [`SealedEscrowMarket`] so member
/// contributions are locked into the witnessed escrow commitment and no officer can
/// abscond — a reclaim is permitted ONLY to the leg's depositor.
#[derive(Clone, Debug)]
pub struct GuildTreasury {
    market: SealedEscrowMarket,
}

impl GuildTreasury {
    /// **Open a treasury** over `terms` — seal the contribution terms (who must lock
    /// what on each side) into a fresh escrow commitment. No value is locked yet.
    pub fn open(terms: EscrowTerms) -> GuildTreasury {
        GuildTreasury {
            market: SealedEscrowMarket::open(terms),
        }
    }

    /// **A member contributes** — lock a conforming `leg` from the member's `wallet`
    /// into escrow custody. The capacity validates the leg against the sealed terms
    /// FIRST (right party, right asset, sufficient amount); on success the value leaves
    /// the wallet into custody (conserved) and the escrow commitment moves. A
    /// non-conforming leg (or an under-funded / wrong-asset wallet) is refused with
    /// nothing moved.
    pub fn contribute(
        &mut self,
        side: Side,
        leg: &Leg,
        wallet: &mut Cell,
    ) -> Result<(), TreasuryError> {
        self.market.deposit(side, leg, wallet)
    }

    /// **THE ANTI-ABSCOND TOOTH — an officer cannot take a member's contribution.**
    /// Attempts to reclaim the leg on `side` on behalf of `officer` (a non-depositor)
    /// into `to`. The sealed-escrow capacity permits a reclaim ONLY to the leg's
    /// original depositor, so this is a real refusal (`EscrowError::NotYourLeg`) — no
    /// value moves. The bank cannot be drained by whoever holds an officer title.
    pub fn attempt_abscond(
        &mut self,
        side: Side,
        officer: CellId,
        to: &mut Cell,
    ) -> Result<i64, TreasuryError> {
        self.market.reclaim(side, officer, to)
    }

    /// **The rightful depositor reclaims their own contribution** before settlement and
    /// is made whole (the non-vacuous contrast to [`attempt_abscond`](Self::attempt_abscond):
    /// the SAME reclaim succeeds for the leg's owner). A reclaimed leg is one-shot — it
    /// can never then be settled.
    pub fn reclaim(
        &mut self,
        side: Side,
        depositor: CellId,
        to: &mut Cell,
    ) -> Result<i64, TreasuryError> {
        self.market.reclaim(side, depositor, to)
    }

    /// **Settle** the treasury atomically — cross each locked leg to its counterparty
    /// per the SEALED terms (both legs must be present). Returns the authorized
    /// `(amount_a, amount_b)`. There is no partial settlement.
    pub fn settle(
        &mut self,
        a_receiving: &mut Cell,
        b_receiving: &mut Cell,
    ) -> Result<(i64, i64), TreasuryError> {
        self.market.settle(a_receiving, b_receiving)
    }

    /// Value held in custody for leg A (in transit while the leg is locked).
    pub fn custody_a(&self) -> i64 {
        self.market.escrow_custody_a()
    }

    /// Value held in custody for leg B (in transit while the leg is locked).
    pub fn custody_b(&self) -> i64 {
        self.market.escrow_custody_b()
    }

    /// The escrow host cell's canonical commitment — moves when a leg is locked,
    /// settled, or reclaimed (a light client witnesses every change).
    pub fn commitment(&self) -> [u8; 32] {
        self.market.commitment()
    }

    /// The escrow's committed state (per-leg status + amount), read back from the host
    /// cell's heap.
    pub fn state(&self) -> Result<EscrowState, EscrowError> {
        self.market.state()
    }
}
