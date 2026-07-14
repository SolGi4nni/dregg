//! # `dreggnet-trade` — scam-proof P2P player trading.
//!
//! Two players who do not trust each other exchange OWNED assets with **no trusted
//! middleman**: "I give you X iff you give me Y." This crate binds a
//! [`dreggnet_asset`] transfer (a real owner-signed spend of an owned note) to a
//! sealed-escrow leg from `starbridge-escrow-market`, so the exchange is a
//! **trustless atomic swap**:
//!
//! * **asset ↔ asset** — a cosmetic for a cosmetic, a trophy for crafting-mats;
//! * **asset ↔ $DREGG-value** — a listing: offer an asset for a price.
//!
//! ## The binding — how atomicity is achieved without a middleman
//!
//! The [sealed escrow](starbridge_escrow_market) is the **coordination ledger**: a
//! host cell whose committed heap tracks each leg's `Empty → Deposited → Consumed`
//! status one-shot, and whose [`settle`](starbridge_escrow_market::settle) consumes
//! BOTH legs in a single step only when both are present. A [`Trade`] rides that
//! switch:
//!
//! 1. **deposit** ([`TradeWorld::deposit`]) — a party commits its leg. An ASSET leg
//!    is a real [`AssetWorld::transfer`](dreggnet_asset::AssetWorld::transfer) of the
//!    owned note into a neutral **escrow-custodian** holder (the executor's signature
//!    gate refuses a non-owner — you cannot offer an asset you do not own); a $DREGG
//!    leg moves value from the party's wallet into the trade's value custody. Either
//!    way the sealed escrow records a live leg. Until settlement the value/asset sits
//!    in neutral custody — neither party can walk with the other's leg.
//! 2. **settle** ([`TradeWorld::settle`]) — the sealed escrow verifies BOTH legs are
//!    present + unconsumed and consumes them atomically; only then does the trade
//!    cross each leg to its counterparty (custody → the other party). No half-open
//!    trade: if one leg is missing, [`settle`](starbridge_escrow_market::settle)
//!    refuses and nothing crosses.
//! 3. **reclaim** ([`TradeWorld::reclaim`]) — the ghost defence. If a counterparty
//!    never deposits, the depositor reclaims its own leg (the sealed escrow consumes
//!    it one-shot, so it can never then be settled) and the custody asset/value
//!    returns to the depositor — **made whole**. The half-open-trade exit-scam is
//!    defeated by construction.
//!
//! ## What travels with the item — provenance
//!
//! An asset's [`AssetId`](dreggnet_asset::AssetId) and its origin minter are carried
//! unchanged across the whole lineage. After a trade the item's provenance
//! (mint → into escrow → to the new owner) **re-verifies**
//! ([`TradeWorld::verify_provenance`]): a rare drop's rarity is a checkable hash
//! chain, not marketing. The new owner can then transfer it; the old owner cannot
//! (its version is spent).
//!
//! ## Honest scope — no pay-to-win
//!
//! Tradable goods are **cosmetics / provenance-trophies / crafting-mats** only —
//! never raw power. Character XP / level / earned power are un-buyable gated turns
//! and are NOT assets in this layer. The scam-proofness is *by construction* (the
//! sealed escrow's both-present-atomic + one-shot teeth + the asset transfer's
//! signature gate), not by policy.
//!
//! ## Named residuals (not built here)
//!
//! * an **order book / auction house** over sealed-auction (this layer settles ONE
//!   matched trade at a time; [`Listing`] is a single offer, not a book);
//! * a **market frontend** (wallet / stall UI);
//! * a **fee sink to the treasury** (a marketplace cut at settle — no settlement
//!   path takes a cut today).

use std::collections::HashMap;

use dregg_cell::Cell;
use dregg_types::CellId;
use starbridge_escrow_market::{
    EscrowError, EscrowState, EscrowTerms, Leg, LegRequirement, LegStatus, Side, deposit_leg,
    move_value, open_escrow, reclaim_leg, settle,
};

pub use dreggnet_asset::{AssetError, AssetId, AssetWorld, ProvenanceReport};

/// The $DREGG value token every value leg is denominated in — the illiquid
/// service-pile currency ("buys cosmetics/AI-DM/seats", never power). A fixed
/// 32-byte asset id.
pub const DREGG_ASSET: [u8; 32] = *b"dreggnet-trade--DREGG-value-tok!";

/// The neutral escrow-custodian holder label in the [`AssetWorld`]. An asset leg is
/// deposited by transferring the owned note to this holder (value only *in transit*
/// — it is never a party to the trade), and crossed onward at settlement or returned
/// at reclaim.
pub const ESCROW_CUSTODY_LABEL: &str = "dreggnet-trade/escrow-custodian";

/// The sealed-escrow coordination host cell's owner + token sentinels (it carries no
/// balance of its own — it hosts the escrow ledger binding).
const ESCROW_HOST_PK: [u8; 32] = *b"dreggnet-trade-escrow-host-pubk!";
const ESCROW_HOST_TOKEN: [u8; 32] = *b"dreggnet-trade-escrow-host-token";

/// A stable [`CellId`] naming a trade party (the depositor identity bound into the
/// sealed-escrow terms). Derived from the party's label so a reclaim's `by` check
/// matches the terms' requirement.
fn party_cell(label: &str) -> CellId {
    let h = blake3::derive_key("dreggnet-trade-party-v1", label.as_bytes());
    CellId::from_bytes(h)
}

/// The [`CellId`] a sealed-escrow leg names as its "asset" for an ASSET leg —
/// derived from the stable [`AssetId`], so the leg is bound to *which* item.
fn asset_leg_token(asset: AssetId) -> CellId {
    CellId::from_bytes(asset.bytes())
}

/// The [`CellId`] naming the $DREGG value asset for a value leg.
fn dregg_leg_token() -> CellId {
    CellId::from_bytes(DREGG_ASSET)
}

/// One side of a trade: what a party puts up.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LegSpec {
    /// An owned asset (a cosmetic / provenance-trophy / crafting-mat), named by its
    /// stable cross-cell [`AssetId`]. Deposited as a real owner-signed transfer of
    /// the note into escrow custody.
    Asset(AssetId),
    /// A quantity of $DREGG value. Deposited by moving value from the party's wallet
    /// into the trade's value custody.
    Dregg(u64),
}

impl LegSpec {
    fn leg_token(&self) -> CellId {
        match self {
            LegSpec::Asset(a) => asset_leg_token(*a),
            LegSpec::Dregg(_) => dregg_leg_token(),
        }
    }
    /// The value the sealed escrow binds for this leg. An asset leg locks a presence
    /// marker of `1` (its *value* is its provenance, not a fungible amount); a $DREGG
    /// leg locks its amount.
    fn leg_amount(&self) -> i64 {
        match self {
            LegSpec::Asset(_) => 1,
            LegSpec::Dregg(v) => *v as i64,
        }
    }
}

/// Why a trade operation could not complete.
#[derive(Clone, Debug)]
pub enum TradeError {
    /// The asset layer refused a transfer — a non-owner offering an asset it does not
    /// own, a double-spend, or an otherwise-inadmissible move (the note signature
    /// gate). The scam-proof "you cannot sell what you do not hold" bit.
    Asset(AssetError),
    /// The sealed-escrow capacity refused — a half-open settle (a leg not deposited),
    /// a one-shot replay, non-conforming terms. The scam-proof "no half-open trade /
    /// no double-settle" bit.
    Escrow(EscrowError),
    /// The party's $DREGG wallet cannot cover the value leg.
    InsufficientDregg {
        /// The wallet's balance.
        have: i64,
        /// The leg amount it must cover.
        need: i64,
    },
    /// The side's leg is already deposited (a re-deposit is refused before any value
    /// moves).
    AlreadyDeposited(Side),
}

impl std::fmt::Display for TradeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TradeError::Asset(e) => write!(f, "asset transfer refused: {e}"),
            TradeError::Escrow(e) => write!(f, "sealed-escrow refused: {e}"),
            TradeError::InsufficientDregg { have, need } => {
                write!(f, "insufficient $DREGG: have {have}, need {need}")
            }
            TradeError::AlreadyDeposited(s) => write!(f, "leg {s:?} is already deposited"),
        }
    }
}

impl std::error::Error for TradeError {}

impl From<AssetError> for TradeError {
    fn from(e: AssetError) -> Self {
        TradeError::Asset(e)
    }
}
impl From<EscrowError> for TradeError {
    fn from(e: EscrowError) -> Self {
        TradeError::Escrow(e)
    }
}

/// The receipt of a settled trade — which side received what.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Settlement {
    /// What side A put up (crossed to side B).
    pub a_gave: LegSpec,
    /// What side B put up (crossed to side A).
    pub b_gave: LegSpec,
}

/// One side's binding within a [`Trade`].
#[derive(Clone, Debug)]
struct SideBinding {
    label: String,
    spec: LegSpec,
    party: CellId,
}

/// **A trade** — a sealed-escrow-coordinated atomic swap between two parties.
///
/// Holds the sealed-escrow coordination host cell (its committed heap is the swap's
/// source of truth), the swap terms, the two side bindings, and (for a value leg)
/// the trade's own $DREGG value custody. Drive it through [`TradeWorld`]:
/// [`deposit`](TradeWorld::deposit) each side, then
/// [`settle`](TradeWorld::settle) — or [`reclaim`](TradeWorld::reclaim) on a ghost.
pub struct Trade {
    escrow: Cell,
    terms: EscrowTerms,
    a: SideBinding,
    b: SideBinding,
    /// $DREGG held in transit while a value leg is locked (empty for asset↔asset).
    dregg_custody: Cell,
}

impl Trade {
    fn binding(&self, side: Side) -> &SideBinding {
        match side {
            Side::A => &self.a,
            Side::B => &self.b,
        }
    }

    /// The sealed-escrow leg status of one side (`Empty` / `Deposited` / `Consumed`).
    pub fn leg_status(&self, side: Side) -> LegStatus {
        EscrowState::read(&self.escrow)
            .map(|s| s.status(side))
            .unwrap_or(LegStatus::Empty)
    }

    /// What side A puts up.
    pub fn side_a(&self) -> LegSpec {
        self.a.spec
    }
    /// What side B puts up.
    pub fn side_b(&self) -> LegSpec {
        self.b.spec
    }
}

/// **The trading world** — the mint / trade surface over a set of players' sovereign
/// asset ledgers plus their $DREGG wallets. Every asset move is a real owner-signed
/// [`AssetWorld`] transfer; every trade's atomicity is the sealed escrow's.
pub struct TradeWorld {
    assets: AssetWorld,
    /// Per-player $DREGG wallets (value cells on the [`DREGG_ASSET`] token), keyed by
    /// player label.
    wallets: HashMap<String, Cell>,
}

impl Default for TradeWorld {
    fn default() -> Self {
        Self::new()
    }
}

impl TradeWorld {
    /// A fresh trading world (no players, no assets).
    pub fn new() -> Self {
        TradeWorld {
            assets: AssetWorld::new(),
            wallets: HashMap::new(),
        }
    }

    /// Access the underlying asset world (mint / transfer / provenance directly).
    pub fn assets(&mut self) -> &mut AssetWorld {
        &mut self.assets
    }

    /// The deterministic pubkey of a player (creating the identity if new).
    pub fn pubkey_of(&mut self, label: &str) -> [u8; 32] {
        self.assets.pubkey_of(label)
    }

    /// **Mint an asset** owned by `minter_label` — a cosmetic / trophy / crafting-mat
    /// drop. Returns the stable [`AssetId`] a trade names it by.
    pub fn mint(&mut self, minter_label: &str, mint_seed: &[u8]) -> AssetId {
        self.assets.mint(minter_label, mint_seed)
    }

    fn wallet(&mut self, label: &str) -> &mut Cell {
        let pk = self.assets.pubkey_of(label);
        self.wallets
            .entry(label.to_string())
            .or_insert_with(|| Cell::with_balance(pk, DREGG_ASSET, 0))
    }

    /// **Credit `amount` of $DREGG** to a player's wallet (a faucet, for standing up a
    /// trade). Value the player can put up as a leg.
    pub fn fund_dregg(&mut self, label: &str, amount: u64) {
        let w = self.wallet(label);
        assert!(w.state.credit_balance(amount), "credit cannot overflow");
    }

    /// A player's $DREGG wallet balance.
    pub fn dregg_balance(&mut self, label: &str) -> i64 {
        self.wallet(label).state.balance()
    }

    /// **Open a trade** — "`a_label` gives `a` iff `b_label` gives `b`". Seals the swap
    /// terms into a fresh sealed-escrow coordination cell; no leg is deposited yet.
    pub fn open_trade(&mut self, a_label: &str, a: LegSpec, b_label: &str, b: LegSpec) -> Trade {
        // Ensure both identities (and the neutral custodian) exist.
        let a_party = party_cell(a_label);
        let b_party = party_cell(b_label);
        let _ = self.assets.pubkey_of(a_label);
        let _ = self.assets.pubkey_of(b_label);
        let _ = self.assets.pubkey_of(ESCROW_CUSTODY_LABEL);

        let terms = EscrowTerms::swap(
            LegRequirement::new(a_party, a.leg_token(), a.leg_amount()),
            LegRequirement::new(b_party, b.leg_token(), b.leg_amount()),
        );
        let mut escrow = Cell::with_balance(ESCROW_HOST_PK, ESCROW_HOST_TOKEN, 0);
        open_escrow(&mut escrow, &terms);

        Trade {
            escrow,
            terms,
            a: SideBinding {
                label: a_label.to_string(),
                spec: a,
                party: a_party,
            },
            b: SideBinding {
                label: b_label.to_string(),
                spec: b,
                party: b_party,
            },
            dregg_custody: Cell::with_balance(ESCROW_HOST_PK, DREGG_ASSET, 0),
        }
    }

    /// **Deposit** a side's leg into the trade. An ASSET leg is a real owner-signed
    /// transfer of the note into the escrow custodian — a NON-OWNER is refused
    /// ([`TradeError::Asset`]), the "you cannot offer what you do not own" gate. A
    /// $DREGG leg moves value from the party's wallet into custody (refused up front
    /// if the wallet cannot cover it). Either way the sealed escrow records a live
    /// leg. A re-deposit is refused before anything moves.
    pub fn deposit(&mut self, trade: &mut Trade, side: Side) -> Result<(), TradeError> {
        // One-shot from Empty: never move value/assets over a live-or-consumed leg.
        if trade.leg_status(side) != LegStatus::Empty {
            return Err(TradeError::AlreadyDeposited(side));
        }
        let (label, spec, party) = {
            let b = trade.binding(side);
            (b.label.clone(), b.spec, b.party)
        };

        match spec {
            LegSpec::Asset(asset) => {
                // The ownership gate: the depositor must currently OWN the asset — this
                // is a real owner-signed spend. A non-owner (or a double-spend) is a
                // real refusal here, BEFORE the escrow leg is recorded.
                self.assets.transfer(asset, &label, ESCROW_CUSTODY_LABEL)?;
            }
            LegSpec::Dregg(amount) => {
                let have = self.wallet(&label).state.balance();
                if have < amount as i64 {
                    return Err(TradeError::InsufficientDregg {
                        have,
                        need: amount as i64,
                    });
                }
                let moved =
                    move_value(self.wallet(&label), &mut trade.dregg_custody, amount as i64);
                assert!(moved, "the funds check above guarantees the move succeeds");
            }
        }

        // Record the (now-genuinely-locked) leg into the sealed-escrow commitment. It
        // conforms by construction, so this only fails on a terms/one-shot violation
        // (already excluded above).
        let leg = Leg::new(party, spec.leg_token(), spec.leg_amount());
        deposit_leg(&mut trade.escrow, &trade.terms, side, &leg)?;
        Ok(())
    }

    /// **Settle** the trade atomically: the sealed escrow verifies BOTH legs are
    /// present + unconsumed and consumes them one-shot ([`settle`]); only then does
    /// the trade CROSS each leg to its counterparty — side A's leg to side B, side B's
    /// to side A. There is no half-open trade: if a leg is missing the escrow refuses
    /// and nothing crosses.
    pub fn settle(&mut self, trade: &mut Trade) -> Result<Settlement, TradeError> {
        // The atomic switch: both-present + one-shot consume, or refuse with no cross.
        settle(&mut trade.escrow, &trade.terms)?;

        let a = trade.a.clone();
        let b = trade.b.clone();
        // Cross A's leg -> B, and B's leg -> A. After the escrow authorized (consumed
        // both legs), the custody holder owns each asset / holds each value, so these
        // moves are infallible.
        self.cross_leg(trade, a.spec, &b.label);
        self.cross_leg(trade, b.spec, &a.label);

        Ok(Settlement {
            a_gave: a.spec,
            b_gave: b.spec,
        })
    }

    /// Move a settled/reclaimed leg out of custody to `to_label`.
    fn cross_leg(&mut self, trade: &mut Trade, spec: LegSpec, to_label: &str) {
        match spec {
            LegSpec::Asset(asset) => {
                self.assets
                    .transfer(asset, ESCROW_CUSTODY_LABEL, to_label)
                    .expect("the custodian owns the deposited asset; the cross is admissible");
            }
            LegSpec::Dregg(amount) => {
                let moved = move_value(
                    &mut trade.dregg_custody,
                    self.wallet(to_label),
                    amount as i64,
                );
                assert!(moved, "custody holds the locked value; the cross succeeds");
            }
        }
    }

    /// **Reclaim** a stranded leg on a ghosting counterparty (the half-open-trade
    /// defence). The sealed escrow permits it only to the leg's depositor and only
    /// while the leg is live ([`reclaim_leg`]), consuming it one-shot — so a reclaimed
    /// leg can never then be settled. The custody asset / value returns to the
    /// depositor: **made whole**.
    pub fn reclaim(&mut self, trade: &mut Trade, side: Side) -> Result<(), TradeError> {
        let (label, spec, party) = {
            let b = trade.binding(side);
            (b.label.clone(), b.spec, b.party)
        };
        reclaim_leg(&mut trade.escrow, &trade.terms, side, party)?;
        // Return the leg to its depositor.
        self.cross_leg(trade, spec, &label);
        Ok(())
    }

    // ── provenance / ownership passthrough ───────────────────────────────────

    /// **Re-verify a traded item's provenance** — the content-addressed lineage
    /// (mint → into escrow → new owner) plus the on-chain spent re-reads. A rare
    /// drop's rarity is a checkable hash chain, not marketing.
    pub fn verify_provenance(&self, asset: AssetId) -> ProvenanceReport {
        self.assets.verify_provenance(asset)
    }

    /// The current holder pubkey of an asset (the tail version's owner).
    pub fn current_owner(&self, asset: AssetId) -> Option<[u8; 32]> {
        self.assets.current_owner(asset)
    }

    /// The current holder label of an asset.
    pub fn current_holder_label(&self, asset: AssetId) -> Option<&str> {
        self.assets.current_holder_label(asset)
    }

    /// The number of versions in an asset's lineage (1 after mint, +1 per transfer).
    pub fn lineage_len(&self, asset: AssetId) -> usize {
        self.assets.lineage_len(asset)
    }
}

/// **A listing** — an offer of an asset for a $DREGG price. A listing is a
/// standing offer, not a lock: the swap itself happens ATOMICALLY at
/// [`buy`](TradeWorld::buy) time, when the real buyer is known — the seller's
/// asset and the buyer's value deposit and settle in one crossing, so neither
/// party can be scammed. (Escrowing the asset the instant it is listed is the
/// named order-book residual.)
#[derive(Clone, Debug)]
pub struct Listing {
    /// The listed asset.
    pub asset: AssetId,
    /// The asking price in $DREGG.
    pub price: u64,
    /// The seller's label.
    pub seller: String,
    /// Set once the listing is sold or cancelled — a listing settles at most once.
    consumed: bool,
}

impl TradeWorld {
    /// **List** `asset` for `price` $DREGG, offered by `seller`. Records the offer;
    /// a non-owner cannot list an asset it does not hold (checked here, and re-checked
    /// as the owner-signed transfer gate at [`buy`](TradeWorld::buy)). No value moves
    /// until a buyer completes the sale.
    pub fn list(
        &mut self,
        seller: &str,
        asset: AssetId,
        price: u64,
    ) -> Result<Listing, TradeError> {
        let seller_pk = self.pubkey_of(seller);
        if self.current_owner(asset) != Some(seller_pk) {
            return Err(TradeError::Asset(AssetError::Refused(
                "the seller does not own the listed asset".to_string(),
            )));
        }
        Ok(Listing {
            asset,
            price,
            seller: seller.to_string(),
            consumed: false,
        })
    }

    /// **Buy** a listing: open the full trade with the real `buyer`, deposit BOTH legs
    /// (the seller's asset — an owner-signed transfer that refuses if the seller no
    /// longer holds it — and the buyer's price), then settle ATOMICALLY. The asset
    /// crosses to the buyer, the value to the seller. If the buyer cannot pay after
    /// the asset is in custody, the seller's asset is returned (made whole) and the
    /// sale is refused — no half-open trade.
    pub fn buy(&mut self, listing: &mut Listing, buyer: &str) -> Result<Settlement, TradeError> {
        if listing.consumed {
            return Err(TradeError::Escrow(EscrowError::LegAlreadyConsumed(Side::A)));
        }
        let seller = listing.seller.clone();
        let mut trade = self.open_trade(
            &seller,
            LegSpec::Asset(listing.asset),
            buyer,
            LegSpec::Dregg(listing.price),
        );
        // The seller's asset enters custody (owner-signed; refused if not owned).
        self.deposit(&mut trade, Side::A)?;
        // The buyer's price enters custody. On a shortfall, undo the asset leg so the
        // seller keeps their item (atomicity: no leg is left stranded).
        if let Err(e) = self.deposit(&mut trade, Side::B) {
            self.reclaim(&mut trade, Side::A)
                .expect("a live, unsettled asset leg is reclaimable by its depositor");
            return Err(e);
        }
        let settlement = self.settle(&mut trade)?;
        listing.consumed = true;
        Ok(settlement)
    }

    /// **Cancel** a listing before a sale — void the standing offer so it can never be
    /// bought. Nothing was locked (a listing does not escrow the asset until a buyer
    /// matches), so the seller already holds the asset.
    pub fn cancel_listing(&mut self, listing: &mut Listing) {
        listing.consumed = true;
    }
}

// Re-export the sealed-escrow `Side` so callers can name trade sides without a second
// dependency.
pub use starbridge_escrow_market::Side as TradeSide;
