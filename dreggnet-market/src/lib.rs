//! # DreggNet offering #commerce — a sealed-bid AUCTION / MARKET.
//!
//! The dungeon (offering #0) proved the [`Offering`] abstraction over a *game*; hosted-Hermes
//! over an *agent*; a grain over *compute*; polis over *governance*. This crate proves it reaches
//! an **economic flow** — a market where **value moves**, conservation-checked — by wrapping the
//! real sealed-bid auction substrate as a [`MarketOffering`]:
//!
//!   * **LIST** ([`advance`](Offering::advance) with [`TURN_LIST`]) — a seller opens a listing: a
//!     REAL factory-born auction cell comes alive through the verified executor (a
//!     `CreateCellFromFactory` turn → a genuine [`TurnReceipt`]). The born cell carries the auction
//!     policy FOR LIFE (the `WriteOnce` commit board + the `StrictMonotonic(PHASE)` lifecycle).
//!   * **BID** ([`TURN_BID`]) — a bidder places a **sealed** commit-reveal bid: the [`Bid::seal`]
//!     digest (`BLAKE3(bidder‖value‖nonce)`) lands on the cell's on-ledger `WriteOnce` commit board
//!     as a real verified turn. The teeth are the substrate's, not ours: a **double-bid** (a bidder
//!     overwriting its own committed sealed bid) is a **real executor refusal** (`WriteOnce`); a
//!     **bid after the commit phase closes** is refused by the auction's own phase gate (nothing
//!     submitted — anti-ghost).
//!   * **SETTLE** ([`TURN_SETTLE`]) — the auctioneer closes the commit phase, reveals the bids, and
//!     **clears to the winning sealed bid**. The value moves through the VERIFIED per-asset ring
//!     settlement ([`settle_ring_verified`], the Rust image of the Lean `Ring.settleRing`): the
//!     winner pays its bid of the payment asset to the seller, the slot delivers the good to the
//!     winner, **per-asset Σδ = 0** or the whole award aborts (atomicity + conservation). A
//!     **below-reserve** clear or a **no-valid-bid** auction does **NOT** settle — no value moves,
//!     no resolve turn commits.
//!
//! [`verify`](Offering::verify) re-verifies the cleared chain: re-derive the settlement from the
//! recorded sealed bids and confirm the winner is the real high bid and the value move conserves
//! every asset. [`render`](Offering::render) / [`actions`](Offering::actions) paint the listing +
//! bids as cap-gated deos affordances.
//!
//! ## The substrate wrapped
//!
//! [`starbridge_sealed_auction`] — its in-process [`Auction`] commit/reveal/settle state machine
//! (whose [`Auction::settle`] folds the award ring through the verified executor, conservation-
//! checked) AND its on-ledger auction cell (the factory descriptor + `*_effects` turn builders the
//! executor re-enforces the `WriteOnce` board / `StrictMonotonic(PHASE)` lifecycle on). We consume
//! both altitudes; we re-implement neither sealed bidding nor settlement. See the crate `[HONEST
//! SCOPE]` note at the bottom for what a fuller market (a continuous order book, multi-asset
//! baskets, a live escrow-market clearing organ) adds.

/// Deterministic fhEgg clearing + hiding Cert-F receipt integration.  This is a
/// deliberately opt-in heavy proving surface; enable Cargo feature
/// `certified-clearing` to compile it.
#[cfg(feature = "certified-clearing")]
pub mod certified_clearing;

/// Hiding fixed-book proof gate for the real Dark Bazaar settlement. The proof
/// is checked against caller-pinned public values before any executor turn is
/// submitted; enable Cargo feature `private-clearing` to compile it.
#[cfg(feature = "private-clearing")]
pub mod private_clearing;

/// Receipt-bound, replay-safe game consequences sourced from a verified private
/// clearing. The target game still executes the state change through its own
/// executor; the gate pins the exact settlement statement, winner, target, and
/// landed receipt, with restart recovery for the post-turn persistence window.
#[cfg(feature = "private-clearing")]
pub mod private_clearing_consequence;

/// Ordered-roster guild and raid rewards driven by an exact verified private
/// clearing winner. The allocation digest binds the winning actor to their
/// character cell and named reward before the ordinary consequence gate runs.
#[cfg(feature = "private-clearing")]
pub mod private_clearing_guild_allocation;

/// Durable global one-shot authority and exact signed-effect outbox for the
/// playable private Bazaar consequence.
#[cfg(feature = "private-clearing")]
pub mod private_bazaar_authority;

/// Concrete Dungeon XP adapter: derives the exact pre-value from the durable
/// target immediately before prepare, seals dispatch before executor mutation,
/// and recovers only from the target's authoritative receipt chain.
#[cfg(feature = "private-clearing")]
pub mod private_bazaar_game_adapter;

/// Frontend-neutral player journey around a private Bazaar raid allocation.
/// Browser and chat adapters receive only ordinary [`Action`]s, a viewer-blind
/// public receipt, and a [`Surface`]; the private book, proof, winner, and target
/// character remain on the verifier/engine side of this boundary.
pub mod private_bazaar_journey;

/// Real OfferingHost lifecycle for the viewer-blind private Bazaar raid.
#[cfg(feature = "private-clearing")]
pub mod private_bazaar_live_host;

/// Composite integrity verifier: the same canonical fhEgg receipt must carry
/// both an authenticated roster quorum and the fixed private-book HidingFRI
/// proof. The BFV-ciphertext/private-root same-opening relation remains named.
#[cfg(feature = "private-attested-clearing")]
pub mod private_attested_clearing;

/// Apex composite verifier requiring authenticated quorum, HidingFRI clearing
/// semantics, and transferable BFV/private-root same-opening evidence in one
/// canonical envelope. Live markets use its source-bound constructor, which
/// requires every signed board ciphertext to byte-identify a distinct canonical
/// proof row; the older proof-only constructor remains for non-market callers.
#[cfg(feature = "private-attested-clearing")]
pub mod private_bfv_attested_clearing;

/// Typed apex from the complete private BFV/HidingFRI/quorum verifier into the
/// existing atomic market + provenance-carrying game asset consequence.
#[cfg(all(feature = "private-attested-clearing", feature = "fhegg-settlement"))]
pub mod private_bfv_live_apex;

/// Authenticated co-endorsement weld between the complete certified market
/// receipt and fhegg-fhe's exact canonical MPC claim. This does not prove that
/// the ciphertexts open to the certified book. It is an opt-in heavy surface.
#[cfg(feature = "authenticated-clearing")]
pub mod authenticated_receipt;

/// Direct additive weld from fhEgg's authenticated encrypted-order clearing
/// receipt into the real Dark Bazaar executor settlement. Enable Cargo feature
/// `fhegg-settlement` to keep the FHE/MPC stack out of ordinary clients.
#[cfg(feature = "fhegg-settlement")]
pub mod fhegg_settlement;

/// One-call process-local atomic composition of authenticated fhEgg clearing
/// with the exact source-bound owned-asset/$DREGG crossing.
#[cfg(feature = "fhegg-settlement")]
pub mod fhegg_atomic_asset;

/// Exact operator-visible BFV opening verification welded into source-bound
/// WriteOnce auction seals. This is an authenticated source-verifier boundary,
/// not a house-blind lattice ZK proof.
#[cfg(feature = "fhegg-settlement")]
pub mod fhegg_source_binding;

/// Strict owning/wire boundary for accepting an authenticated fhEgg settlement
/// from a remote worker without receiving trader plaintext. Shared by any web,
/// Telegram, Discord, or native host that can transport opaque bytes.
#[cfg(feature = "fhegg-settlement")]
pub mod fhegg_transport;

/// Host-selected computation-integrity registry for the frontend-neutral
/// settlement operation. Uploaded bundles never choose or weaken this policy.
#[cfg(feature = "fhegg-settlement")]
pub mod fhegg_verifier_registry;

/// Owner-gated settlement of a real provenance-carrying asset (for example a
/// Descent loot note) to the sealed auction's already-verified winner.
pub mod asset_backed;

/// Hosted encrypted-amount constant-product game table and its strict external
/// producer wire. This heavy BFV surface is independently opt-in.
#[cfg(feature = "dark-amm-game")]
pub mod dark_amm_game;

/// Public-only two-phase collective Dark AMM service: Tier-1 same-opening
/// stages one encrypted candidate and an independent FHDAR decision advances
/// it. This does not alter the single-host strict-v3 offering above.
#[cfg(feature = "dark-amm-game")]
pub mod dark_amm_collective;
#[cfg(feature = "dark-amm-game")]
pub mod dark_amm_collective_worker;

/// THE PLAYABLE DARK POOL — a blind relic vendor a player can actually press a button on.
/// Reserves live only as BFV ciphertexts under an n-of-n collective key, a swap is admitted
/// only when one homomorphic constant-product check opens (under a FULL threshold quorum) to
/// the public invariant, and the relic + `$DREGG` cross through the owner-gated sealed escrow
/// with a real committed journal turn as the receipt. Distinct from [`dark_amm_game`], which
/// is upload-only and has no affordances. See [`dark_pool_offering`].
#[cfg(feature = "dark-pool-offering")]
pub mod dark_pool_offering;

/// THE ORACLE PIT — a confidential prediction market whose SUBJECT is the daily Descent.
/// Public odds, private positions: a position rides a BFV ciphertext under an n-of-n collective
/// key plus a hiding commitment frozen on a real `WriteOnce` board, the published line is the
/// quadratic cost function's marginal prices opened by a FULL threshold quorum, and the market
/// settles on the run record's EXACT re-execution through the Lean-emitted dungeon program — not
/// on any asserted result. See [`oracle_pit`].
#[cfg(feature = "oracle-pit")]
pub mod oracle_pit;

use dreggnet_offerings::{
    Action, BinaryOperationDescriptor, BinaryOperationError, BinaryOperationReceipt,
    BinaryOperationReplayMaterial, DreggIdentity, Offering, OfferingError, Outcome, RunCost,
    SessionConfig, Surface, VerifyReport,
};

#[cfg(feature = "fhegg-settlement")]
use fhegg_fhe::attestation::{InMemoryReplayGuard, QuorumVerifierError};
#[cfg(feature = "fhegg-settlement")]
use fhegg_verifier_registry::FheggVerifierRegistry;
#[cfg(feature = "fhegg-settlement")]
use std::cell::RefCell;

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CellId, EmbeddedExecutor, field_from_u64,
};
use dregg_cell::{CellMode, FactoryCreationParams};

use dregg_intent::verified_settle::VerifiedLedger;

use starbridge_sealed_auction::CellId as AuctionCellId;
use starbridge_sealed_auction::{
    AUCTION_FACTORY_VK, AssetId, Auction, AuctionError, Bid, COMMIT_BASE, COMMIT_CAPACITY,
    HIGH_BID_SLOT, PHASE_COMMIT, PHASE_SLOT, Phase, SELLER_SLOT, Seal, WINNER_SLOT,
    auction_child_program_vk, auction_factory_descriptor, close_commit_effects, commit_bid_effects,
    commit_slot, fund_ledger, resolve_effects, reveal_bid_effects,
};

use deos_view::{MenuItem, ViewNode};

/// The affordance verb a **seller** fires to open a listing/auction. `arg` is the RESERVE price
/// (the auction does not clear below it). One listing per session (a re-list is refused).
pub const TURN_LIST: &str = "list";

/// The affordance verb a **bidder** fires to place a sealed commit-reveal bid. `arg` is the bid
/// VALUE (the price offered). The `(bidder, value, nonce)` secret is held in the session until
/// SETTLE reveals it; only the [`Bid::seal`] digest is public during the commit phase.
pub const TURN_BID: &str = "bid";

/// Replayable source-bound bid carrying a canonical exact-opening verifier
/// certificate in [`Action::text`]. Available only with `fhegg-settlement`.
#[cfg(feature = "fhegg-settlement")]
pub const TURN_BID_FHEGG: &str = "bid-fhegg-source";

/// Seller-side exact encrypted-supply binding. Fired after ordinary LIST and
/// before any source-bound bid, carrying a listing certificate in `Action::text`.
#[cfg(feature = "fhegg-settlement")]
pub const TURN_BIND_FHEGG_SUPPLY: &str = "bind-fhegg-supply";

/// The first WriteOnce commit-board slot is reserved for the fhEgg listing
/// source whenever one is installed. Source-bound bidder slots begin after it.
pub const FHEGG_LISTING_SOURCE_SLOT: usize = COMMIT_BASE;

/// The affordance verb the listing **seller** fires to close the commit phase, reveal, and clear to
/// the winning sealed bid (the value moves, conservation-checked). `arg` is unused. A different
/// actor is refused before mutation; deterministic no-sale/protocol refusals are preflighted before
/// `COMMIT → REVEAL` lands.
pub const TURN_SETTLE: &str = "settle";

/// Stable host/catalog key for the distinct Dark Bazaar crawl offering.
///
/// [`Offering`] deliberately does not prescribe registry keys; hosts register an
/// offering under a key of their choice.  Exporting this value keeps the web,
/// Telegram, Discord, and native catalog registrations on one canonical route.
pub const DARK_BAZAAR_OFFERING_KEY: &str = "bazaar";

/// The product-grade disclosure every Dark Bazaar crawl surface paints.
///
/// Keep this blunt: the current crawl consumes the real sealed-auction executor
/// and conservation-checked settlement, but it does not yet consume the optional
/// fhEgg proof/FHE work.
pub const DARK_BAZAAR_CRAWL_DISCLOSURE: &str = "CRAWL grade: operator-visible-at-settle / check-level. NOT Tier0 house-blind; NOT a STARK/ZK proof; NOT source-bound.";

/// Stable exact-tie policy inherited from the sealed-auction substrate.
///
/// Reveals live in a `BTreeMap<seal, Bid>` and `winner()` returns the last maximum,
/// so equal-value bids resolve to the lexicographically greatest committed seal.
/// That is opaque but deterministic and replayable; it is not an iteration-order
/// accident.
pub const DARK_BAZAAR_TIE_POLICY: &str =
    "Highest bid wins; exact ties resolve by lexicographically greatest committed bid seal.";

/// The seller / awarding party's in-process auction-ledger handle (the low byte the verified
/// per-asset ledger indexes by). Receives the winner's payment.
const SELLER_HANDLE: AuctionCellId = 1;
/// The award-slot cell's handle — delivers the good (`slot_asset`) to the winner.
const SLOT_HANDLE: AuctionCellId = 2;
/// Bidder handles start here (bidder `i` = `BIDDER_BASE + i`), disjoint from seller/slot.
const BIDDER_BASE: AuctionCellId = 10;

/// The payment asset — what bidders bid in (the money that moves to the seller).
const PAY: AssetId = [0xA1_u8; 32];
/// The good on offer — the task-token / slot the seller's award cell delivers to the winner.
const GOOD: AssetId = [0x60_u8; 32];

/// A placed sealed bid, held in the session so SETTLE can reveal it. Carries the auction-ledger
/// `handle`, the on-ledger commit `slot` the seal was frozen into (a re-bid to this slot is the
/// `WriteOnce` executor refusal — the anti-double-bid tooth), and the [`Bid`] secret.
#[derive(Clone, Copy, Debug)]
struct FheggBidSourceBinding {
    session_digest: [u8; 32],
    binding_digest: [u8; 32],
    message_digest: [u8; 32],
    ciphertext_digest: [u8; 32],
}

#[derive(Clone, Copy, Debug)]
struct FheggListingSourceBinding {
    asset: [u8; 32],
    session_digest: [u8; 32],
    binding_digest: [u8; 32],
    message_digest: [u8; 32],
    ciphertext_digest: [u8; 32],
}

#[derive(Clone, Debug)]
struct PlacedBid {
    /// The identity that placed it (a re-bid by the same identity targets its own `slot`).
    who: DreggIdentity,
    /// The auction-ledger handle (seller/slot-disjoint) — the bidder cell in the settlement ring.
    handle: AuctionCellId,
    /// The on-ledger commit-board slot this bid's seal is frozen into (`WriteOnce`).
    slot: usize,
    /// The sealed bid secret `(bidder, value, nonce)` — revealed at SETTLE.
    bid: Bid,
    /// Exact public source digests included in a source-bound seal. `None` is
    /// the legacy CRAWL bid and is never accepted by the fhEgg settlement gate.
    fhegg_source: Option<FheggBidSourceBinding>,
}

impl PlacedBid {
    fn seal(&self) -> Seal {
        match self.fhegg_source {
            Some(source) => self.bid.seal_with_source(&source.binding_digest),
            None => self.bid.seal(),
        }
    }
}

/// The record of a cleared auction — the conserved post-ledger + the winning bid + the per-asset
/// conservation the SETTLE move produced. Held so [`MarketOffering::verify`] can re-derive it and a
/// driver can read the value that moved.
#[derive(Clone, Debug)]
pub struct Clearing {
    /// The winning sealed bid (the real high bid among the reveals).
    pub winner: Bid,
    /// The verified post-ledger the award ring folded to (conservation-checked).
    pub post: VerifiedLedger,
    /// The payment-asset total before/after the clear — EQUAL (per-asset Σδ = 0).
    pub pay_conserved: (i128, i128),
    /// The good-asset total before/after the clear — EQUAL (per-asset Σδ = 0).
    pub good_conserved: (i128, i128),
}

impl Clearing {
    /// The winning price (what the winner pays the seller in the payment asset).
    pub fn price(&self) -> i128 {
        self.winner.value
    }

    /// Whether every touched asset's total supply was preserved across the clear (Σδ = 0).
    pub fn conserved(&self) -> bool {
        self.pay_conserved.0 == self.pay_conserved.1
            && self.good_conserved.0 == self.good_conserved.1
    }
}

/// A side-effect-free settlement dry run. The auction mirror and value ledger
/// are advanced only on these private copies, so every policy refusal can be
/// returned before the first executor turn mutates the live session.
struct SettlementPlan {
    auction: Auction,
    clearing: Clearing,
}

/// **A live market/auction session over the REAL sealed-auction substrate.** Owns the embedded
/// verified executor + the born auction cell (the listing's on-ledger handle, carrying the auction
/// policy for life), the in-process [`Auction`] commit/reveal/settle mirror (the executable witness
/// of the sealed-bid crypto — whose `settle` clears through the verified per-asset ring), the placed
/// sealed bids, the reserve price, and the accumulated [`TurnReceipt`] chain (the birth + each
/// commit + the atomic close/reveals/resolve settlement).
pub struct MarketSession {
    /// The agent driving the market (the auction cell's owner; signs every turn).
    cclerk: AppCipherclerk,
    /// The real embedded verified executor — the sole referee of every LIST/BID/SETTLE turn.
    executor: EmbeddedExecutor,
    /// The born auction cell (`None` until LIST births it). The listing's on-ledger handle; carries
    /// the `WriteOnce` commit board + `StrictMonotonic(PHASE)` lifecycle FOR LIFE.
    auction_cell: Option<CellId>,
    /// The in-process commit/reveal/settle state machine mirroring the on-ledger cell — the
    /// consumed substrate's executable witness of the sealed-bid protocol + the conserved settle.
    auction: Option<Auction>,
    /// The reserve price — the auction does NOT clear below it (a below-reserve high bid is refused).
    reserve: i128,
    /// The seller's identity (bound at LIST; the awarding party).
    seller: Option<DreggIdentity>,
    /// The placed sealed bids, in commit order (each frozen into its own `WriteOnce` slot).
    bids: Vec<PlacedBid>,
    /// Exact seller ask + concrete asset frozen into the reserved listing
    /// source slot. Required by fhEgg settlement; absent on the legacy crawl.
    fhegg_listing_source: Option<FheggListingSourceBinding>,
    /// A monotone nonce counter — each sealed bid gets a fresh blinding nonce.
    next_nonce: u64,
    /// The committed receipt chain (birth + commits + atomic settlement).
    receipts: Vec<dregg_app_framework::TurnReceipt>,
    /// The cleared auction (`Some` once SETTLE clears to a winner) — the conserved value move.
    clearing: Option<Clearing>,
    /// The deterministic session seed (a re-derivation of the listing under this seed reproduces it).
    seed: u64,
}

impl MarketSession {
    /// Whether the market has been listed (the auction cell is born).
    pub fn is_listed(&self) -> bool {
        self.auction_cell.is_some()
    }

    /// The current auction phase (`None` until listed).
    pub fn phase(&self) -> Option<Phase> {
        self.auction.as_ref().map(|a| a.phase)
    }

    /// Whether the auction has settled (cleared to a winner).
    pub fn is_settled(&self) -> bool {
        self.clearing.is_some()
    }

    /// The number of committed sealed bids so far.
    pub fn bid_count(&self) -> usize {
        self.bids.len()
    }

    /// The number of real verified turns committed (birth + commits + atomic settlement).
    pub fn receipts_len(&self) -> usize {
        self.receipts.len()
    }

    /// The clearing record (`Some` once settled) — the winner + the conserved post-ledger.
    pub fn clearing(&self) -> Option<&Clearing> {
        self.clearing.as_ref()
    }

    /// The reserve price this listing will not clear below.
    pub fn reserve(&self) -> i128 {
        self.reserve
    }

    /// Read the born auction cell's live `PHASE` register off the executor ledger (the on-ledger
    /// phase, `None` if unlisted). The on-ledger mirror of [`Self::phase`].
    pub fn onledger_phase(&self) -> Option<u64> {
        let cell = self.auction_cell?;
        let state = self.executor.cell_state(cell)?;
        Some(field_to_u64(&state.fields[PHASE_SLOT]))
    }

    /// Assign (or look up) the bidder handle + on-ledger slot for `who`. Returns
    /// `(handle, slot, already_placed)` — a bidder that has already bid keeps its slot (a re-bid to
    /// it is the `WriteOnce` refusal).
    fn bidder_slot(&self, who: &DreggIdentity) -> (AuctionCellId, usize, bool) {
        for pb in &self.bids {
            if &pb.who == who {
                return (pb.handle, pb.slot, true);
            }
        }
        let bidder_idx = self.bids.len();
        let slot_idx = bidder_idx + usize::from(self.fhegg_listing_source.is_some());
        (
            BIDDER_BASE + bidder_idx as AuctionCellId,
            commit_slot(slot_idx),
            false,
        )
    }

    fn fhegg_listing_source_seal_for(&self, source: &FheggListingSourceBinding) -> Option<Seal> {
        let seller = self.seller.as_ref()?;
        let mut hasher =
            blake3::Hasher::new_derive_key("dreggnet-market/fhegg/source-bound-listing/v1");
        hasher.update(&self.seed.to_be_bytes());
        hasher.update(&self.reserve.to_be_bytes());
        hasher.update(&(seller.0.len() as u64).to_be_bytes());
        hasher.update(seller.0.as_bytes());
        hasher.update(&source.asset);
        hasher.update(&1u16.to_be_bytes());
        hasher.update(&source.session_digest);
        hasher.update(&source.binding_digest);
        hasher.update(&source.message_digest);
        hasher.update(&source.ciphertext_digest);
        Some(*hasher.finalize().as_bytes())
    }

    fn fhegg_listing_source_seal(&self) -> Option<Seal> {
        self.fhegg_listing_source
            .as_ref()
            .and_then(|source| self.fhegg_listing_source_seal_for(source))
    }

    /// Build a freshly-funded settlement ledger from the recorded sealed bids: each bidder funded
    /// with its bid value in `PAY` (so the winner can really pay), the award slot funded in `GOOD`,
    /// seller/slot live. The conserved award ring folds against THIS ledger.
    fn fund_settlement(&self) -> VerifiedLedger {
        let good_supply: i128 = self
            .bids
            .iter()
            .map(|b| b.bid.value.max(0))
            .sum::<i128>()
            .max(1);
        let mut rows: Vec<(AuctionCellId, AssetId, i128)> = Vec::new();
        for pb in &self.bids {
            rows.push((pb.handle, PAY, pb.bid.value));
            rows.push((pb.handle, GOOD, 0));
        }
        rows.push((SELLER_HANDLE, PAY, 0));
        rows.push((SELLER_HANDLE, GOOD, 0));
        rows.push((SLOT_HANDLE, GOOD, good_supply));
        rows.push((SLOT_HANDLE, PAY, 0));
        fund_ledger(&rows)
    }
}

/// **The market offering** — a stateless factory over the sealed-bid auction. Each
/// [`open`](Offering::open) deploys a fresh [`MarketSession`] (its own embedded executor + the
/// deployed auction factory); each session hosts ONE listing driven LIST → BID* → SETTLE.
pub struct MarketOffering {
    /// Run-credits a BID's confined pricing overlay costs (`0` → free tier). The substrate turns are
    /// always free + verifiable; this only prices an optional intelligence overlay a frontend runs.
    bid_credits: u64,
}

impl MarketOffering {
    /// The free-tier market (no credit debited per action; the substrate turns are free).
    pub fn new() -> Self {
        MarketOffering { bid_credits: 0 }
    }

    /// A paid-tier market: each BID costs `credits` run-credits (a frontend debits them; the core
    /// only names the cost — the substrate turn itself is always free + verifiable).
    pub fn paid_bids(credits: u64) -> Self {
        MarketOffering {
            bid_credits: credits,
        }
    }

    /// LIST — a seller opens a listing: birth a REAL auction cell through the verified executor and
    /// bind the auction genesis (seller + COMMIT phase). The Landed receipt is the birth turn.
    fn do_list(&self, s: &mut MarketSession, input: &Action, actor: DreggIdentity) -> Outcome {
        if s.is_listed() {
            return Outcome::Refused(
                "this market is already listed (one listing per session)".into(),
            );
        }
        let reserve = input.arg.max(0) as i128;

        // Deploy the auction factory into the embedded executor and birth the auction cell — a real
        // `CreateCellFromFactory` turn refereed by the verified executor. The born cell carries the
        // auction policy (WriteOnce board + StrictMonotonic phase) FOR LIFE.
        s.executor.deploy_factory(auction_factory_descriptor());
        let owner = s.cclerk.public_key().0;
        // A deterministic token so the listing's cell id re-derives under the seed (replay identity).
        let token: [u8; 32] =
            *blake3::hash(format!("dreggnet-market listing seed={}", s.seed).as_bytes()).as_bytes();
        let params = FactoryCreationParams {
            mode: CellMode::Sovereign,
            program_vk: Some(auction_child_program_vk()),
            initial_fields: vec![],
            initial_caps: vec![],
            owner_pubkey: owner,
        };
        // Fund the agent cell so the birth's creation budget is covered.
        s.executor.with_ledger_mut(|ledger| {
            if let Some(agent) = ledger.get_mut(&s.cclerk.cell_id()) {
                agent.state.set_balance(1_000_000_000);
            }
        });
        let birth = s
            .cclerk
            .create_from_factory(AUCTION_FACTORY_VK, owner, token, params);
        let receipt = match s.executor.submit_turn(&birth) {
            Ok(r) => r,
            Err(e) => {
                return Outcome::Refused(format!("the listing cell failed to come alive: {e}"));
            }
        };
        let born = CellId::derive_raw(&owner, &token);
        // Grant the driving agent an owner cap on the born cell + bind the SELLER register (genesis).
        s.executor.with_ledger_mut(|ledger| {
            if let Some(agent) = ledger.get_mut(&s.cclerk.cell_id()) {
                agent.capabilities.grant(born, AuthRequired::Signature);
            }
            if let Some(cell) = ledger.get_mut(&born) {
                cell.state
                    .set_field(SELLER_SLOT, field_from_u64(SELLER_HANDLE as u64));
                // PHASE starts at 0 == COMMIT (born fields are zero) — the listing opens in COMMIT.
            }
        });

        s.auction_cell = Some(born);
        s.auction = Some(Auction::new(SELLER_HANDLE, SLOT_HANDLE, PAY, GOOD));
        s.reserve = reserve;
        s.seller = Some(actor);
        s.receipts.push(receipt.clone());
        Outcome::Landed {
            receipt,
            ended: false,
        }
    }

    /// BID — a bidder places a sealed commit-reveal bid. A re-bid by the same identity targets its
    /// own committed slot → a REAL `WriteOnce` executor refusal (the anti-double-bid tooth); a bid
    /// after the commit phase closes is refused by the auction's own phase gate (anti-ghost).
    fn do_bid(&self, s: &mut MarketSession, input: &Action, actor: DreggIdentity) -> Outcome {
        self.do_bid_with_source(s, input, actor, None)
    }

    fn do_bid_with_source(
        &self,
        s: &mut MarketSession,
        input: &Action,
        actor: DreggIdentity,
        fhegg_source: Option<FheggBidSourceBinding>,
    ) -> Outcome {
        let Some(cell) = s.auction_cell else {
            return Outcome::Refused("nothing is listed yet — LIST first".into());
        };
        if s.is_settled() {
            return Outcome::Refused("the auction has already settled".into());
        }
        // The commit-phase gate (the consumed substrate's own refusal): no bid after the commit
        // phase closes. Nothing is submitted on a miss (anti-ghost).
        let phase = s
            .auction
            .as_ref()
            .map(|a| a.phase)
            .unwrap_or(Phase::Settled);
        if phase != Phase::Commit {
            return Outcome::Refused("the commit phase is closed — no more sealed bids".into());
        }
        if input.arg < 0 {
            return Outcome::Refused("a bid value must be non-negative".into());
        }
        let value = input.arg as i128;

        let (handle, slot, already) = s.bidder_slot(&actor);

        if already {
            // THE ANTI-DOUBLE-BID TOOTH — a bidder overwriting its own committed sealed bid. We
            // submit the overwrite turn to the bidder's frozen commit slot; the executor's
            // `WriteOnce(commit slot)` REFUSES it. Nothing commits (anti-ghost).
            let switched = Bid::new(handle, value, s.next_nonce);
            let switched_seal = match fhegg_source {
                Some(source) => switched.seal_with_source(&source.binding_digest),
                None => switched.seal(),
            };
            let action = s.cclerk.make_action(
                cell,
                "commit_bid",
                commit_bid_effects(cell, slot, &switched_seal),
            );
            return match s.executor.submit_action(&s.cclerk, action) {
                Ok(_) => Outcome::Refused(
                    "a double-bid unexpectedly committed (the WriteOnce board should have refused it)".into(),
                ),
                Err(e) => Outcome::Refused(format!("double-bid refused: {e}")),
            };
        }

        // A fresh sealed bid — a real verified commit turn onto the WriteOnce board.
        let nonce = s.next_nonce;
        s.next_nonce += 1;
        let bid = Bid::new(handle, value, nonce);
        let seal = match fhegg_source {
            Some(source) => bid.seal_with_source(&source.binding_digest),
            None => bid.seal(),
        };
        let action =
            s.cclerk
                .make_action(cell, "commit_bid", commit_bid_effects(cell, slot, &seal));
        let receipt = match s.executor.submit_action(&s.cclerk, action) {
            Ok(r) => r,
            Err(e) => return Outcome::Refused(format!("the sealed commit was refused: {e}")),
        };
        // Mirror into the in-process auction (the executable sealed-bid witness).
        if let Some(a) = s.auction.as_mut() {
            if let Err(e) = a.commit(seal) {
                return Outcome::Refused(format!("commit refused by the auction protocol: {e}"));
            }
        }
        s.bids.push(PlacedBid {
            who: actor,
            handle,
            slot,
            bid,
            fhegg_source,
        });
        s.receipts.push(receipt.clone());
        Outcome::Landed {
            receipt,
            ended: false,
        }
    }

    /// SETTLE — the auctioneer closes the commit phase, reveals every sealed bid, and clears to the
    /// winning bid. The value moves through the VERIFIED per-asset ring settlement (conserved). A
    /// below-reserve high bid or a no-valid-bid auction does NOT settle (no value moves, no resolve).
    ///
    /// The public action path authenticates the listing seller before calling this method. The
    /// private clearing paths call it only after their stronger proof/receipt authorization gates.
    fn do_settle(&self, s: &mut MarketSession) -> Outcome {
        let Some(cell) = s.auction_cell else {
            return Outcome::Refused("nothing is listed yet — LIST first".into());
        };

        // Resolve every deterministic refusal on private state before COMMIT→REVEAL lands on the
        // executor. In particular, reserve failure must not close bidding, append receipts, or
        // desynchronise the in-process phase from the on-ledger phase.
        let SettlementPlan { auction, clearing } = match self.preflight_settlement(s) {
            Ok(plan) => plan,
            Err(why) => return Outcome::Refused(why),
        };
        let winner = clearing.winner;

        // Build the full lifecycle as one executor turn. The call forest is journaled atomically:
        // close + every reveal + resolve either all commit or all roll back.
        let mut actions = Vec::with_capacity(s.bids.len() + 2);
        actions.push(
            s.cclerk
                .make_action(cell, "close_commit", close_commit_effects(cell)),
        );
        for placed in &s.bids {
            let b = placed.bid;
            actions.push(s.cclerk.make_action(
                cell,
                "reveal_bid",
                reveal_bid_effects(cell, field_from_u64(b.bidder as u64), b.value.max(0) as u64),
            ));
        }
        actions.push(s.cclerk.make_action(
            cell,
            "resolve",
            resolve_effects(
                cell,
                field_from_u64(winner.bidder as u64),
                winner.value.max(0) as u64,
            ),
        ));
        let turn = s.cclerk.make_turn_with_actions(actions);
        let receipt = match s.executor.submit_turn(&turn) {
            Ok(r) => r,
            Err(e) => {
                return Outcome::Refused(format!("the atomic settlement turn was refused: {e}"));
            }
        };
        s.receipts.push(receipt.clone());
        s.auction = Some(auction);
        s.clearing = Some(clearing);
        Outcome::Landed {
            receipt,
            ended: true,
        }
    }

    /// Exercise every deterministic reveal/settlement gate on private copies.
    /// An error from here is therefore a strictly read-only refusal.
    fn preflight_settlement(&self, s: &MarketSession) -> Result<SettlementPlan, String> {
        if s.is_settled() {
            return Err("the auction has already settled".into());
        }
        if s.bids.is_empty() {
            return Err("no sealed bids were placed — nothing to settle".into());
        }
        if s.phase() != Some(Phase::Commit) {
            return Err("the auction is not in the commit phase — settlement cannot start".into());
        }
        let cell = s
            .auction_cell
            .ok_or_else(|| "the listed auction cell is missing".to_string())?;
        let state = s
            .executor
            .cell_state(cell)
            .ok_or_else(|| "the listed auction cell is missing from the ledger".to_string())?;
        if state.fields[PHASE_SLOT] != field_from_u64(PHASE_COMMIT) {
            return Err(
                "the on-ledger auction is not in the commit phase — settlement cannot start".into(),
            );
        }
        if state.fields[SELLER_SLOT] != field_from_u64(SELLER_HANDLE as u64) {
            return Err("the on-ledger seller binding differs from the live auction".into());
        }
        if state.fields[WINNER_SLOT] != field_from_u64(0)
            || state.fields[HIGH_BID_SLOT] != field_from_u64(0)
        {
            return Err("the on-ledger result registers are already occupied".into());
        }

        // Settlement must consume exactly the board represented by this session: no altered
        // recorded seal and no untracked/ghost commitment can influence a different book. This
        // also catches a stale or spliced replay image before submitting the atomic turn (and thus
        // before even the executor's refusal nonce/fee path can move).
        let listing_source = s.fhegg_listing_source_seal();
        for slot in COMMIT_BASE..COMMIT_BASE + COMMIT_CAPACITY {
            let expected = if slot == FHEGG_LISTING_SOURCE_SLOT {
                listing_source
            } else {
                None
            }
            .or_else(|| {
                s.bids
                    .iter()
                    .find(|placed| placed.slot == slot)
                    .map(PlacedBid::seal)
            })
            .unwrap_or([0; 32]);
            if state.fields[slot] != expected {
                return Err(format!(
                    "the on-ledger commit board differs from the recorded sealed book at slot {slot}"
                ));
            }
        }

        let mut auction = s
            .auction
            .clone()
            .ok_or_else(|| "the listed auction mirror is missing".to_string())?;
        auction.seal_commit_phase();
        for placed in &s.bids {
            let revealed = match placed.fhegg_source {
                Some(source) => auction.reveal_source_bound(placed.bid, &source.binding_digest),
                None => auction.reveal(placed.bid),
            };
            if let Err(error) = revealed {
                return Err(format!(
                    "a reveal was refused by the auction protocol: {error}"
                ));
            }
        }

        let ledger = s.fund_settlement();
        let pay_before = ledger.total_asset(&PAY);
        let good_before = ledger.total_asset(&GOOD);
        let (post, winner) = match auction.settle(&ledger) {
            Ok(settlement) => settlement,
            Err(AuctionError::NoWinner) => {
                return Err("no valid revealed bid — the auction does not settle".into());
            }
            Err(error) => {
                return Err(format!(
                    "settlement rejected by the verified executor: {error}"
                ));
            }
        };

        if winner.value < s.reserve {
            return Err(format!(
                "the high sealed bid {} is below the reserve {} — no sale, nothing settles",
                winner.value, s.reserve
            ));
        }

        let pay_after = post.total_asset(&PAY);
        let good_after = post.total_asset(&GOOD);
        Ok(SettlementPlan {
            auction,
            clearing: Clearing {
                winner,
                post,
                pay_conserved: (pay_before, pay_after),
                good_conserved: (good_before, good_after),
            },
        })
    }
}

impl Default for MarketOffering {
    fn default() -> Self {
        MarketOffering::new()
    }
}

impl Offering for MarketOffering {
    type Session = MarketSession;

    fn open(&self, cfg: SessionConfig) -> Result<MarketSession, OfferingError> {
        let seed = cfg.seed.unwrap_or(1);
        // A deterministic federation id from the seed (stable listing identity per session).
        let fed = *blake3::hash(format!("dreggnet-market fed seed={seed}").as_bytes()).as_bytes();
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), fed);
        let executor = EmbeddedExecutor::new(&cclerk, "default");
        Ok(MarketSession {
            cclerk,
            executor,
            auction_cell: None,
            auction: None,
            reserve: 0,
            seller: None,
            bids: Vec::new(),
            fhegg_listing_source: None,
            next_nonce: 1,
            receipts: Vec::new(),
            clearing: None,
            seed,
        })
    }

    fn actions(&self, session: &MarketSession) -> Vec<Action> {
        if !session.is_listed() {
            return vec![Action::new(
                "List an item (open a sealed auction)",
                TURN_LIST,
                0,
                true,
            )];
        }
        if session.is_settled() {
            return Vec::new();
        }
        let in_commit = session.phase() == Some(Phase::Commit);
        vec![
            Action::new("Place a sealed bid", TURN_BID, 0, in_commit),
            Action::new(
                "Seller settle — reveal and clear to the winning bid",
                TURN_SETTLE,
                0,
                in_commit && !session.bids.is_empty(),
            ),
        ]
    }

    fn advance(&self, session: &mut MarketSession, input: Action, actor: DreggIdentity) -> Outcome {
        match input.turn.as_str() {
            TURN_LIST => self.do_list(session, &input, actor),
            TURN_BID => self.do_bid(session, &input, actor),
            TURN_SETTLE => match session.seller.as_ref() {
                Some(seller) if seller != &actor => {
                    Outcome::Refused("only the listing seller may settle this auction".to_string())
                }
                _ => self.do_settle(session),
            },
            other => Outcome::Refused(format!("unknown market affordance: {other}")),
        }
    }

    /// Re-verify the cleared chain: re-derive the settlement from the recorded sealed bids and
    /// confirm (a) the winner is the real high bid, (b) the value move conserves every asset
    /// (per-asset Σδ = 0), and (c) the on-ledger WINNER / HIGH_BID registers match the real winner.
    /// Before settlement, verify confirms the seller binding and the exact sealed book (including
    /// the absence of untracked commitments) match the on-ledger image.
    fn verify(&self, session: &MarketSession) -> VerifyReport {
        let turns = session.receipts_len();
        let Some(cell) = session.auction_cell else {
            return VerifyReport::broken(turns, "nothing listed — no chain to verify");
        };

        // (a) The seller binding and the entire WriteOnce board must match this exact session book.
        let Some(state) = session.executor.cell_state(cell) else {
            return VerifyReport::broken(turns, "the listing cell is not in the ledger");
        };
        let expected_phase = match session.phase() {
            Some(Phase::Commit) => 0,
            Some(Phase::Reveal) => 1,
            Some(Phase::Settled) => 2,
            None => return VerifyReport::broken(turns, "the listed auction mirror is missing"),
        };
        if field_to_u64(&state.fields[PHASE_SLOT]) != expected_phase {
            return VerifyReport::broken(
                turns,
                "the in-process and on-ledger auction phases differ",
            );
        }
        if state.fields[SELLER_SLOT] != field_from_u64(SELLER_HANDLE as u64) {
            return VerifyReport::broken(
                turns,
                "the on-ledger seller binding differs from the live auction",
            );
        }
        let listing_source = session.fhegg_listing_source_seal();
        for slot in COMMIT_BASE..COMMIT_BASE + COMMIT_CAPACITY {
            let expected = if slot == FHEGG_LISTING_SOURCE_SLOT {
                listing_source
            } else {
                None
            }
            .or_else(|| {
                session
                    .bids
                    .iter()
                    .find(|placed| placed.slot == slot)
                    .map(PlacedBid::seal)
            })
            .unwrap_or([0; 32]);
            if state.fields[slot] != expected {
                return VerifyReport::broken(
                    turns,
                    format!(
                        "the on-ledger commit board differs from the recorded sealed book at slot {slot}"
                    ),
                );
            }
        }

        if session.clearing.is_none()
            && (state.fields[WINNER_SLOT] != field_from_u64(0)
                || state.fields[HIGH_BID_SLOT] != field_from_u64(0))
        {
            return VerifyReport::broken(
                turns,
                "an unsettled auction has occupied on-ledger result registers",
            );
        }

        let Some(clearing) = &session.clearing else {
            // Not yet cleared — the committed board is consistent; that is all there is to check.
            return VerifyReport::ok(turns);
        };

        // (b) Re-derive the clear from scratch through the same verified settlement path.
        let mut replay = Auction::new(SELLER_HANDLE, SLOT_HANDLE, PAY, GOOD);
        for pb in &session.bids {
            if replay.commit(pb.seal()).is_err() {
                return VerifyReport::broken(turns, "a recorded seal failed re-commit");
            }
        }
        replay.seal_commit_phase();
        for pb in &session.bids {
            let revealed = match pb.fhegg_source {
                Some(source) => replay.reveal_source_bound(pb.bid, &source.binding_digest),
                None => replay.reveal(pb.bid),
            };
            if revealed.is_err() {
                return VerifyReport::broken(
                    turns,
                    "a recorded bid failed re-reveal (not committed)",
                );
            }
        }
        let ledger = session.fund_settlement();
        let (post2, winner2) = match replay.settle(&ledger) {
            Ok(pw) => pw,
            Err(e) => return VerifyReport::broken(turns, format!("re-settlement failed: {e}")),
        };
        // The winner must be the real high bid, and the re-derived post-ledger must match.
        if winner2 != clearing.winner {
            return VerifyReport::broken(
                turns,
                "the re-derived winner differs from the recorded winner",
            );
        }
        let real_high = session
            .bids
            .iter()
            .map(|b| b.bid.value)
            .max()
            .unwrap_or(i128::MIN);
        if clearing.winner.value != real_high {
            return VerifyReport::broken(turns, "the recorded winner is not the real high bid");
        }
        if post2 != clearing.post {
            return VerifyReport::broken(
                turns,
                "the re-derived post-ledger differs (settlement not reproducible)",
            );
        }
        // (c) Conservation must hold (per-asset Σδ = 0).
        if !clearing.conserved() {
            return VerifyReport::broken(turns, "the clear did not conserve every asset (Σδ ≠ 0)");
        }
        // (d) The on-ledger result registers announce the real winner.
        let onchain_winner = field_to_u64(&state.fields[WINNER_SLOT]);
        let onchain_high = field_to_u64(&state.fields[HIGH_BID_SLOT]);
        if onchain_winner != clearing.winner.bidder as u64 {
            return VerifyReport::broken(
                turns,
                "the on-ledger WINNER register does not match the real winner",
            );
        }
        if onchain_high != clearing.winner.value.max(0) as u64 {
            return VerifyReport::broken(
                turns,
                "the on-ledger HIGH_BID register does not match the winning bid",
            );
        }
        VerifyReport::ok(turns)
    }

    fn render(&self, session: &MarketSession) -> Surface {
        let mut children: Vec<ViewNode> = Vec::new();

        if !session.is_listed() {
            children.push(ViewNode::Text(
                "No listing yet. A seller opens a sealed auction.".into(),
            ));
        } else {
            let phase = match session.phase() {
                Some(Phase::Commit) => "COMMIT (sealed bids accepted)",
                Some(Phase::Reveal) => "REVEAL",
                Some(Phase::Settled) => "SETTLED",
                None => "—",
            };
            children.push(ViewNode::Section {
                title: "Listing".into(),
                tag: "muted".into(),
                children: vec![ViewNode::Text(format!(
                    "reserve {} · phase {} · sealed bids {}",
                    session.reserve,
                    phase,
                    session.bid_count()
                ))],
            });
            if let Some(c) = &session.clearing {
                children.push(ViewNode::Section {
                    title: "Cleared".into(),
                    tag: "genuine".into(),
                    children: vec![ViewNode::Text(format!(
                        "winner bidder#{} at price {} · value moved conservation-checked (Σδ=0: {})",
                        c.winner.bidder, c.winner.value, c.conserved()
                    ))],
                });
            }
        }

        children.push(ViewNode::Section {
            title: "Verified turns".into(),
            tag: "genuine".into(),
            children: vec![ViewNode::Text(session.receipts_len().to_string())],
        });

        let items: Vec<MenuItem> = self
            .actions(session)
            .into_iter()
            .map(|a| MenuItem {
                label: a.label,
                turn: a.turn,
                arg: a.arg,
                enabled: a.enabled,
            })
            .collect();
        if !items.is_empty() {
            children.push(ViewNode::Section {
                title: "Market actions".into(),
                tag: "accent".into(),
                children: vec![ViewNode::Menu { items }],
            });
        }

        Surface(ViewNode::Section {
            title: "DreggNet Market — sealed-bid auction".into(),
            tag: "accent".into(),
            children,
        })
    }

    fn price(&self, input: &Action) -> RunCost {
        // The substrate turns are always free + verifiable; only a BID carries the optional
        // confined-pricing overlay a frontend runs (the free tier by default).
        if input.turn == TURN_BID {
            RunCost::credits(self.bid_credits)
        } else {
            RunCost::free()
        }
    }
}

/// A distinct, catalog-key-capable **Dark Bazaar CRAWL** offering.
///
/// This first playable whole-system slice deliberately delegates the real
/// [`MarketOffering`] executor, commit/reveal protocol, verified settlement, and
/// replay verifier.  It is a separate offering type and surface so a host can
/// register it under [`DARK_BAZAAR_OFFERING_KEY`] without pretending the ordinary
/// market has acquired privacy/proof properties it does not have.
///
/// # Honest grade
///
/// Bids are sealed during commit and become visible to the operator at SETTLE.
/// Verification is the existing check-level replay plus conservation gate. This
/// crawl is **not** Tier0 house-blind, does **not** carry a STARK/ZK proof, and is
/// **not** source-bound. The optional `certified-clearing` feature remains wholly
/// outside this default offering.
pub struct DarkBazaarOffering {
    market: MarketOffering,
    /// Exact-opening source verifier selected by the host. Its signatures make
    /// the operator-visible reencryption check replayable; they are not ZK.
    #[cfg(feature = "fhegg-settlement")]
    fhegg_source_verifier: Option<[u8; 32]>,
    /// Relying-party policy, selected by the host rather than the uploaded
    /// receipt. `None` keeps the default crawl unable to accept fhEgg bundles.
    #[cfg(feature = "fhegg-settlement")]
    fhegg_verifier: Option<FheggVerifierRegistry>,
    /// Live-process replay floor for the hosted operation. An OfferingHost with
    /// a binary-operation-capable resume store reconstructs this floor on boot
    /// by re-verifying/replaying its durable operation journal; callers that
    /// bypass that host seam retain process-local semantics only.
    #[cfg(feature = "fhegg-settlement")]
    fhegg_replay: RefCell<InMemoryReplayGuard>,
}

impl DarkBazaarOffering {
    /// Canonical host/catalog key for this offering.
    pub const KEY: &'static str = DARK_BAZAAR_OFFERING_KEY;

    /// Open the free-tier Dark Bazaar crawl.
    pub fn new() -> Self {
        Self {
            market: MarketOffering::new(),
            #[cfg(feature = "fhegg-settlement")]
            fhegg_source_verifier: None,
            #[cfg(feature = "fhegg-settlement")]
            fhegg_verifier: None,
            #[cfg(feature = "fhegg-settlement")]
            fhegg_replay: RefCell::new(InMemoryReplayGuard::default()),
        }
    }

    /// A paid-tier crawl whose BID affordance costs `credits` run-credits.
    pub fn paid_bids(credits: u64) -> Self {
        Self {
            market: MarketOffering::paid_bids(credits),
            #[cfg(feature = "fhegg-settlement")]
            fhegg_source_verifier: None,
            #[cfg(feature = "fhegg-settlement")]
            fhegg_verifier: None,
            #[cfg(feature = "fhegg-settlement")]
            fhegg_replay: RefCell::new(InMemoryReplayGuard::default()),
        }
    }

    /// Build a Bazaar whose hosted fhEgg operation accepts only an exact,
    /// deployment-selected Ed25519 quorum roster. Uploaded bytes never select
    /// or weaken this policy.
    #[cfg(feature = "fhegg-settlement")]
    pub fn with_fhegg_quorum(
        ordered_public_keys: Vec<[u8; 32]>,
        threshold: usize,
    ) -> Result<Self, QuorumVerifierError> {
        Ok(Self::with_fhegg_verifier_registry(
            FheggVerifierRegistry::authenticated_quorum(ordered_public_keys, threshold)?,
        ))
    }

    /// Install one already reconstructed relying-party verifier registry. The
    /// registry's constructors are the policy boundary; uploaded operation
    /// bytes cannot replace this value.
    #[cfg(feature = "fhegg-settlement")]
    pub fn with_fhegg_verifier_registry(registry: FheggVerifierRegistry) -> Self {
        Self {
            market: MarketOffering::new(),
            fhegg_source_verifier: None,
            fhegg_verifier: Some(registry),
            fhegg_replay: RefCell::new(InMemoryReplayGuard::default()),
        }
    }

    /// Reconstruct and install the complete private-BFV receipt verifier from
    /// pinned public deployment configuration. Any public-preimage or verifier-
    /// id mismatch fails before the hosted operation is advertised.
    #[cfg(all(feature = "fhegg-settlement", feature = "private-attested-clearing"))]
    pub fn with_private_bfv_attested_registry(
        config: fhegg_verifier_registry::PrivateBfvHostedVerifierConfig,
    ) -> Result<Self, fhegg_verifier_registry::FheggVerifierRegistryError> {
        Ok(Self::with_fhegg_verifier_registry(config.install()?))
    }

    /// The canonical key a heterogeneous [`dreggnet_offerings::OfferingHost`] can
    /// register this offering under.
    pub const fn key(&self) -> &'static str {
        Self::KEY
    }
}

impl Default for DarkBazaarOffering {
    fn default() -> Self {
        Self::new()
    }
}

/// Session wrapper keeping the Dark Bazaar route/type distinct while retaining
/// the real market's executor-backed state.
pub struct DarkBazaarSession {
    market: MarketSession,
    /// The proof-verified semantic settlement retained by the live private
    /// market. A fresh local receipt envelope may be rejoined to this claim
    /// after restart, but can never redefine it.
    #[cfg(feature = "private-clearing")]
    verified_private_clearing_receipt: Option<private_clearing::PrivateClearingReceipt>,
}

impl DarkBazaarSession {
    /// Read the underlying real market session for low-level inspection.
    pub fn market(&self) -> &MarketSession {
        &self.market
    }

    /// Whether a real factory-born listing exists.
    pub fn is_listed(&self) -> bool {
        self.market.is_listed()
    }

    /// Whether the verified settlement has landed.
    pub fn is_settled(&self) -> bool {
        self.market.is_settled()
    }

    /// Number of sealed bids committed through the real executor.
    pub fn bid_count(&self) -> usize {
        self.market.bid_count()
    }

    /// The real conservation-checked clearing, once settled.
    pub fn clearing(&self) -> Option<&Clearing> {
        self.market.clearing()
    }

    /// The frontend-agnostic identity whose sealed bid won the verified clear.
    pub fn winning_actor(&self) -> Option<&DreggIdentity> {
        self.market.winning_actor()
    }

    /// Atomically cross an existing owned asset to this Bazaar session's verified
    /// winner for the winning amount of `$DREGG`.
    ///
    /// This is the cross-game seam: a caller can hand in an `AssetId` minted by The
    /// Descent (or craft/inventory) in the SAME `TradeWorld`; no remint or synthetic
    /// `GOOD` token is involved. The asset layer re-checks seller ownership, sealed
    /// escrow binds both legs, and provenance is re-verified after the cross.
    pub fn settle_winning_asset(
        &self,
        world: &mut dreggnet_trade::TradeWorld,
        asset: dreggnet_trade::AssetId,
    ) -> Result<asset_backed::AssetBackedClearing, asset_backed::AssetBackedError> {
        self.market.settle_winning_asset(world, asset)
    }
}

impl Offering for DarkBazaarOffering {
    type Session = DarkBazaarSession;

    fn open(&self, cfg: SessionConfig) -> Result<Self::Session, OfferingError> {
        self.market.open(cfg).map(|market| DarkBazaarSession {
            market,
            #[cfg(feature = "private-clearing")]
            verified_private_clearing_receipt: None,
        })
    }

    fn actions(&self, session: &Self::Session) -> Vec<Action> {
        self.market
            .actions(&session.market)
            .into_iter()
            .map(|mut action| {
                action.label = match action.turn.as_str() {
                    TURN_LIST => "Open a Dark Bazaar listing (real auction cell)".into(),
                    TURN_BID => "Place a sealed bid (operator sees it at SETTLE)".into(),
                    TURN_SETTLE => {
                        "Seller SETTLE — reveal to operator and clear check-level".into()
                    }
                    _ => action.label,
                };
                action
            })
            .collect()
    }

    fn advance(&self, session: &mut Self::Session, input: Action, actor: DreggIdentity) -> Outcome {
        #[cfg(feature = "fhegg-settlement")]
        if input.turn == TURN_BID_FHEGG {
            return self.advance_fhegg_source_bound_bid(session, &input, actor);
        }
        #[cfg(feature = "fhegg-settlement")]
        if input.turn == TURN_BIND_FHEGG_SUPPLY {
            return self.advance_fhegg_listing_source(session, &input, actor);
        }
        self.market.advance(&mut session.market, input, actor)
    }

    fn verify(&self, session: &Self::Session) -> VerifyReport {
        let mut report = self.market.verify(&session.market);
        #[cfg(feature = "fhegg-settlement")]
        let grade = if session.market.fhegg_listing_source.is_some()
            && session
                .market
                .bids
                .iter()
                .all(|bid| bid.fhegg_source.is_some())
        {
            "operator-visible exact-source-bound board (not Tier0/house-blind lattice ZK)"
        } else {
            "CRAWL check-level replay (not Tier0/STARK/ZK/source-bound)"
        };
        #[cfg(not(feature = "fhegg-settlement"))]
        let grade = "CRAWL check-level replay (not Tier0/STARK/ZK/source-bound)";
        report.detail = format!("Dark Bazaar {grade}: {}", report.detail);
        report
    }

    fn render(&self, session: &Self::Session) -> Surface {
        let market_surface = self.market.render(&session.market).0;
        let mut children = vec![
            ViewNode::Section {
                title: format!("Offering key: {}", Self::KEY),
                tag: "muted".into(),
                children: vec![
                    ViewNode::Text(DARK_BAZAAR_CRAWL_DISCLOSURE.into()),
                    ViewNode::Text(
                        "Real now: sealed commit/reveal executor turns and conservation-checked value settlement.".into(),
                    ),
                    ViewNode::Text(DARK_BAZAAR_TIE_POLICY.into()),
                ],
            },
        ];
        #[cfg(feature = "fhegg-settlement")]
        if self.fhegg_verifier.is_some() {
            children.push(ViewNode::Section {
                title: "Shielded settlement operation".into(),
                tag: "accent".into(),
                children: vec![
                    ViewNode::Text(fhegg_transport::FHEGG_SETTLEMENT_OPERATION.to_string()),
                    ViewNode::Text(fhegg_transport::FHEGG_SETTLEMENT_DISCLOSURE.to_string()),
                ],
            });
        }
        children.push(market_surface);
        Surface(ViewNode::Section {
            title: "The Dark Bazaar — playable CRAWL".into(),
            tag: "accent".into(),
            children,
        })
    }

    fn binary_operations(&self, _session: &Self::Session) -> Vec<BinaryOperationDescriptor> {
        #[cfg(feature = "fhegg-settlement")]
        if self.fhegg_verifier.is_some() {
            return vec![fhegg_transport::FheggSettlementOperation::descriptor()];
        }
        Vec::new()
    }

    fn binary_operation_replay_material(
        &self,
        _session: &Self::Session,
        name: &str,
        payload: &[u8],
    ) -> Result<Option<BinaryOperationReplayMaterial>, BinaryOperationError> {
        #[cfg(feature = "fhegg-settlement")]
        {
            if name != fhegg_transport::FHEGG_SETTLEMENT_OPERATION {
                return Err(BinaryOperationError::UnknownOperation(name.to_string()));
            }
            if self.fhegg_verifier.is_none() {
                return Err(BinaryOperationError::Refused(
                    "the host has no configured fhEgg computation-integrity policy".to_string(),
                ));
            }
            let canonical = fhegg_transport::FheggSettlementBundle::from_wire_bytes(payload)
                .map_err(|error| BinaryOperationError::Malformed(error.to_string()))?
                .to_wire_bytes();
            if canonical != payload {
                return Err(BinaryOperationError::Malformed(
                    "fhEgg settlement bundle is not canonically encoded".to_string(),
                ));
            }
            return Ok(Some(BinaryOperationReplayMaterial::new(
                canonical,
                fhegg_transport::FHEGG_SETTLEMENT_DISCLOSURE,
            )));
        }
        #[cfg(not(feature = "fhegg-settlement"))]
        {
            let _ = (_session, payload);
            Err(BinaryOperationError::UnknownOperation(name.to_string()))
        }
    }

    fn invoke_binary_operation(
        &self,
        session: &mut Self::Session,
        name: &str,
        payload: &[u8],
        _actor: DreggIdentity,
    ) -> Result<BinaryOperationReceipt, BinaryOperationError> {
        #[cfg(feature = "fhegg-settlement")]
        {
            if name != fhegg_transport::FHEGG_SETTLEMENT_OPERATION {
                return Err(BinaryOperationError::UnknownOperation(name.to_string()));
            }
            let verifier = self.fhegg_verifier.as_ref().ok_or_else(|| {
                BinaryOperationError::Refused(
                    "the host has no configured fhEgg computation-integrity policy".to_string(),
                )
            })?;
            let operation = fhegg_transport::FheggSettlementOperation::from_wire_bytes(payload)
                .map_err(|error| BinaryOperationError::Malformed(error.to_string()))?;
            let mut replay = self.fhegg_replay.borrow_mut();
            let receipt = operation
                .execute(self, session, verifier, &mut *replay)
                .map_err(|error| BinaryOperationError::Refused(error.to_string()))?;
            return Ok(BinaryOperationReceipt {
                operation: name.to_string(),
                receipt_id: receipt.claim_digest,
                public_fields: vec![
                    ("price".to_string(), receipt.price.to_string()),
                    ("volume".to_string(), receipt.volume.to_string()),
                    ("winner".to_string(), receipt.winner.0),
                ],
            });
        }
        #[cfg(not(feature = "fhegg-settlement"))]
        {
            let _ = (session, payload);
            Err(BinaryOperationError::UnknownOperation(name.to_string()))
        }
    }

    fn price(&self, input: &Action) -> RunCost {
        self.market.price(input)
    }
}

/// Read a `u64` from the last 8 big-endian bytes of a field element (the inverse of
/// [`field_from_u64`] for the phase / winner / bid-value registers the auction cell stores).
fn field_to_u64(f: &[u8; 32]) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&f[24..32]);
    u64::from_be_bytes(b)
}

#[cfg(test)]
mod settlement_refusal_tests;

#[cfg(test)]
mod dark_bazaar_tests {
    use super::*;

    fn identity(name: &str) -> DreggIdentity {
        DreggIdentity(name.to_string())
    }

    fn land(
        offering: &DarkBazaarOffering,
        session: &mut DarkBazaarSession,
        turn: &str,
        arg: i64,
        actor: &str,
    ) {
        let outcome =
            offering.advance(session, Action::new(turn, turn, arg, true), identity(actor));
        assert!(outcome.landed(), "{turn} should land, got {outcome:?}");
    }

    #[test]
    fn dark_bazaar_is_distinct_keyed_and_honestly_disclosed() {
        let offering = DarkBazaarOffering::new();
        assert_eq!(offering.key(), "bazaar");
        assert_eq!(DarkBazaarOffering::KEY, DARK_BAZAAR_OFFERING_KEY);

        let session = offering
            .open(SessionConfig::with_seed(710))
            .expect("crawl opens");
        let painted = format!("{:?}", offering.render(&session).view());
        for required in [
            "operator-visible-at-settle / check-level",
            "NOT Tier0 house-blind",
            "NOT a STARK/ZK proof",
            "NOT source-bound",
            "conservation-checked value settlement",
        ] {
            assert!(
                painted.contains(required),
                "surface must disclose {required:?}: {painted}"
            );
        }
        assert!(
            offering
                .actions(&session)
                .iter()
                .any(|a| a.turn == TURN_LIST && a.label.contains("Dark Bazaar"))
        );
    }

    #[test]
    fn dark_bazaar_crawl_lands_real_settlement_and_check_level_verify() {
        let offering = DarkBazaarOffering::new();
        let mut session = offering
            .open(SessionConfig::with_seed(711))
            .expect("crawl opens");

        land(&offering, &mut session, TURN_LIST, 25, "seller");
        land(&offering, &mut session, TURN_BID, 30, "alice");
        land(&offering, &mut session, TURN_BID, 50, "bob");
        land(&offering, &mut session, TURN_BID, 40, "carol");
        land(&offering, &mut session, TURN_SETTLE, 0, "seller");

        let clearing = session.clearing().expect("real settlement landed");
        assert_eq!(clearing.price(), 50);
        assert!(clearing.conserved(), "the real value move conserves");
        assert!(session.is_settled());

        let report = offering.verify(&session);
        assert!(report.verified, "real chain re-verifies: {}", report.detail);
        assert!(report.detail.contains("check-level replay"));
        assert!(report.detail.contains("not Tier0/STARK/ZK/source-bound"));
    }

    #[test]
    fn dark_bazaar_exact_ties_follow_the_deterministic_seal_policy() {
        fn run(seed: u64) -> AuctionCellId {
            let offering = DarkBazaarOffering::new();
            let mut session = offering
                .open(SessionConfig::with_seed(seed))
                .expect("crawl opens");
            land(&offering, &mut session, TURN_LIST, 0, "seller");
            land(&offering, &mut session, TURN_BID, 50, "alice");
            land(&offering, &mut session, TURN_BID, 50, "bob");
            land(&offering, &mut session, TURN_SETTLE, 0, "seller");
            session.clearing().expect("tie settles").winner.bidder
        }

        let expected = [
            Bid::new(BIDDER_BASE, 50, 1),
            Bid::new(BIDDER_BASE + 1, 50, 2),
        ]
        .into_iter()
        .max_by_key(Bid::seal)
        .expect("two tied bids")
        .bidder;
        assert_eq!(run(712), expected);
        assert_eq!(
            run(713),
            expected,
            "tie result is independent of session seed"
        );
    }
}
