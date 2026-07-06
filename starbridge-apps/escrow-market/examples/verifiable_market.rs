//! # The verifiable market — two apps, one clearing.
//!
//! Neither app is a market on its own:
//!
//!   * `sealed-auction` discovers **who wins at what price** without
//!     front-running — bids are committed as hashes before anyone reveals, so no
//!     bidder can peek at another's number, and no bidder can switch after
//!     peeking (the seal binds one bid). But the auction *trusts the auctioneer*
//!     to actually move the money afterwards.
//!
//!   * `escrow-market` moves value **atomically and conservation-respecting**
//!     between two mutually-distrustful parties — the winning payment and the
//!     seller's good both lock into escrow and cross in ONE step (2-of-2), or a
//!     ghosting party is defeated by a one-shot reclaim. But an escrow has no
//!     idea *what the price is* — it enforces terms someone hands it.
//!
//! Compose them and you get a real market: the **sealed auction is the
//! front-run-proof price-discovery organ**, and the **escrow is the atomic,
//! conserved clearing organ**. The auction's discovered `(winner, price)`
//! becomes the escrow's `EscrowTerms` — winner pays `price` of the payment asset
//! iff the seller delivers the good. The seam between them is exactly one value:
//! the clearing price the sealed bids revealed.
//!
//! Run with: `cargo run -p starbridge-escrow-market --example verifiable_market`

use dregg_cell::Cell;
use dregg_types::CellId;

use starbridge_escrow_market::{
    EscrowTerms, Leg, LegRequirement, LegStatus, SealedEscrowMarket, Side,
};
use starbridge_sealed_auction::{Auction, Bid, Phase};

// ── The two assets that cross in the clearing. ──
/// The payment asset (what buyers bid in).
const PAY: [u8; 32] = [0xA1_u8; 32];
/// The good on offer — a single compute slot / task token the seller delivers.
const GOOD: [u8; 32] = [0x60_u8; 32];

/// How much of the good the seller delivers to the winner (one slot).
const GOOD_QTY: i64 = 1;

// ── Auction-side bidder ids (u8 cell handles inside the sealed-auction) mapped
//    to real 32-byte party pubkeys on the escrow side. The bridge between the two
//    apps' altitudes is nothing more than "which pubkey is bidder N". ──
const SELLER_ID: u8 = 1;
const SLOT_ID: u8 = 2;
const ALICE_ID: u8 = 10;
const BOB_ID: u8 = 11;
const CAROL_ID: u8 = 12;

fn pubkey(handle: u8) -> [u8; 32] {
    let mut pk = [0u8; 32];
    pk[0] = handle;
    pk[31] = handle.wrapping_mul(37).wrapping_add(1);
    pk
}

fn party(pk: [u8; 32], asset: [u8; 32]) -> CellId {
    Cell::with_balance(pk, asset, 0).id()
}

fn wallet(pk: [u8; 32], asset: [u8; 32], balance: i64) -> Cell {
    Cell::with_balance(pk, asset, balance)
}

fn main() {
    println!("=== The verifiable market: a sealed bid clears through escrow ===\n");

    // ─────────────────────────────────────────────────────────────────────────
    // ORGAN 1 — sealed-auction: front-run-proof price discovery.
    // ─────────────────────────────────────────────────────────────────────────
    let alice = Bid::new(ALICE_ID, 30, 0xA1A1);
    let bob = Bid::new(BOB_ID, 50, 0xB0B0); // the top bid — should win at 50
    let carol = Bid::new(CAROL_ID, 40, 0xCACA);

    let mut auction = Auction::new(SELLER_ID, SLOT_ID, PAY, GOOD);

    println!("COMMIT phase — each bidder broadcasts only the HASH of its bid:");
    for (name, bid) in [("alice", &alice), ("bob", &bob), ("carol", &carol)] {
        auction
            .commit(bid.seal())
            .expect("bidder commits a sealed bid");
        let s = bid.seal();
        println!(
            "  {name:5} sealed  {:02x}{:02x}{:02x}{:02x}… (value hidden)",
            s[0], s[1], s[2], s[3]
        );
    }

    // Tooth: a reveal before the commit phase closes is refused.
    assert_eq!(auction.phase, Phase::Commit);
    assert!(
        auction.reveal(bob).is_err(),
        "a reveal before close must be refused"
    );
    println!("  tooth · a reveal BEFORE the commit phase closes is refused\n");

    auction.seal_commit_phase();
    println!("REVEAL phase — now the sealed values open:");
    for (name, bid) in [("alice", &alice), ("bob", &bob), ("carol", &carol)] {
        auction.reveal(*bid).expect("a committed bid reveals");
        println!("  {name:5} revealed {}", bid.value);
    }

    // Teeth that make the discovered price TRUSTWORTHY:
    let outsider = Bid::new(99, 999, 1);
    assert!(auction.reveal(outsider).is_err());
    println!("  tooth · a NON-COMMITTED outsider (bidding 999!) cannot win — it never sealed");
    let bob_switched = Bid::new(BOB_ID, 70, 0xB0B0);
    assert!(auction.reveal(bob_switched).is_err());
    println!("  tooth · bob cannot peek-then-raise — the changed bid no longer matches his seal\n");

    let winner = auction.winner().expect("a winner is discovered");
    let price = winner.value as i64;
    assert_eq!(winner.bidder, BOB_ID, "the top sealed bid wins");
    assert_eq!(price, 50, "the clearing price is the winning sealed bid");
    println!(
        "DISCOVERED · bidder {} wins the slot at a clearing price of {} (sealed-bid first-price).\n",
        winner.bidder, price
    );

    // ─────────────────────────────────────────────────────────────────────────
    // THE SEAM — the auction's (winner, price) becomes the escrow's terms.
    // ─────────────────────────────────────────────────────────────────────────
    let winner_pk = pubkey(winner.bidder);
    let seller_pk = pubkey(SELLER_ID);

    // ─────────────────────────────────────────────────────────────────────────
    // ORGAN 2 — escrow-market: atomic, conserved clearing of THAT trade.
    //   Leg A: the winner pays `price` of PAY.
    //   Leg B: the seller delivers `GOOD_QTY` of GOOD.
    //   They cross in one step, or not at all.
    // ─────────────────────────────────────────────────────────────────────────
    happy_path_clearing(winner_pk, seller_pk, price);
    reclaim_defence(winner_pk, seller_pk, price);

    println!(
        "\nOne market: sealed price discovery upstream, atomic conserved clearing downstream."
    );
    println!("Neither app trusts the other's operator — the seal binds the bid, the escrow binds");
    println!("the swap, and value is conserved end to end. ( ⌐■_■ )");
}

/// The happy path: both legs deposit, the trade clears atomically, value conserved.
fn happy_path_clearing(winner_pk: [u8; 32], seller_pk: [u8; 32], price: i64) {
    println!(
        "CLEARING (happy path) — winner pays {price} PAY  ⇄  seller delivers {GOOD_QTY} GOOD:"
    );

    let winner_id = party(winner_pk, PAY);
    let seller_id = party(seller_pk, GOOD);

    let terms = EscrowTerms::swap(
        LegRequirement::new(winner_id, CellId::from_bytes(PAY), price),
        LegRequirement::new(seller_id, CellId::from_bytes(GOOD), GOOD_QTY),
    );
    let mut market = SealedEscrowMarket::open(terms);

    // Wallets: the winner is funded in PAY and will receive GOOD; the seller holds
    // the GOOD and will receive PAY.
    let mut winner_pays = wallet(winner_pk, PAY, price);
    let mut winner_gets = wallet(winner_pk, GOOD, 0);
    let mut seller_delivers = wallet(seller_pk, GOOD, GOOD_QTY);
    let mut seller_gets = wallet(seller_pk, PAY, 0);

    // Conservation baselines across wallets + the escrow's in-transit custody.
    let total_pay = |m: &SealedEscrowMarket, w: &Cell, s: &Cell| {
        w.state.balance() + s.state.balance() + m.escrow_custody_a()
    };
    let total_good = |m: &SealedEscrowMarket, w: &Cell, s: &Cell| {
        w.state.balance() + s.state.balance() + m.escrow_custody_b()
    };
    assert_eq!(total_pay(&market, &winner_pays, &seller_gets), price);
    assert_eq!(
        total_good(&market, &winner_gets, &seller_delivers),
        GOOD_QTY
    );

    // Winner locks the payment leg — a light client SEES the commitment move.
    let before = market.commitment();
    market
        .deposit(
            Side::A,
            &Leg::new(winner_id, CellId::from_bytes(PAY), price),
            &mut winner_pays,
        )
        .expect("the winner's payment leg deposits");
    assert_ne!(
        before,
        market.commitment(),
        "the deposit re-seals the escrow commitment"
    );
    println!("  winner locked {price} PAY into escrow (payment leg)");

    // Tooth: settling with only one leg present is refused — no half-open trade.
    assert!(
        market.settle(&mut winner_gets, &mut seller_gets).is_err(),
        "cannot clear a half-open trade"
    );
    println!(
        "  tooth · settling with only the payment leg present is refused (no half-open clear)"
    );

    // Seller locks the delivery leg.
    market
        .deposit(
            Side::B,
            &Leg::new(seller_id, CellId::from_bytes(GOOD), GOOD_QTY),
            &mut seller_delivers,
        )
        .expect("the seller's delivery leg deposits");
    let view = market.state().expect("escrow state");
    assert_eq!(view.status(Side::A), LegStatus::Deposited);
    assert_eq!(view.status(Side::B), LegStatus::Deposited);
    println!("  seller locked {GOOD_QTY} GOOD into escrow (delivery leg)");

    // Clear atomically: both legs cross to their counterparties in one step.
    let (moved_pay, moved_good) = market
        .settle(&mut winner_gets, &mut seller_gets)
        .expect("both legs present — the trade clears atomically");
    assert_eq!((moved_pay, moved_good), (price, GOOD_QTY));

    assert_eq!(
        winner_gets.state.balance(),
        GOOD_QTY,
        "the winner received the good"
    );
    assert_eq!(
        seller_gets.state.balance(),
        price,
        "the seller was paid the clearing price"
    );
    assert_eq!(winner_pays.state.balance(), 0);
    assert_eq!(seller_delivers.state.balance(), 0);

    // Conservation held across the whole clearing.
    assert_eq!(
        total_pay(&market, &winner_pays, &seller_gets),
        price,
        "PAY conserved"
    );
    assert_eq!(
        total_good(&market, &winner_gets, &seller_delivers),
        GOOD_QTY,
        "GOOD conserved"
    );
    println!(
        "  CLEARED atomically · winner has the slot, seller has {price} PAY, value conserved\n"
    );
}

/// The reclaim defence: the seller ghosts after the winner locks payment; the
/// winner reclaims its own leg one-shot and is made whole — no value stranded.
fn reclaim_defence(winner_pk: [u8; 32], seller_pk: [u8; 32], price: i64) {
    println!("CLEARING (adversarial) — the seller never delivers; the winner must not lose funds:");

    let winner_id = party(winner_pk, PAY);
    let seller_id = party(seller_pk, GOOD);

    let terms = EscrowTerms::swap(
        LegRequirement::new(winner_id, CellId::from_bytes(PAY), price),
        LegRequirement::new(seller_id, CellId::from_bytes(GOOD), GOOD_QTY),
    );
    let mut market = SealedEscrowMarket::open(terms);

    let mut winner_pays = wallet(winner_pk, PAY, price);
    market
        .deposit(
            Side::A,
            &Leg::new(winner_id, CellId::from_bytes(PAY), price),
            &mut winner_pays,
        )
        .expect("the winner's payment leg deposits");
    assert_eq!(winner_pays.state.balance(), 0, "payment locked into escrow");
    println!("  winner locked {price} PAY; the seller then GHOSTS (never deposits the good)");

    // The winner reclaims its own leg and is made whole.
    let reclaimed = market
        .reclaim(Side::A, winner_id, &mut winner_pays)
        .expect("the winner reclaims its own leg");
    assert_eq!(reclaimed, price);
    assert_eq!(
        winner_pays.state.balance(),
        price,
        "the winner is made whole"
    );
    println!("  winner reclaimed {price} PAY — made whole, no funds stranded");

    // One-shot: a reclaimed leg cannot then be settled (or re-reclaimed).
    assert!(
        market
            .reclaim(Side::A, winner_id, &mut winner_pays)
            .is_err(),
        "the reclaim is one-shot"
    );
    println!("  tooth · the reclaim is one-shot — a reclaimed leg can never also settle");
}
