//! The verifiable market as a green-gated test: a sealed-bid auction discovers
//! the winner + clearing price (front-run-proof), and that exact trade clears
//! through the atomic escrow with per-asset conservation + a reclaim defence.
//!
//! This is the test twin of `examples/verifiable_market.rs` — the runnable
//! example prints the transcript; this asserts the interlock in CI.

use dregg_cell::Cell;
use dregg_types::CellId;

use starbridge_escrow_market::{
    EscrowTerms, Leg, LegRequirement, LegStatus, SealedEscrowMarket, Side,
};
use starbridge_sealed_auction::{Auction, Bid, Phase};

const PAY: [u8; 32] = [0xA1u8; 32];
const GOOD: [u8; 32] = [0x60u8; 32];
const GOOD_QTY: i64 = 1;

const SELLER_ID: u8 = 1;
const SLOT_ID: u8 = 2;

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

/// Run the sealed-bid auction; return (winner_handle, clearing_price) with the
/// front-run teeth asserted.
fn discover_price() -> (u8, i64) {
    let alice = Bid::new(10, 30, 0xA1A1);
    let bob = Bid::new(11, 50, 0xB0B0);
    let carol = Bid::new(12, 40, 0xCACA);

    let mut auction = Auction::new(SELLER_ID, SLOT_ID, PAY, GOOD);
    for bid in [&alice, &bob, &carol] {
        auction.commit(bid.seal()).expect("commit sealed bid");
    }
    // Tooth: reveal before close is refused.
    assert_eq!(auction.phase, Phase::Commit);
    assert!(auction.reveal(bob).is_err());

    auction.seal_commit_phase();
    for bid in [&alice, &bob, &carol] {
        auction.reveal(*bid).expect("reveal committed bid");
    }
    // Tooth: an uncommitted outsider cannot win; a peeked-then-raised bid fails its seal.
    assert!(auction.reveal(Bid::new(99, 999, 1)).is_err());
    assert!(auction.reveal(Bid::new(11, 70, 0xB0B0)).is_err());

    let winner = auction.winner().expect("a winner");
    assert_eq!(winner.bidder, 11);
    assert_eq!(winner.value, 50);
    (winner.bidder, winner.value as i64)
}

#[test]
fn a_sealed_bid_clears_through_escrow_with_conservation() {
    let (winner_handle, price) = discover_price();
    let winner_pk = pubkey(winner_handle);
    let seller_pk = pubkey(SELLER_ID);

    let winner_id = party(winner_pk, PAY);
    let seller_id = party(seller_pk, GOOD);

    let terms = EscrowTerms::swap(
        LegRequirement::new(winner_id, CellId::from_bytes(PAY), price),
        LegRequirement::new(seller_id, CellId::from_bytes(GOOD), GOOD_QTY),
    );
    let mut market = SealedEscrowMarket::open(terms);

    let mut winner_pays = wallet(winner_pk, PAY, price);
    let mut winner_gets = wallet(winner_pk, GOOD, 0);
    let mut seller_delivers = wallet(seller_pk, GOOD, GOOD_QTY);
    let mut seller_gets = wallet(seller_pk, PAY, 0);

    let total_pay = |m: &SealedEscrowMarket, w: &Cell, s: &Cell| {
        w.state.balance() + s.state.balance() + m.escrow_custody_a()
    };
    let total_good = |m: &SealedEscrowMarket, w: &Cell, s: &Cell| {
        w.state.balance() + s.state.balance() + m.escrow_custody_b()
    };

    let before = market.commitment();
    market
        .deposit(
            Side::A,
            &Leg::new(winner_id, CellId::from_bytes(PAY), price),
            &mut winner_pays,
        )
        .expect("payment leg deposits");
    assert_ne!(
        before,
        market.commitment(),
        "the deposit re-seals the escrow commitment"
    );

    // No half-open clear.
    assert!(market.settle(&mut winner_gets, &mut seller_gets).is_err());

    market
        .deposit(
            Side::B,
            &Leg::new(seller_id, CellId::from_bytes(GOOD), GOOD_QTY),
            &mut seller_delivers,
        )
        .expect("delivery leg deposits");
    let view = market.state().unwrap();
    assert_eq!(view.status(Side::A), LegStatus::Deposited);
    assert_eq!(view.status(Side::B), LegStatus::Deposited);

    let (moved_pay, moved_good) = market
        .settle(&mut winner_gets, &mut seller_gets)
        .expect("both legs present — clears atomically");
    assert_eq!((moved_pay, moved_good), (price, GOOD_QTY));

    assert_eq!(winner_gets.state.balance(), GOOD_QTY, "winner got the good");
    assert_eq!(
        seller_gets.state.balance(),
        price,
        "seller was paid the clearing price"
    );
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
}

#[test]
fn a_ghosting_seller_is_defeated_by_reclaim() {
    let (winner_handle, price) = discover_price();
    let winner_pk = pubkey(winner_handle);
    let seller_pk = pubkey(SELLER_ID);
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
        .expect("payment locks");
    assert_eq!(winner_pays.state.balance(), 0);

    let reclaimed = market
        .reclaim(Side::A, winner_id, &mut winner_pays)
        .expect("winner reclaims its own leg");
    assert_eq!(reclaimed, price);
    assert_eq!(winner_pays.state.balance(), price, "winner made whole");

    // One-shot: cannot reclaim (or settle) twice.
    assert!(
        market
            .reclaim(Side::A, winner_id, &mut winner_pays)
            .is_err()
    );
}
