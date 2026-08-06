//! **POLE 1 of the sealed-auction verified-settlement gate: REGISTERED ⇒ the award SETTLES.**
//!
//! Its twin is `no_verified_gate_pole.rs`, which must live in a SEPARATE test binary: the
//! `IntentVerifiedGate` is a process-global `OnceLock` inside `dregg-intent`, so a single process
//! can only ever exhibit ONE of the two polarities. Two files = two binaries = both poles pinned.
//!
//! # What this is guarding
//!
//! `Auction::settle` folds the award ring through `dregg_intent::verified_settle::settle_ring_verified`,
//! which has been FAIL-CLOSED since the twin-deletion sweep (`e3f0e7b92`): with no gate registered
//! it REFUSES rather than let an unverified in-process Rust fold decide who won an auction. That
//! refusal is correct and stays. What was missing is that NOTHING in this crate registered a gate —
//! the crate named `register_distributed_gates()` in a doc comment (`src/lib.rs:30`) and had no
//! dependency edge to call it — so `examples/sealed_compute_auction.rs` panicked on its `.unwrap()`
//! and no award could ever close. This is the un-called-initializer class, one entry point later
//! than the `/clear` CLI that was fixed first.
//!
//! Deleting the `install_verified_auction_gate()` call below makes this file's asserts fail.

use starbridge_sealed_auction::{
    AssetId, Auction, AuctionError, Bid, CellId, fund_ledger, install_verified_auction_gate,
    verified_auction_gate_available,
};

const PAY: AssetId = [0u8; 32];
const TOKEN: AssetId = {
    let mut a = [0u8; 32];
    a[0] = 1;
    a
};

const ALICE: CellId = 10;
const BOB: CellId = 11;
const SELLER: CellId = 1;
const SLOT: CellId = 2;

/// The installer must succeed AND report itself available. A failure here is a hard red, never a
/// skip: an auction test over an auction that cannot close is worse than a red one, and a
/// `return`-on-absent-archive is exactly how this regression stayed invisible at the `/clear` CLI.
fn arm() {
    install_verified_auction_gate().unwrap_or_else(|e| {
        panic!(
            "the verified auction gate did not install: {e}\n\
             An award ring settles through the linked verified Lean executor; without it every \
             award is refused and no auction can close. Seed a HEAD-matching \
             dregg-lean-ffi/libdregg_lean.a and rebuild."
        )
    });
    assert!(
        verified_auction_gate_available(),
        "install_verified_auction_gate() returned Ok but the availability probe says otherwise"
    );
}

fn run_to_reveal() -> (Auction, Bid) {
    let alice = Bid::new(ALICE, 30, 0xA1A1);
    let bob = Bid::new(BOB, 50, 0xB0B0); // the top bid
    let mut auction = Auction::new(SELLER, SLOT, PAY, TOKEN);
    auction.commit(alice.seal()).unwrap();
    auction.commit(bob.seal()).unwrap();
    auction.seal_commit_phase();
    auction.reveal(alice).unwrap();
    auction.reveal(bob).unwrap();
    (auction, bob)
}

/// **THE POSITIVE POLE.** With the gate installed, a funded award SETTLES — and moves the exact
/// value. Asserting the post-column (not merely `is_ok`) is what makes this a settlement rather
/// than a smoke test.
#[test]
fn a_registered_gate_settles_the_award_and_moves_the_value() {
    arm();
    let (mut auction, bob) = run_to_reveal();

    let ledger = fund_ledger(&[
        (BOB, PAY, 100),
        (SELLER, PAY, 0),
        (SLOT, TOKEN, 100),
        (BOB, TOKEN, 0),
    ]);
    let pay_before = ledger.total_asset(&PAY);
    let token_before = ledger.total_asset(&TOKEN);

    let (post, winner) = auction
        .settle(&ledger)
        .expect("a funded award must settle through the registered verified executor");

    assert_eq!(winner.bidder, bob.bidder, "the top bid must win");
    assert_eq!(winner.value, 50);
    // The winner paid its bid to the seller…
    assert_eq!(post.get(SELLER, &PAY), 50);
    assert_eq!(post.get(BOB, &PAY), 50, "100 funded − 50 bid");
    // …and took delivery from the slot. Both legs of `award_ring` move `winner.value`, so the slot
    // delivers 50 of the task-token — not its whole 100 balance.
    assert_eq!(post.get(BOB, &TOKEN), 50);
    assert_eq!(post.get(SLOT, &TOKEN), 50, "100 held − 50 delivered");
    // Conservation, per touched asset.
    assert_eq!(post.total_asset(&PAY), pay_before);
    assert_eq!(post.total_asset(&TOKEN), token_before);
}

/// **THE DECIDING POLE, inside a registered process.** Registration alone is not evidence: a gate
/// that answered "ok" unconditionally would pass the test above and settle every award nobody can
/// pay. So an award the winner CANNOT fund must still be refused — and refused as a VERDICT
/// (`SettlementRejected`), never as an absent build.
#[test]
fn a_registered_gate_still_refuses_an_award_the_winner_cannot_pay() {
    arm();
    let (mut auction, _bob) = run_to_reveal();

    // BOB won at 50 but holds 3.
    let ledger = fund_ledger(&[
        (BOB, PAY, 3),
        (SELLER, PAY, 0),
        (SLOT, TOKEN, 100),
        (BOB, TOKEN, 0),
    ]);

    let err = auction
        .settle(&ledger)
        .expect_err("an unpayable award must NOT settle");

    assert!(
        matches!(err, AuctionError::SettlementRejected(_)),
        "an unpayable award is a VERDICT on the award, not an absent gate — the two must not be \
         confusable, since their fixes are opposite. got: {err:?}"
    );
    assert!(
        !matches!(err, AuctionError::AwardNeverJudged { .. }),
        "a judged-and-refused award must never be reported as never-judged: {err:?}"
    );
}
