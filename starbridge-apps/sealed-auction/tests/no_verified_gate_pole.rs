//! **POLE 2: UNREGISTERED ⇒ the award is REFUSED, and the refusal names the BUILD — not the auction.**
//!
//! This file must never call `install_verified_auction_gate()`, and nothing it links may either.
//! The `IntentVerifiedGate` is a process-global `OnceLock` in `dregg-intent`, so this polarity is
//! only observable in a process that has no gate at all — which is why it is a separate test
//! binary from `verified_gate_registered_pole.rs` rather than another `#[test]` beside it.
//!
//! # Both halves are load-bearing, and the second is the one that was missing
//!
//! **That it REFUSES** is the fail-closed guarantee: an unverified in-process Rust fold must not
//! decide who won an auction. That was already correct.
//!
//! **What it SAYS** is the part that over-reached. `Auction::settle` used to map every executor
//! error into `AuctionError::SettlementRejected`, whose `Display` reads *"award settlement rejected
//! by the verified executor"*. For an absent gate that sentence is false in the way that costs the
//! most: the award was not rejected, it was NEVER JUDGED — and the reader goes debugging the
//! auction. The `/clear` CLI lost a day to the identical wording before
//! `exec-lean/src/bin/drex_clear.rs::fail_verified_core_absent` split it, and the split was then
//! copy-pasted into `dreggnet-market` and nowhere else. This test pins the distinction at a THIRD
//! surface, now that it derives from one classifier
//! (`dregg_intent::verified_settle::unjudged`) instead of being re-remembered per app.

use dregg_intent::verified_settle::Unjudged;
use starbridge_sealed_auction::{
    AssetId, Auction, AuctionError, Bid, CellId, fund_ledger, verified_auction_gate_available,
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

/// A fully funded, perfectly conserving award — so the ONLY thing that can refuse it is the absent
/// gate. Using an under-funded book here would make the test pass for the wrong reason, which is
/// the shape a falsifier dies in.
fn a_perfectly_good_award() -> (Auction, dregg_intent::verified_settle::VerifiedLedger) {
    let alice = Bid::new(ALICE, 30, 0xA1A1);
    let bob = Bid::new(BOB, 50, 0xB0B0);
    let mut auction = Auction::new(SELLER, SLOT, PAY, TOKEN);
    auction.commit(alice.seal()).unwrap();
    auction.commit(bob.seal()).unwrap();
    auction.seal_commit_phase();
    auction.reveal(alice).unwrap();
    auction.reveal(bob).unwrap();
    let ledger = fund_ledger(&[
        (BOB, PAY, 100),
        (SELLER, PAY, 0),
        (SLOT, TOKEN, 100),
        (BOB, TOKEN, 0),
    ]);
    (auction, ledger)
}

#[test]
fn an_unregistered_gate_refuses_and_blames_the_build_not_the_auction() {
    // PREMISE, asserted rather than assumed, and asserted at the REAL registry rather than at this
    // crate's own installer flag: `dregg_intent::verified_gate::is_registered()` is the OnceLock
    // the fold actually consults, so a gate installed by ANY path in this binary is visible here.
    // Checking only `verified_auction_gate_available()` would miss exactly that, and the polarity
    // would vanish while the test stayed green — the shape a falsifier dies in.
    assert!(
        !dregg_intent::verified_gate::is_registered(),
        "premise broken: something installed the verified intent gate in THIS test binary, so the \
         no-gate polarity is unobservable and this test proves nothing. Keep this file's process \
         free of any `register_distributed_gates()` / `install_verified_auction_gate()` call."
    );
    assert!(!verified_auction_gate_available());

    let (mut auction, ledger) = a_perfectly_good_award();
    let pay_before = ledger.total_asset(&PAY);

    let err = auction
        .settle(&ledger)
        .expect_err("FAIL-CLOSED: with no verified gate, an award must NOT settle");

    // (1) It must be typed as NEVER JUDGED, and specifically as a WIRING BUG — this binary never
    //     installed a gate. `NoVerifiedCore` would be the wrong diagnosis and send the reader to
    //     seed an archive that is not the problem.
    let AuctionError::AwardNeverJudged { cause, diagnosis } = &err else {
        panic!(
            "an absent gate must be typed as NEVER JUDGED, not as a verdict on the award. \
             `SettlementRejected` here is the exact laundering this pole exists to forbid. got: \
             {err:?}"
        )
    };
    assert_eq!(
        *cause,
        Unjudged::WiringBug,
        "no gate registered at all is a WIRING BUG (fixed in code), not a missing Lean archive \
         (fixed in the environment) — the two fixes are opposite: {diagnosis}"
    );

    // (2) The rendered sentence must point at the BUILD and must not accuse the auction. Assert
    //     BOTH directions: presence of the cure, absence of the blame. A message that merely
    //     contained "WIRING BUG" while still reading "rejected the award" would satisfy a
    //     one-sided check and mislead exactly as before.
    let rendered = err.to_string();
    assert_eq!(
        &rendered, diagnosis,
        "Display must surface the diagnosis, not a generic rejection line"
    );
    for needle in [
        "WIRING BUG",
        "NEVER JUDGED",
        "register_distributed_gates",
        "install_verified_auction_gate",
        "not a problem with the ring",
    ] {
        assert!(
            rendered.contains(needle),
            "the refusal must name the cure ({needle:?} missing): {rendered}"
        );
    }
    for forbidden in ["rejected the ring", "rejected by the verified executor"] {
        assert!(
            !rendered.contains(forbidden),
            "an award that was never judged must not be reported as rejected ({forbidden:?}): \
             {rendered}"
        );
    }

    // (3) FAIL-CLOSED means nothing moved: a refused award leaves the book exactly as it was.
    assert_eq!(ledger.total_asset(&PAY), pay_before);
    assert_eq!(ledger.get(SELLER, &PAY), 0, "the seller must not be paid");
    assert_eq!(
        ledger.get(BOB, &TOKEN),
        0,
        "the winner must not take delivery"
    );
}
