//! **The market, DRIVEN** — the `MarketOffering` exercised end to end through the real
//! sealed-auction substrate + the verified per-asset settlement. Every assertion rides a REAL
//! executor turn (a genuine [`TurnReceipt`]) or a real refusal; the value move at SETTLE is the
//! conserved per-asset ring settlement (Σδ = 0). Nothing here is a flag.

use dreggnet_market::{MarketOffering, TURN_BID, TURN_LIST, TURN_SETTLE};
use dreggnet_offerings::{Action, DreggIdentity, Offering, Outcome, SessionConfig};

fn seller() -> DreggIdentity {
    DreggIdentity("seller-alice".to_string())
}
fn bidder(n: &str) -> DreggIdentity {
    DreggIdentity(format!("bidder-{n}"))
}

fn list(off: &MarketOffering, s: &mut dreggnet_market::MarketSession, reserve: i64) -> Outcome {
    off.advance(s, Action::new("list", TURN_LIST, reserve, true), seller())
}
fn bid(
    off: &MarketOffering,
    s: &mut dreggnet_market::MarketSession,
    who: &str,
    value: i64,
) -> Outcome {
    off.advance(s, Action::new("bid", TURN_BID, value, true), bidder(who))
}
fn settle(off: &MarketOffering, s: &mut dreggnet_market::MarketSession) -> Outcome {
    off.advance(s, Action::new("settle", TURN_SETTLE, 0, true), seller())
}

/// THE HAPPY PATH: list → three sealed bids → settle clears to the top bid, the value moves
/// conservation-checked (Σδ = 0), every step a real verified turn, and verify() holds.
#[test]
fn list_bid_settle_clears_to_the_winning_bid_conserved() {
    let off = MarketOffering::new();
    let mut s = off.open(SessionConfig::with_seed(7)).expect("market opens");

    // LIST — a real factory-born auction cell (a genuine birth receipt).
    let out = list(&off, &mut s, 25);
    let Outcome::Landed { receipt, .. } = out else {
        panic!("LIST must land, got {out:?}")
    };
    assert_ne!(
        receipt.turn_hash, [0u8; 32],
        "LIST is a real verified birth turn"
    );
    assert!(s.is_listed());

    // THREE sealed bids — each a real WriteOnce commit turn. Bob (50) is the top bid.
    for (who, v) in [("alice", 30), ("bob", 50), ("carol", 40)] {
        let out = bid(&off, &mut s, who, v);
        let Outcome::Landed { receipt, .. } = out else {
            panic!("BID {who} must land, got {out:?}")
        };
        assert_ne!(
            receipt.turn_hash, [0u8; 32],
            "a sealed bid is a real verified turn"
        );
    }
    assert_eq!(s.bid_count(), 3);

    // SETTLE — reveal + clear to the winning sealed bid; the value moves conserved.
    let out = settle(&off, &mut s);
    let Outcome::Landed { receipt, ended } = out else {
        panic!("SETTLE must land, got {out:?}")
    };
    assert_ne!(
        receipt.turn_hash, [0u8; 32],
        "SETTLE resolve is a real verified turn"
    );
    assert!(ended, "a cleared auction ends the session");

    let c = s.clearing().expect("the auction cleared");
    assert_eq!(c.winner.value, 50, "cleared to the TOP sealed bid");
    assert_eq!(c.price(), 50, "the winner pays its winning bid");
    assert!(
        c.conserved(),
        "the value move conserves every asset (Σδ = 0)"
    );
    // Per-asset Σδ = 0: PAY and GOOD totals unchanged across the clear.
    assert_eq!(c.pay_conserved.0, c.pay_conserved.1, "PAY conserved");
    assert_eq!(c.good_conserved.0, c.good_conserved.1, "GOOD conserved");
    // The winner really received the good and the seller really received the payment.
    assert_eq!(
        c.post.get(c.winner.bidder, &[0x60u8; 32]),
        50,
        "winner received 50 GOOD"
    );
    assert_eq!(
        c.post.get(1 /*seller*/, &[0xA1u8; 32]),
        50,
        "seller received 50 PAY"
    );
    assert_eq!(
        c.post.get(c.winner.bidder, &[0xA1u8; 32]),
        0,
        "winner paid its 50 PAY"
    );

    // verify() re-derives the clear: the winner is the real high bid, conservation holds, and the
    // on-ledger WINNER / HIGH_BID registers announce the real winner.
    let rep = off.verify(&s);
    assert!(
        rep.verified,
        "the cleared chain re-verifies: {}",
        rep.detail
    );
    assert!(
        rep.turns >= 5,
        "genesis birth + 3 commits + one atomic close/reveals/resolve turn"
    );
}

/// THE ANTI-DOUBLE-BID TOOTH: a bidder overwriting its own committed sealed bid is a REAL executor
/// refusal (`WriteOnce` commit board). Nothing commits.
#[test]
fn a_double_bid_is_refused() {
    let off = MarketOffering::new();
    let mut s = off.open(SessionConfig::with_seed(11)).expect("opens");
    assert!(list(&off, &mut s, 0).landed());

    assert!(
        bid(&off, &mut s, "mallory", 30).landed(),
        "the first sealed bid lands"
    );
    let out = bid(&off, &mut s, "mallory", 70); // same bidder tries to raise → overwrite its slot
    assert!(
        matches!(out, Outcome::Refused(_)),
        "a double-bid must be refused, got {out:?}"
    );
    if let Outcome::Refused(why) = &out {
        assert!(
            why.to_lowercase().contains("double-bid"),
            "refusal cites the double-bid: {why}"
        );
    }
    assert_eq!(
        s.bid_count(),
        1,
        "the refused double-bid committed nothing (anti-ghost)"
    );
}

/// THE COMMIT-PHASE TOOTH: a bid after the commit phase closes is refused (nothing submitted).
#[test]
fn a_bid_after_close_is_refused() {
    let off = MarketOffering::new();
    let mut s = off.open(SessionConfig::with_seed(13)).expect("opens");
    assert!(list(&off, &mut s, 0).landed());
    assert!(bid(&off, &mut s, "a", 20).landed());
    assert!(bid(&off, &mut s, "b", 40).landed());

    // Settle closes the commit phase (and clears). A subsequent bid is refused.
    assert!(settle(&off, &mut s).landed(), "settle clears");
    let out = bid(&off, &mut s, "late", 999);
    assert!(
        matches!(out, Outcome::Refused(_)),
        "a bid after close/settle must be refused, got {out:?}"
    );
    assert_eq!(s.bid_count(), 2, "the late bid committed nothing");
}

/// A below-reserve refusal is atomic: it does not close COMMIT, so the auction can still receive a
/// bid that meets reserve and settle normally.
#[test]
fn a_below_reserve_refusal_does_not_close_commit() {
    let off = MarketOffering::new();
    let mut s = off.open(SessionConfig::with_seed(29)).expect("opens");
    assert!(list(&off, &mut s, 100).landed()); // reserve 100 — below-reserve so no sale
    assert!(bid(&off, &mut s, "a", 20).landed());
    let receipts_before = s.receipts_len();
    assert!(
        matches!(settle(&off, &mut s), Outcome::Refused(_)),
        "below-reserve does not settle"
    );
    assert!(!s.is_settled());
    assert_eq!(s.receipts_len(), receipts_before);

    let out = bid(&off, &mut s, "b", 140);
    assert!(
        out.landed(),
        "the refusal must leave COMMIT open for a qualifying bid, got {out:?}"
    );
    assert!(settle(&off, &mut s).landed());
}

/// THE RESERVE TOOTH: a high sealed bid below the reserve does NOT settle — no value moves.
#[test]
fn a_below_reserve_auction_does_not_settle() {
    let off = MarketOffering::new();
    let mut s = off.open(SessionConfig::with_seed(17)).expect("opens");
    assert!(list(&off, &mut s, 100).landed()); // reserve 100
    assert!(bid(&off, &mut s, "a", 30).landed());
    assert!(bid(&off, &mut s, "b", 60).landed()); // top bid 60 < reserve 100

    let out = settle(&off, &mut s);
    assert!(
        matches!(out, Outcome::Refused(_)),
        "below-reserve must not settle, got {out:?}"
    );
    if let Outcome::Refused(why) = &out {
        assert!(
            why.to_lowercase().contains("reserve"),
            "refusal cites the reserve: {why}"
        );
    }
    assert!(!s.is_settled(), "no clearing recorded — no value moved");
    assert!(s.clearing().is_none());
}

/// THE NO-VALID-BID TOOTH: an auction with no sealed bids does NOT settle.
#[test]
fn a_no_bid_auction_does_not_settle() {
    let off = MarketOffering::new();
    let mut s = off.open(SessionConfig::with_seed(19)).expect("opens");
    assert!(list(&off, &mut s, 0).landed());
    let out = settle(&off, &mut s);
    assert!(
        matches!(out, Outcome::Refused(_)),
        "no bids must not settle, got {out:?}"
    );
    assert!(!s.is_settled());
}

/// The offering surface round-trips: actions() tracks the phase; render() paints the listing + bids.
#[test]
fn the_surface_tracks_the_market() {
    let off = MarketOffering::new();
    let mut s = off.open(SessionConfig::with_seed(23)).expect("opens");
    // Unlisted → only LIST is offered.
    let acts = off.actions(&s);
    assert_eq!(acts.len(), 1);
    assert_eq!(acts[0].turn, TURN_LIST);

    assert!(list(&off, &mut s, 10).landed());
    // Listed + COMMIT → BID and SETTLE are affordances.
    let acts = off.actions(&s);
    assert!(acts.iter().any(|a| a.turn == TURN_BID && a.enabled));
    assert!(bid(&off, &mut s, "x", 40).landed());
    assert!(settle(&off, &mut s).landed());
    // Settled → no actions; render mentions the winner.
    assert!(off.actions(&s).is_empty());
    let surface = off.render(&s);
    let _ = surface.view(); // paints a real deos ViewNode
}
