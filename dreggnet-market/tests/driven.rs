//! **The market, DRIVEN** — the `MarketOffering` exercised end to end through the real
//! sealed-auction substrate + the verified per-asset settlement. Every assertion rides a REAL
//! executor turn (a genuine [`TurnReceipt`]) or a real refusal; the value move at SETTLE is the
//! conserved per-asset ring settlement (Σδ = 0). Nothing here is a flag.

/// The verified settlement gate this binary installs before every test — see
/// `tests/support/mod.rs`. Without it `settle_ring_verified` refuses every award as
/// NEVER JUDGED, which is a host-wiring fact about this binary and not a market verdict.
mod support;

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
    support::install_verified_settlement_gate();
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
    support::install_verified_settlement_gate();
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
    support::install_verified_settlement_gate();
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
    support::install_verified_settlement_gate();
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
    support::install_verified_settlement_gate();
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
    support::install_verified_settlement_gate();
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
    support::install_verified_settlement_gate();
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

/// Every string a viewer can read off a rendered surface — text nodes, section titles, pill labels,
/// menu-item labels — so a test can assert what a bidder can and cannot see.
fn rendered_text(surface: &dreggnet_offerings::Surface) -> String {
    use deos_view::ViewNode;
    fn walk(n: &ViewNode, out: &mut String) {
        match n {
            ViewNode::Text(t) => {
                out.push_str(t);
                out.push('\n');
            }
            ViewNode::Pill { text, .. } => {
                out.push_str(text);
                out.push('\n');
            }
            ViewNode::Progress {
                label, value, max, ..
            } => {
                out.push_str(&format!("{label} {value}/{max}\n"));
            }
            ViewNode::Section {
                title, children, ..
            } => {
                out.push_str(title);
                out.push('\n');
                for c in children {
                    walk(c, out);
                }
            }
            ViewNode::Menu { items } => {
                for it in items {
                    out.push_str(&it.label);
                    out.push('\n');
                }
            }
            ViewNode::VStack(cs) | ViewNode::Row(cs) | ViewNode::List(cs) | ViewNode::Table(cs) => {
                for c in cs {
                    walk(c, out);
                }
            }
            _ => {}
        }
    }
    let mut out = String::new();
    walk(surface.view(), &mut out);
    out
}

/// **THE SEAL SURVIVES THE PER-VIEWER RENDER.** The surface now discloses one thing it never did: a
/// bidder's OWN sealed bid, because "have I bid, and for what" is the one question a sealed auction
/// owes the person who bid. The disclosure must be exactly that and no wider — a rival bidder, the
/// SELLER, and a spectator must each read their own position and nobody else's, right up until the
/// clear opens every seal by the rules.
///
/// Non-vacuous by construction: each bidder's own view is asserted to CONTAIN its own number, so a
/// render that simply stopped printing bid values cannot make this pass.
#[test]
fn a_bidders_own_bid_is_disclosed_to_them_and_to_nobody_else() {
    support::install_verified_settlement_gate();
    let off = MarketOffering::new();
    let mut s = off
        .open(SessionConfig::with_seed(11))
        .expect("market opens");
    assert!(matches!(list(&off, &mut s, 25), Outcome::Landed { .. }));

    // Distinct, unambiguous values: no one number is a substring of another, and none collides
    // with the reserve (25), a bid count, or a turn count.
    let book = [("alice", 137), ("bob", 941), ("carol", 663)];
    for (who, v) in book {
        assert!(
            matches!(bid(&off, &mut s, who, v), Outcome::Landed { .. }),
            "bid {who} must land"
        );
    }

    // The seal DIGEST is hex, and hex digits are decimal digits — a 3-digit bid value can appear
    // inside a commitment by coincidence, which would make the exclusion scan below fail for a
    // reason that is not a leak. Drop the digest lines before scanning for numbers; they are
    // asserted separately.
    let scannable = |surface: &dreggnet_offerings::Surface| -> String {
        rendered_text(surface)
            .lines()
            .filter(|l| !l.contains("Its seal is"))
            .collect::<Vec<_>>()
            .join("\n")
    };

    for (who, v) in book {
        let mine = scannable(&off.render_for(&s, &bidder(who)));
        assert!(
            mine.contains("Your sealed bid"),
            "{who} is not shown their own bid section:\n{mine}"
        );
        assert!(
            rendered_text(&off.render_for(&s, &bidder(who))).contains("Its seal is"),
            "{who} is not shown the commitment their bid is frozen under"
        );
        assert!(
            mine.contains(&v.to_string()),
            "{who} cannot read their own bid ({v}) — the disclosure is missing, so the exclusion \
             below would pass vacuously:\n{mine}"
        );
        // …and nothing of anyone else's.
        for (other, ov) in book {
            if other == who {
                continue;
            }
            assert!(
                !mine.contains(&ov.to_string()),
                "{who} read {other}'s sealed bid ({ov}) off their own surface:\n{mine}"
            );
        }
    }

    // The SELLER holds the settle capability and still may not read a seal before opening it.
    let sellers = scannable(&off.render_for(&s, &seller()));
    // A spectator (an identity with no role at this auction) likewise.
    let spectator = scannable(&off.render_for(&s, &DreggIdentity("nosy".to_string())));
    let public = scannable(&off.render(&s));
    for (label, view) in [
        ("the seller", &sellers),
        ("a spectator", &spectator),
        ("the public render", &public),
    ] {
        for (who, v) in book {
            assert!(
                !view.contains(&v.to_string()),
                "{label} read {who}'s sealed bid ({v}) before the clear:\n{view}"
            );
        }
        assert!(
            !view.contains("Your sealed bid"),
            "{label} was served an own-bid section it has no bid for"
        );
    }
    // The seller is still TOLD they are the seller and what they can do — fog is not silence.
    assert!(
        sellers.contains("You are the SELLER"),
        "the seller is not told their role:\n{sellers}"
    );
    assert!(
        public.contains("What the seal is"),
        "the domain plaque explaining the hiding is missing from the public render"
    );

    // AFTER THE CLEAR the seals are open by the rules, and the winner is public to everyone.
    //
    // ⚑ THIS IS UNCONDITIONAL AGAIN. It used to be `if let Outcome::Landed { .. } = settle(...)`,
    // under a comment explaining that `settle_ring_verified` is FAIL-CLOSED without a registered
    // verified-executor gate and "this crate's test harness installs none". The observation was
    // correct and the conclusion was not: a fog assertion that only fires when the settle happens
    // to land asserts NOTHING in a harness where the settle never lands, which was every run for
    // three days. The harness installs the gate now (`tests/support/mod.rs`), so the clear is a
    // real one and the disclosure it produces is checked every time.
    let out = settle(&off, &mut s);
    assert!(
        out.landed(),
        "the market must clear before the post-clear disclosure can be checked: {out:?}"
    );
    let after = scannable(&off.render(&s));
    assert!(
        after.contains("941"),
        "the cleared auction does not publish the winning bid:\n{after}"
    );
}
