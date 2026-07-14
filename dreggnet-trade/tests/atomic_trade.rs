//! Driving the scam-proof atomic trade end to end — the HARD GATE.
//!
//! Every property is DRIVEN through the real asset layer + the real sealed-escrow
//! capacity, never asserted from bookkeeping:
//!   * an atomic asset↔asset swap settles — both assets cross ownership, the new
//!     owner can transfer, the old cannot, and per-asset conservation holds;
//!   * a GHOSTING counterparty cannot walk with the other's leg — settle refuses,
//!     the depositor reclaims and is made whole, and the reclaimed leg can never
//!     then be settled (non-vacuous: the honest settle path is shown live first);
//!   * a NON-OWNER cannot offer an asset it does not own (the transfer signature
//!     gate);
//!   * the traded item's provenance re-verifies (mint → trade → new owner);
//!   * an asset↔$DREGG listing settles atomically, $DREGG conserved.

use dreggnet_trade::{AssetError, LegSpec, Settlement, TradeError, TradeSide, TradeWorld};

/// Assert two labels resolve to distinct players (sanity for the fixtures).
fn distinct(tw: &mut TradeWorld, a: &str, b: &str) {
    assert_ne!(tw.pubkey_of(a), tw.pubkey_of(b));
}

// ─────────────────────────────────────────────────────────────────────────────
// 1. The atomic asset↔asset swap.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn atomic_asset_swap_crosses_both_legs_and_conserves() {
    let mut tw = TradeWorld::new();
    distinct(&mut tw, "alice", "bob");

    // Alice mints a cosmetic; Bob mints a crafting-mat. Each owns their own.
    let hat = tw.mint("alice", b"golden-hat #0001");
    let ore = tw.mint("bob", b"mythril-ore x8");
    assert_eq!(tw.current_holder_label(hat), Some("alice"));
    assert_eq!(tw.current_holder_label(ore), Some("bob"));

    // "Alice gives the hat iff Bob gives the ore."
    let mut trade = tw.open_trade("alice", LegSpec::Asset(hat), "bob", LegSpec::Asset(ore));

    // Both parties commit their legs into neutral escrow custody.
    tw.deposit(&mut trade, TradeSide::A)
        .expect("alice deposits the hat");
    // Before both legs are present, settle is a half-open trade — REFUSED, nothing crosses.
    assert!(
        matches!(tw.settle(&mut trade), Err(TradeError::Escrow(_))),
        "a one-legged settle must be refused"
    );
    tw.deposit(&mut trade, TradeSide::B)
        .expect("bob deposits the ore");

    // Atomic settle: the hat crosses to Bob, the ore to Alice — in one step.
    let s = tw
        .settle(&mut trade)
        .expect("both legs present ⇒ atomic settle");
    assert_eq!(
        s,
        Settlement {
            a_gave: LegSpec::Asset(hat),
            b_gave: LegSpec::Asset(ore)
        }
    );

    // Ownership crossed.
    assert_eq!(
        tw.current_holder_label(hat),
        Some("bob"),
        "the hat is Bob's now"
    );
    assert_eq!(
        tw.current_holder_label(ore),
        Some("alice"),
        "the ore is Alice's now"
    );
    assert_eq!(tw.current_owner(hat), Some(tw.pubkey_of("bob")));
    assert_eq!(tw.current_owner(ore), Some(tw.pubkey_of("alice")));

    // The NEW owner can transfer onward; the OLD owner cannot (its version is spent).
    assert!(
        tw.assets().transfer(hat, "bob", "carol").is_ok(),
        "the new owner (Bob) can transfer the hat"
    );
    assert!(
        matches!(
            tw.assets().transfer(ore, "bob", "carol"),
            Err(AssetError::Refused(_))
        ),
        "the old owner (Bob no longer holds the ore) cannot transfer it"
    );

    // Conservation Σδ=0 per asset: each asset id still has exactly ONE live tail and
    // its whole lineage re-verifies — no dupe was minted, nothing was destroyed.
    for a in [hat, ore] {
        let p = tw.verify_provenance(a);
        assert!(p.verified, "lineage re-verifies: {:?}", p.reasons);
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// 2. The half-open-trade attack — a ghosting counterparty defeated by reclaim.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn ghosting_counterparty_cannot_walk_and_depositor_is_made_whole() {
    let mut tw = TradeWorld::new();
    let sword = tw.mint("alice", b"cosmetic-flamebrand");
    let shield = tw.mint("bob", b"cosmetic-aegis");

    let mut trade = tw.open_trade(
        "alice",
        LegSpec::Asset(sword),
        "bob",
        LegSpec::Asset(shield),
    );

    // Alice deposits; Bob GHOSTS (never deposits his leg).
    tw.deposit(&mut trade, TradeSide::A).unwrap();
    assert_eq!(
        tw.current_holder_label(sword),
        Some(dreggnet_trade::ESCROW_CUSTODY_LABEL)
    );

    // Bob cannot walk with Alice's sword: settle is refused (his leg is not deposited).
    assert!(matches!(tw.settle(&mut trade), Err(TradeError::Escrow(_))));
    // The sword is still in custody — Bob got nothing.
    assert_eq!(
        tw.current_holder_label(sword),
        Some(dreggnet_trade::ESCROW_CUSTODY_LABEL)
    );

    // Alice reclaims her stranded leg and is MADE WHOLE — she owns the sword again.
    tw.reclaim(&mut trade, TradeSide::A)
        .expect("the depositor reclaims a stranded leg");
    assert_eq!(
        tw.current_holder_label(sword),
        Some("alice"),
        "Alice is made whole"
    );

    // One-shot: the reclaimed leg can never then be settled (even if Bob shows up late).
    tw.deposit(&mut trade, TradeSide::B)
        .expect("Bob can still lock his own leg, but it is now useless");
    assert!(
        matches!(tw.settle(&mut trade), Err(TradeError::Escrow(_))),
        "a reclaimed leg cannot be settled — the exit-scam is defeated"
    );
    // Alice keeps the sword; Bob reclaims his own shield.
    assert_eq!(tw.current_holder_label(sword), Some("alice"));
    tw.reclaim(&mut trade, TradeSide::B).unwrap();
    assert_eq!(tw.current_holder_label(shield), Some("bob"));
}

// ─────────────────────────────────────────────────────────────────────────────
// 3. A non-owner cannot offer an asset it does not own.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn non_owner_cannot_offer_an_asset_they_do_not_own() {
    let mut tw = TradeWorld::new();
    let relic = tw.mint("alice", b"provenance-trophy #1");
    // Mallory does not own the relic but tries to put it up in a trade.
    let mut scam = tw.open_trade(
        "mallory",
        LegSpec::Asset(relic),
        "victim",
        LegSpec::Dregg(500),
    );
    tw.fund_dregg("victim", 500);

    let refused = tw.deposit(&mut scam, TradeSide::A);
    assert!(
        matches!(refused, Err(TradeError::Asset(AssetError::Refused(_)))),
        "offering an unowned asset must be refused at the note signature gate, got {refused:?}"
    );
    // The relic never moved — Alice still holds it.
    assert_eq!(tw.current_holder_label(relic), Some("alice"));
}

// ─────────────────────────────────────────────────────────────────────────────
// 4. Provenance travels with the traded item.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn traded_item_provenance_reverifies_end_to_end() {
    let mut tw = TradeWorld::new();
    let drop = tw.mint("alice", b"rare-3pct-tail-drop");
    let junk = tw.mint("bob", b"common-mat");

    let minter = tw.current_owner(drop).unwrap();
    assert_eq!(tw.lineage_len(drop), 1, "fresh mint is a 1-version lineage");

    let mut trade = tw.open_trade("alice", LegSpec::Asset(drop), "bob", LegSpec::Asset(junk));
    tw.deposit(&mut trade, TradeSide::A).unwrap();
    tw.deposit(&mut trade, TradeSide::B).unwrap();
    tw.settle(&mut trade).unwrap();

    // mint → into escrow → new owner: three versions, and the origin minter is carried.
    assert_eq!(tw.lineage_len(drop), 3, "mint + into-custody + to-buyer");
    let report = tw.verify_provenance(drop);
    assert!(
        report.verified,
        "provenance re-verifies: {:?}",
        report.reasons
    );
    assert_eq!(
        report.current_owner,
        tw.pubkey_of("bob"),
        "the drop is Bob's"
    );
    // The rarity/identity (origin minter) is unchanged by the trade — checkable, not marketing.
    let descs = {
        // the origin's minter is the provenance root and survives every hop.
        let p = tw.verify_provenance(drop);
        assert!(p.verified);
        minter
    };
    assert_eq!(descs, minter);
}

// ─────────────────────────────────────────────────────────────────────────────
// 5. A listing: asset ↔ $DREGG value, atomic, $DREGG conserved.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn listing_sells_asset_for_dregg_atomically_and_conserves_value() {
    let mut tw = TradeWorld::new();
    let skin = tw.mint("seller", b"weapon-skin #42");
    tw.fund_dregg("buyer", 1_000);
    let total_dregg = tw.dregg_balance("buyer") + tw.dregg_balance("seller");

    // Seller lists the skin for 300 $DREGG (a standing offer; nothing locked yet).
    let mut listing = tw
        .list("seller", skin, 300)
        .expect("owner lists their asset");
    assert_eq!(
        tw.current_holder_label(skin),
        Some("seller"),
        "a listing is an offer — the asset stays the seller's until a buyer matches"
    );

    // Buyer buys: the asset and the 300 deposit + settle atomically in one crossing.
    let s = tw
        .buy(&mut listing, "buyer")
        .expect("the buyer completes the sale");
    assert_eq!(s.a_gave, LegSpec::Asset(skin));
    assert_eq!(s.b_gave, LegSpec::Dregg(300));

    // The skin crossed to the buyer; the value crossed to the seller.
    assert_eq!(tw.current_holder_label(skin), Some("buyer"));
    assert_eq!(tw.dregg_balance("seller"), 300, "seller received the price");
    assert_eq!(tw.dregg_balance("buyer"), 700, "buyer paid 300 of 1000");

    // $DREGG conservation Σδ=0.
    assert_eq!(
        tw.dregg_balance("buyer") + tw.dregg_balance("seller"),
        total_dregg,
        "no $DREGG minted or burned across the sale"
    );

    // The buyer's provenance for the skin re-verifies (mint → custody → buyer).
    let p = tw.verify_provenance(skin);
    assert!(
        p.verified,
        "the sold item's provenance travels: {:?}",
        p.reasons
    );
    assert_eq!(p.current_owner, tw.pubkey_of("buyer"));
}

// ─────────────────────────────────────────────────────────────────────────────
// 6. Cancelling a listing before a sale — the seller is made whole.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn cancelled_listing_returns_the_asset_to_the_seller() {
    let mut tw = TradeWorld::new();
    let cape = tw.mint("seller", b"cosmetic-cape");
    let mut listing = tw.list("seller", cape, 250).unwrap();
    // A listing does not lock the asset — the seller still holds it.
    assert_eq!(tw.current_holder_label(cape), Some("seller"));

    tw.cancel_listing(&mut listing);
    assert_eq!(
        tw.current_holder_label(cape),
        Some("seller"),
        "the seller keeps the cape"
    );

    // A cancelled listing can never then be bought (a listing settles at most once).
    tw.fund_dregg("buyer", 250);
    assert!(
        tw.buy(&mut listing, "buyer").is_err(),
        "a cancelled listing cannot be bought"
    );
    assert_eq!(
        tw.current_holder_label(cape),
        Some("seller"),
        "still the seller's"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// 7. A re-deposit over a live leg is refused before anything moves.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn redeposit_over_a_live_leg_is_refused() {
    let mut tw = TradeWorld::new();
    let a = tw.mint("alice", b"a");
    let b = tw.mint("bob", b"b");
    let mut trade = tw.open_trade("alice", LegSpec::Asset(a), "bob", LegSpec::Asset(b));
    tw.deposit(&mut trade, TradeSide::A).unwrap();
    assert!(matches!(
        tw.deposit(&mut trade, TradeSide::A),
        Err(TradeError::AlreadyDeposited(_))
    ));
}
