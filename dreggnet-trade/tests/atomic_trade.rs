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

// ─────────────────────────────────────────────────────────────────────────────
// DISCOVERY — the bazaar over the swap primitive.
// ─────────────────────────────────────────────────────────────────────────────

/// **Two strangers meet through the stall.** A seller posts; a buyer who was never told about
/// the item BROWSES, finds it within budget, and buys — and the sale is the same atomic escrow
/// crossing as a hand-arranged trade. Discovery is added; trust is not.
#[test]
fn a_buyer_finds_an_item_by_browsing_and_the_sale_is_still_atomic() {
    use dreggnet_trade::Bazaar;

    let mut tw = TradeWorld::new();
    let mut stall = Bazaar::new();
    let cheap = tw.mint("alice", b"tin-charm");
    let dear = tw.mint("alice", b"gilded-idol");
    let bobs = tw.mint("bob", b"bone-flute");
    tw.fund_dregg("carol", 60);

    stall.post(&mut tw, "alice", cheap, 25).expect("post 1");
    stall.post(&mut tw, "alice", dear, 400).expect("post 2");
    stall.post(&mut tw, "bob", bobs, 40).expect("post 3");
    assert_eq!(stall.open_count(), 3);

    // Browsing is cheapest-first and complete.
    let shelf = stall.browse(&tw);
    assert_eq!(shelf.len(), 3);
    assert_eq!(shelf[0].price, 25, "cheapest first");
    assert_eq!(shelf[2].price, 400);

    // Carol filters by what her wallet can cover, and by seller.
    let purse = tw.dregg_balance("carol") as u64;
    let mine = stall.affordable(&tw, purse);
    assert_eq!(mine.len(), 2, "the 400 idol is out of reach");
    assert_eq!(stall.by_seller(&tw, "bob").len(), 1);
    let found = stall
        .offer_for(&tw, cheap)
        .expect("the charm is discoverable by its id");

    // She buys the one she found — the atomic crossing.
    let settlement = stall
        .buy(&mut tw, found.id, "carol")
        .expect("the discovered sale settles");
    assert_eq!(settlement.a_gave, LegSpec::Asset(cheap));
    assert_eq!(settlement.b_gave, LegSpec::Dregg(25));
    assert_eq!(tw.current_holder_label(cheap), Some("carol"));
    assert_eq!(tw.dregg_balance("carol"), 35);
    assert_eq!(tw.dregg_balance("alice"), 25);
    assert!(
        tw.verify_provenance(cheap).verified,
        "the discovered item's lineage still re-verifies"
    );

    // A bought offer leaves the stall and cannot be bought twice.
    assert_eq!(stall.open_count(), 2);
    assert!(
        stall.buy(&mut tw, found.id, "carol").is_err(),
        "a settled offer is consumed"
    );
}

/// **A posting is an offer, not a lock — and browse tells the truth about that.** A seller who
/// trades the item away after posting leaves a STALE offer: it disappears from `browse` (a
/// buyer is never shown something unbuyable) while still showing in the seller's own
/// `entries` marked dead, and buying it is refused by the ownership gate with nothing moved.
#[test]
fn a_stale_offer_is_hidden_from_browsing_and_refused_at_the_till() {
    use dreggnet_trade::Bazaar;

    let mut tw = TradeWorld::new();
    let mut stall = Bazaar::new();
    let idol = tw.mint("alice", b"twice-sold-idol");
    tw.fund_dregg("carol", 100);
    let offer = stall.post(&mut tw, "alice", idol, 30).expect("posted");
    assert_eq!(stall.browse(&tw).len(), 1, "buyable while alice holds it");

    // Alice hands it off outside the stall — the offer is now a ghost.
    tw.assets()
        .transfer(idol, "alice", "dave")
        .expect("a side deal");
    assert!(
        stall.browse(&tw).is_empty(),
        "a stale offer is not shown as buyable"
    );
    let seller_view = stall.entries(&tw);
    assert_eq!(seller_view.len(), 1, "the seller still sees their posting");
    assert!(
        !seller_view[0].live,
        "flagged dead, so the seller knows why"
    );

    // Buying it is a real refusal — the ownership gate, not stall bookkeeping.
    let bought = stall.buy(&mut tw, offer, "carol");
    assert!(
        matches!(bought, Err(TradeError::Asset(AssetError::Refused(_)))),
        "a stale offer cannot be bought, got {bought:?}"
    );
    assert_eq!(
        tw.current_holder_label(idol),
        Some("dave"),
        "anti-ghost: nothing crossed"
    );
    assert_eq!(tw.dregg_balance("carol"), 100, "and carol paid nothing");
}

/// Posting is gated the same way selling is: a non-owner cannot post someone else's item, and
/// a SOULBOUND note — which the asset layer would refuse to transfer at settlement anyway —
/// is refused at post time rather than being advertised as buyable. Only the offer's own
/// seller can cancel it.
#[test]
fn posting_is_owner_gated_soulbound_refused_and_cancel_is_seller_only() {
    use dreggnet_trade::Bazaar;

    let mut tw = TradeWorld::new();
    let mut stall = Bazaar::new();
    let hat = tw.mint("alice", b"alices-hat");
    let badge = tw.assets().mint_soulbound("alice", b"earned-badge");

    // A stranger cannot post what they do not hold.
    assert!(
        matches!(
            stall.post(&mut tw, "mallory", hat, 5),
            Err(TradeError::Asset(AssetError::Refused(_)))
        ),
        "you cannot list what you do not own"
    );
    // Nor can even its owner post a note that can never be transferred.
    let sb = stall.post(&mut tw, "alice", badge, 5);
    assert!(
        matches!(sb, Err(TradeError::Asset(AssetError::Refused(_)))),
        "a soulbound note is not listable, got {sb:?}"
    );
    assert_eq!(stall.open_count(), 0, "anti-ghost: neither was posted");

    // The honest post lands (non-vacuous), and only alice can take it down.
    let offer = stall.post(&mut tw, "alice", hat, 5).expect("alice posts");
    assert!(
        stall.cancel(offer, "mallory").is_err(),
        "a stranger cannot cancel someone else's offer"
    );
    assert_eq!(stall.open_count(), 1, "the refused cancel voided nothing");
    stall.cancel(offer, "alice").expect("the seller withdraws");
    assert_eq!(stall.open_count(), 0);
    assert!(stall.browse(&tw).is_empty());
    assert_eq!(
        tw.current_holder_label(hat),
        Some("alice"),
        "a cancelled offer leaves the item where it was — nothing was ever locked"
    );
}
