//! `dreggnet-surfaces`, DRIVEN end-to-end (not named): each of the four features renders a real
//! [`deos_view::ViewNode`] surface (the tree carries the expected Sections/rows/menus), the
//! playable TradeOffering's actions fire REAL trade turns (a listing → a settle; a paid-out buyer
//! is a non-vacuous Refused), and the read-surfaces render populated vs empty state. The 6 Offering
//! verbs are exercised, and `register_surfaces` mounts all four on an OfferingHost (the do-once
//! web/discord/telegram reach).

use deos_view::ViewNode;
use dreggnet_offerings::{Action, DreggIdentity, Offering, OfferingHost, SessionConfig};

use dreggnet_surfaces::{
    CheevoShowcase, GuildPage, InventoryOffering, TradeOffering, register_surfaces,
};

// ── ViewNode-walk assertion helpers ──────────────────────────────────────────────────────────

/// Find a `Section` with the given title anywhere in the tree.
fn find_section<'a>(node: &'a ViewNode, title: &str) -> Option<&'a ViewNode> {
    match node {
        ViewNode::Section {
            title: t, children, ..
        } => {
            if t == title {
                return Some(node);
            }
            children.iter().find_map(|c| find_section(c, title))
        }
        ViewNode::VStack(cs)
        | ViewNode::Row(cs)
        | ViewNode::List(cs)
        | ViewNode::Table(cs)
        | ViewNode::Grid { children: cs, .. } => cs.iter().find_map(|c| find_section(c, title)),
        _ => None,
    }
}

/// The first `Table` among a node's children (recursively).
fn first_table(node: &ViewNode) -> Option<&Vec<ViewNode>> {
    match node {
        ViewNode::Table(rows) => Some(rows),
        ViewNode::Section { children, .. }
        | ViewNode::VStack(children)
        | ViewNode::Row(children)
        | ViewNode::List(children)
        | ViewNode::Grid { children, .. } => children.iter().find_map(first_table),
        _ => None,
    }
}

/// Count the `Menu` rows anywhere under a node.
fn menu_item_count(node: &ViewNode) -> usize {
    match node {
        ViewNode::Menu { items } => items.len(),
        ViewNode::Section { children, .. }
        | ViewNode::VStack(children)
        | ViewNode::Row(children)
        | ViewNode::List(children)
        | ViewNode::Table(children)
        | ViewNode::Grid { children, .. } => children.iter().map(menu_item_count).sum(),
        _ => 0,
    }
}

/// Whether any `Pill` under the node has text containing `needle`.
fn pill_with_text(node: &ViewNode, needle: &str) -> bool {
    match node {
        ViewNode::Pill { text, .. } => text.contains(needle),
        ViewNode::Section { children, .. }
        | ViewNode::VStack(children)
        | ViewNode::Row(children)
        | ViewNode::List(children)
        | ViewNode::Table(children)
        | ViewNode::Grid { children, .. } => children.iter().any(|c| pill_with_text(c, needle)),
        _ => false,
    }
}

/// Whether any `Text` under the node contains `needle`.
fn text_contains(node: &ViewNode, needle: &str) -> bool {
    match node {
        ViewNode::Text(s) => s.contains(needle),
        ViewNode::Section { children, .. }
        | ViewNode::VStack(children)
        | ViewNode::Row(children)
        | ViewNode::List(children)
        | ViewNode::Table(children)
        | ViewNode::Grid { children, .. } => children.iter().any(|c| text_contains(c, needle)),
        _ => false,
    }
}

fn actor() -> DreggIdentity {
    DreggIdentity("driver".to_string())
}

fn act(turn: &str, arg: i64) -> Action {
    Action::new(turn, turn, arg, true)
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// 1. TradeOffering — a playable market #2 that fires REAL trade turns.
// ═══════════════════════════════════════════════════════════════════════════════════════════

#[test]
fn trade_renders_valid_viewnode_and_fires_a_listing_to_a_settle() {
    let offering = TradeOffering::new();
    let mut s = offering.open(SessionConfig::default()).expect("open");

    // The render is a real ViewNode tree with the expected sections.
    let surface = offering.render(&s);
    let root = surface.view();
    assert!(
        matches!(root, ViewNode::Section { .. }),
        "the trade surface roots at a Section"
    );
    assert!(
        find_section(
            root,
            "DreggNet Trade — a player market (atomic asset swaps)"
        )
        .is_some(),
        "the market title section is present"
    );
    // The goods overview is a Table with a header + a row per good (3 goods).
    let goods = find_section(root, "Goods").expect("a Goods section");
    let goods_rows = first_table(goods).expect("the Goods section holds a Table");
    assert_eq!(goods_rows.len(), 4, "header + 3 goods rows");

    // Initially every good is in stock → three List actions, no listings.
    let acts = offering.actions(&s);
    assert_eq!(acts.len(), 3, "three List actions at open");
    assert!(acts.iter().all(|a| a.turn == "list"));

    // LIST good 0 — a REAL owner-signed transfer turn (Landed with a receipt).
    let out = offering.advance(&mut s, act("list", 0), actor());
    assert!(out.landed(), "listing good 0 lands a real turn: {out:?}");
    assert_eq!(s.turns(), 1, "one committed turn");
    assert_eq!(s.listed_count(), 1, "good 0 is now in custody");

    // The listing now shows as a Section{Menu} of buyable rows.
    let surface = offering.render(&s);
    let listings = find_section(surface.view(), "Open listings").expect("an Open listings section");
    assert_eq!(menu_item_count(listings), 1, "one open listing (a buy row)");

    // BUY good 0 (price 2, buyer has 3 coins) — a SETTLE: coins cross to the seller, the good
    // crosses custody → buyer. A real atomic swap that Lands.
    let out = offering.advance(&mut s, act("buy", 0), actor());
    assert!(out.landed(), "the settle lands a real turn: {out:?}");
    assert_eq!(s.sold_count(), 1, "good 0 sold to the buyer");
    assert_eq!(
        s.coin_balance(),
        1,
        "2 of 3 coins spent on the price-2 good"
    );
    assert_eq!(
        s.holder_of(0).as_deref(),
        Some("buyer"),
        "the good is now held by the buyer on the real substrate"
    );

    // The goods table now marks good 0 sold (a `sold` status Pill).
    let surface = offering.render(&s);
    let goods = find_section(surface.view(), "Goods").expect("a Goods section");
    assert!(
        pill_with_text(goods, "sold"),
        "good 0 shows a `sold` status pill"
    );

    // A second full listing→settle (good 1, price 1) — drains the last coin.
    assert!(offering.advance(&mut s, act("list", 1), actor()).landed());
    assert!(offering.advance(&mut s, act("buy", 1), actor()).landed());
    assert_eq!(s.coin_balance(), 0, "the buyer is now paid out");

    // NON-VACUOUS REFUSED — list good 2, then a buy the paid-out buyer cannot afford is a real
    // refusal (driven through a genuine already-spent-coin executor rejection), and the good is
    // NOT crossed (no half-open trade).
    assert!(offering.advance(&mut s, act("list", 2), actor()).landed());
    let refused = offering.advance(&mut s, act("buy", 2), actor());
    assert!(!refused.landed(), "the paid-out buyer cannot settle");
    match refused {
        dreggnet_offerings::Outcome::Refused(why) => {
            assert!(
                why.contains("cannot pay") || why.contains("trade-coin"),
                "non-vacuous: {why}"
            );
        }
        other => panic!("expected a Refused, got {other:?}"),
    }
    assert_eq!(
        s.sold_count(),
        2,
        "good 2 did NOT sell (the refusal crossed nothing)"
    );
    assert_eq!(
        s.holder_of(2).as_deref(),
        Some("market-custodian"),
        "good 2 is still safely in custody"
    );

    // verify() re-verifies every good's provenance + current holder off the real substrate.
    let report = offering.verify(&s);
    assert!(
        report.verified,
        "the trade chain re-verifies: {}",
        report.detail
    );

    // price() is the free tier (the substrate turns are free + verifiable).
    assert!(!offering.price(&act("buy", 0)).is_paid());
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// 2. InventoryOffering — a read-surface, populated vs empty.
// ═══════════════════════════════════════════════════════════════════════════════════════════

#[test]
fn inventory_renders_owned_notes_as_a_table_populated_and_empty() {
    // POPULATED — five owned notes render as a Table (header + 5 rows).
    let offering = InventoryOffering::demo("Adventurer");
    let mut s = offering.open(SessionConfig::default()).expect("open");
    assert_eq!(s.len(), 5, "five demo notes minted");

    let surface = offering.render(&s);
    let items = find_section(surface.view(), "Items").expect("an Items section");
    let rows = first_table(items).expect("the Items section holds a Table");
    assert_eq!(rows.len(), 6, "header + 5 item rows");
    assert!(text_contains(items, "Ember Cloak"), "a named item renders");

    // The read-surface exposes no moves; advance is a read-only refusal.
    assert!(
        offering.actions(&s).is_empty(),
        "a read-surface has no actions"
    );
    assert!(
        !offering.advance(&mut s, act("noop", 0), actor()).landed(),
        "advance is a read-only refusal"
    );

    // verify() re-verifies every note's provenance off the substrate.
    let report = offering.verify(&s);
    assert!(report.verified, "provenance re-verifies: {}", report.detail);
    assert_eq!(report.turns, 5);

    // EMPTY — the empty-state surface shows the "no items" text, no table.
    let empty = InventoryOffering::new("Newcomer");
    let es = empty.open(SessionConfig::default()).expect("open");
    assert!(es.is_empty());
    let esurf = empty.render(&es);
    let eitems = find_section(esurf.view(), "Items").expect("an Items section");
    assert!(text_contains(eitems, "No items owned"), "empty state text");
    assert!(first_table(eitems).is_none(), "no table in the empty state");
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// 3. CheevoShowcase — a read-surface over REAL earned soulbound achievements.
// ═══════════════════════════════════════════════════════════════════════════════════════════

#[test]
fn cheevo_showcase_renders_earned_achievements_populated_and_empty() {
    // POPULATED — the demo earns REAL cheevos from a genuine verified descent run.
    let offering = CheevoShowcase::demo();
    let mut s = offering.open(SessionConfig::default()).expect("open");
    assert_eq!(
        s.len(),
        2,
        "two real cheevos earned (reached-depth + speed)"
    );

    let surface = offering.render(&s);
    let ach = find_section(surface.view(), "Achievements").expect("an Achievements section");
    let rows = first_table(ach).expect("the Achievements section holds a Table");
    assert_eq!(rows.len(), 3, "header + 2 earned rows");
    assert!(text_contains(ach, "Ada"), "the earner renders");
    assert!(
        text_contains(ach, "reached depth 3") || text_contains(ach, "won in"),
        "the witness (why) renders"
    );

    // Read-only; the seal-integrity verify passes for genuine earned cheevos.
    assert!(offering.actions(&s).is_empty());
    assert!(!offering.advance(&mut s, act("noop", 0), actor()).landed());
    assert!(
        offering.verify(&s).verified,
        "the earned cheevos are seal-intact"
    );

    // EMPTY — the empty-state surface.
    let empty = CheevoShowcase::empty();
    let es = empty.open(SessionConfig::default()).expect("open");
    let esurf = empty.render(&es);
    assert!(
        text_contains(esurf.view(), "No achievements earned"),
        "empty state text"
    );
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// 4. GuildPage — a read-surface over the roster + the aggregate verified-clears leaderboard.
// ═══════════════════════════════════════════════════════════════════════════════════════════

#[test]
fn guild_page_renders_roster_and_verified_clears_leaderboard() {
    // POPULATED — three members admitted via real cap grants + one genuine verified clear.
    let offering = GuildPage::demo("The Iron Wardens");
    let mut s = offering.open(SessionConfig::default()).expect("open");
    assert_eq!(s.roster_len(), 3, "three members admitted");
    let stats = s.stats();
    assert_eq!(stats.members, 3, "the cap set has three members");
    assert!(
        stats.verified_clears >= 1,
        "at least one real verified clear counted"
    );
    assert_eq!(stats.survivors, 3, "three live-character survivors");

    let surface = offering.render(&s);
    let roster = find_section(surface.view(), "Roster").expect("a Roster section");
    let rows = first_table(roster).expect("the Roster holds a Table");
    assert_eq!(rows.len(), 4, "header + 3 member rows");
    assert!(text_contains(roster, "Aria"), "a member renders");
    let board = find_section(surface.view(), "Leaderboard (aggregate proven)")
        .expect("a Leaderboard section");
    assert!(
        text_contains(board, "Verified clears"),
        "the aggregate renders"
    );

    // Read-only; verify re-checks every member genuinely holds the guild cap.
    assert!(offering.actions(&s).is_empty());
    assert!(!offering.advance(&mut s, act("noop", 0), actor()).landed());
    assert!(
        offering.verify(&s).verified,
        "every rostered member holds the cap"
    );

    // EMPTY — the empty-state surface.
    let empty = GuildPage::new("Nascent Order");
    let es = empty.open(SessionConfig::default()).expect("open");
    assert!(es.is_empty());
    let esurf = empty.render(&es);
    let eroster = find_section(esurf.view(), "Roster").expect("a Roster section");
    assert!(text_contains(eroster, "No members yet"), "empty state text");
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// 5. The do-once web/discord/telegram reach — register_surfaces mounts all four on an
//    OfferingHost, and each renders its ViewNode surface THROUGH the host seam.
// ═══════════════════════════════════════════════════════════════════════════════════════════

#[test]
fn register_surfaces_mounts_the_four_on_an_offering_host() {
    let mut host = OfferingHost::new();
    register_surfaces(&mut host);

    for key in ["trade", "inventory", "cheevos", "guild"] {
        assert!(host.has(key), "`{key}` is registered on the host");
    }

    // Drive a render of each through the host — the do-once ViewNode surface reaches the frontend
    // seam identically (the same tree every renderer walks).
    for key in ["trade", "inventory", "cheevos", "guild"] {
        let id = host.open(key).expect("open a session through the host");
        let surface = host.render(key, &id).expect("the host renders the surface");
        assert!(
            matches!(surface.view(), ViewNode::Section { .. }),
            "`{key}` renders a Section-rooted ViewNode surface"
        );
        assert!(
            host.verify(key, &id).is_some(),
            "`{key}` verifies through the host"
        );
    }

    // The playable one fires a real turn through the host: list good 0 lands.
    let id = host.open("trade").expect("open trade");
    let out = host
        .advance("trade", &id, act("list", 0), actor())
        .expect("advance through the host");
    assert!(
        out.landed(),
        "a real trade turn fires through the host seam: {out:?}"
    );
}
