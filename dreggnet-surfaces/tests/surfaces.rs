//! `dreggnet-surfaces`, DRIVEN end-to-end (not named): each of the four features renders a real
//! [`deos_view::ViewNode`] surface (the tree carries the expected Sections/rows/menus), the
//! playable TradeOffering's actions fire REAL trade turns (a listing → a settle; a paid-out buyer
//! is a non-vacuous Refused), and the read-surfaces render populated vs empty state. The 6 Offering
//! verbs are exercised, and `register_surfaces` mounts all four on an OfferingHost (the do-once
//! web/discord/telegram reach).

use deos_view::ViewNode;
use dreggnet_offerings::{Action, DreggIdentity, Offering, OfferingHost, SessionConfig};

use dreggnet_surfaces::companion::TURN_OVERLEVEL;
use dreggnet_surfaces::party::{
    TURN_ACT, TURN_ADVANCE_ENEMY, TURN_CLAIM, TURN_FORK, TURN_LAUNCH, TURN_MISPLAY, TURN_READY,
    TURN_RESOLVE_FORK,
};
use dreggnet_surfaces::{
    CheevoShowcase, CompanionOffering, CraftOffering, GuildPage, InventoryOffering, PartyOffering,
    TavernOffering, TradeOffering, register_surfaces,
};
use dungeon_on_dregg::combat::{WARDEN, is_hero};

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

    // The one interactive move: a Gift action per still-owned note (5), each a real transfer.
    let acts = offering.actions(&s);
    assert_eq!(acts.len(), 5, "a gift action per owned note");
    assert!(acts.iter().all(|a| a.turn == "gift"));

    // GIFT item 0 to a friend — a REAL owner-signed transfer turn (Landed with a receipt).
    let out = offering.advance(&mut s, act("gift", 0), actor());
    assert!(out.landed(), "gifting item 0 lands a real turn: {out:?}");
    assert_eq!(s.held_count(), 4, "one note gifted away");
    assert_eq!(
        s.holder_of(0).as_deref(),
        Some("a friend"),
        "item 0 now held by the friend on the real substrate"
    );
    // Only the 4 still-owned notes remain giftable.
    assert_eq!(
        offering.actions(&s).len(),
        4,
        "the gifted note is no longer giftable"
    );

    // NON-VACUOUS REFUSED — re-gifting a note the player no longer holds is a genuine executor
    // refusal (the signature-vs-owner gate), and nothing crosses.
    let refused = offering.advance(&mut s, act("gift", 0), actor());
    assert!(
        !refused.landed(),
        "a re-gift of an un-held note is refused: {refused:?}"
    );
    assert_eq!(s.held_count(), 4, "the refusal crossed nothing");
    // A wrong verb is a read-only refusal (buy/sell for a price is the market).
    assert!(!offering.advance(&mut s, act("noop", 0), actor()).landed());

    // The gifted note's holder pill renders on the substrate.
    let surface = offering.render(&s);
    let items = find_section(surface.view(), "Items").expect("an Items section");
    assert!(
        pill_with_text(items, "gifted"),
        "a gifted holder pill renders"
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

    // The one interactive move: an Admit action per pending applicant (the demo seeds 2).
    assert_eq!(s.applicant_count(), 2, "two pending applicants");
    let acts = offering.actions(&s);
    assert_eq!(acts.len(), 2, "an admit action per applicant");
    assert!(acts.iter().all(|a| a.turn == "admit"));

    // ADMIT applicant 0 — a REAL cap grant + committed membership turn (Landed with a receipt).
    let out = offering.advance(&mut s, act("admit", 0), actor());
    assert!(
        out.landed(),
        "admitting an applicant lands a real turn: {out:?}"
    );
    assert_eq!(s.roster_len(), 4, "the roster grew by one");
    assert_eq!(s.applicant_count(), 1, "one applicant remains");
    assert_eq!(s.stats().members, 4, "the cap set grew");

    // NON-VACUOUS — the other side of the membership tooth: a stranger (no cap) writing the guild
    // cell is a genuine `CapabilityNotHeld` executor refusal, never a silent apply.
    let refusal = s.stranger_write_refused();
    assert!(
        refusal.is_some(),
        "a non-member's write is refused by the executor: {refusal:?}"
    );

    // A wrong verb / out-of-range applicant is refused.
    assert!(!offering.advance(&mut s, act("noop", 0), actor()).landed());
    assert!(!offering.advance(&mut s, act("admit", 9), actor()).landed());

    // verify re-checks every rostered member (the newly admitted one included) holds the cap.
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
// 5. CraftOffering — a playable forge loop that fires REAL craft turns.
// ═══════════════════════════════════════════════════════════════════════════════════════════

#[test]
fn craft_renders_valid_viewnode_and_forges_consuming_inputs() {
    let offering = CraftOffering::new();
    let mut s = offering.open(SessionConfig::default()).expect("open");

    // The render is a real ViewNode tree with the forge sections.
    let root_surface = offering.render(&s);
    let root = root_surface.view();
    assert!(
        matches!(root, ViewNode::Section { .. }),
        "roots at a Section"
    );
    let mats = find_section(root, "Materials").expect("a Materials section");
    let mrows = first_table(mats).expect("Materials holds a Table");
    assert_eq!(mrows.len(), 8, "header + 7 material rows");
    assert!(
        find_section(root, "Recipes").is_some(),
        "a Recipes menu section"
    );

    // Three recipes from the COMMITTED catalog; Greatblade (3/3) + Charm (2/2) are craftable,
    // Aegis is below floor (2/3 — its `hide:drake` input is not stocked).
    let acts = offering.actions(&s);
    assert_eq!(acts.len(), 3, "three recipes on the bench");
    assert!(
        acts[0].enabled && acts[1].enabled,
        "the fully-stocked recipes are craftable"
    );
    assert!(!acts[2].enabled, "Aegis is below its 3-input typed floor");

    // FORGE recipe 0 (Greatblade, inputs 0+1+2) — a real craft: inputs burned, output minted.
    let out = offering.advance(&mut s, act("craft", 0), actor());
    assert!(out.landed(), "the craft lands a real turn: {out:?}");
    assert_eq!(s.output_count(), 1, "one output forged");
    assert_eq!(
        s.live_material_count(),
        4,
        "three of seven materials consumed"
    );

    // The forged output renders in a Forged table.
    let surface = offering.render(&s);
    assert!(
        find_section(surface.view(), "Forged").is_some(),
        "the forged output renders"
    );

    // NON-VACUOUS REFUSED — re-crafting recipe 0 is refused (its inputs are burned), and a
    // below-floor Aegis is refused (typed floor unmet). Neither mints.
    let reuse = offering.advance(&mut s, act("craft", 0), actor());
    assert!(
        !reuse.landed(),
        "re-crafting consumed inputs is refused: {reuse:?}"
    );
    let below = offering.advance(&mut s, act("craft", 2), actor());
    assert!(!below.landed(), "a below-floor craft is refused: {below:?}");
    assert_eq!(s.output_count(), 1, "the refused crafts minted nothing");

    // A second real craft (Charm, inputs 3+4) still lands — the refusals were non-vacuous.
    let out2 = offering.advance(&mut s, act("craft", 1), actor());
    assert!(out2.landed(), "the Charm craft lands: {out2:?}");
    assert_eq!(s.output_count(), 2, "two outputs forged");

    // verify() re-verifies every output's provenance off the real substrate.
    let report = offering.verify(&s);
    assert!(
        report.verified,
        "the forge chain re-verifies: {}",
        report.detail
    );
    assert!(!offering.price(&act("craft", 0)).is_paid(), "the free tier");
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// 6. CompanionOffering — a playable hatch + collection that fires REAL leveling turns.
// ═══════════════════════════════════════════════════════════════════════════════════════════

#[test]
fn companion_renders_collection_and_hatches_and_raises() {
    let offering = CompanionOffering::demo();
    let mut s = offering.open(SessionConfig::default()).expect("open");
    assert_eq!(s.len(), 1, "the demo seeds one starter companion");

    // The collection renders as a Table (header + 1 companion).
    let surface = offering.render(&s);
    let coll = find_section(surface.view(), "Companions").expect("a Companions section");
    let rows = first_table(coll).expect("the Companions section holds a Table");
    assert_eq!(rows.len(), 2, "header + 1 companion row");
    assert!(
        text_contains(coll, "frostwyrm"),
        "the starter species renders"
    );

    // HATCH a new companion — a real mint + its genesis leveling turn (Landed).
    let out = offering.advance(&mut s, act("hatch", 1), actor());
    assert!(out.landed(), "a hatch mints + lands a real turn: {out:?}");
    assert_eq!(s.len(), 2, "the collection grew by one");
    let new_idx = 1;
    assert_eq!(
        s.level_of(new_idx),
        1,
        "a fresh hatch enters at level 1 (genesis turn)"
    );

    // NON-VACUOUS REFUSED — force-leveling the fresh companion (level 1, 0 XP) past its XP floor is
    // a real gate refusal that commits nothing.
    let refused = offering.advance(&mut s, act(TURN_OVERLEVEL, new_idx as i64), actor());
    assert!(
        !refused.landed(),
        "an un-earned level-up is refused: {refused:?}"
    );
    assert_eq!(s.level_of(new_idx), 1, "anti-ghost: still level 1");

    // The SAME companion RAISEs (earn the floor, then level) — the refusal was non-vacuous.
    let raised = offering.advance(&mut s, act("raise", new_idx as i64), actor());
    assert!(raised.landed(), "a real raise lands: {raised:?}");
    assert_eq!(s.level_of(new_idx), 2, "the companion leveled to 2");

    // verify() re-verifies every companion's owned identity off the substrate.
    assert!(offering.verify(&s).verified, "the companions re-verify");

    // EMPTY — a fresh roost renders the empty-collection state.
    let empty = CompanionOffering::new();
    let es = empty.open(SessionConfig::default()).expect("open");
    assert!(es.is_empty());
    let esurf = empty.render(&es);
    assert!(
        text_contains(esurf.view(), "No companions yet"),
        "empty-state text"
    );
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// 7. TavernOffering — a read-surface posting board (presence + LFG board + party roster).
// ═══════════════════════════════════════════════════════════════════════════════════════════

#[test]
fn tavern_renders_presence_and_lfg_board_populated_and_empty() {
    let offering = TavernOffering::demo("The Salted Tankard");
    let mut s = offering.open(SessionConfig::default()).expect("open");
    assert_eq!(s.patron_count(), 4, "four patrons");
    assert_eq!(s.present_count(), 3, "three present");

    let surface = offering.render(&s);
    let presence = find_section(surface.view(), "Presence").expect("a Presence section");
    let rows = first_table(presence).expect("Presence holds a Table");
    assert_eq!(rows.len(), 5, "header + 4 patron rows");
    assert!(
        pill_with_text(presence, "present"),
        "a present pill renders"
    );
    let board = find_section(surface.view(), "LFG board").expect("an LFG board section");
    assert!(text_contains(board, "LFG the Salt Shore"), "a post renders");
    assert!(
        find_section(surface.view(), "Party").is_some(),
        "the party roster renders"
    );

    // Read-only: advance is a refusal (posts fire on the live tavern node).
    assert!(
        offering.actions(&s).is_empty(),
        "a read-surface has no actions"
    );
    assert!(
        !offering.advance(&mut s, act("post", 0), actor()).landed(),
        "advance is a read-only refusal"
    );
    assert!(offering.verify(&s).verified, "the board is consistent");

    // EMPTY — the empty-hall state.
    let empty = TavernOffering::new("Empty Hall");
    let es = empty.open(SessionConfig::default()).expect("open");
    assert!(es.is_empty());
    assert!(
        text_contains(empty.render(&es).view(), "The hall is empty"),
        "empty-state text"
    );
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// 8. PartyOffering — live formation; identity-bound role action + signed fork ballots.
// ═══════════════════════════════════════════════════════════════════════════════════════════

#[test]
fn party_renders_roster_resolves_a_target_and_fights_in_the_arena() {
    let offering = PartyOffering::new();
    let mut s = offering.open(SessionConfig::default()).expect("open");
    assert_eq!(s.seat_count(), 0, "a new shared table begins as a lobby");

    let surface = offering.render(&s);
    let roster = find_section(surface.view(), "Roster").expect("a Roster section");
    let rows = first_table(roster).expect("Roster holds a Table");
    assert_eq!(rows.len(), 5, "header + four open role rows");

    let players = [
        DreggIdentity("alice".into()),
        DreggIdentity("bob".into()),
        DreggIdentity("carol".into()),
        DreggIdentity("dana".into()),
    ];
    for (idx, player) in players.iter().enumerate() {
        assert!(
            offering
                .advance(&mut s, act(TURN_CLAIM, idx as i64), player.clone())
                .landed(),
            "player claims a distinct role"
        );
        assert!(
            offering
                .advance(&mut s, act(TURN_READY, 0), player.clone())
                .landed(),
            "claimed role readies"
        );
    }
    assert!(
        offering
            .advance(&mut s, act(TURN_LAUNCH, 0), players[0].clone())
            .landed(),
        "the first claimant launches the full ready roster"
    );
    assert!(s.launched());

    // THE COLLECTIVE TARGET — three actual seats cast three individually
    // custody-signed Warden ballots, then the leader resolves the real quorum.
    for player in players.iter().take(3) {
        assert!(
            offering
                .advance(&mut s, act(TURN_FORK, 0), player.clone())
                .landed(),
            "each seat's own signed ballot lands"
        );
    }
    let before_resolve = s.turns();
    let usurped = offering.advance(&mut s, act(TURN_RESOLVE_FORK, 0), players[1].clone());
    assert!(
        !usurped.landed(),
        "a non-leader cannot resolve even a quorum-ready fork: {usurped:?}"
    );
    assert_eq!(s.turns(), before_resolve, "leader refusal is anti-ghost");
    let forked = offering.advance(&mut s, act(TURN_RESOLVE_FORK, 0), players[0].clone());
    assert!(
        forked.landed(),
        "the quorum-certified fork resolves: {forked:?}"
    );
    if let dreggnet_offerings::Outcome::Landed { receipt, .. } = &forked {
        assert_ne!(
            receipt.turn_hash, [0u8; 32],
            "a genuine committed fork turn hash"
        );
    }
    assert_eq!(
        s.last_fork(),
        Some("Warden"),
        "the party concentrates on the crowd's winning target"
    );

    // Initiative is dice-derived. Enemy slots are explicit hosted actions, not
    // render-time side effects, so drive them until a hero is active.
    for _ in 0..4 {
        if s.arena_active().is_some_and(is_hero) {
            break;
        }
        assert!(
            offering
                .advance(&mut s, act(TURN_ADVANCE_ENEMY, 0), players[0].clone(),)
                .landed(),
            "the leader advances the active enemy"
        );
    }

    // Alice's authenticated identity—not the forged arg—selects the Tank cell,
    // and the corresponding guard lands in the real tactical Arena.
    let out = offering.advance(&mut s, act(TURN_ACT, 99), players[0].clone());
    assert!(out.landed(), "the tank's tactical move lands: {out:?}");

    // NON-VACUOUS REFUSED — Bob's cross-role misplay reaches Alice's already
    // spent Tank WriteOnce tooth. Bob can still use Scout when a hero is active.
    let misplay = offering.advance(&mut s, act(TURN_MISPLAY, 0), players[1].clone());
    assert!(
        !misplay.landed(),
        "a cross-role misplay is refused: {misplay:?}"
    );
    for _ in 0..4 {
        if s.arena_active().is_some_and(is_hero) {
            break;
        }
        assert!(
            offering
                .advance(&mut s, act(TURN_ADVANCE_ENEMY, 0), players[0].clone(),)
                .landed()
        );
    }
    let warden_hp_before = s.arena_hp(WARDEN).expect("Warden is in the Arena");
    assert!(
        offering
            .advance(&mut s, act(TURN_ACT, 0), players[1].clone())
            .landed(),
        "the scout's own tactical move lands (the refusal was non-vacuous)"
    );
    assert!(
        s.arena_hp(WARDEN).expect("Warden remains in the Arena") < warden_hp_before,
        "the shared-surface role action changed real tactical HP"
    );

    assert!(
        offering.verify(&s).verified,
        "the party, vote, and Arena worlds re-verify"
    );
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// 9. The do-once web/discord/telegram reach — register_surfaces mounts all EIGHT on an
//    OfferingHost, and each renders its ViewNode surface THROUGH the host seam.
// ═══════════════════════════════════════════════════════════════════════════════════════════

#[test]
fn register_surfaces_mounts_all_eight_on_an_offering_host() {
    let mut host = OfferingHost::new();
    register_surfaces(&mut host);

    let keys = [
        "trade",
        "inventory",
        "cheevos",
        "guild",
        "craft",
        "companion",
        "tavern",
        "party",
    ];
    for key in keys {
        assert!(host.has(key), "`{key}` is registered on the host");
    }

    // Drive a render of each through the host — the do-once ViewNode surface reaches the frontend
    // seam identically (the same tree every renderer walks).
    for key in keys {
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

    // The playable ones fire a real turn through the host seam.
    for (key, action) in [
        ("trade", act("list", 0)),
        ("craft", act("craft", 0)),
        ("companion", act("hatch", 1)),
        ("party", act(TURN_CLAIM, 0)),
    ] {
        let id = host.open(key).expect("open playable");
        let out = host
            .advance(key, &id, action, actor())
            .expect("advance through the host");
        assert!(
            out.landed(),
            "`{key}` fires a real turn through the host: {out:?}"
        );
    }
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// 10. PER-IDENTITY WORLDS — `register_surfaces_for` mounts a world that belongs to ONE player,
//     so two identities' hosts are disjoint ledgers (the fix for one shared "Adventurer").
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// One identity's host: the eight surfaces on a world seeded for `player`.
fn host_for(player: &str) -> OfferingHost {
    let mut host = OfferingHost::new();
    dreggnet_surfaces::register_surfaces_for(&mut host, player);
    host
}

/// Render `key`'s surface as text, for a substring assertion.
fn rendered(host: &OfferingHost, key: &str, id: &dreggnet_offerings::SessionId) -> String {
    format!(
        "{:?}",
        host.render(key, id)
            .unwrap_or_else(|| panic!("`{key}` renders"))
            .view()
    )
}

/// **THE ISOLATION FALSIFIER.** Alice forges a Greatblade in her own world; Bob's inventory does
/// NOT list it. Before the per-identity mount, both stood on the ONE `SharedWorld::demo("Adventurer")`
/// `register_surfaces` built, so every web/Telegram viewer read the same ledger.
#[test]
fn two_identities_worlds_are_isolated() {
    let mut alice = host_for("alice");
    let mut bob = host_for("bob");
    let id = dreggnet_offerings::SessionId::new("primary");

    for host in [&mut alice, &mut bob] {
        host.ensure_open("craft", &id).expect("craft opens");
        host.ensure_open("inventory", &id).expect("inventory opens");
        host.ensure_open("trade", &id).expect("trade opens");
    }

    // Nobody holds a Greatblade — it is never seeded, only forged.
    assert!(!rendered(&alice, "inventory", &id).contains("Greatblade"));
    assert!(!rendered(&bob, "inventory", &id).contains("Greatblade"));

    // Alice forges one (recipe 0 — the safe Greatblade bench).
    let out = alice
        .advance("craft", &id, act("craft", 0), actor())
        .expect("alice's craft is live");
    assert!(out.landed(), "the greatblade craft lands: {out:?}");

    // Her OWN composition still holds: the note is in her inventory and listable on her stall.
    assert!(
        rendered(&alice, "inventory", &id).contains("Greatblade"),
        "alice's forged note is on her own shelf (one ledger per identity, no re-mint)"
    );
    assert!(
        alice
            .actions("trade", &id)
            .expect("live")
            .iter()
            .any(|a| a.turn == "list" && a.label.contains("Greatblade") && a.enabled),
        "alice can list what alice forged"
    );

    // …and BOB sees nothing of it — a disjoint world, forge, ledger and registry.
    let bob_inventory = rendered(&bob, "inventory", &id);
    assert!(
        !bob_inventory.contains("Greatblade"),
        "bob's inventory holds no note alice forged: {bob_inventory}"
    );
    assert!(
        !bob.actions("trade", &id)
            .expect("live")
            .iter()
            .any(|a| a.label.contains("Greatblade")),
        "bob cannot list a note alice forged"
    );
}

/// The shelf each world keys on is the VIEWER's label, not a shared `"Adventurer"` — the per-identity
/// world renders the identity it was mounted for, and the anonymous mount still renders the demo one.
#[test]
fn a_per_identity_world_carries_the_viewers_own_label() {
    let id = dreggnet_offerings::SessionId::new("primary");
    let mut carol = host_for("carol");
    carol.ensure_open("inventory", &id).expect("opens");
    let text = rendered(&carol, "inventory", &id);
    assert!(text.contains("carol"), "carol's own shelf label: {text}");
    assert!(
        !text.contains(dreggnet_surfaces::DEMO_PLAYER),
        "the shared demo label is gone from an identified world: {text}"
    );

    // The anonymous path is explicit and still works (a single-player demo host).
    let mut demo = OfferingHost::new();
    register_surfaces(&mut demo);
    demo.ensure_open("inventory", &id).expect("opens");
    assert!(rendered(&demo, "inventory", &id).contains(dreggnet_surfaces::DEMO_PLAYER));
}
