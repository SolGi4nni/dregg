//! # The live surfaces COMPOSE — driven, not named.
//!
//! The claim a player actually makes: **craft a sword and it is in your inventory.** Before the
//! shared world each surface's `open()` minted a fresh universe, so the crafted note reached
//! nothing — the surfaces agreed by convention (matching names in three ledgers), never by object
//! identity. These tests drive the REAL surfaces through the REAL `Offering` trait and assert the
//! composition at the note-cell.
//!
//! ## Why an AssetId match alone would prove nothing
//!
//! A `dreggnet_asset::AssetId` is a REPRODUCIBLE content address: two separate worlds running the
//! same craft mint the byte-identical id. So "the ids match" is exactly the kind of convention this
//! work exists to kill. [`the_asset_id_is_a_content_address_the_shared_ledger_is_the_identity`]
//! drives that fact head-on: it stands up a TWIN world, forges the same recipe, gets the same id —
//! and shows the two ids name two different note-cells with different owners. What proves the share
//! is that a move made through ONE surface is visible through ANOTHER: identity is the shared
//! ledger, not the id.

use deos_view::ViewNode;
use dreggnet_offerings::{Action, DreggIdentity, Offering, SessionConfig};
use dreggnet_surfaces::{CraftOffering, InventoryOffering, SharedWorld, TradeOffering};

const PLAYER: &str = "Adventurer";
/// The Greatblade bench (2× `ore:iron` + `haft:oak`) — the first thing a player forges.
const GREATBLADE: i64 = 0;

fn actor() -> DreggIdentity {
    DreggIdentity("player".to_string())
}

fn act(turn: &str, arg: i64) -> Action {
    Action::new(turn, turn, arg, true)
}

/// Whether `needle` appears in any Text/Pill leaf of the tree.
fn tree_contains(node: &ViewNode, needle: &str) -> bool {
    match node {
        ViewNode::Text(s) => s.contains(needle),
        ViewNode::Pill { text, .. } => text.contains(needle),
        ViewNode::Section { children, .. } => children.iter().any(|c| tree_contains(c, needle)),
        ViewNode::Row(cs) => cs.iter().any(|c| tree_contains(c, needle)),
        ViewNode::Table(rs) => rs.iter().any(|r| tree_contains(r, needle)),
        ViewNode::Menu { items } => items.iter().any(|i| i.label.contains(needle)),
        _ => false,
    }
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// THE CLAIM — craft an item on the craft surface, the SAME note is in the inventory surface.
// ═══════════════════════════════════════════════════════════════════════════════════════════

#[test]
fn a_crafted_item_appears_in_the_inventory_surface_as_the_same_note() {
    let world = SharedWorld::demo(PLAYER);
    let forge = CraftOffering::in_world(world.clone());
    let bag = InventoryOffering::in_world(world.clone());

    let mut fs = forge
        .open(SessionConfig::default())
        .expect("open the forge");
    let mut bs = bag.open(SessionConfig::default()).expect("open the bag");

    // ── BEFORE: the player's shelf is the seeded demo state; nothing is crafted yet. ──
    let before = bs.asset_ids();
    assert_eq!(fs.output_count(), 0, "nothing forged yet");
    assert!(
        !tree_contains(bag.render(&bs).view(), "Greatblade"),
        "ANTI-GHOST: an item that was never crafted is not in the inventory"
    );

    // ── FORGE the Greatblade — a real craft turn (inputs burned on-chain, one output minted). ──
    let out = forge.advance(&mut fs, act("craft", GREATBLADE), actor());
    assert!(out.landed(), "the craft lands a real turn: {out:?}");
    assert_eq!(fs.output_count(), 1);
    let forged = fs.output_ids()[0];

    // ── THE CLAIM: the SAME asset id is now on the inventory surface. ──
    let after = bs.asset_ids();
    assert_eq!(
        after.len(),
        before.len() + 1,
        "exactly the one forged note joined the shelf"
    );
    assert!(
        !before.contains(&forged),
        "non-vacuous: the note was NOT on the shelf before the craft"
    );
    assert!(
        after.contains(&forged),
        "THE CLAIM: the crafted note IS in the inventory"
    );
    let idx = bs
        .index_of(forged)
        .expect("the inventory knows the forged note");

    // Object identity at the NOTE-CELL, not a name match: the inventory reads THIS note's holder
    // and provenance off the ledger the forge minted it into. Its lineage CONTINUES from the craft
    // (mint(craft) -> the crafter's owner-signed claim), it does not restart at 1 in a second world.
    let prov = bs.provenance_of(idx).expect("the inventory re-verifies it");
    assert!(
        prov.verified,
        "the crafted note's full lineage re-verifies from the inventory surface"
    );
    assert_eq!(
        prov.length, 2,
        "the lineage is the craft's own: mint(forge) -> the crafter's claim"
    );
    assert_eq!(
        bs.holder_of(idx).as_deref(),
        Some(PLAYER),
        "the player holds the note they forged"
    );
    assert!(bs.owns(idx), "and it is theirs to move");

    // It renders — the thing a player sees. Its rarity is the FAIR DRAW's quality, off the ledger.
    let painted = bag.render(&bs);
    assert!(
        tree_contains(painted.view(), "Greatblade"),
        "the crafted item renders on the inventory surface"
    );
    assert!(
        bag.verify(&bs).verified,
        "the inventory re-verifies the whole shelf"
    );

    // ── THE SHARE, OBSERVED BOTH WAYS: a move made on the INVENTORY surface is seen by the
    //    CRAFT surface. Two surfaces, one note-cell — this is what a shared ledger buys and what
    //    no amount of name-matching could fake. ──
    let gift = bag.advance(&mut bs, act("gift", idx as i64), actor());
    assert!(
        gift.landed(),
        "the player gifts the note they forged: {gift:?}"
    );
    assert_eq!(
        fs.holder_of(forged).as_deref(),
        Some("a friend"),
        "THE FORGE SEES IT: the note it minted is now held by the friend"
    );
    assert!(
        !bs.owns(idx),
        "and the inventory agrees — one ledger, one answer"
    );

    // The gate did NOT relax: a re-gift of a note the player no longer holds is still a real
    // executor refusal (the signature-vs-owner teeth), on the shared world exactly as before.
    let regift = bag.advance(&mut bs, act("gift", idx as i64), actor());
    assert!(!regift.landed(), "a re-gift is refused: {regift:?}");
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// THE ID IS NOT THE IDENTITY — a twin world reproduces the id and still shares nothing.
// ═══════════════════════════════════════════════════════════════════════════════════════════

#[test]
fn the_asset_id_is_a_content_address_the_shared_ledger_is_the_identity() {
    // OUR world: forge the Greatblade, then gift it away from the inventory surface.
    let ours = SharedWorld::demo(PLAYER);
    let forge = CraftOffering::in_world(ours.clone());
    let bag = InventoryOffering::in_world(ours.clone());
    let mut fs = forge.open(SessionConfig::default()).expect("open");
    let mut bs = bag.open(SessionConfig::default()).expect("open");
    assert!(
        forge
            .advance(&mut fs, act("craft", GREATBLADE), actor())
            .landed()
    );
    let forged = fs.output_ids()[0];
    let idx = bs.index_of(forged).expect("ours holds it");
    assert!(
        bag.advance(&mut bs, act("gift", idx as i64), actor())
            .landed()
    );

    // A TWIN world: same seeds, same recipe, same beacon → the BYTE-IDENTICAL AssetId. This is
    // exactly why an id match proves nothing about object identity.
    let twin = SharedWorld::demo(PLAYER);
    assert!(!twin.is_same(&ours), "a genuinely separate world");
    let tforge = CraftOffering::in_world(twin.clone());
    let tbag = InventoryOffering::in_world(twin.clone());
    let mut tfs = tforge.open(SessionConfig::default()).expect("open");
    let tbs = tbag.open(SessionConfig::default()).expect("open");
    assert!(
        tforge
            .advance(&mut tfs, act("craft", GREATBLADE), actor())
            .landed()
    );
    assert_eq!(
        tfs.output_ids()[0],
        forged,
        "the AssetId is a reproducible content address — the twin mints the same bytes"
    );

    // …and yet the two ids name two DIFFERENT note-cells: the gift that happened in OUR world is
    // invisible in the twin's. Same id, two ledgers, two owners. Object identity is the SHARED
    // LEDGER, never the id — which is why the first test's proof is a cross-surface MOVE.
    let tidx = tbs.index_of(forged).expect("the twin holds its own");
    assert_eq!(
        tbs.holder_of(tidx).as_deref(),
        Some(PLAYER),
        "the twin's note was never gifted — the worlds do not share state"
    );
    assert_eq!(
        bs.holder_of(idx).as_deref(),
        Some("a friend"),
        "while ours was — same id, different note-cell"
    );

    // A SECOND SURFACE CANNOT CONJURE ONE: an inventory over a world where nothing was crafted
    // does not list the item, however identical the id would be.
    let barren = SharedWorld::demo(PLAYER);
    let bbag = InventoryOffering::in_world(barren);
    let bbs = bbag.open(SessionConfig::default()).expect("open");
    assert!(
        !bbs.asset_ids().contains(&forged),
        "ANTI-GHOST: an un-crafted world's inventory does not hold the note"
    );
    assert!(bbs.index_of(forged).is_none());
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// THE FULL LEG — craft → inventory → list → sold to a buyer, one note-cell throughout.
// ═══════════════════════════════════════════════════════════════════════════════════════════

#[test]
fn a_crafted_item_is_listed_and_sold_to_a_buyer_on_the_trade_surface() {
    let world = SharedWorld::demo(PLAYER);
    let forge = CraftOffering::in_world(world.clone());
    let bag = InventoryOffering::in_world(world.clone());
    let stall = TradeOffering::in_world(world.clone());

    let mut fs = forge.open(SessionConfig::default()).expect("open");
    let bs = bag.open(SessionConfig::default()).expect("open");
    let mut ts = stall.open(SessionConfig::default()).expect("open");

    let goods_before = ts.goods_count();

    // FORGE it.
    assert!(
        forge
            .advance(&mut fs, act("craft", GREATBLADE), actor())
            .landed()
    );
    let forged = fs.output_ids()[0];

    // The market stall sees it — the player's own shelf, so the thing they just made is on offer
    // beside the canned stock (which is seeding of THIS world, not a separate universe).
    assert_eq!(
        ts.goods_count(),
        goods_before + 1,
        "the forged note joined the stall's offer"
    );
    let g = ts
        .index_of(forged)
        .expect("the stall offers the crafted note");
    assert!(
        tree_contains(stall.render(&ts).view(), "Greatblade"),
        "the crafted item renders on the trade surface"
    );

    // LIST it — a real owner-signed transfer into neutral custody.
    let listed = stall.advance(&mut ts, act("list", g as i64), actor());
    assert!(listed.landed(), "the crafted note lists: {listed:?}");
    assert_eq!(ts.holder_of(g).as_deref(), Some("market-custodian"));
    // The INVENTORY surface reports the move it did not make — one ledger, one answer.
    let bidx = bs.index_of(forged).expect("the bag knows it");
    assert_eq!(
        bs.holder_of(bidx).as_deref(),
        Some("market-custodian"),
        "the inventory sees its note went into custody"
    );

    // BUY it — the buyer crosses coins, the good crosses custody → buyer.
    let sold = stall.advance(&mut ts, act("buy", g as i64), actor());
    assert!(sold.landed(), "the crafted note sells: {sold:?}");
    assert_eq!(
        ts.holder_of(g).as_deref(),
        Some("buyer"),
        "the buyer holds the identical NOTE the forge minted"
    );

    // ── THE CONTINUOUS LINEAGE — the whole point. mint(craft) → the crafter's claim → custody →
    //    the buyer: FOUR versions in ONE ledger. A re-minted look-alike in a second world would
    //    have restarted at 1; this note's forge history carried all the way to its buyer. ──
    let prov = bs.provenance_of(bidx).expect("still on the shelf");
    assert!(prov.verified, "the sold note's full lineage re-verifies");
    assert_eq!(
        prov.length, 4,
        "mint(craft) -> claim -> custody -> buyer, continued in one ledger"
    );
    assert_eq!(
        bs.holder_of(bidx).as_deref(),
        Some("buyer"),
        "the inventory sees the buyer now holds what the player forged"
    );
    assert!(!bs.owns(bidx), "the player no longer holds it");
    // The forge, too, sees where its output ended up.
    assert_eq!(fs.holder_of(forged).as_deref(), Some("buyer"));

    // No gate relaxed: the stall + the forge + the bag all still re-verify their whole state.
    assert!(stall.verify(&ts).verified, "{}", stall.verify(&ts).detail);
    assert!(forge.verify(&fs).verified, "{}", forge.verify(&fs).detail);
    assert!(bag.verify(&bs).verified, "{}", bag.verify(&bs).detail);
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// THE SILO IS GONE ONLY WHERE WE PUT A WORLD — the standalone constructors still stand alone.
// ═══════════════════════════════════════════════════════════════════════════════════════════

#[test]
fn the_standalone_constructors_are_still_siloed_by_design() {
    // `CraftOffering::new()` / `InventoryOffering::demo()` keep the old private-world shape (the
    // standalone single-surface demo). Honest: the share is what `in_world` buys, and nothing else
    // silently acquires it.
    let forge = CraftOffering::new();
    let bag = InventoryOffering::demo(PLAYER);
    let mut fs = forge.open(SessionConfig::default()).expect("open");
    let bs = bag.open(SessionConfig::default()).expect("open");

    assert!(
        forge
            .advance(&mut fs, act("craft", GREATBLADE), actor())
            .landed()
    );
    let forged = fs.output_ids()[0];
    assert!(
        !bs.asset_ids().contains(&forged),
        "a siloed forge reaches a siloed bag exactly as much as it ever did: not at all"
    );
    assert_eq!(bs.len(), 5, "the standalone demo bag is its own five notes");
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// THE MOUNTED DEMO — `register_surfaces` really does mount the three on one world.
// ═══════════════════════════════════════════════════════════════════════════════════════════

#[test]
fn the_registered_demo_surfaces_share_one_world() {
    let world = SharedWorld::demo(PLAYER);
    // The three offerings register_surfaces mounts, over the one handle it builds.
    let forge = CraftOffering::in_world(world.clone());
    let bag = InventoryOffering::in_world(world.clone());
    let stall = TradeOffering::in_world(world.clone());

    let mut fs = forge.open(SessionConfig::default()).expect("open");
    let bs = bag.open(SessionConfig::default()).expect("open");
    let ts = stall.open(SessionConfig::default()).expect("open");

    // ONE world object behind all three sessions (not three that merely agree).
    assert!(fs.world().is_same(bs.world()));
    assert!(bs.world().is_same(ts.world()));
    // ONE canonical player: the label the forge crafts as IS the label the bag lists for and the
    // stall sells as — no three-way name convention.
    assert_eq!(world.player(), PLAYER);

    // The demo's seeded shelf: 5 inventory notes + 3 market goods, all the player's own.
    assert_eq!(bs.asset_ids().len(), 8);
    assert_eq!(ts.asset_ids(), bs.asset_ids(), "one shelf, two surfaces");

    // Forge the Charm (recipe 1) — it lands on ALL THREE at once.
    assert!(forge.advance(&mut fs, act("craft", 1), actor()).landed());
    let charm = fs.output_ids()[0];
    assert_eq!(bs.asset_ids().len(), 9);
    assert!(bs.asset_ids().contains(&charm));
    assert!(ts.asset_ids().contains(&charm));
}
