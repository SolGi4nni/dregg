//! The BANKED relic crosses the Dark Bazaar — the banked custody relic IS the auctioned note.
//!
//! The sibling `descent_asset_bazaar.rs` auctions a MANUFACTURED `roll_drop("boss:…")` draw — a
//! fresh draw disconnected from any run's banked custody. This drives the ACTUAL Descent through
//! the bank → asset wire: a real run banks a specific relic, that banked relic mints (its provenance
//! the banked run's day-seed + custody slot), the SAME AssetWorld is adopted by the trade substrate,
//! a sealed Bazaar auction fixes the winner + price, and the banked note crosses atomically. The
//! winner then holds an AssetId whose provenance REPLAYS to the banked run — not a manufactured draw.

/// The verified settlement gate this binary installs before every test — see
/// `tests/support/mod.rs`. Without it `settle_ring_verified` refuses every award as
/// NEVER JUDGED, which is a host-wiring fact about this binary and not a market verdict.
mod support;

use dreggnet_market::{DarkBazaarOffering, TURN_BID, TURN_LIST, TURN_SETTLE};
use dreggnet_offerings::{Action, DreggIdentity, Offering, Outcome, SessionConfig};
use dreggnet_trade::TradeWorld;
use dungeon_on_dregg::descent::{BANKED, Descent};
use dungeon_on_dregg::loot::{LootVault, banked_relic_chest, banked_relic_drop};

fn actor(name: &str) -> DreggIdentity {
    DreggIdentity(name.to_string())
}

fn land(
    offering: &DarkBazaarOffering,
    session: &mut dreggnet_market::DarkBazaarSession,
    turn: &str,
    arg: i64,
    who: &str,
) {
    let out = offering.advance(session, Action::new(turn, turn, arg, true), actor(who));
    assert!(
        matches!(out, Outcome::Landed { .. }),
        "{turn} refused: {out:?}"
    );
}

#[test]
fn a_banked_descent_relic_crosses_the_bazaar_to_the_verified_winner() {
    support::install_verified_settlement_gate();
    const SELLER: &str = "descent-player:alice";
    const LOW: &str = "bazaar-bidder:bob";
    const WINNER: &str = "bazaar-bidder:carol";

    // Drive a REAL Descent: floor 1, slay the guardian, loot the way-2 key, CLIMB OUT, then flee
    // (the terminal bank). The key ends in BANKED custody — a real committed cell write, not a draw.
    //
    // ⚑ The `ascend()` is not decoration. `d8e4ec3e2` ("descent: the one-way door swings BOTH
    // ways") made `flee` demand `depth == 0` — "you cannot bank from below — climb out first" —
    // which is what makes the Descent lethal. This test still teleported out of floor 1 and had
    // been red on `dungeon_on_dregg::descent`'s refusal, not on anything the market does, since
    // 2026-07-25 12:29.
    let mut d = Descent::deploy(0x5A).expect("deploy + genesis");
    d.delve().expect("way 1 open");
    d.smite().expect("floor-1 guardian falls");
    d.loot(1).expect("carry the way-2 key");
    d.ascend().expect("climb back to the mouth");
    d.flee().expect("bank the pack — run ends");
    let day_seed = *d.day_seed();
    let banked_slot = 1usize;
    assert_eq!(
        d.read_relic(banked_slot),
        BANKED,
        "the way-key is a committed BANKED relic on the cell"
    );

    // The auctioned note is minted FROM the banked relic (the wire), NOT roll_drop("boss:…").
    let mut vault = LootVault::new();
    let minted = d
        .mint_banked_relics(&mut vault, SELLER)
        .expect("banked relics mint");
    let note = minted
        .iter()
        .find(|m| m.slot == banked_slot)
        .expect("the banked key was minted")
        .item
        .clone();
    let prov = vault.provenance(note.asset_id).expect("known loot");
    assert_eq!(
        prov.run_seed, day_seed,
        "provenance root = the banked run's day-seed"
    );
    assert_eq!(
        prov.chest,
        banked_relic_chest(banked_slot),
        "provenance names the banked custody slot, not a boss draw"
    );
    assert!(prov.asset.verified);

    // Adopt the SAME note world (no remint) and fund real $DREGG bidders.
    let mut world = TradeWorld::with_assets(vault.into_assets());
    world.fund_dregg(LOW, 40);
    world.fund_dregg(WINNER, 90);

    let offering = DarkBazaarOffering::new();
    let mut session = offering
        .open(SessionConfig::with_seed(0xBA2A_A2))
        .expect("Bazaar opens");
    land(&offering, &mut session, TURN_LIST, 10, SELLER);
    land(&offering, &mut session, TURN_BID, 40, LOW);
    land(&offering, &mut session, TURN_BID, 90, WINNER);
    land(&offering, &mut session, TURN_SETTLE, 0, SELLER);
    assert_eq!(session.winning_actor(), Some(&actor(WINNER)));

    // The banked note crosses atomically to the verified winner for $DREGG.
    let crossed = session
        .settle_winning_asset(&mut world, note.asset_id)
        .expect("the banked Descent note crosses atomically");
    assert_eq!(crossed.asset, note.asset_id);
    assert_eq!(crossed.price, 90);
    assert_eq!(crossed.seller, actor(SELLER));
    assert_eq!(crossed.winner, actor(WINNER));
    assert!(crossed.provenance.verified);
    assert_eq!(world.current_holder_label(note.asset_id), Some(WINNER));
    assert_eq!(world.lineage_len(note.asset_id), 3); // mint -> escrow -> winner
    assert_eq!(world.dregg_balance(WINNER), 0);
    assert_eq!(world.dregg_balance(SELLER), 90);

    // ⚑ THE WINNER HOLDS AN ASSETID WHOSE PROVENANCE REPLAYS TO THE BANKED RUN. Re-deriving the
    // banked relic's drop from (run day-seed, banked slot) and minting it fresh for the same player
    // yields the byte-identical AssetId the winner now holds — the auctioned note is the banked
    // relic's lineage, replayable to the run, not a manufactured `roll_drop` draw.
    let mut replay = LootVault::new();
    let replay_note = replay
        .claim(SELLER, &banked_relic_drop(&day_seed, banked_slot))
        .expect("the banked drop re-derives + mints");
    assert_eq!(
        replay_note.asset_id.bytes(),
        note.asset_id.bytes(),
        "the auctioned note re-derives from the banked run — provenance REPLAYS"
    );
}
