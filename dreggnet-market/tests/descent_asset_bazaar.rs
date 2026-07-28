//! The Descent -> Dark Bazaar engine weld, driven end to end.
//!
//! A fair-drawn Descent drop mints a real owned note. The exact AssetWorld is then
//! adopted by the trade substrate, a sealed Bazaar auction fixes winner + price,
//! and the original AssetId crosses atomically for $DREGG. No synthetic `GOOD`, no
//! remint, and the post-sale provenance chain must re-verify.

/// The verified settlement gate this binary installs before every test — see
/// `tests/support/mod.rs`. Without it `settle_ring_verified` refuses every award as
/// NEVER JUDGED, which is a host-wiring fact about this binary and not a market verdict.
mod support;

use dreggnet_market::{DarkBazaarOffering, TURN_BID, TURN_LIST, TURN_SETTLE};
use dreggnet_offerings::{Action, DreggIdentity, Offering, Outcome, SessionConfig};
use dreggnet_trade::TradeWorld;
use dungeon_on_dregg::loot::{LootVault, roll_drop};
use procgen_dregg::CommittedSeed;

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
fn fair_descent_loot_crosses_to_the_verified_bazaar_winner_without_remint() {
    support::install_verified_settlement_gate();
    const SELLER: &str = "descent-player:alice";
    const LOW: &str = "bazaar-bidder:bob";
    const WINNER: &str = "bazaar-bidder:carol";

    // The item begins as a genuine fair draw tied to a committed Descent run seed.
    let run_seed = CommittedSeed::from_bytes([0xD3; 32]);
    let draw = roll_drop(&run_seed, "boss:the Tide-Warden", 0);
    let mut vault = LootVault::new();
    let loot = vault.claim(SELLER, &draw).expect("fair drop mints");
    assert!(
        vault
            .provenance(loot.asset_id)
            .expect("known loot")
            .asset
            .verified
    );

    // Adopt the SAME note world and fund real $DREGG wallets for the bidders.
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

    let crossed = session
        .settle_winning_asset(&mut world, loot.asset_id)
        .expect("the original Descent note crosses atomically");
    assert_eq!(crossed.asset, loot.asset_id);
    assert_eq!(crossed.price, 90);
    assert_eq!(crossed.seller, actor(SELLER));
    assert_eq!(crossed.winner, actor(WINNER));
    assert!(crossed.provenance.verified);
    assert_eq!(world.current_holder_label(loot.asset_id), Some(WINNER));
    assert_eq!(world.lineage_len(loot.asset_id), 3); // mint -> escrow -> winner
    assert_eq!(world.dregg_balance(WINNER), 0);
    assert_eq!(world.dregg_balance(SELLER), 90);
}

#[test]
fn asset_cross_refuses_if_the_verified_winner_cannot_pay_and_returns_the_loot() {
    support::install_verified_settlement_gate();
    const SELLER: &str = "descent-player:alice";
    const WINNER: &str = "bazaar-bidder:empty-wallet";

    let run_seed = CommittedSeed::from_bytes([0x51; 32]);
    let draw = roll_drop(&run_seed, "chest:the Black Reliquary", 0);
    let mut vault = LootVault::new();
    let loot = vault.claim(SELLER, &draw).expect("fair drop mints");
    let mut world = TradeWorld::with_assets(vault.into_assets());

    let offering = DarkBazaarOffering::new();
    let mut session = offering
        .open(SessionConfig::with_seed(0xBAD_C01))
        .expect("Bazaar opens");
    land(&offering, &mut session, TURN_LIST, 50, SELLER);
    land(&offering, &mut session, TURN_BID, 50, WINNER);
    land(&offering, &mut session, TURN_SETTLE, 0, SELLER);

    let err = session
        .settle_winning_asset(&mut world, loot.asset_id)
        .expect_err("an unfunded winner cannot take the loot");
    assert!(err.to_string().contains("insufficient $DREGG"), "{err}");
    assert_eq!(world.current_holder_label(loot.asset_id), Some(SELLER));
    assert!(world.verify_provenance(loot.asset_id).verified);
}
