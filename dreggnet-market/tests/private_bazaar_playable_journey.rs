//! Public contract smoke for the private Bazaar journey.
//!
//! The full private-proof -> durable exact Dungeon effect crash/recovery path
//! lives beside the concrete adapter, where it can inspect the opaque prepared
//! token. This integration test pins what an external frontend may observe:
//! one payload-free Enter action and a structurally pending, viewer-blind
//! receipt bound to independently loaded deployment policy.

#![cfg(feature = "private-clearing")]

use dregg_app_framework::symbol;
use dreggnet_market::private_bazaar_journey::{
    PrivateBazaarDeploymentPin, PrivateBazaarJourneyError, PrivateBazaarPublicAction,
    PrivateBazaarPublicPhase, PrivateBazaarRaidJourney, PrivateBazaarRaidPolicy,
};
use dreggnet_market::private_clearing_guild_allocation::{GuildMember, GuildReward, GuildRoster};
use dreggnet_market::{DarkBazaarOffering, TURN_LIST};
use dreggnet_offerings::{Action, DreggIdentity, Offering, Outcome, SessionConfig};
use dungeon_on_dregg::progression::{
    PRIVATE_BAZAAR_XP_EVENT, PRIVATE_BAZAAR_XP_METHOD, deploy_hero,
};

#[test]
fn payload_free_entry_mints_only_a_viewer_blind_pending_receipt() {
    let actor = DreggIdentity("journey:guild-member".to_owned());
    let hero = deploy_hero(0x83);
    hero.set_executor_signing_key([0xA7; 32]);
    let roster = GuildRoster::new(vec![GuildMember::new(actor.clone(), hero.cell_id())]).unwrap();
    let reward = GuildReward::new("raid-xp/ashen-vault/v1", 144).unwrap();
    let pin = PrivateBazaarDeploymentPin::new(
        [0x31; 32],
        roster.digest(),
        PrivateBazaarRaidPolicy::reward_commitment_for_configuration(&reward),
        PRIVATE_BAZAAR_XP_METHOD,
        symbol(PRIVATE_BAZAAR_XP_EVENT),
        hero.executor_pubkey().unwrap(),
        hero.federation_id(),
    )
    .unwrap();
    let policy = PrivateBazaarRaidPolicy::load(pin, roster, reward).unwrap();

    let offering = DarkBazaarOffering::new();
    let mut market = offering.open(SessionConfig::with_seed(0xB4_2A_A2)).unwrap();
    assert!(matches!(
        offering.advance(&mut market, Action::new("list", TURN_LIST, 1, true), actor,),
        Outcome::Landed { .. }
    ));

    let mut journey = PrivateBazaarRaidJourney::new(&market, policy).unwrap();
    assert_eq!(journey.actions().len(), 1);
    let forged = Action::new(
        "enter with illicit value",
        dreggnet_market::private_bazaar_journey::TURN_ENTER_PRIVATE_BAZAAR,
        3,
        true,
    );
    assert_eq!(
        journey.advance_public(&forged),
        Err(PrivateBazaarJourneyError::PublicActionCarriesPayload)
    );

    let receipt = journey
        .advance_public(&PrivateBazaarPublicAction::Enter.offering_action())
        .unwrap();
    assert_eq!(receipt.phase(), PrivateBazaarPublicPhase::Pending);
    assert!(receipt.source_use_id().is_none());
    assert!(receipt.operation_id().is_none());
    assert!(receipt.game_receipt_hash().is_none());
    assert!(receipt.game_turn_hash().is_none());
    assert!(receipt.game_post_state().is_none());

    let public = format!(
        "{:?}\n{:?}",
        receipt.public_fields(),
        receipt.surface().view()
    );
    for forbidden in [
        "journey:guild-member",
        "winner",
        "reserve",
        "private bid",
        "proof bytes",
        "witness",
    ] {
        assert!(
            !public.contains(forbidden),
            "public receipt leaked {forbidden}: {public}"
        );
    }
    assert!(journey.actions().is_empty(), "Enter is write-once");
}
