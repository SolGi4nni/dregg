//! The opt-in private Bazaar deployment is mounted through Telegram's real
//! generic catalog/open/press path. No proof, bid, target, or reward rides the
//! callback; the one public Enter button lands the underlying LIST receipt.

#![cfg(feature = "private-bazaar-live")]

use dreggnet_catalog::PrivateBazaarLiveDeployment;
use dreggnet_market::private_bazaar_journey::{
    PrivateBazaarDeploymentPin, PrivateBazaarRaidPolicy,
};
use dreggnet_market::private_bazaar_live_host::PRIVATE_BAZAAR_RAID_KEY;
use dreggnet_market::private_clearing_guild_allocation::{GuildMember, GuildReward, GuildRoster};
use dreggnet_offerings::DreggIdentity;
use dreggnet_telegram::api::encode_callback;
use dreggnet_telegram::host::{HostPress, TelegramHost};
use dreggnet_telegram::transport::MockTransport;
use dreggnet_telegram::{CallbackQuery, TelegramFrontend};
use dungeon_on_dregg::progression::{
    PRIVATE_BAZAAR_XP_METHOD, deploy_hero, private_bazaar_xp_event_topic,
};

const SECRET: [u8; 32] = [0x71; 32];
const PLAYER: u64 = 719;

#[test]
fn telegram_opens_and_drives_the_configured_private_bazaar_host() {
    let hero = deploy_hero(0x71);
    hero.set_executor_signing_key([0x72; 32]);
    let roster = GuildRoster::new(vec![GuildMember::new(
        DreggIdentity("telegram-private-raider".to_owned()),
        hero.cell_id(),
    )])
    .unwrap();
    let reward = GuildReward::new("raid-xp/telegram/v1", 144).unwrap();
    let pin = PrivateBazaarDeploymentPin::new(
        [0x73; 32],
        roster.digest(),
        PrivateBazaarRaidPolicy::reward_commitment_for_configuration(&reward),
        PRIVATE_BAZAAR_XP_METHOD,
        private_bazaar_xp_event_topic(),
        hero.executor_pubkey().unwrap(),
        hero.federation_id(),
    )
    .unwrap();
    let policy = PrivateBazaarRaidPolicy::load(pin, roster, reward).unwrap();
    let temp = tempfile::tempdir().unwrap();
    let deployment = PrivateBazaarLiveDeployment::open(policy, 1, temp.path()).unwrap();

    let mut telegram = TelegramHost::with_private_bazaar(
        SECRET,
        MockTransport::new(),
        &[PLAYER],
        deployment.clone(),
    );
    assert!(
        telegram
            .list_offerings()
            .iter()
            .any(|offering| offering.key == PRIVATE_BAZAAR_RAID_KEY)
    );

    let chat = 719_i64;
    let sid = telegram
        .open(PRIVATE_BAZAAR_RAID_KEY, chat, None, PLAYER)
        .expect("the configured route opens in a DM");
    let surface =
        TelegramFrontend::<MockTransport>::surface_id(chat, None, PRIVATE_BAZAAR_RAID_KEY);
    let action = telegram
        .frontend()
        .session(&surface)
        .and_then(|slot| slot.presented.first())
        .cloned()
        .expect("payload-free Enter is presented");
    assert_eq!(action.arg, 0);
    assert!(action.text.is_none());

    match telegram.press(CallbackQuery {
        chat_id: chat,
        message_thread_id: None,
        message_id: None,
        from_user_id: PLAYER,
        data: encode_callback(&action),
    }) {
        HostPress::Advanced { key, outcome } => {
            assert_eq!(key, PRIVATE_BAZAAR_RAID_KEY);
            assert!(
                outcome.landed(),
                "Enter lands a real LIST turn: {outcome:?}"
            );
        }
        other => panic!("Telegram must drive the configured host, got {other:?}"),
    }
    assert!(
        deployment
            .registry()
            .contains(dreggnet_offerings::seed_from_id(sid.as_str()))
    );
    assert!(
        telegram
            .verify(PRIVATE_BAZAAR_RAID_KEY, &sid)
            .expect("the route remains live")
            .verified
    );
}
