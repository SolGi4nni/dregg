//! Dungeon, Descent, the Dark Bazaar crawl, and the proof-assigned raid are one kind of
//! *addressed operation* on Telegram without becoming one game.
//!
//! The common layer in this test is session address, audience projection, receipts, proof
//! operations, replay status, and standing verification. Concrete action vocabularies stay owned
//! by each offering and are explicitly checked not to bleed across surfaces.

use std::collections::BTreeSet;

use dreggnet_catalog::game_kind;
use dreggnet_offerings::Outcome;
use dreggnet_telegram::api::{decode_callback, encode_callback};
use dreggnet_telegram::host::{HostPress, TelegramHost};
use dreggnet_telegram::runtime::{TextDecision, describe_press, route_text_decided};
use dreggnet_telegram::transport::MockTransport;
use dreggnet_telegram::{CallbackQuery, TelegramFrontend};

const BOT_SECRET: [u8; 32] = [0x63; 32];
const ALICE: u64 = 63_001;

fn host() -> TelegramHost<MockTransport> {
    TelegramHost::new(BOT_SECRET, MockTransport::new(), &[ALICE])
}

fn surface_turns(host: &TelegramHost<MockTransport>, chat: i64, key: &str) -> BTreeSet<String> {
    let surface = TelegramFrontend::<MockTransport>::surface_id(chat, None, key);
    host.frontend()
        .session(&surface)
        .expect("the game surface is live")
        .presented
        .iter()
        .map(|action| action.turn.clone())
        .collect()
}

#[test]
fn four_rulebooks_share_one_session_record_without_sharing_legality() {
    let mut host = host();
    let cases = [
        ("descent", 63_101, "delve"),
        ("dungeon", 63_102, "choose"),
        ("bazaar", 63_103, "list"),
        ("private-raid", 63_104, "join-private-raid"),
    ];

    for (key, chat, own_turn) in cases {
        let sid = host.open(key, chat, None, ALICE).unwrap_or_else(|error| {
            panic!("{key} opens through the common Telegram host: {error}")
        });
        let surface = TelegramFrontend::<MockTransport>::surface_id(chat, None, key);
        let presented_count = host
            .frontend()
            .session(&surface)
            .expect("the game surface is live")
            .presented
            .len();
        let turns = surface_turns(&host, chat, key);
        assert!(
            turns.contains(own_turn),
            "{key} keeps its own action vocabulary: {turns:?}"
        );

        let message = host
            .frontend()
            .transport()
            .last()
            .expect("the surface was rendered");
        let kind = game_kind(key).expect("the common spine classifies every game");
        assert!(message.text.contains("Session record"), "{}", message.text);
        assert!(message.text.contains(kind.as_str()), "{}", message.text);
        let status = host
            .game_status(chat, None, ALICE)
            .unwrap_or_else(|error| panic!("{key} exposes the common status: {error}"));
        assert_eq!(status.key, key);
        assert_eq!(status.kind, kind.as_str());
        assert_eq!(status.session, sid);
        assert!(status.private_projection);
        if key == "bazaar" {
            assert!(
                !status.verified && status.verification_detail.contains("check-level"),
                "the crawl's honest pre-listing status is surfaced, not upgraded: {}",
                status.verification_detail
            );
        } else {
            assert!(status.verified, "{}", status.verification_detail);
        }
        assert!(status.replay_recipe);
        assert_eq!(
            status.turn_affordances, presented_count,
            "same-turn choices remain distinct affordances"
        );

        // The frontend record is common, but no game receives another game's action table.
        for foreign in ["delve", "choose", "list", "join-private-raid"] {
            if foreign != own_turn {
                assert!(
                    !turns.contains(foreign),
                    "{key} must not inherit {foreign:?} from the common presentation spine: {turns:?}"
                );
            }
        }
    }
}

#[test]
fn status_is_viewer_safe_and_a_landed_ack_names_the_exact_receipt() {
    let mut host = host();
    let chat = 63_201;
    host.open("descent", chat, None, ALICE)
        .expect("Descent opens");
    let identity = host.identity(ALICE);

    let (status, decision) = route_text_decided(&mut host, chat, None, ALICE, "/status");
    let status = status.expect("/status replies");
    assert!(matches!(
        decision,
        TextDecision::GameStatus {
            key: Some(ref key),
            inspected: true,
        } if key == "descent"
    ));
    assert!(
        status.contains("Game record · descent / descent"),
        "{status}"
    );
    assert!(status.contains("Record · VERIFIED"), "{status}");
    assert!(
        status.contains("Audience · private single-reader"),
        "{status}"
    );
    assert!(
        !status.contains(identity.as_str()),
        "status must not disclose which actor selected the private projection: {status}"
    );

    let surface = TelegramFrontend::<MockTransport>::surface_id(chat, None, "descent");
    let action = host
        .frontend()
        .session(&surface)
        .expect("Descent surface")
        .presented
        .iter()
        .find(|action| action.enabled)
        .expect("Descent has an enabled opening action")
        .clone();
    let press = host.press(CallbackQuery::press(
        chat,
        ALICE,
        encode_callback(&action.turn, action.arg),
    ));
    let expected = match &press {
        HostPress::Advanced {
            outcome: Outcome::Landed { receipt, .. },
            ..
        } => hex::encode(receipt.receipt_hash()),
        other => panic!("the offered Descent action lands: {other:?}"),
    };
    let ack = describe_press(press);
    assert!(
        ack.contains(&expected),
        "receipt join missing from ack: {ack}"
    );
    assert_eq!(expected.len(), 64, "the displayed join is not truncated");

    // The standing verification control remains frontend chrome, never one of the executor's
    // offered actions. A forged callback-shaped status/verify string cannot become game legality.
    let game_actions = host
        .frontend()
        .session(&surface)
        .expect("repainted Descent surface")
        .presented
        .iter()
        .map(|action| (action.turn.clone(), action.arg))
        .collect::<BTreeSet<_>>();
    assert!(!game_actions.contains(&("status".to_string(), 0)));
    assert!(decode_callback("status:0").is_some());
    assert!(matches!(
        host.press(CallbackQuery::press(chat, ALICE, "status:0")),
        HostPress::NotOffered
    ));
}

#[test]
fn group_status_is_viewer_blind_and_non_games_are_not_mislabeled() {
    let mut host = host();
    let group = -63_301;
    host.open("private-raid", group, None, ALICE)
        .expect("the shielded-assignment raid has a public group projection");
    let status = host
        .game_status(group, None, ALICE)
        .expect("the group game has status");
    assert!(!status.private_projection);
    let text = dreggnet_telegram::runtime::describe_game_status(&status);
    assert!(text.contains("shared viewer-blind projection"), "{text}");
    assert!(!text.contains(host.identity(ALICE).as_str()), "{text}");

    let dm = 63_302;
    host.open("doc", dm, None, ALICE)
        .expect("a service offering opens");
    let (reply, decision) = route_text_decided(&mut host, dm, None, ALICE, "/status");
    let reply = reply.expect("the non-game refusal is legible");
    assert!(reply.contains("not a game surface"), "{reply}");
    assert!(reply.contains("/verify"), "{reply}");
    assert!(matches!(
        decision,
        TextDecision::GameStatus {
            key: Some(ref key),
            inspected: false,
        } if key == "doc"
    ));
}
