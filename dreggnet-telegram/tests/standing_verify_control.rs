//! The visible Telegram replay control, across the flagship and the hosted Dungeon.
//!
//! The control is not an offering action: it never reaches a game executor, never binds a
//! player, and never enters the move log. It routes by the message it was pressed on and invokes
//! that offering's existing verifier, including the Dungeon verifier that replays Chutes-bound
//! narrated receipts.

use dreggnet_offerings::dungeon::DungeonOffering;
use dreggnet_offerings::{DreggIdentity, Offering, Outcome, SessionConfig};
use dreggnet_telegram::api::{InlineKeyboardButton, LOCK_GLYPH, decode_callback, encode_callback};
use dreggnet_telegram::host::{HostPress, TelegramHost};
use dreggnet_telegram::transport::{MessageId, MockTransport};
use dreggnet_telegram::verify_control::{
    TURN_VERIFY, VERIFY_ARG, VERIFY_LABEL, is_verify_callback,
};
use dreggnet_telegram::{CallbackQuery, TelegramFrontend};
use dungeon_on_dregg::narrator::{Narrated, legal_commands};

const BOT_SECRET: [u8; 32] = [37; 32];
const ALICE: u64 = 52_001;
const BOB: u64 = 52_002;

fn host() -> TelegramHost<MockTransport> {
    TelegramHost::new(BOT_SECRET, MockTransport::new(), &[ALICE, BOB])
}

fn message_of(host: &TelegramHost<MockTransport>, chat: i64, key: &str) -> MessageId {
    let surface = TelegramFrontend::<MockTransport>::surface_id(chat, None, key);
    host.frontend()
        .session(&surface)
        .and_then(|session| session.message_id)
        .unwrap_or_else(|| panic!("{key} has a live Telegram message"))
}

fn buttons_on(host: &TelegramHost<MockTransport>, message: MessageId) -> Vec<InlineKeyboardButton> {
    host.frontend()
        .transport()
        .visible(message)
        .expect("the live message is visible")
        .reply_markup
        .as_ref()
        .expect("the offering has its standing verify control")
        .inline_keyboard
        .iter()
        .flatten()
        .cloned()
        .collect()
}

fn verify_button(host: &TelegramHost<MockTransport>, message: MessageId) -> InlineKeyboardButton {
    buttons_on(host, message)
        .into_iter()
        .find(|button| {
            decode_callback(&button.callback_data)
                .is_some_and(|(turn, arg)| is_verify_callback(&turn, arg))
        })
        .expect("the offering visibly carries re-verification")
}

fn first_game_button(
    host: &TelegramHost<MockTransport>,
    message: MessageId,
) -> InlineKeyboardButton {
    buttons_on(host, message)
        .into_iter()
        .find(|button| {
            !button.text.starts_with(LOCK_GLYPH)
                && button.web_app.is_none()
                && button.callback_data.starts_with("g.")
        })
        .expect("the live offering exposes an enabled game action")
}

fn assert_verified(press: HostPress, key: &str) -> usize {
    match press {
        HostPress::Verified {
            key: actual,
            report: Some(report),
        } => {
            assert_eq!(actual, key);
            assert!(report.verified, "{}", report.detail);
            report.turns
        }
        other => panic!("{key}'s visible verifier must replay its chain: {other:?}"),
    }
}

#[test]
fn descent_verify_is_visible_canonical_read_only_and_cannot_bind_identity() {
    let mut host = host();
    let chat = 52_731;
    host.open("descent", chat, None, ALICE)
        .expect("native Descent opens");
    let message = message_of(&host, chat, "descent");
    let verify = verify_button(&host, message);
    assert_eq!(verify.text, VERIFY_LABEL);
    assert_eq!(
        decode_callback(&verify.callback_data),
        Some((TURN_VERIFY.to_string(), VERIFY_ARG))
    );

    // Same reserved verb, forged argument: fail closed before any verifier or executor work.
    let sent_before = host.frontend().transport().sent.len();
    assert!(matches!(
        host.press(CallbackQuery::press_on_message(
            chat,
            message,
            BOB,
            encode_callback(TURN_VERIFY, 9),
        )),
        HostPress::NotOffered
    ));
    assert_eq!(host.frontend().transport().sent.len(), sent_before);

    // Bob may inspect the public chain, but a read-only inspection cannot claim the unbound run.
    assert_eq!(
        assert_verified(
            host.press(CallbackQuery::press_on_message(
                chat,
                message,
                BOB,
                verify.callback_data.clone(),
            )),
            "descent",
        ),
        1,
        "genesis alone replays"
    );
    assert_eq!(
        host.frontend().transport().sent.len(),
        sent_before,
        "verification never repaints or mutates the surface"
    );

    let action = first_game_button(&host, message);
    assert!(matches!(
        host.press(CallbackQuery::press_on_message(
            chat,
            message,
            ALICE,
            action.callback_data,
        )),
        HostPress::Advanced {
            outcome: Outcome::Landed { .. },
            ..
        }
    ));
    let alice = host.identity(ALICE);
    let bob = host.identity(BOB);
    let committed = host
        .frontend()
        .transport()
        .visible(message)
        .expect("Descent repainted after the landed turn")
        .text
        .clone();
    assert!(committed.contains(alice.as_str()), "{committed}");
    assert!(!committed.contains(bob.as_str()), "{committed}");

    let sent_before_replay = host.frontend().transport().sent.len();
    assert_eq!(
        assert_verified(
            host.press(CallbackQuery::press_on_message(
                chat,
                message,
                BOB,
                verify.callback_data,
            )),
            "descent",
        ),
        2,
        "genesis plus Alice's move replay"
    );
    assert_eq!(host.frontend().transport().sent.len(), sent_before_replay);
    assert_eq!(
        host.frontend()
            .transport()
            .visible(message)
            .expect("surface remains")
            .text,
        committed,
        "Bob's replay check cannot replace Alice's attribution"
    );

    let menu_chat = 52_739;
    let menu_session = host.present_offerings_menu(menu_chat, None);
    let menu_message = host
        .frontend()
        .session(&menu_session)
        .and_then(|session| session.message_id)
        .expect("the offerings menu has a live message");
    assert!(
        buttons_on(&host, menu_message).iter().all(|button| {
            decode_callback(&button.callback_data)
                .is_none_or(|(turn, arg)| !is_verify_callback(&turn, arg))
        }),
        "a menu with no active offering must not show a dead verify control"
    );
}

#[test]
fn verify_routes_by_message_and_remains_after_descent_settlement() {
    let mut host = host();
    let chat = 52_732;
    host.open("descent", chat, None, ALICE)
        .expect("native Descent opens");
    let descent_message = message_of(&host, chat, "descent");
    host.open("dungeon", chat, None, ALICE)
        .expect("the hosted Dungeon opens beside it");
    let dungeon_message = message_of(&host, chat, "dungeon");
    let descent_verify = verify_button(&host, descent_message).callback_data;
    let dungeon_verify = verify_button(&host, dungeon_message).callback_data;

    assert_eq!(
        assert_verified(
            host.press(CallbackQuery::press_on_message(
                chat,
                descent_message,
                BOB,
                descent_verify.clone(),
            )),
            "descent",
        ),
        1
    );
    assert_eq!(
        assert_verified(
            host.press(CallbackQuery::press_on_message(
                chat,
                dungeon_message,
                BOB,
                dungeon_verify.clone(),
            )),
            "dungeon",
        ),
        1,
        "the older/newer active pointer cannot redirect a message-addressed check"
    );

    let dungeon_action = first_game_button(&host, dungeon_message);
    assert!(matches!(
        host.press(CallbackQuery::press_on_message(
            chat,
            dungeon_message,
            ALICE,
            dungeon_action.callback_data,
        )),
        HostPress::Advanced {
            key,
            outcome: Outcome::Landed { .. },
        } if key == "dungeon"
    ));
    assert_eq!(
        assert_verified(
            host.press(CallbackQuery::press_on_message(
                chat,
                dungeon_message,
                BOB,
                dungeon_verify,
            )),
            "dungeon",
        ),
        2
    );

    let mut ended = false;
    for _ in 0..64 {
        let action = first_game_button(&host, descent_message);
        let press = host.press(CallbackQuery::press_on_message(
            chat,
            descent_message,
            ALICE,
            action.callback_data,
        ));
        match press {
            HostPress::Advanced {
                key,
                outcome:
                    Outcome::Landed {
                        ended: turn_ended, ..
                    },
            } => {
                assert_eq!(key, "descent");
                if turn_ended {
                    ended = true;
                    break;
                }
            }
            other => panic!("an exposed Descent action must land: {other:?}"),
        }
    }
    assert!(ended, "the surface-driven Descent settles within 64 turns");
    let terminal_buttons = buttons_on(&host, descent_message);
    let descent_surface = TelegramFrontend::<MockTransport>::surface_id(chat, None, "descent");
    assert_eq!(
        host.frontend()
            .session(&descent_surface)
            .expect("the terminal surface remains live")
            .presented
            .len(),
        0,
        "terminal Descent removes every offering game action"
    );
    let terminal_verify: Vec<_> = terminal_buttons
        .iter()
        .filter(|button| {
            decode_callback(&button.callback_data)
                .is_some_and(|(turn, arg)| is_verify_callback(&turn, arg))
        })
        .collect();
    assert_eq!(terminal_verify.len(), 1, "proof checking remains visible");
    assert_eq!(terminal_verify[0].text, VERIFY_LABEL);
    assert!(
        assert_verified(
            host.press(CallbackQuery::press_on_message(
                chat,
                descent_message,
                BOB,
                terminal_verify[0].callback_data.clone(),
            )),
            "descent",
        ) > 1
    );
}

#[test]
fn dungeon_verifier_replays_narrated_receipts_with_telegram_identity() {
    let telegram = host();
    let actor: DreggIdentity = telegram.identity(ALICE);
    let offering = DungeonOffering::new();
    let mut session = offering
        .open(SessionConfig::with_seed(52_733))
        .expect("the hosted Dungeon opens");
    let (_, command) = legal_commands(&session.narrated_view())
        .into_iter()
        .next()
        .expect("the current room exposes a closed narrated command");
    let narrated = Narrated::new(
        command,
        "The confined narrator describes the move without gaining state authority.",
    );
    session
        .advance_narrated_receipt(&narrated, actor.clone())
        .expect("the native narrated command lands");

    assert_eq!(session.actor_of_step(0), Some(&actor));
    let report = offering.verify(&session);
    assert!(report.verified, "{}", report.detail);
    assert_eq!(report.turns, 2, "genesis plus the narrated turn replay");
    assert!(
        is_verify_callback(TURN_VERIFY, VERIFY_ARG),
        "the visible Telegram control targets this same Offering verifier"
    );
}
