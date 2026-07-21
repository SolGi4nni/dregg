//! **Two offerings live in ONE chat, both addressable.**
//!
//! ## The bug this file exists for
//! A Telegram session was keyed by chat alone (`tg:{chat_id}`), and the host kept ONE offering key
//! per chat (`active: HashMap<SessionId, String>`) over ONE message slot. So opening a second
//! offering STOLE the chat's surface: the first offering's message stopped being re-presented, its
//! keyboard went stale, and a press on it answered `NotOffered` (or, worse, resolved against the
//! new offering because the chat's `presented` list had been overwritten). Two people in one group
//! could not play different games, and one person could not keep a document open beside a board.
//!
//! ## The fix, and what is deliberately NOT changed
//! The `OfferingHost` already addressed a session as `(key, id)`, so two offerings in one chat were
//! ALREADY two separate host sessions — the collision was purely in the SURFACE. So the host
//! session id stays chat-scoped (its deterministic seed, its durable resume log, and its Mini App
//! deep link are all untouched), and only the surface splits: one message per `(chat, offering)`,
//! named by `TelegramFrontend::surface_id` (`tg:-5#tug`).
//!
//! A press then routes by **the message it was pressed on** (`CallbackQuery::message_id`, the Bot
//! API's own `callback_query.message.message_id`) — which is the honest answer to "which of these
//! boards did you press". A synthesized press that names no message (a `/act` command, a Mini App
//! `sendData` round-trip, an older test) falls back to the chat's most recent surface, so the
//! single-offering UX is exactly as it was.

use dreggnet_offerings::SessionId;
use dreggnet_telegram::api::encode_callback;
use dreggnet_telegram::host::{HostPress, OPERATION_GUIDE_SLOT, TelegramHost};
use dreggnet_telegram::transport::{MessageId, MockTransport};
use dreggnet_telegram::{CallbackQuery, TelegramFrontend};

use dungeon_on_dregg::KP_PRESS_ON;

const BOT_SECRET: [u8; 32] = [7u8; 32];
const ALICE: u64 = 1001;
const BOB: u64 = 1002;

fn host() -> TelegramHost<MockTransport> {
    TelegramHost::new(BOT_SECRET, MockTransport::new(), &[ALICE, BOB])
}

/// The live message id of `key`'s surface in this chat.
fn message_of(h: &TelegramHost<MockTransport>, chat: i64, key: &str) -> MessageId {
    let surface = TelegramFrontend::<MockTransport>::surface_id(chat, None, key);
    h.frontend()
        .session(&surface)
        .and_then(|s| s.message_id)
        .unwrap_or_else(|| panic!("{key} has a live surface in chat {chat}"))
}

/// **THE COLLISION TEST.** Two different offerings open in one chat both stay live and addressable:
/// each owns its own message, each keeps its own keyboard, and a press on either message advances
/// THAT offering — including a press on the FIRST one after the second was opened, which is the
/// exact move that used to be swallowed.
#[test]
fn two_offerings_open_in_one_chat_both_stay_live_and_addressable() {
    let mut h = host();
    let chat: i64 = 88;
    let sid: SessionId = TelegramFrontend::<MockTransport>::session_id(chat, None);

    // Open the dungeon, then — WITHOUT closing it — the council.
    h.open("dungeon", chat, None, ALICE).expect("dungeon opens");
    let dungeon_msg = message_of(&h, chat, "dungeon");
    h.open("council", chat, None, ALICE).expect("council opens");
    let council_msg = message_of(&h, chat, "council");

    // Two DISTINCT messages: the second offering did not take over the first one's.
    assert_ne!(
        dungeon_msg, council_msg,
        "each offering owns its own message; the second must not steal the first's surface"
    );
    let dungeon_surface = TelegramFrontend::<MockTransport>::surface_id(chat, None, "dungeon");
    let council_surface = TelegramFrontend::<MockTransport>::surface_id(chat, None, "council");
    let companion_count = h
        .frontend()
        .companion_messages(&dungeon_surface, OPERATION_GUIDE_SLOT)
        .len()
        + h.frontend()
            .companion_messages(&council_surface, OPERATION_GUIDE_SLOT)
            .len();
    assert_eq!(
        h.frontend().transport().messages_in(chat).len(),
        2 + companion_count,
        "the chat holds two routable surfaces plus their non-interactive operation guides"
    );
    assert_eq!(
        h.frontend().surfaces_in_chat(&sid).len(),
        2,
        "…and the frontend tracks both"
    );

    // BOTH host sessions are live and independently verifiable.
    assert!(
        h.verify("dungeon", &sid).is_some(),
        "the dungeon session survived the council opening"
    );
    assert!(
        h.verify("council", &sid).is_some(),
        "the council session is live in the same chat"
    );

    // A press on the DUNGEON's message advances the DUNGEON — even though the council was opened
    // more recently. This is the press that used to be lost.
    match h.press(CallbackQuery::press_on_message(
        chat,
        dungeon_msg,
        ALICE,
        encode_callback("choose", KP_PRESS_ON as i64),
    )) {
        HostPress::Advanced { key, outcome } => {
            assert_eq!(key, "dungeon", "the press routed by ITS OWN message");
            assert!(outcome.landed(), "a real dungeon turn landed: {outcome:?}");
        }
        other => panic!("a press on the dungeon's message must advance the dungeon, got {other:?}"),
    }

    // …and a press on the COUNCIL's message advances the COUNCIL.
    match h.press(CallbackQuery::press_on_message(
        chat,
        council_msg,
        ALICE,
        encode_callback("propose", 0),
    )) {
        HostPress::Advanced { key, outcome } => {
            assert_eq!(key, "council", "the press routed by ITS OWN message");
            assert!(outcome.landed(), "a real council turn landed: {outcome:?}");
        }
        other => panic!("a press on the council's message must advance the council, got {other:?}"),
    }

    // Both chains re-verify: two real, separately committed histories in one chat.
    let dungeon = h.verify("dungeon", &sid).expect("dungeon is live");
    let council = h.verify("council", &sid).expect("council is live");
    assert!(dungeon.verified, "dungeon chain: {}", dungeon.detail);
    assert!(council.verified, "council chain: {}", council.detail);
    assert_eq!(dungeon.turns, 2, "dungeon: genesis + one turn");
    assert_eq!(council.turns, 2, "council: genesis + one turn");
}

/// Each surface keeps **its own keyboard**: opening a second offering does not overwrite the
/// first's presented affordances, so a press the first surface really offers is not answered
/// `NotOffered`, and a press only the second offers is not accidentally accepted on the first.
#[test]
fn each_surface_keeps_its_own_presented_affordances() {
    let mut h = host();
    let chat: i64 = 89;

    h.open("dungeon", chat, None, ALICE).expect("dungeon opens");
    h.open("council", chat, None, ALICE).expect("council opens");

    let dungeon_surface = TelegramFrontend::<MockTransport>::surface_id(chat, None, "dungeon");
    let council_surface = TelegramFrontend::<MockTransport>::surface_id(chat, None, "council");

    let dungeon_turns: Vec<String> = h
        .frontend()
        .session(&dungeon_surface)
        .expect("the dungeon surface is live")
        .presented
        .iter()
        .map(|a| a.turn.clone())
        .collect();
    let council_turns: Vec<String> = h
        .frontend()
        .session(&council_surface)
        .expect("the council surface is live")
        .presented
        .iter()
        .map(|a| a.turn.clone())
        .collect();

    assert!(
        dungeon_turns.iter().any(|t| t == "choose"),
        "the dungeon surface still offers its own moves: {dungeon_turns:?}"
    );
    assert!(
        council_turns.iter().any(|t| t == "propose"),
        "the council surface offers its own moves: {council_turns:?}"
    );
    assert!(
        !dungeon_turns.iter().any(|t| t == "propose"),
        "the council's affordances did not bleed onto the dungeon's keyboard: {dungeon_turns:?}"
    );

    // A council turn pressed on the DUNGEON's message is refused before the substrate — the
    // surfaces are genuinely separate, not one pooled affordance list.
    let dungeon_msg = message_of(&h, chat, "dungeon");
    assert!(
        matches!(
            h.press(CallbackQuery::press_on_message(
                chat,
                dungeon_msg,
                ALICE,
                encode_callback("propose", 0),
            )),
            HostPress::NotOffered
        ),
        "a council turn is not on the dungeon's surface"
    );
}

/// The single-offering UX is unchanged: a press that names NO message (a `/act` command, a Mini App
/// round-trip) routes to the chat's most recent surface — which, in a chat with one offering open,
/// is that offering, exactly as before.
#[test]
fn a_press_naming_no_message_routes_to_the_chats_most_recent_surface() {
    let mut h = host();
    let chat: i64 = 90;
    let sid = h.open("dungeon", chat, None, ALICE).expect("dungeon opens");
    assert_eq!(h.active_offering(&sid), Some("dungeon"));

    match h.press(CallbackQuery::press(
        chat,
        ALICE,
        encode_callback("choose", KP_PRESS_ON as i64),
    )) {
        HostPress::Advanced { key, outcome } => {
            assert_eq!(key, "dungeon");
            assert!(outcome.landed(), "the turn landed: {outcome:?}");
        }
        other => panic!("a message-less press must reach the chat's surface, got {other:?}"),
    }

    // Open a second offering: the chat's most recent surface moves to it, so a message-less press
    // now addresses the council — the honest reading of "this chat's session" for an input that
    // names no board.
    h.open("council", chat, None, ALICE).expect("council opens");
    match h.press(CallbackQuery::press(
        chat,
        ALICE,
        encode_callback("propose", 0),
    )) {
        HostPress::Advanced { key, .. } => assert_eq!(key, "council"),
        other => panic!("a message-less press addresses the newest surface, got {other:?}"),
    }
    // …and the dungeon is still there, unharmed, reachable by its own message.
    let dungeon_msg = message_of(&h, chat, "dungeon");
    match h.press(CallbackQuery::press_on_message(
        chat,
        dungeon_msg,
        ALICE,
        encode_callback("choose", KP_PRESS_ON as i64),
    )) {
        HostPress::Advanced { key, .. } => assert_eq!(key, "dungeon"),
        other => panic!("the dungeon is still addressable, got {other:?}"),
    }
}

/// The **offerings menu stays live** beside an opened offering: opening one game no longer makes
/// the menu message inert, so a second game can be opened from it by pressing the menu's own
/// message. (The menu is a chat-level surface; an offering's is its own.)
#[test]
fn the_offerings_menu_survives_opening_an_offering() {
    let mut h = host();
    let chat: i64 = 91;
    let sid = h.present_offerings_menu(chat, None);
    let menu_msg = h
        .frontend()
        .session(&sid)
        .and_then(|s| s.message_id)
        .expect("the menu was presented");

    let dungeon_index = h
        .list_offerings()
        .iter()
        .position(|o| o.key == "dungeon")
        .expect("the dungeon is registered");
    let council_index = h
        .list_offerings()
        .iter()
        .position(|o| o.key == "council")
        .expect("the council is registered");

    match h.press(CallbackQuery::press_on_message(
        chat,
        menu_msg,
        ALICE,
        encode_callback("open", dungeon_index as i64),
    )) {
        HostPress::Opened(key) => assert_eq!(key, "dungeon"),
        other => panic!("the menu press opens the dungeon, got {other:?}"),
    }

    // The MENU message is still the menu — press it again for a second offering.
    match h.press(CallbackQuery::press_on_message(
        chat,
        menu_msg,
        BOB,
        encode_callback("open", council_index as i64),
    )) {
        HostPress::Opened(key) => assert_eq!(key, "council"),
        other => panic!("the menu is still live for a second open, got {other:?}"),
    }

    assert!(h.verify("dungeon", &sid).is_some(), "the dungeon is live");
    assert!(h.verify("council", &sid).is_some(), "the council is live");
}
