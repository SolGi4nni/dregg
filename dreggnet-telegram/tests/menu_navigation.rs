//! **MULTI-STEP MENU NAVIGATION** — open → submenu → back → another submenu, every step asserted
//! to render something the user can actually see.
//!
//! ## The bugs this file exists for
//!
//! 1. **The invisible re-present.** A re-present EDITS the session's live message in place. That
//!    is right when a turn LANDS (one live surface per offering), and wrong when the user
//!    EXPLICITLY asks for a surface: `/offerings` in a long chat edited the previous menu message
//!    wherever it had scrolled to, and the command itself replies nothing — so a second
//!    `/offerings` produced NO VISIBLE OUTPUT AT ALL and the bot read as dead. Same for re-opening
//!    an offering already open. A single-step test never sees this: the first `/offerings` sends.
//!    Only the SECOND one edits.
//!
//! 2. **The restart dead button.** The frontend's message index is in-memory, so after a restart
//!    every button in the chat names a message this process has never presented. `press` refused
//!    those outright (`NotOffered`), which also made the documented restart-resume path — which
//!    only fires on `NoSession` — unreachable for real presses, since a real press always carries
//!    its message id. Every pre-restart button was permanently dead.
//!
//! 3. **The arbitrary rebind.** The resume path bound the chat to the FIRST open key in the
//!    registry's `BTreeMap` order. With `craft` and `doc` both persisted for one chat, every
//!    post-restart press rebound to `craft` no matter which message was pressed.
//!
//! Driven at the HANDLER layer over `MockTransport` — no token, no network. That proves the
//! routing, not the live edge.

use dreggnet_offerings::SessionId;
use dreggnet_telegram::api::encode_callback;
use dreggnet_telegram::host::{HostPress, TURN_OPEN, TelegramHost};
use dreggnet_telegram::runtime::{
    PressDecision, TextDecision, route_callback_decided, route_text_decided,
};
use dreggnet_telegram::transport::{MessageId, MockTransport};
use dreggnet_telegram::{CallbackQuery, TelegramFrontend};

const BOT_SECRET: [u8; 32] = [0x5a; 32];
/// A positive chat id → a DM, so nothing is refused for hiding per-player state.
const CHAT: i64 = 990011;
const ALICE: u64 = 7001;

type Host = TelegramHost<MockTransport>;

fn host() -> Host {
    TelegramHost::new(BOT_SECRET, MockTransport::new(), &[ALICE])
}

fn chat_session() -> SessionId {
    TelegramFrontend::<MockTransport>::session_id(CHAT, None)
}

fn menu_message(host: &Host) -> MessageId {
    let menu = TelegramFrontend::<MockTransport>::surface_id(CHAT, None, "@menu");
    host.frontend()
        .session(&menu)
        .and_then(|slot| slot.message_id)
        .expect("the offerings menu has a live message")
}

fn surface_message(host: &Host, key: &str) -> MessageId {
    let surface = TelegramFrontend::<MockTransport>::surface_id(CHAT, None, key);
    host.frontend()
        .session(&surface)
        .and_then(|slot| slot.message_id)
        .expect("the offering surface has a live message")
}

/// The catalog index of `key` — the `arg` a menu button carries.
fn menu_index(host: &Host, key: &str) -> i64 {
    host.list_offerings()
        .iter()
        .position(|o| o.key == key)
        .map(|i| i as i64)
        .unwrap_or_else(|| panic!("{key} is registered in the catalog"))
}

/// How many requests this chat has received so far — the "did the user see anything?" counter.
fn seen(host: &Host) -> usize {
    host.frontend().transport().sent_to(CHAT).len()
}

/// **The full navigation: menu → open → back to menu → open another → play the first.**
/// Every step must produce something visible, and each press must reach the surface it was
/// pressed on.
#[test]
fn multi_step_menu_navigation_renders_at_every_step() {
    let mut host = host();

    // ── 1. /offerings — the menu appears.
    let before = seen(&host);
    let (_, decision) = route_text_decided(&mut host, CHAT, None, ALICE, "/offerings");
    assert!(matches!(decision, TextDecision::Menu), "{decision:?}");
    assert!(
        seen(&host) > before,
        "step 1 (/offerings) must paint something in the chat"
    );
    let menu_1 = menu_message(&host);
    let menu_keyboard = host
        .frontend()
        .transport()
        .visible(menu_1)
        .and_then(|req| req.reply_markup.as_ref())
        .expect("the menu carries an inline keyboard");
    assert_eq!(
        menu_keyboard.inline_keyboard.len(),
        host.list_offerings().len(),
        "one menu button per registered offering"
    );

    // ── 2. Press "open dungeon" ON THE MENU MESSAGE — the submenu (the offering's surface).
    let before = seen(&host);
    let (_, decision) = route_callback_decided(
        &mut host,
        CallbackQuery::press_on_message(
            CHAT,
            menu_1,
            ALICE,
            encode_callback(TURN_OPEN, menu_index(&host, "dungeon")),
        ),
    );
    assert!(
        matches!(&decision, PressDecision::Opened(key) if key == "dungeon"),
        "step 2 must open the dungeon, got {decision:?}"
    );
    assert!(
        seen(&host) > before,
        "step 2 (open dungeon) must paint the dungeon surface"
    );
    let dungeon_message = surface_message(&host, "dungeon");
    assert_ne!(
        dungeon_message.0, menu_1.0,
        "the offering gets its OWN message, not the menu's"
    );

    // ── 3. BACK — /offerings again. THIS is the step that used to be invisible: the menu
    //       message already exists, so a re-present would EDIT it up the scrollback and the
    //       command replies nothing. It must post a FRESH message instead.
    let before = seen(&host);
    let (_, decision) = route_text_decided(&mut host, CHAT, None, ALICE, "/offerings");
    assert!(matches!(decision, TextDecision::Menu), "{decision:?}");
    assert!(
        seen(&host) > before,
        "step 3 (BACK to the menu) must paint something — an in-place edit of a scrolled-away \
         menu is not a visible response"
    );
    let menu_2 = menu_message(&host);
    assert_ne!(
        menu_2.0, menu_1.0,
        "asking for the menu again REPOSTS it at the bottom of the chat"
    );

    // ── 4. Press a DIFFERENT offering on the fresh menu message.
    let before = seen(&host);
    let (_, decision) = route_callback_decided(
        &mut host,
        CallbackQuery::press_on_message(
            CHAT,
            menu_2,
            ALICE,
            encode_callback(TURN_OPEN, menu_index(&host, "craft")),
        ),
    );
    assert!(
        matches!(&decision, PressDecision::Opened(key) if key == "craft"),
        "step 4 must open craft, got {decision:?}"
    );
    assert!(seen(&host) > before, "step 4 must paint the craft surface");
    let craft_message = surface_message(&host, "craft");
    assert!(
        craft_message.0 != dungeon_message.0 && craft_message.0 != menu_2.0,
        "three distinct live surfaces coexist in the chat"
    );

    // ── 5. A press on the FIRST offering's message still reaches the FIRST offering, even
    //       though craft was opened after it (the menu press must not steal the dungeon's
    //       keyboard).
    let dungeon_button = host
        .frontend()
        .transport()
        .visible(dungeon_message)
        .and_then(|req| req.reply_markup.as_ref())
        .and_then(|kb| kb.inline_keyboard.iter().flatten().next())
        .map(|b| b.callback_data.clone())
        .expect("the dungeon surface offers at least one affordance");
    let (_, decision) = route_callback_decided(
        &mut host,
        CallbackQuery::press_on_message(CHAT, dungeon_message, ALICE, dungeon_button),
    );
    match decision {
        PressDecision::Landed { key, .. } | PressDecision::ExecutorRefused { key, .. } => {
            assert_eq!(
                key, "dungeon",
                "the press reached the message's own offering"
            );
        }
        other => panic!("step 5 must reach the dungeon's substrate, got {other:?}"),
    }

    // ── 6. The oldest menu message is still routable — pressing it opens, it is not a dead
    //       button just because the menu was reposted.
    let (_, decision) = route_callback_decided(
        &mut host,
        CallbackQuery::press_on_message(
            CHAT,
            menu_1,
            ALICE,
            encode_callback(TURN_OPEN, menu_index(&host, "dungeon")),
        ),
    );
    assert!(
        matches!(&decision, PressDecision::Opened(key) if key == "dungeon"),
        "a press on the reposted-away menu message still opens, got {decision:?}"
    );
}

/// **`/open <key>` twice must be visible twice.** The same invisible-edit bug, on the command
/// that names an offering directly.
#[test]
fn reopening_an_offering_reposts_instead_of_editing_a_scrolled_away_message() {
    let mut host = host();

    let (_, first) = route_text_decided(&mut host, CHAT, None, ALICE, "/open dungeon");
    assert!(
        matches!(&first, TextDecision::Open { err: None, .. }),
        "{first:?}"
    );
    let first_message = surface_message(&host, "dungeon");

    let before = seen(&host);
    let (_, second) = route_text_decided(&mut host, CHAT, None, ALICE, "/open dungeon");
    assert!(
        matches!(&second, TextDecision::Open { err: None, .. }),
        "{second:?}"
    );
    assert!(
        seen(&host) > before,
        "re-opening must paint a visible message"
    );
    assert_ne!(
        surface_message(&host, "dungeon").0,
        first_message.0,
        "re-opening REPOSTS the live surface at the bottom of the chat"
    );
}

/// **After a restart, a button pressed on a pre-restart message must not be dead.**
///
/// A fresh `TelegramHost` models the restarted process: its in-memory message index is empty, so
/// the press names a message it has never presented. It must resume the chat's durable session
/// and repost a live surface, not refuse.
#[test]
fn a_press_on_a_message_this_process_never_presented_is_not_a_dead_button() {
    let dir = tempfile::tempdir().expect("a temp session dir");
    let store = dir.path().to_path_buf();

    // ── Process #1: open the dungeon and play one turn, durably.
    let pre_restart_message = {
        let build = {
            let store = store.clone();
            move || dreggnet_telegram::runtime::try_durable_telegram_host(store, Vec::new())
        };
        let mut host: Host = TelegramHost::try_with_hosts_and_game_epochs(
            BOT_SECRET,
            MockTransport::new(),
            build,
            dreggnet_catalog::PlayerWorlds::new,
            dreggnet_catalog::GameEpochLedger::in_memory_random().expect("epoch ledger"),
        )
        .expect("the durable host opens");
        route_text_decided(&mut host, CHAT, None, ALICE, "/open dungeon");
        surface_message(&host, "dungeon")
    };

    // ── Process #2: the SAME store, a brand-new in-memory frontend (the restart).
    let build = {
        let store = store.clone();
        move || dreggnet_telegram::runtime::try_durable_telegram_host(store, Vec::new())
    };
    let mut host: Host = TelegramHost::try_with_hosts_and_game_epochs(
        BOT_SECRET,
        MockTransport::new(),
        build,
        dreggnet_catalog::PlayerWorlds::new,
        dreggnet_catalog::GameEpochLedger::in_memory_random().expect("epoch ledger"),
    )
    .expect("the durable host reopens");

    assert!(
        host.frontend()
            .surface_of_message(CHAT, None, pre_restart_message)
            .is_none(),
        "the restarted process has never presented that message — this is the whole setup"
    );

    let (ack, decision) = route_callback_decided(
        &mut host,
        CallbackQuery::press_on_message(
            CHAT,
            pre_restart_message,
            ALICE,
            encode_callback("choose", 0),
        ),
    );
    assert!(
        !matches!(decision, PressDecision::NoSession),
        "the durable session must be resumed, not reported missing: {ack}"
    );
    assert!(
        !host.frontend().transport().sent_to(CHAT).is_empty(),
        "the restart-resume path must REPOST a live surface into the chat, not leave the user \
         with only dead buttons"
    );
    assert!(
        host.active_offering(&chat_session()).is_some(),
        "the chat is bound to its resumed offering again"
    );
}

/// **`/cancel` always works — with a session, mid-armed-text, and from a cold chat.**
#[test]
fn cancel_is_an_escape_from_every_state() {
    // ── From a cold chat with nothing open.
    let mut host = host();
    let (reply, decision) = route_text_decided(&mut host, CHAT, None, ALICE, "/cancel");
    assert!(
        matches!(&decision, TextDecision::Cancelled { cleared } if cleared.is_empty()),
        "{decision:?}"
    );
    assert!(reply.is_some(), "/cancel always answers");
    assert!(
        !host.frontend().transport().sent_to(CHAT).is_empty(),
        "/cancel reposts the menu so the user has somewhere to go"
    );

    // ── With sessions open: they are cleared from the chat's presentation state, and the
    //    committed sessions survive (a re-open brings them back).
    let mut host = host();
    route_text_decided(&mut host, CHAT, None, ALICE, "/open dungeon");
    route_text_decided(&mut host, CHAT, None, ALICE, "/open craft");
    let (_, decision) = route_text_decided(&mut host, CHAT, None, ALICE, "/cancel");
    let TextDecision::Cancelled { cleared } = decision else {
        panic!("expected Cancelled, got {decision:?}");
    };
    assert!(
        cleared.contains(&"dungeon".to_string()) && cleared.contains(&"craft".to_string()),
        "both surfaces were cleared: {cleared:?}"
    );
    assert!(
        host.frontend()
            .surfaces_in_chat(&chat_session())
            .iter()
            .all(|sid| TelegramFrontend::<MockTransport>::offering_of(sid) == Some("@menu")),
        "only the freshly-reposted menu remains live in the chat"
    );

    // The committed session is NOT destroyed — /open brings it straight back.
    let (_, reopened) = route_text_decided(&mut host, CHAT, None, ALICE, "/open dungeon");
    assert!(
        matches!(&reopened, TextDecision::Open { err: None, .. }),
        "a cancelled chat re-opens its untouched session: {reopened:?}"
    );

    // ── Mid-armed-text: /cancel disarms, so the next plain message is chatter again.
    let mut host = host();
    route_text_decided(&mut host, CHAT, None, ALICE, "/open doc");
    let doc_message = surface_message(&host, "doc");
    let text_button = host
        .frontend()
        .session(&TelegramFrontend::<MockTransport>::surface_id(
            CHAT, None, "doc",
        ))
        .and_then(|slot| {
            slot.presented
                .iter()
                .find(|a| a.wants_text && a.text.is_none())
                .cloned()
        });
    // NOT conditional: the document surface DOES offer a free-text template (that is what
    // `free_text_routing.rs` arms), so an absent one is a regression, not a reason to skip.
    let action = text_button.expect("the doc surface offers a free-text affordance to arm");
    let press = host.press(CallbackQuery::press_on_message(
        CHAT,
        doc_message,
        ALICE,
        encode_callback(&action.turn, action.arg),
    ));
    assert!(
        matches!(press, HostPress::TextArmed { .. }),
        "the text slot armed: {press:?}"
    );
    assert!(
        host.pending_text_action(&chat_session()).is_some(),
        "the arm is pending"
    );
    route_text_decided(&mut host, CHAT, None, ALICE, "/cancel");
    assert!(
        host.pending_text_action(&chat_session()).is_none(),
        "/cancel disarms the pending text slot — the next message is chatter again"
    );
}

/// **`/close <key>` is the destructive escape — and it must not create a NEW wedge.**
///
/// It ends the session, forgets its durable move-log, and a fresh `/open` must work afterwards. A
/// catalog GAME additionally has an epoch generation bound to its address; closing without
/// retiring it would leave the ledger holding an `active` generation for a session that no longer
/// exists, so this drives a game key on purpose.
#[test]
fn close_forgets_the_move_log_and_a_fresh_open_still_works() {
    let dir = tempfile::tempdir().expect("a temp session dir");
    let store = dir.path().to_path_buf();
    let build = {
        let store = store.clone();
        move || dreggnet_telegram::runtime::try_durable_telegram_host(store, Vec::new())
    };
    let mut host: Host = TelegramHost::try_with_hosts_and_game_epochs(
        BOT_SECRET,
        MockTransport::new(),
        build,
        dreggnet_catalog::PlayerWorlds::new,
        dreggnet_catalog::GameEpochLedger::in_memory_random().expect("epoch ledger"),
    )
    .expect("the durable host opens");

    let (_, opened) = route_text_decided(&mut host, CHAT, None, ALICE, "/open dungeon");
    assert!(
        matches!(&opened, TextDecision::Open { err: None, .. }),
        "{opened:?}"
    );
    let logs_before = std::fs::read_dir(&store)
        .expect("the store dir exists")
        .filter_map(|e| e.ok())
        .filter(|e| e.path().extension().is_some_and(|x| x == "log"))
        .count();
    assert!(logs_before > 0, "the open persisted a move-log");

    let (reply, decision) = route_text_decided(&mut host, CHAT, None, ALICE, "/close dungeon");
    assert!(
        matches!(&decision, TextDecision::Closed { key, closed: true } if key == "dungeon"),
        "/close ends the session: {decision:?} ({reply:?})"
    );
    let logs_after = std::fs::read_dir(&store)
        .expect("the store dir exists")
        .filter_map(|e| e.ok())
        .filter(|e| e.path().extension().is_some_and(|x| x == "log"))
        .count();
    assert!(
        logs_after < logs_before,
        "/close FORGOT the durable move-log ({logs_before} → {logs_after})"
    );

    // The whole point of an escape hatch: what comes after it works.
    let (_, reopened) = route_text_decided(&mut host, CHAT, None, ALICE, "/open dungeon");
    assert!(
        matches!(&reopened, TextDecision::Open { err: None, .. }),
        "a closed game re-opens clean — /close must not wedge the address: {reopened:?}"
    );

    // Closing something that is not open says so, and is not an error.
    let (_, none_open) = route_text_decided(&mut host, CHAT, None, ALICE, "/close craft");
    assert!(
        matches!(&none_open, TextDecision::Closed { closed: false, .. }),
        "{none_open:?}"
    );
}

/// **An armed free-text slot EXPIRES.** Without a TTL a chat that armed a slot and walked away
/// has every later message swallowed into that offering, forever, with no input able to clear it.
#[test]
fn an_armed_text_slot_expires_and_stops_swallowing_messages() {
    let mut host = host();
    route_text_decided(&mut host, CHAT, None, ALICE, "/open doc");
    let doc_message = surface_message(&host, "doc");
    // NOT conditional (see `cancel_is_an_escape_from_every_state`): a doc surface without a
    // free-text template would make this test vacuous, so demand one.
    let action = host
        .frontend()
        .session(&TelegramFrontend::<MockTransport>::surface_id(
            CHAT, None, "doc",
        ))
        .and_then(|slot| {
            slot.presented
                .iter()
                .find(|a| a.wants_text && a.text.is_none())
                .cloned()
        })
        .expect("the doc surface offers a free-text affordance to arm");

    let press = host.press(CallbackQuery::press_on_message(
        CHAT,
        doc_message,
        ALICE,
        encode_callback(&action.turn, action.arg),
    ));
    assert!(matches!(press, HostPress::TextArmed { .. }), "{press:?}");
    assert!(
        host.pending_text_action(&chat_session()).is_some(),
        "armed now"
    );

    host.backdate_arms(dreggnet_telegram::host::TEXT_ARM_TTL + std::time::Duration::from_secs(1));
    assert!(
        host.pending_text_action(&chat_session()).is_none(),
        "an arm older than TEXT_ARM_TTL is not honoured"
    );
    let (_, decision) = route_text_decided(&mut host, CHAT, None, ALICE, "just chatting");
    assert!(
        matches!(decision, TextDecision::Ignored),
        "after expiry a plain message is ordinary chatter, not offering input: {decision:?}"
    );
}
