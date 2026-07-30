//! **The driven end-to-end proof — a `DungeonOffering` played through the `TelegramFrontend`.**
//!
//! The SAME offering core `dreggnet-offerings/tests/driven.rs` drives through a `MockFrontend`,
//! driven here through a REAL [`TelegramFrontend`] over a network-free [`MockTransport`] — NO
//! Discord, NO Telegram token, NO network. It proves the offering core is frontend-agnostic: the
//! same `DungeonOffering`, a new renderer.
//!
//! What is asserted at the logic level (what a live token would add is only the actual HTTP
//! send/long-poll — the [`transport::Transport`] seam):
//! - **render → a Telegram message + inline keyboard**: `present` builds the real `sendMessage`
//!   wire body (asserted as JSON), with ONE inline-keyboard button per cap-gated affordance, each
//!   button's `callback_data` carrying its `{turn, arg}`;
//! - **collect(callback_query) → (SessionId, Action, DreggIdentity)**: a synthetic press decodes
//!   back into the exact typed [`Action`] the core resolves, attributed to the presser's derived
//!   identity;
//! - **a real turn**: the collected action, resolved on the substrate, lands a real `TurnReceipt`
//!   (a winning line), and an illegal move is a real executor `Refused` (the anti-ghost tooth);
//! - **verify()** re-verifies the whole committed chain by replay;
//! - **identity** is a real derived Ed25519 key, deterministic + distinct per Telegram user.

use dreggnet_offerings::dungeon::{DungeonOffering, KEEP_NAME, TURN_CHOOSE};
use dreggnet_offerings::{Frontend, Offering, Outcome, SessionConfig};
use dreggnet_telegram::api::{
    LOCK_GLYPH, TELEGRAM_KEYBOARD_MAX_ROWS, TELEGRAM_PARSE_MODE, TELEGRAM_TEXT_LIMIT,
    decode_callback, encode_callback,
};
use dreggnet_telegram::cipherclerk::TelegramCipherclerk;
use dreggnet_telegram::render::{fit_surface_for_wire, render_surface_html, render_surface_text};
use dreggnet_telegram::transport::MockTransport;
use dreggnet_telegram::{CallbackQuery, ChatKind, TelegramFrontend};
use dungeon_on_dregg::{KP_CLAIM_RED, KP_PRESS_ON, KP_TRADE_BLOWS};

const BOT_SECRET: [u8; 32] = [7u8; 32];
/// A private-chat (DM) id — positive → single-player.
const DM_CHAT: i64 = 1001;

fn new_fe() -> TelegramFrontend<MockTransport> {
    TelegramFrontend::new(BOT_SECRET, MockTransport::new())
}

/// `render` → a Telegram message + an inline keyboard of one button per cap-gated affordance; the
/// sent request IS the real Bot API `sendMessage` wire body (asserted as JSON), each button's
/// `callback_data` carrying its `{turn, arg}`.
#[test]
fn present_builds_a_message_and_one_keyboard_button_per_affordance() {
    let off = DungeonOffering::new();
    let s = off
        .open(SessionConfig::with_seed(3))
        .expect("the Keep opens");
    let acts = off.actions(&s);
    assert!(acts.len() >= 2, "the gatehall offers >1 candidate move");
    let surface = off.render(&s);

    let mut fe = new_fe();
    let sid = TelegramFrontend::<MockTransport>::session_id(DM_CHAT, None);
    fe.spin_session(sid.clone());
    fe.present(&sid, &surface, &acts);

    let req = fe.transport().last().expect("a sendMessage was sent");
    assert_eq!(
        req.chat_id, DM_CHAT,
        "the message targets the session's chat"
    );
    assert!(
        req.text.contains(KEEP_NAME),
        "the message text names the Keep + room: {:?}",
        req.text
    );
    // The text half is the deos surface walked to prose — the Menu is NOT duplicated into text —
    // in the WIRE form: entity-escaped, with any board fenced, matching the `parse_mode` below.
    //
    // ⚑ AND THE MESSAGE IS THE FITTED HEAD, NOT NECESSARILY THE WHOLE SURFACE. This used to assert
    // `req.text == render_surface_html(&surface)` outright, which was true only while every surface
    // fit in one Telegram message. The Keep's does not (4,705 characters against a 4,096 ceiling),
    // and the adapter now continues the tail into companion pages rather than refusing to paint at
    // all (`render::fit_surface_for_wire`). So the contract asserted here is the stronger one: the
    // message carries the HEAD of that split, and the split is LOSSLESS — head plus continuation
    // covers the whole surface, with nothing dropped on the floor.
    let (head, continuation) = fit_surface_for_wire(&surface, TELEGRAM_TEXT_LIMIT);
    assert_eq!(
        req.text,
        render_surface_html(&head),
        "the message text is the rendered surface head, in the form the parse mode declares"
    );
    assert!(
        req.text.chars().count() <= TELEGRAM_TEXT_LIMIT,
        "the head fits Telegram's ceiling: {} chars",
        req.text.chars().count()
    );
    // NOTHING WAS DROPPED: every line of the full surface is either in the message or on a
    // continuation page. Asserted over the PLAIN reading, because the pages carry no parse mode.
    let carried = format!(
        "{}\n{}",
        render_surface_text(&head),
        continuation.join("\n")
    );
    // `▸` is the walker's DEPTH marker for a nested section heading, not content: a section that
    // moves to a page of its own is rendered at depth 0 there and heads it without one. Comparing
    // with the marker stripped keeps this about what was carried, not about where it sits.
    let carried = carried.replace("▸ ", "");
    for line in render_surface_text(&surface).lines() {
        let line = line.trim().trim_start_matches("▸ ");
        // The continuation note is new text the head gained; the surface never had it.
        if line.is_empty() || line.starts_with("The last ") {
            continue;
        }
        assert!(
            carried.contains(line),
            "the split lost a line of the surface: {line:?}"
        );
    }
    assert_eq!(
        req.parse_mode.as_deref(),
        Some(TELEGRAM_PARSE_MODE),
        "an interactive surface declares its parse mode, or its board is laid out proportionally"
    );

    let kb = req
        .reply_markup
        .as_ref()
        .expect("a non-terminal room offers an inline keyboard");
    // ONE BUTTON per cap-gated affordance — but not one ROW each: the renderer packs short labels
    // several to a row and bounds the total (`TELEGRAM_KEYBOARD_MAX_ROWS`), so the shape to assert
    // is the button set, not the row count. The gatehall is well under the bound, so nothing is
    // dropped and the buttons appear in the offering's own order.
    let buttons: Vec<_> = kb.inline_keyboard.iter().flatten().collect();
    assert_eq!(
        buttons.len(),
        acts.len(),
        "one keyboard button per cap-gated affordance"
    );
    assert!(
        kb.inline_keyboard.len() <= TELEGRAM_KEYBOARD_MAX_ROWS,
        "the keyboard is bounded: {} rows",
        kb.inline_keyboard.len()
    );
    // Asserted as a SET, not a sequence: the renderer sorts live affordances ahead of locked ones,
    // so the keyboard's order is the offering's order WITHIN each band, not across them.
    for act in &acts {
        let wire = encode_callback(&act.turn, act.arg);
        let btn = buttons
            .iter()
            .find(|b| b.callback_data == wire)
            .unwrap_or_else(|| panic!("{} is on the keyboard", act.label));
        // decode round-trips back to the same (turn, arg).
        assert_eq!(
            decode_callback(&btn.callback_data),
            Some((act.turn.clone(), act.arg)),
            "callback_data decodes back to the affordance"
        );
    }

    // The sent struct IS the real Bot API `sendMessage` JSON wire body.
    let json = serde_json::to_string(req).expect("serialize the sendMessage body");
    assert!(
        json.contains("\"chat_id\":1001"),
        "wire body carries chat_id: {json}"
    );
    assert!(
        json.contains("\"inline_keyboard\""),
        "wire body carries the keyboard: {json}"
    );
    assert!(
        json.contains("\"callback_data\":\"choose:"),
        "buttons carry callback_data: {json}"
    );
}

/// `collect(callback_query)` → the exact typed `(SessionId, Action, DreggIdentity)` — a synthetic
/// press decodes back to the presented affordance and is attributed to the presser's derived id.
#[test]
fn collect_maps_a_press_back_to_the_typed_action_and_derived_identity() {
    let off = DungeonOffering::new();
    let s = off.open(SessionConfig::with_seed(3)).expect("open");
    let acts = off.actions(&s);

    let mut fe = new_fe();
    let sid = TelegramFrontend::<MockTransport>::session_id(DM_CHAT, None);
    fe.spin_session(sid.clone());
    fe.present(&sid, &off.render(&s), &acts);

    // A press of the press-on button by Telegram user 42.
    let ev = CallbackQuery::press(
        DM_CHAT,
        42,
        encode_callback(TURN_CHOOSE, KP_PRESS_ON as i64),
    );
    let (got_sid, action, actor) = fe
        .collect(ev)
        .expect("a press maps back to a presented affordance");
    assert_eq!(
        got_sid, sid,
        "the session is reconstructed from the chat id"
    );
    assert_eq!(action.turn, TURN_CHOOSE);
    assert_eq!(action.arg, KP_PRESS_ON as i64);
    assert_eq!(
        actor,
        fe.identity(42),
        "the press is attributed to the presser's derived dregg identity"
    );

    // A press of an affordance never presented (a chat with nothing on offer) collects None.
    let stray = CallbackQuery::press(DM_CHAT, 42, encode_callback("choose", 999));
    assert!(
        fe.collect(stray).is_none(),
        "an unpresented affordance is not collected (the frontend never offered it)"
    );
    // A press in an unknown chat collects None.
    let elsewhere =
        CallbackQuery::press(7777, 42, encode_callback(TURN_CHOOSE, KP_PRESS_ON as i64));
    assert!(
        fe.collect(elsewhere).is_none(),
        "a press in an unknown chat is not collected"
    );
}

/// **The HARD GATE — a `DungeonOffering` plays a winning line through the `TelegramFrontend`.**
/// The full lifecycle: spin → present → collect a press → the CORE advances one real turn →
/// re-present → … → teardown; each move a real landed `TurnReceipt`; the whole chain re-verifies.
#[test]
fn a_dungeon_plays_a_winning_line_through_telegram_and_verifies() {
    let off = DungeonOffering::new();
    let mut s = off.open(SessionConfig::with_seed(9)).expect("open");
    assert_eq!(s.current_passage_name().as_deref(), Some("gatehall"));
    assert_eq!(s.receipts_len(), 1, "genesis is the first verified turn");

    let mut fe = new_fe();
    let sid = TelegramFrontend::<MockTransport>::session_id(DM_CHAT, None);
    fe.spin_session(sid.clone());
    assert_eq!(
        fe.session(&sid).map(|slot| slot.kind),
        Some(ChatKind::Dm),
        "a positive chat id is single-player"
    );

    // Present the gatehall, then a Telegram user presses "press on".
    fe.present(&sid, &off.render(&s), &off.actions(&s));
    let press = CallbackQuery::press(
        DM_CHAT,
        42,
        encode_callback(TURN_CHOOSE, KP_PRESS_ON as i64),
    );
    let (_, action, actor) = fe.collect(press).expect("collect the press");

    // The CORE resolves it on the substrate — one real committed turn.
    match off.advance(&mut s, action, actor.clone()) {
        Outcome::Landed { receipt, ended } => {
            assert!(!ended, "pressing on does not end the Keep");
            assert_ne!(receipt.turn_hash, [0u8; 32], "a genuine committed turn");
        }
        other => panic!("a legal move must land a real receipt, got {other:?}"),
    }
    assert_eq!(s.receipts_len(), 2, "a real verified turn landed");
    assert_eq!(s.current_passage_name().as_deref(), Some("hall"));

    // Re-present the plundered hall, then press "claim the crown for the Red Hand".
    fe.present(&sid, &off.render(&s), &off.actions(&s));
    let claim = CallbackQuery::press(
        DM_CHAT,
        42,
        encode_callback(TURN_CHOOSE, KP_CLAIM_RED as i64),
    );
    let (_, action2, actor2) = fe.collect(claim).expect("collect the claim");
    assert!(
        off.advance(&mut s, action2, actor2).landed(),
        "claiming the crown lands a real turn"
    );
    assert_eq!(s.receipts_len(), 3);
    assert_eq!(
        s.actor_of_step(0),
        Some(&actor),
        "the mover is the presser's derived identity, not a Telegram nickname"
    );

    // The whole committed chain re-verifies by replay.
    let report = off.verify(&s);
    assert!(
        report.verified,
        "the honest line re-verifies: {}",
        report.detail
    );
    assert_eq!(report.turns, 3);

    // Teardown archives the session surface.
    fe.teardown(&sid);
    assert!(
        fe.session(&sid).is_none(),
        "teardown drops the session slot"
    );
}

/// An illegal move collected through Telegram is a real executor refusal (the anti-ghost tooth):
/// the ineligible affordance is shown as a dimmed lock-glyph button but is still pressable — firing
/// it commits nothing, lands no receipt, moves the world not at all. The honest prefix re-verifies.
#[test]
fn an_illegal_move_collected_through_telegram_is_refused_anti_ghost() {
    let off = DungeonOffering::new();
    let mut s = off.open(SessionConfig::with_seed(8)).expect("open");

    let mut fe = new_fe();
    let sid = TelegramFrontend::<MockTransport>::session_id(DM_CHAT, None);
    fe.spin_session(sid.clone());

    // Two survivable trade-blows (hp 50 → 30 → 10), each collected through Telegram + landed.
    for _ in 0..2 {
        fe.present(&sid, &off.render(&s), &off.actions(&s));
        let blow = CallbackQuery::press(
            DM_CHAT,
            42,
            encode_callback(TURN_CHOOSE, KP_TRADE_BLOWS as i64),
        );
        let (_, action, actor) = fe.collect(blow).expect("collect a survivable blow");
        assert!(
            off.advance(&mut s, action, actor).landed(),
            "a survivable blow lands"
        );
    }
    assert_eq!(s.read_var("hp"), 10, "two blows dropped hp to 10");
    let before = s.receipts_len();

    // At hp 10 the trade-blows affordance is a dimmed cap-tooth (its `{ hp >= 21 }` fails). It is
    // rendered as a LOCK_GLYPH button — shown, not hidden — but still carries callback_data.
    fe.present(&sid, &off.render(&s), &off.actions(&s));
    let req = fe.transport().last().expect("presented");
    let kb = req.reply_markup.as_ref().expect("keyboard");
    let locked = kb
        .inline_keyboard
        .iter()
        .flatten()
        .find(|b| b.callback_data == encode_callback(TURN_CHOOSE, KP_TRADE_BLOWS as i64))
        .expect("the trade-blows button is still offered");
    assert!(
        locked.text.starts_with(LOCK_GLYPH),
        "the ineligible affordance is a dimmed lock-glyph button, not hidden: {:?}",
        locked.text
    );

    // Press it anyway — the collected action carries enabled=false; the REAL executor refuses it.
    let press = CallbackQuery::press(
        DM_CHAT,
        42,
        encode_callback(TURN_CHOOSE, KP_TRADE_BLOWS as i64),
    );
    let (_, action, actor) = fe.collect(press).expect("collect the locked press");
    assert!(
        !action.enabled,
        "the collected affordance is the dimmed cap-tooth"
    );
    match off.advance(&mut s, action, actor) {
        Outcome::Refused(_) => {}
        other => panic!("a killing blow must be a real executor refusal, got {other:?}"),
    }
    assert_eq!(
        s.receipts_len(),
        before,
        "no receipt landed for the refused move"
    );
    assert_eq!(s.read_var("hp"), 10, "hp unchanged after the refusal");
    assert_eq!(
        s.current_passage_name().as_deref(),
        Some("gatehall"),
        "still in the gatehall — the world did not move"
    );
    assert!(
        off.verify(&s).verified,
        "the honest prefix re-verifies after the refusal"
    );
}

/// Identity is a REAL derived Ed25519 key (mirroring the discord `UserCipherclerk`): deterministic,
/// distinct per Telegram user, and equal to the standalone cipherclerk derivation.
#[test]
fn derived_identity_is_deterministic_distinct_and_a_real_ed25519_key() {
    let fe = new_fe();

    // Deterministic + distinct.
    assert_eq!(fe.identity(1), fe.identity(1), "same user → same identity");
    assert_ne!(
        fe.identity(1),
        fe.identity(2),
        "distinct users → distinct identities"
    );

    // A real Ed25519 public key: 32 bytes → 64 lowercase hex chars.
    let id = fe.identity(42);
    assert_eq!(
        id.as_str().len(),
        64,
        "an Ed25519 public key is 64 hex chars"
    );
    assert!(
        id.as_str().chars().all(|c| c.is_ascii_hexdigit()),
        "the identity is a hex-encoded key"
    );

    // Equal to the standalone cclerk derivation (the frontend derives no bespoke key).
    assert_eq!(
        id,
        TelegramCipherclerk::derive(&BOT_SECRET, 42).identity(),
        "identity() is exactly the derived cclerk's public-key handle"
    );
}

/// A group (negative chat id) is classified as a collective; a forum topic scopes a session under a
/// thread and round-trips through the session-id codec.
#[test]
fn group_and_forum_topic_session_classification_round_trips() {
    let mut fe = new_fe();

    let group = TelegramFrontend::<MockTransport>::session_id(-500, None);
    fe.spin_session(group.clone());
    assert_eq!(fe.session(&group).map(|s| s.kind), Some(ChatKind::Group));
    assert!(ChatKind::classify(-500, None).is_collective());

    let topic = TelegramFrontend::<MockTransport>::session_id(-500, Some(88));
    fe.spin_session(topic.clone());
    assert_eq!(
        fe.session(&topic).map(|s| s.kind),
        Some(ChatKind::ForumTopic)
    );
    // The session id encodes (chat, topic) reversibly.
    assert_eq!(
        TelegramFrontend::<MockTransport>::chat_of(&topic),
        Some((-500, Some(88)))
    );
    // The group and the topic are DISTINCT sessions in the same supergroup.
    assert_ne!(
        group, topic,
        "a forum topic is its own session under the group"
    );
}

/// The transport is the sole network seam: an armed failure surfaces as a `TransportError` through
/// the fallible `present_result`, and the (infallible) trait `present` records it observably.
#[test]
fn a_transport_failure_surfaces_and_does_not_panic() {
    // Arm the next send to fail at construction (spin_session sends nothing, so the first
    // present_result hits the one-shot armed failure).
    let mut transport = MockTransport::new();
    transport.fail_next("telegram: 429 Too Many Requests");
    let mut fe = TelegramFrontend::new(BOT_SECRET, transport);

    let sid = TelegramFrontend::<MockTransport>::session_id(DM_CHAT, None);
    fe.spin_session(sid.clone());

    let off = DungeonOffering::new();
    let s = off.open(SessionConfig::with_seed(3)).expect("open");
    let surface = off.render(&s);
    let acts = off.actions(&s);

    // The fallible form returns the armed error.
    let err = fe
        .present_result(&sid, &surface, &acts)
        .expect_err("the armed send fails");
    assert!(
        err.to_string().contains("429"),
        "the transport error is surfaced: {err}"
    );

    // A subsequent send succeeds (the failure was one-shot); the infallible trait `present`
    // records nothing further.
    assert!(
        fe.present_result(&sid, &surface, &acts).is_ok(),
        "the next send succeeds"
    );
    assert!(
        fe.last_send_error().is_none(),
        "no lingering error after a good send"
    );
}
