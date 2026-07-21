//! **The RUNTIME-SHELL proof — the update loop's decode + route drives real turns, and a
//! restart resumes a persisted session.** All over [`MockTransport`]: no token, no network —
//! exactly the seam split the shell is built on (the only untestable inch is the live
//! `api.telegram.org` edge, which needs the ops-gated token).
//!
//! - a REAL Bot API `getUpdates` JSON body (a `callback_query` update) decodes to the typed
//!   event, routes through the ONE router, lands a REAL substrate turn, and re-presents;
//! - the text-command surface (`/help`, `/offerings`, `/open`, `/verify`) routes;
//! - a session persisted through the durable [`FileResumeStore`]-backed host SURVIVES a process
//!   restart: a stale button press from before the restart auto-resumes the chat and still
//!   lands, and the resumed chain re-verifies by replay.

use std::path::PathBuf;

use dreggnet_telegram::api::encode_callback;
use dreggnet_telegram::host::{HostPress, TelegramHost};
use dreggnet_telegram::runtime::{
    BotEvent, HELP_TEXT, durable_telegram_host, parse_updates, route_callback, route_text,
};
use dreggnet_telegram::transport::MockTransport;
use dreggnet_telegram::{CallbackQuery, TelegramFrontend};
use dungeon_on_dregg::{KP_CLAIM_RED, KP_PRESS_ON};
use serde_json::json;

/// A deterministic bot secret (a real deploy loads/derives 32 bytes in the bin).
const BOT_SECRET: [u8; 32] = [9u8; 32];
const ALICE: u64 = 1001;

/// A fresh in-memory host (no council members needed for the dungeon).
fn host() -> TelegramHost<MockTransport> {
    TelegramHost::new(BOT_SECRET, MockTransport::new(), &[])
}

/// A unique scratch directory for one test (pid + a monotone counter), created fresh.
fn scratch_dir(tag: &str) -> PathBuf {
    use std::sync::atomic::{AtomicU64, Ordering};
    static N: AtomicU64 = AtomicU64::new(0);
    let n = N.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!(
        "tg-runtime-shell-{}-{}-{}",
        std::process::id(),
        tag,
        n
    ));
    let _ = std::fs::remove_dir_all(&dir);
    dir
}

/// A REAL `getUpdates` result body (the exact JSON shape Telegram sends for an inline-button
/// press) decodes to the typed callback event, routes through the ONE router, lands ONE real
/// substrate turn, and the surface is re-presented for the next press.
#[test]
fn a_simulated_callback_update_drives_a_real_advance_and_represents() {
    let mut h = host();
    let chat: i64 = 42;
    let sid = h
        .open("dungeon", chat, None, ALICE)
        .expect("the dungeon opens");
    let sent_before = h.frontend().transport().sent.len();

    // The wire shape: a callback_query update, its `data` exactly a presented button's payload.
    let data = encode_callback("choose", KP_PRESS_ON as i64);
    let result = json!([{
        "update_id": 700,
        "callback_query": {
            "id": "cbq-1",
            "from": { "id": ALICE, "is_bot": false, "first_name": "Alice" },
            "message": {
                "message_id": 1,
                "chat": { "id": chat, "type": "private" },
                "text": "…"
            },
            "data": data,
        }
    }]);

    let (events, next) = parse_updates(&result);
    assert_eq!(next, Some(701), "the next poll offset confirms the update");
    assert_eq!(events.len(), 1, "one decoded event");
    let BotEvent::Callback { callback_id, query } = &events[0] else {
        panic!(
            "a callback_query decodes to BotEvent::Callback, got {:?}",
            events[0]
        );
    };
    assert_eq!(callback_id, "cbq-1");
    assert_eq!(query.chat_id, chat);
    assert_eq!(query.from_user_id, ALICE);
    assert_eq!(query.data, data);

    // Route it — the press must land a REAL verified turn on the substrate.
    let ack = route_callback(&mut h, query.clone());
    assert!(
        ack.contains("landed"),
        "the ack reports the landed turn: {ack}"
    );

    // The surface was re-presented (the next press resolves against the current keyboard).
    let sent_after = h.frontend().transport().sent.len();
    assert!(
        sent_after > sent_before,
        "the advance re-presented the surface ({sent_before} → {sent_after})"
    );

    // And the committed chain really grew: genesis + one landed turn.
    let report = h.verify("dungeon", &sid).expect("the session is live");
    assert!(report.verified, "the chain re-verifies: {}", report.detail);
    assert_eq!(report.turns, 2, "genesis + the one routed turn");
}

/// The text-command surface routes: `/help` answers, `/offerings` presents the menu keyboard,
/// `/open` opens an offering, `/verify` reaches the real re-verifier, and a malformed update
/// entry is skipped, never a crash.
#[test]
fn text_commands_route_through_the_shell() {
    let mut h = host();
    let chat: i64 = 55;

    assert_eq!(
        route_text(&mut h, chat, None, ALICE, "/help").as_deref(),
        Some(HELP_TEXT),
        "/help answers the command surface"
    );

    // /offerings presents the menu — a message whose keyboard has one row per offering.
    assert_eq!(route_text(&mut h, chat, None, ALICE, "/offerings"), None);
    let menu = h.frontend().transport().last().expect("the menu was sent");
    let rows = menu
        .reply_markup
        .as_ref()
        .expect("the menu is an inline keyboard")
        .inline_keyboard
        .len();
    assert_eq!(
        rows,
        h.list_offerings().len(),
        "one open-button per registered offering"
    );

    // /open (with the group-style @botname suffix) opens the offering in the chat.
    assert_eq!(
        route_text(&mut h, chat, None, ALICE, "/open@DreggBot dungeon"),
        None
    );
    let sid = TelegramFrontend::<MockTransport>::session_id(chat, None);
    assert_eq!(h.active_offering(&sid), Some("dungeon"));

    // /verify reaches the offering's REAL re-verifier through the same router.
    let reply = route_text(&mut h, chat, None, ALICE, "/verify").expect("/verify replies");
    assert!(
        reply.contains("re-verified by replay"),
        "the verify reply carries the real report: {reply}"
    );

    // An unknown offering is an honest error, not a panic.
    let err = route_text(&mut h, chat, None, ALICE, "/open not-a-thing").expect("errors reply");
    assert!(err.contains("Cannot open"), "honest refusal: {err}");

    // A malformed update entry (no data, no text) is skipped.
    let (events, next) = parse_updates(&json!([{ "update_id": 1, "callback_query": {"id": "x"} }]));
    assert!(events.is_empty(), "a partial update decodes to nothing");
    assert_eq!(next, Some(2), "…but its offset is still consumed");
}

/// **The restart tooth**: a session played through a durable-store host SURVIVES a process
/// restart — the fresh host resumes it by move-log replay on boot, a STALE button press from
/// before the restart auto-rebinds the chat (`resume_chat` inside `route_callback`) and still
/// lands, and the whole resumed chain re-verifies.
#[test]
fn a_restart_resumes_a_persisted_session_and_a_stale_press_still_lands() {
    let dir = scratch_dir("restart");
    let chat: i64 = 7;
    let sid = TelegramFrontend::<MockTransport>::session_id(chat, None);

    // ── Process 1: open the dungeon, land one real turn, then "crash" (drop). ──
    {
        let d = dir.clone();
        let mut h1 = TelegramHost::with_host(BOT_SECRET, MockTransport::new(), move || {
            durable_telegram_host(Some(d), vec![])
        });
        h1.open("dungeon", chat, None, ALICE).expect("opens");
        match h1.press(CallbackQuery::press(
            chat,
            ALICE,
            encode_callback("choose", KP_PRESS_ON as i64),
        )) {
            HostPress::Advanced { outcome, .. } => {
                assert!(outcome.landed(), "the first turn landed: {outcome:?}")
            }
            other => panic!("expected an advance, got {other:?}"),
        }
    }
    assert!(
        std::fs::read_dir(&dir)
            .map(|d| d.count() > 0)
            .unwrap_or(false),
        "the move-log is durably on disk"
    );

    // ── Process 2: a FRESH host over the same dir (the restart). ──
    let d = dir.clone();
    let mut h2 = TelegramHost::with_host(BOT_SECRET, MockTransport::new(), move || {
        durable_telegram_host(Some(d), vec![])
    });

    // A stale button press from BEFORE the restart: this process never presented anything, so
    // the raw router answers NoSession — route_callback auto-resumes the chat and retries.
    let ack = route_callback(
        &mut h2,
        CallbackQuery::press(chat, ALICE, encode_callback("choose", KP_CLAIM_RED as i64)),
    );
    assert!(
        ack.contains("landed"),
        "the stale press auto-resumed the chat and landed: {ack}"
    );

    // The resumed chain is the SAME session: genesis + the pre-restart turn + the new one.
    let report = h2
        .verify("dungeon", &sid)
        .expect("the resumed session is live");
    assert!(
        report.verified,
        "the resumed chain re-verifies by replay: {}",
        report.detail
    );
    assert_eq!(
        report.turns, 3,
        "genesis + the pre-restart turn + the post-restart turn — nothing was dropped"
    );

    // A chat with NO persisted session is still an honest miss after the resume path.
    let miss = route_callback(
        &mut h2,
        CallbackQuery::press(999, ALICE, encode_callback("choose", 1)),
    );
    assert!(
        miss.contains("/offerings"),
        "an unknown chat is pointed at the menu: {miss}"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

/// The composed native campaign rides the same durable Telegram host: its submitted `delve`
/// survives process death, a stale `smite` press rebinds the chat to that exact campaign, and
/// the actor-bound dual-executor journal re-verifies. No helper plays either move for the user.
#[test]
fn the_descent_campaign_is_playable_and_restart_safe_on_telegram() {
    let dir = scratch_dir("descent-campaign-restart");
    let chat: i64 = 73;
    let sid = TelegramFrontend::<MockTransport>::session_id(chat, None);

    {
        let d = dir.clone();
        let mut h1 = TelegramHost::with_host(BOT_SECRET, MockTransport::new(), move || {
            durable_telegram_host(Some(d), vec![])
        });
        h1.open("descent-campaign", chat, None, ALICE)
            .expect("the campaign opens from Telegram's shared catalog");
        match h1.press(CallbackQuery::press(
            chat,
            ALICE,
            encode_callback("delve", 0),
        )) {
            HostPress::Advanced { key, outcome } => {
                assert_eq!(key, "descent-campaign");
                assert!(outcome.landed(), "the manual delve landed: {outcome:?}");
            }
            other => panic!("the presented campaign delve must advance: {other:?}"),
        }
        let report = h1
            .verify("descent-campaign", &sid)
            .expect("campaign is live");
        assert!(report.verified, "{}", report.detail);
        assert_eq!(report.turns, 2);
    }

    let d = dir.clone();
    let mut h2 = TelegramHost::with_host(BOT_SECRET, MockTransport::new(), move || {
        durable_telegram_host(Some(d), vec![])
    });
    let ack = route_callback(
        &mut h2,
        CallbackQuery::press(chat, ALICE, encode_callback("smite", 0)),
    );
    assert!(
        ack.contains("landed"),
        "the stale campaign press resumes and lands: {ack}"
    );
    let report = h2
        .verify("descent-campaign", &sid)
        .expect("the restarted campaign is live");
    assert!(report.verified, "{}", report.detail);
    assert_eq!(
        report.turns, 3,
        "genesis plus the pre- and post-restart player moves"
    );

    let _ = std::fs::remove_dir_all(&dir);
}
