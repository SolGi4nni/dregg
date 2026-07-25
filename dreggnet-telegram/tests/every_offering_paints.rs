//! **No offering may open into SILENCE.**
//!
//! The frontend's `present` is infallible by signature: it swallows a transport error into
//! `last_send_error`, which no command surface ever read. So an offering whose surface exceeds
//! Telegram's 4096-character ceiling, or whose affordance encodes past the 64-byte
//! `callback_data` limit, or whose projection cannot be derived at all, would `open` with `Ok`,
//! ack "Opened …", and paint NOTHING — indistinguishable, from the chat, from a dead bot. Every
//! other test in this crate drives ONE offering, so none of them can see it.
//!
//! This walks the WHOLE registered catalog and demands one of exactly two honest outcomes per
//! offering:
//!
//! 1. it paints a message the user can see, or
//! 2. it refuses with a legible reason.
//!
//! `Ok` + nothing visible is the third outcome, and it is the bug.
//!
//! Handler layer over `MockTransport` — no token, no network. `MockTransport` never fails a send,
//! so what this proves is that every catalog surface REACHES the transport with a well-formed
//! request (the Bot API limit checks in `present_result_with_callback_data` run first and are the
//! realistic failure), and that no `Ok` open leaves the chat empty.

use dreggnet_telegram::host::TelegramHost;
use dreggnet_telegram::runtime::{TextDecision, route_text_decided};
use dreggnet_telegram::transport::MockTransport;

const BOT_SECRET: [u8; 32] = [0x71; 32];
/// A positive chat id → a DM, so nothing is refused for hiding per-player state.
const CHAT: i64 = 4242042;
const ALICE: u64 = 909090;

#[test]
fn every_registered_offering_opens_into_something_visible_or_says_why_not() {
    let mut host: TelegramHost<MockTransport> =
        TelegramHost::new(BOT_SECRET, MockTransport::new(), &[ALICE]);
    let keys: Vec<String> = host
        .list_offerings()
        .iter()
        .map(|o| o.key.clone())
        .collect();
    assert!(keys.len() >= 20, "the full catalog is mounted: {keys:?}");

    let mut painted = Vec::new();
    let mut refused = Vec::new();
    for key in &keys {
        let before = host.frontend().transport().sent_to(CHAT).len();
        let (reply, decision) =
            route_text_decided(&mut host, CHAT, None, ALICE, &format!("/open {key}"));
        let after = host.frontend().transport().sent_to(CHAT).len();
        match decision {
            TextDecision::Open { err: None, .. } => {
                assert!(
                    after > before,
                    "/open {key} answered Ok and painted NOTHING — the chat sees silence, which \
                     is exactly how a working bot reads as dead"
                );
                painted.push(key.clone());
            }
            TextDecision::Open { err: Some(why), .. } => {
                let reply = reply.unwrap_or_default();
                assert!(
                    !reply.trim().is_empty(),
                    "/open {key} refused ({why}) but replied nothing"
                );
                refused.push((key.clone(), why));
            }
            other => panic!("/open {key} did not route as an open: {other:?}"),
        }
    }

    // A refusal is allowed (a game that cannot bind its epoch here, say) — silence is not. But if
    // NOTHING painted, this test would be vacuously satisfied by a wholly broken catalog.
    assert!(
        painted.len() >= keys.len() / 2,
        "most of the catalog must actually paint; painted={painted:?} refused={refused:?}"
    );
}

/// The same demand for the MENU itself, which is the entry point every user meets first.
#[test]
fn the_offerings_menu_paints_a_button_per_offering() {
    let mut host: TelegramHost<MockTransport> =
        TelegramHost::new(BOT_SECRET, MockTransport::new(), &[ALICE]);
    let (_, decision) = route_text_decided(&mut host, CHAT, None, ALICE, "/offerings");
    assert!(
        matches!(decision, TextDecision::Menu),
        "the menu was presented, not refused: {decision:?}"
    );
    let sent = host.frontend().transport().sent_to(CHAT);
    let menu = sent.last().expect("the menu message went out");
    let keyboard = menu
        .reply_markup
        .as_ref()
        .expect("the menu carries an inline keyboard");
    assert_eq!(
        keyboard.inline_keyboard.len(),
        host.list_offerings().len(),
        "one button per registered offering"
    );
    // Telegram's own limits, asserted on the real wire body rather than assumed.
    assert!(
        menu.text.chars().count() <= dreggnet_telegram::api::TELEGRAM_TEXT_LIMIT,
        "the menu text fits Telegram's ceiling ({} chars)",
        menu.text.chars().count()
    );
    for button in keyboard.inline_keyboard.iter().flatten() {
        assert!(
            (1..=64).contains(&button.callback_data.len()),
            "`{}` carries 1..=64 callback bytes, found {}",
            button.text,
            button.callback_data.len()
        );
    }
}
