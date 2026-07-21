//! Cross-surface coherence for the Lean-authored native Descent.
//!
//! Telegram consumes the offering's ordered action list and renders it; it does not own a
//! second legality table. These tests select only what the current keyboard exposes, including
//! a locked action, so the native executor remains the sole referee throughout.

use dreggnet_offerings::native_descent::NativeDescentOffering;
use dreggnet_offerings::{Offering, Outcome, SessionConfig};
use dreggnet_telegram::CallbackQuery;
use dreggnet_telegram::api::{
    InlineKeyboardButton, LOCK_GLYPH, build_present_request, decode_callback, encode_callback,
};
use dreggnet_telegram::host::{HostPress, TURN_VERIFY, TelegramHost};
use dreggnet_telegram::runtime::describe_press;
use dreggnet_telegram::transport::MockTransport;
use dreggnet_telegram::verify_control::is_verify_callback;

const BOT_SECRET: [u8; 32] = [29; 32];
const ALICE: u64 = 41_001;
const BOB: u64 = 41_002;
const CHAT: i64 = 41_731;

fn host() -> TelegramHost<MockTransport> {
    TelegramHost::new(BOT_SECRET, MockTransport::new(), &[ALICE, BOB])
}

fn current_buttons(host: &TelegramHost<MockTransport>) -> Vec<InlineKeyboardButton> {
    host.frontend()
        .transport()
        .last()
        .expect("Descent has painted a Telegram surface")
        .reply_markup
        .as_ref()
        .map(|markup| {
            markup
                .inline_keyboard
                .iter()
                .flatten()
                .filter(|button| {
                    button.web_app.is_none()
                        && decode_callback(&button.callback_data)
                            .is_none_or(|(turn, arg)| !is_verify_callback(&turn, arg))
                })
                .cloned()
                .collect()
        })
        .unwrap_or_default()
}

fn current_text(host: &TelegramHost<MockTransport>) -> String {
    host.frontend()
        .transport()
        .last()
        .expect("Descent has painted a Telegram surface")
        .text
        .clone()
}

fn is_full_digest(word: &str) -> bool {
    word.len() == 64 && word.bytes().all(|byte| byte.is_ascii_hexdigit())
}

#[test]
fn telegram_preserves_native_action_order_and_surfaces_locked_executor_reasons() {
    let offering = NativeDescentOffering::new();
    let session = offering
        .open(SessionConfig::with_seed(41_731))
        .expect("native Descent opens");
    let actions = offering.actions(&session);
    let expected = build_present_request(CHAT, None, &offering.render(&session), &actions);

    let mut host = host();
    let sid = host
        .open("descent", CHAT, None, ALICE)
        .expect("native Descent opens through Telegram");
    let actual = host
        .frontend()
        .transport()
        .last()
        .expect("Telegram presents Descent");

    let actual_game_rows: Vec<_> = actual
        .reply_markup
        .as_ref()
        .expect("Telegram paints game actions plus verification")
        .inline_keyboard
        .iter()
        .filter(|row| {
            row.first().is_none_or(|button| {
                decode_callback(&button.callback_data)
                    .is_none_or(|(turn, arg)| !is_verify_callback(&turn, arg))
            })
        })
        .cloned()
        .collect();
    assert_eq!(
        actual_game_rows,
        expected
            .reply_markup
            .expect("the native actions build a keyboard")
            .inline_keyboard,
        "Telegram must consume the native ordered action list verbatim before host controls"
    );
    let buttons = current_buttons(&host);
    assert_eq!(buttons.len(), actions.len());
    for (button, action) in buttons.iter().zip(&actions) {
        assert_eq!(
            decode_callback(&button.callback_data),
            Some((action.turn.clone(), action.arg)),
            "button order and typed action identity stay aligned"
        );
        assert_eq!(
            button.text.starts_with(LOCK_GLYPH),
            !action.enabled,
            "locked state is visible without becoming a Telegram legality rule"
        );
    }

    let before = host.verify("descent", &sid).expect("live verifier");
    let locked = buttons
        .iter()
        .find(|button| button.text.starts_with(LOCK_GLYPH))
        .expect("the complete locked catalogue stays visible")
        .clone();
    let refused = host.press(CallbackQuery::press(
        CHAT,
        ALICE,
        locked.callback_data.clone(),
    ));
    let reason = match &refused {
        HostPress::Advanced {
            key,
            outcome: Outcome::Refused(reason),
        } => {
            assert_eq!(key, "descent");
            assert!(
                !reason.trim().is_empty(),
                "the executor supplies the reason"
            );
            reason.clone()
        }
        other => panic!("a locked Telegram action must reach the executor: {other:?}"),
    };
    assert!(
        describe_press(refused).contains(&reason),
        "the Telegram acknowledgement must preserve the executor's exact reason"
    );
    let after = host.verify("descent", &sid).expect("live verifier");
    assert_eq!(after.turns, before.turns, "a refusal is anti-ghost");
}

#[test]
fn telegram_terminal_record_names_the_actor_and_routes_live_reverification() {
    let mut host = host();
    let sid = host
        .open("descent", CHAT, None, ALICE)
        .expect("native Descent opens through Telegram");
    let alice = host.identity(ALICE);

    let first = current_buttons(&host)
        .into_iter()
        .find(|button| !button.text.starts_with(LOCK_GLYPH))
        .expect("a fresh Descent has a legal action");
    let landed = host.press(CallbackQuery::press(CHAT, ALICE, first.callback_data));
    assert!(
        matches!(
            &landed,
            HostPress::Advanced {
                outcome: Outcome::Landed { ended: false, .. },
                ..
            }
        ),
        "the keyboard's first legal action lands: {landed:?}"
    );
    assert!(
        current_text(&host).contains(alice.as_str()),
        "the rendered player is the Telegram-derived actor"
    );

    let alice_button = current_buttons(&host)
        .into_iter()
        .find(|button| !button.text.starts_with(LOCK_GLYPH))
        .expect("the bound player has another legal action");
    let intruder = host.press(CallbackQuery::press(CHAT, BOB, alice_button.callback_data));
    match &intruder {
        HostPress::Advanced {
            outcome: Outcome::Refused(reason),
            ..
        } => assert!(
            reason.contains(alice.as_str()),
            "the refusal attributes the run to its real actor: {reason}"
        ),
        other => panic!("a substituted Telegram actor must be refused: {other:?}"),
    }
    assert!(
        current_text(&host).contains(alice.as_str()),
        "a refused viewer cannot replace the rendered player attribution"
    );

    // Repaint for Alice, then follow only the first enabled button the native ordering exposes.
    // No Descent verb or transition rule is encoded in this driver.
    host.open("descent", CHAT, None, ALICE)
        .expect("the same live session repaints for its player");
    let mut terminal_ack = None;
    for _ in 0..64 {
        let button = current_buttons(&host)
            .into_iter()
            .find(|button| !button.text.starts_with(LOCK_GLYPH))
            .expect("a live native Descent exposes an enabled action");
        let pressed = host.press(CallbackQuery::press(CHAT, ALICE, button.callback_data));
        let ended = match &pressed {
            HostPress::Advanced {
                outcome: Outcome::Landed { ended, .. },
                ..
            } => *ended,
            other => panic!("an enabled native action must land: {other:?}"),
        };
        if ended {
            terminal_ack = Some(describe_press(pressed));
            break;
        }
    }
    let terminal_ack = terminal_ack.expect("the surface-driven line settles within 64 turns");
    assert!(
        terminal_ack.contains("/verify"),
        "Telegram names its live terminal verify affordance: {terminal_ack}"
    );

    let terminal = current_text(&host);
    assert!(terminal.contains("proof/share record"), "{terminal}");
    assert!(terminal.contains(alice.as_str()), "{terminal}");
    assert!(
        terminal.contains("re-verify this exact record"),
        "{terminal}"
    );
    let share = terminal
        .split_once("proof/share record:")
        .expect("terminal surface carries a share record")
        .1;
    let root = share
        .split_once("root ")
        .expect("share record names a root")
        .1
        .split_whitespace()
        .next()
        .expect("root value");
    let receipt = share
        .split_once("receipt ")
        .expect("share record names a receipt")
        .1
        .split_whitespace()
        .next()
        .expect("receipt value");
    assert!(is_full_digest(root), "share root must be lossless: {root}");
    assert!(
        is_full_digest(receipt),
        "share receipt must be lossless: {receipt}"
    );
    assert!(
        current_buttons(&host).is_empty(),
        "a settled Descent offers no game actions"
    );

    let verified = host.press(CallbackQuery::press(
        CHAT,
        ALICE,
        encode_callback(TURN_VERIFY, 0),
    ));
    match verified {
        HostPress::Verified {
            key,
            report: Some(report),
        } => {
            assert_eq!(key, "descent");
            assert!(report.verified, "{}", report.detail);
        }
        other => panic!("the terminal verify command must replay the chain: {other:?}"),
    }
}
