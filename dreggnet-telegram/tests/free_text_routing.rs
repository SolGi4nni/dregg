//! **FREE-TEXT input routing — the runtime routes a plain-text message into a SELECTED text
//! affordance.** All over [`MockTransport`] (no token, no network), the same seam split the
//! runtime shell is built on.
//!
//! The gap this closes: a text-input offering (the collaborative document, hosted Hermes, names,
//! compute settle) presents affordances that SOLICIT free text
//! ([`Action::wants_text`](dreggnet_offerings::Action::wants_text)), but the runtime only routed
//! fixed commands + numeric `/act` args, so a plain-text message a user typed fell through to
//! [`TextDecision::Ignored`] and the offering could never be driven in-chat.
//!
//! It is now SELECTABLE and DELIBERATE: a button press on a text affordance ARMS that specific
//! `(turn, arg)` for the chat ([`HostPress::TextArmed`]); the NEXT plain-text message becomes THAT
//! affordance's text payload and advances one real turn (the executor stays the sole referee).
//! With nothing armed, plain messages are ordinary chatter — Ignored (never swallowed, even with a
//! text offering open: the old `find(wants_text)` captured every message the moment any text
//! offering was open, and always into the FIRST text affordance). A command is still a command.

use dreggnet_telegram::api::encode_callback;
use dreggnet_telegram::host::{HostPress, TelegramHost};
use dreggnet_telegram::runtime::{TextDecision, help_text, route_text_decided};
use dreggnet_telegram::transport::MockTransport;
use dreggnet_telegram::{CallbackQuery, TelegramFrontend};

/// A deterministic bot secret (a real deploy loads/derives 32 bytes in the bin).
const BOT_SECRET: [u8; 32] = [9u8; 32];
const ALICE: u64 = 1001;

/// A fresh in-memory host over the full catalog (no council members needed here).
fn host() -> TelegramHost<MockTransport> {
    TelegramHost::new(BOT_SECRET, MockTransport::new(), &[])
}

/// **With a text affordance ARMED, a plain-text message routes as its input** — it reaches the
/// substrate as one real turn (the executor referees it), instead of falling through to `Ignored`.
#[test]
fn an_armed_text_affordance_routes_plain_text_as_input() {
    let mut h = host();
    let chat: i64 = 77;
    let sid = h
        .open("doc", chat, None, ALICE)
        .expect("the document opens");

    // Nothing is armed on a fresh open — capture is a deliberate act, not automatic.
    assert!(
        h.pending_text_action(&sid).is_none(),
        "a fresh open arms nothing — plain text is not yet claimed",
    );

    // Press the "…continue the document" insert template (turn=insert, arg=0 on an empty doc) —
    // this ARMS it (a text affordance carries no content on a bare press).
    match h.press(CallbackQuery::press(
        chat,
        ALICE,
        encode_callback("insert", 0),
    )) {
        HostPress::TextArmed { key, action } => {
            assert_eq!(key, "doc");
            assert!(action.wants_text, "the armed affordance solicits text");
            assert_eq!(action.turn, "insert");
        }
        other => panic!("pressing a text template must ARM it, got {other:?}"),
    }

    // Now the chat has a pending (armed) text affordance.
    let pending = h
        .pending_text_action(&sid)
        .expect("the armed insert is pending");
    assert!(pending.wants_text);
    assert_eq!(
        pending.text, None,
        "a template — the user supplies the prose"
    );

    // A plain-text (non-command) message: routed as the armed affordance's text input.
    let (reply, decision) = route_text_decided(
        &mut h,
        chat,
        None,
        ALICE,
        "the dragon's hoard glittered in the torchlight",
    );
    match decision {
        TextDecision::TextInput { .. } => {}
        other => panic!("expected the free text to route as TextInput, got {other:?}"),
    }
    // It reached the substrate (the executor is the referee), so the router has an ack to send —
    // NOT the silent `None` of ignored chatter.
    assert!(
        reply.is_some(),
        "a routed text input yields a human ack (the executor's verdict)",
    );

    // The arm is ONE-SHOT: the surface moved on, so a second plain message is Ignored again.
    let (_r2, d2) = route_text_decided(&mut h, chat, None, ALICE, "and a second stray line");
    assert!(
        matches!(d2, TextDecision::Ignored),
        "after the armed input is consumed, plain text is chatter again, got {d2:?}",
    );
}

/// **The greedy-capture gate (#5b): a text offering open but NOTHING armed does NOT swallow
/// chatter.** This is the whole point of making selection deliberate — a group chat with a
/// document open no longer turns every member's message into an offering input.
#[test]
fn a_text_offering_open_but_unarmed_ignores_plain_chatter() {
    let mut h = host();
    let chat: i64 = -5005; // a group chat
    let sid = h
        .open("doc", chat, None, ALICE)
        .expect("the document opens");
    // The document DOES present text affordances…
    assert!(
        h.frontend()
            .session(&sid)
            .map(|s| s.presented.iter().any(|a| a.wants_text))
            .unwrap_or(false),
        "the document surface offers text affordances",
    );
    // …but nothing is armed, so plain chatter is Ignored (not swallowed into the document).
    assert!(h.pending_text_action(&sid).is_none(), "nothing armed");
    let (reply, decision) =
        route_text_decided(&mut h, chat, None, ALICE, "hey has anyone seen bob");
    assert!(
        matches!(decision, TextDecision::Ignored),
        "an unarmed text offering must ignore chatter (no greedy capture), got {decision:?}",
    );
    assert!(reply.is_none(), "ignored chatter draws no reply");
}

/// With an offering open that solicits NO text (the dungeon — scene-choice buttons only), a
/// plain-text message stays `Ignored`: pressing a non-text button never arms anything.
#[test]
fn plain_text_with_no_text_affordance_stays_ignored() {
    let mut h = host();
    let chat: i64 = 78;
    let sid = h
        .open("dungeon", chat, None, ALICE)
        .expect("the dungeon opens");

    assert!(
        h.pending_text_action(&sid).is_none(),
        "the dungeon presents no text-soliciting affordance (scene choices only)",
    );

    let (reply, decision) = route_text_decided(&mut h, chat, None, ALICE, "hello, anyone here?");
    assert!(
        matches!(decision, TextDecision::Ignored),
        "with no text affordance armed, plain chatter is ignored, got {decision:?}",
    );
    assert!(reply.is_none(), "ignored chatter draws no reply");
}

/// No open session at all: a plain-text message is ordinary chatter (nothing armed), ignored.
#[test]
fn plain_text_with_no_open_session_stays_ignored() {
    let mut h = host();
    let chat: i64 = 79;
    let sid = TelegramFrontend::<MockTransport>::session_id(chat, None);
    assert!(h.pending_text_action(&sid).is_none(), "nothing is open");

    let (reply, decision) = route_text_decided(&mut h, chat, None, ALICE, "just talking");
    assert!(matches!(decision, TextDecision::Ignored));
    assert!(reply.is_none());
}

/// A command is STILL a command even while a text affordance is ARMED — the leading `/` wins, so
/// `/help` is not swallowed as document prose.
#[test]
fn a_command_still_routes_as_a_command_while_text_is_armed() {
    let mut h = host();
    let chat: i64 = 80;
    let sid = h
        .open("doc", chat, None, ALICE)
        .expect("the document opens");
    // Arm the insert template.
    let _ = h.press(CallbackQuery::press(
        chat,
        ALICE,
        encode_callback("insert", 0),
    ));
    assert!(
        h.pending_text_action(&sid).is_some(),
        "a text affordance is armed",
    );

    // `/help` — a command — routes as Help, not as text input, despite the armed affordance.
    let (reply, decision) = route_text_decided(&mut h, chat, None, ALICE, "/help");
    assert!(
        matches!(decision, TextDecision::Help),
        "a leading-slash command still routes as a command, got {decision:?}",
    );
    assert_eq!(
        reply.as_deref(),
        Some(help_text().as_str()),
        "the help text answered — the command was not swallowed as document text",
    );
}
