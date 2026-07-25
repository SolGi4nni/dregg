//! **A Telegram `message_id` is unique only WITHIN a chat — so the surface index must be
//! chat-scoped.**
//!
//! ## The bug this file exists for
//! One [`TelegramFrontend`] served many chats, but keyed its "which surface owns this message"
//! index by the bare `message_id`. A Bot API `message_id` is unique per CHAT, not globally: two
//! different chats routinely mint the same id. So chat B's `message_id 2` overwrote chat A's, and
//! A's later press on its own message 2 then resolved chat B's surface — wrong offering key,
//! `bound_game_view` fails, the button reads `NotOffered` (a dead button). It also cross-wrote the
//! `armed` free-text slot. The executor still referees (no forged commit), but it is a real
//! cross-chat correctness/DoS bug against any public multi-chat bot.
//!
//! ## Why the stock test transport hid it
//! [`dreggnet_telegram::transport::MockTransport`] hands out GLOBALLY monotonic ids, so two chats
//! never collide there — the exact blind spot the audit flagged. This file drives with a transport
//! whose ids are per-chat monotonic, which is the real Telegram semantics, and reproduces the
//! collision directly.
//!
//! ## The fix
//! `by_message` is keyed by `(chat_id, topic, message_id)` — the full chat-scoped address, taken
//! straight off the [`CallbackQuery`] — so two chats sharing a bare id resolve to their OWN
//! surfaces.

use std::collections::HashMap;

use deos_view::ViewNode;
use dreggnet_offerings::{Action, Frontend, SessionId, Surface};
use dreggnet_telegram::api::{SendMessageRequest, encode_callback};
use dreggnet_telegram::transport::{MessageId, Transport, TransportError};
use dreggnet_telegram::{CallbackQuery, TelegramFrontend};

/// A transport that assigns **per-chat** monotonically increasing message ids — the real Telegram
/// semantics (`message_id` is unique within a chat, not globally). This is what makes two chats
/// mint the same bare id, which the globally-monotonic `MockTransport` can never do.
#[derive(Default)]
struct PerChatIds {
    next: HashMap<i64, i64>,
}

impl Transport for PerChatIds {
    fn send_message(&mut self, req: &SendMessageRequest) -> Result<MessageId, TransportError> {
        let slot = self.next.entry(req.chat_id).or_insert(1);
        let id = *slot;
        *slot += 1;
        Ok(MessageId(id))
    }
}

/// Two DIFFERENT chats each open their own offering. Because message ids are per-chat, both live
/// surfaces carry the SAME bare `message_id`. A press in each chat must route to THAT chat's own
/// session — never the other chat's, which a bare-`message_id` key silently conflated.
#[test]
fn presses_in_two_chats_with_the_same_message_id_route_to_their_own_sessions() {
    let mut fe: TelegramFrontend<PerChatIds> =
        TelegramFrontend::new([9u8; 32], PerChatIds::default());

    // Two distinct group chats, each hosting a distinct offering.
    let chat_a: i64 = -100;
    let chat_b: i64 = -200;
    let surface_a = TelegramFrontend::<PerChatIds>::surface_id(chat_a, None, "tug");
    let surface_b = TelegramFrontend::<PerChatIds>::surface_id(chat_b, None, "council");

    let action_a = Action::new("Pull", "pull", 7, true);
    let action_b = Action::new("Propose", "propose", 0, true);

    let msg_a = fe
        .present_result(
            &surface_a,
            &Surface(ViewNode::Text("tug".into())),
            std::slice::from_ref(&action_a),
        )
        .expect("present chat A");
    let msg_b = fe
        .present_result(
            &surface_b,
            &Surface(ViewNode::Text("council".into())),
            std::slice::from_ref(&action_b),
        )
        .expect("present chat B");

    // THE COLLISION PRECONDITION: per-chat ids, so both surfaces carry the same bare message_id.
    // A bare-`message_id` key would have B's insert overwrite A's here.
    assert_eq!(
        msg_a, msg_b,
        "both chats mint the same per-chat message_id (real Telegram semantics)"
    );

    // A press on chat A's message resolves chat A's OWN surface…
    let (routed_a, got_a, _id_a) = fe
        .collect(CallbackQuery::press_on_message(
            chat_a,
            msg_a,
            1001,
            encode_callback(&action_a.turn, action_a.arg),
        ))
        .expect("chat A press routes to a session");
    assert_eq!(
        routed_a, surface_a,
        "chat A's press must resolve chat A's surface, not chat B's"
    );
    assert_eq!(got_a, action_a, "…and decodes to chat A's own affordance");

    // …and a press on chat B's message resolves chat B's own surface, though it shares the id.
    let (routed_b, got_b, _id_b) = fe
        .collect(CallbackQuery::press_on_message(
            chat_b,
            msg_b,
            1002,
            encode_callback(&action_b.turn, action_b.arg),
        ))
        .expect("chat B press routes to a session");
    assert_eq!(
        routed_b, surface_b,
        "chat B's press must resolve chat B's own surface"
    );
    assert_eq!(got_b, action_b, "…and decodes to chat B's own affordance");

    // The surfaces are genuinely different sessions (not the same id twice).
    assert_ne!(
        surface_a, surface_b,
        "the two chats host distinct sessions despite the shared message_id"
    );

    // Cross-affordance guard: chat A's surface never offered chat B's `propose`, so a press on
    // chat A's message carrying B's action is refused — each same-id surface keeps its OWN
    // presented affordances (the `armed`/offering cross-write can't happen).
    assert!(
        fe.collect(CallbackQuery::press_on_message(
            chat_a,
            msg_a,
            1001,
            encode_callback(&action_b.turn, action_b.arg),
        ))
        .is_none(),
        "chat A's surface never offered chat B's action, even at the same message_id"
    );
}

/// The teardown of one chat's surface must not evict another chat's identically-numbered message
/// from the index. (A bare-`message_id` key would drop `by_message[id]` and orphan the sibling.)
#[test]
fn tearing_down_one_chat_does_not_orphan_the_other_chats_same_id_message() {
    let mut fe: TelegramFrontend<PerChatIds> =
        TelegramFrontend::new([3u8; 32], PerChatIds::default());

    let chat_a: i64 = -11;
    let chat_b: i64 = -22;
    let surface_a = TelegramFrontend::<PerChatIds>::surface_id(chat_a, None, "tug");
    let surface_b = TelegramFrontend::<PerChatIds>::surface_id(chat_b, None, "council");
    let action_b = Action::new("Propose", "propose", 0, true);

    fe.present_result(
        &surface_a,
        &Surface(ViewNode::Text("tug".into())),
        &[Action::new("Pull", "pull", 7, true)],
    )
    .expect("present chat A");
    let msg_b = fe
        .present_result(
            &surface_b,
            &Surface(ViewNode::Text("council".into())),
            std::slice::from_ref(&action_b),
        )
        .expect("present chat B");

    // Teardown of chat A's surface (same bare id as B's) must leave B routable.
    fe.teardown(&surface_a);

    let (routed_b, _got_b, _id_b) = fe
        .collect(CallbackQuery::press_on_message(
            chat_b,
            msg_b,
            1002,
            encode_callback(&action_b.turn, action_b.arg),
        ))
        .expect("chat B still routes after chat A's same-id surface was torn down");
    assert_eq!(routed_b, surface_b);
}
