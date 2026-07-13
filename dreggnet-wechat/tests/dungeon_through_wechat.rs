//! **The HARD GATE — a `DungeonOffering` plays through the `WeChatFrontend`.**
//!
//! The SAME offering core the Discord bot and the Telegram frontend drive, driven here through a
//! REAL [`WeChatFrontend`] over a network-free [`MockTransport`] — NO Discord, NO WeChat token, NO
//! network. It proves the offering core is frontend-agnostic: the same `DungeonOffering`, a new
//! renderer (an OA numbered-reply surface instead of an inline keyboard).
//!
//! What is asserted at the logic level (what a live token/cert would add is only the actual HTTP
//! send — the [`transport::Transport`] seam):
//! - **render → an OA text message + numbered reply list**: `present` builds the real `custom/send`
//!   wire body, with ONE numbered line per cap-gated affordance;
//! - **collect(reply) → (SessionId, Action, DreggIdentity)**: a numbered reply decodes back into the
//!   exact typed [`Action`] the core resolves, attributed to the sender's derived identity;
//! - **a real turn**: the collected action, resolved on the substrate, lands a real `TurnReceipt`
//!   (a winning line), and an illegal move is a real executor `Refused` (the anti-ghost tooth);
//! - **verify()** re-verifies the whole committed chain by replay;
//! - **identity** is a real derived Ed25519 key, deterministic + distinct per OpenID.

use deos_view::LOCK_GLYPH; // the SHARED backend's lock glyph (no crate-local codec)
use dreggnet_offerings::dungeon::{DungeonOffering, TURN_CHOOSE};
use dreggnet_offerings::{Action, Frontend, Offering, Outcome, SessionConfig};
use dreggnet_wechat::transport::MockTransport;
use dreggnet_wechat::{WeChatFrontend, WeChatMessage};
use dungeon_on_dregg::{KP_CLAIM_RED, KP_PRESS_ON, KP_TRADE_BLOWS};

const BOT_SECRET: [u8; 32] = [7u8; 32];
const OPENID: &str = "oPLAYER_wechat_openid_0001";

fn new_fe() -> WeChatFrontend<MockTransport> {
    WeChatFrontend::new(BOT_SECRET, MockTransport::new())
}

/// The 1-based reply number selecting the affordance carrying `arg` (its position in the current
/// ballot), from a fresh render — exactly what a user reads off the numbered list.
fn reply_for(
    off: &DungeonOffering,
    s: &dreggnet_offerings::dungeon::DungeonSession,
    arg: i64,
) -> String {
    let acts = off.actions(s);
    let pos = acts
        .iter()
        .position(|a: &Action| a.arg == arg)
        .expect("the affordance is on the current ballot");
    (pos + 1).to_string()
}

/// **The HARD GATE — a `DungeonOffering` plays a winning line through the `WeChatFrontend`.**
/// The full lifecycle: spin → present → collect a numbered reply → the CORE advances one real turn
/// → re-present → … → teardown; each move a real landed `TurnReceipt`; the whole chain re-verifies.
#[test]
fn a_dungeon_plays_a_winning_line_through_wechat_and_verifies() {
    let off = DungeonOffering::new();
    let mut s = off.open(SessionConfig::with_seed(9)).expect("open");
    assert_eq!(s.current_passage_name().as_deref(), Some("gatehall"));
    assert_eq!(s.receipts_len(), 1, "genesis is the first verified turn");

    let mut fe = new_fe();
    let sid = WeChatFrontend::<MockTransport>::session_id(OPENID);
    fe.spin_session(sid.clone());
    assert_eq!(
        fe.session(&sid).map(|slot| slot.openid.as_str()),
        Some(OPENID),
        "the session is the 1:1 OA conversation with the OpenID"
    );

    // Present the gatehall, then the WeChat user replies with the press-on number.
    fe.present(&sid, &off.render(&s), &off.actions(&s));
    let reply = reply_for(&off, &s, KP_PRESS_ON as i64);
    let (got_sid, action, actor) = fe
        .collect(WeChatMessage::text(OPENID, reply))
        .expect("collect the numbered reply");
    assert_eq!(got_sid, sid, "the reply resolves to its session");
    assert_eq!(action.arg, KP_PRESS_ON as i64);
    assert_eq!(action.turn, TURN_CHOOSE);
    assert_eq!(
        actor,
        fe.identity(OPENID.to_string()),
        "the sender's derived dregg identity attributes the move"
    );
    assert_eq!(actor.as_str().len(), 64, "a real Ed25519 pubkey hex handle");

    // The CORE resolves it on the substrate — one real committed turn.
    match off.advance(&mut s, action, actor.clone()) {
        Outcome::Landed { receipt, ended } => {
            assert!(!ended, "pressing on does not end the Keep");
            assert_ne!(receipt.turn_hash, [0u8; 32], "a genuine committed turn");
        }
        other => panic!("a legal WeChat move must land a real receipt, got {other:?}"),
    }
    assert_eq!(
        s.receipts_len(),
        2,
        "a real verified turn landed from WeChat"
    );
    assert_eq!(s.current_passage_name().as_deref(), Some("hall"));

    // Re-present the plundered hall, then reply with the claim-the-crown number.
    fe.present(&sid, &off.render(&s), &off.actions(&s));
    let claim_reply = reply_for(&off, &s, KP_CLAIM_RED as i64);
    let (_, action2, actor2) = fe
        .collect(WeChatMessage::text(OPENID, claim_reply))
        .expect("collect the claim");
    assert!(
        off.advance(&mut s, action2, actor2).landed(),
        "claiming the crown lands a real turn"
    );
    assert_eq!(s.receipts_len(), 3);
    assert_eq!(
        s.actor_of_step(0),
        Some(&actor),
        "the mover is the sender's derived identity, not a WeChat nickname"
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

/// An illegal move collected through WeChat is a real executor refusal (the anti-ghost tooth): the
/// ineligible affordance is shown as a dimmed lock-glyph numbered line but is still selectable —
/// firing it commits nothing, lands no receipt, moves the world not at all. The prefix re-verifies.
#[test]
fn an_illegal_move_collected_through_wechat_is_refused_anti_ghost() {
    let off = DungeonOffering::new();
    let mut s = off.open(SessionConfig::with_seed(8)).expect("open");

    let mut fe = new_fe();
    let sid = WeChatFrontend::<MockTransport>::session_id(OPENID);
    fe.spin_session(sid.clone());

    // Two survivable trade-blows (hp 50 → 30 → 10), each collected through WeChat + landed.
    for _ in 0..2 {
        fe.present(&sid, &off.render(&s), &off.actions(&s));
        let reply = reply_for(&off, &s, KP_TRADE_BLOWS as i64);
        let (_, action, actor) = fe
            .collect(WeChatMessage::text(OPENID, reply))
            .expect("collect a survivable blow");
        assert!(
            off.advance(&mut s, action, actor).landed(),
            "a survivable blow lands"
        );
    }
    assert_eq!(s.read_var("hp"), 10, "two blows dropped hp to 10");
    let before = s.receipts_len();

    // At hp 10 the trade-blows affordance is a dimmed cap-tooth (its `{ hp >= 21 }` fails). Its
    // numbered line is LOCK_GLYPH-prefixed + `(locked)` — shown, not hidden — but still selectable.
    fe.present(&sid, &off.render(&s), &off.actions(&s));
    let req = fe.transport().last().expect("presented");
    assert!(
        req.text.content.contains(LOCK_GLYPH) && req.text.content.contains("(locked)"),
        "the ineligible affordance is a dimmed lock line, not hidden: {}",
        req.text.content
    );

    // Reply with its number anyway — the collected action carries enabled=false; the REAL executor
    // refuses it (the executor is the sole referee, not the numbered-list decoration).
    let reply = reply_for(&off, &s, KP_TRADE_BLOWS as i64);
    let (_, action, actor) = fe
        .collect(WeChatMessage::text(OPENID, reply))
        .expect("a dimmed affordance is still selectable (anti-ghost is the executor's job)");
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
        "the world did not move"
    );
    assert!(
        off.verify(&s).verified,
        "the honest prefix re-verifies after the refusal"
    );
}

/// The transport is the sole network seam: an armed failure surfaces as a `TransportError` through
/// the fallible `present_result`, and the (infallible) trait `present` records it observably.
#[test]
fn a_transport_failure_surfaces_and_does_not_panic() {
    let mut transport = MockTransport::new();
    transport.fail_next("errcode 45015: response out of time limit");
    let mut fe = WeChatFrontend::new(BOT_SECRET, transport);

    let sid = WeChatFrontend::<MockTransport>::session_id(OPENID);
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
        err.to_string().contains("45015"),
        "the transport error is surfaced: {err}"
    );

    // A subsequent send succeeds (the failure was one-shot).
    assert!(
        fe.present_result(&sid, &surface, &acts).is_ok(),
        "the next send succeeds"
    );
    assert!(
        fe.last_send_error().is_none(),
        "no lingering error after a good send"
    );
}
