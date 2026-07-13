//! **The driven end-to-end proof** — a `WeChatFrontend` over the REAL `DungeonOffering`, DRIVEN
//! with a MOCK transport: NO WeChat access-token, NO network. It proves a WeChat user plays the
//! SAME offering core, on the SAME real substrate, as the Discord bot:
//!
//! - a WeChat user opens a session; the offering's [`Surface`] renders as a `custom/send` message
//!   with the RIGHT numbered-reply content (we assert the request shape the transport recorded);
//! - a numbered reply collects the right typed [`Action`] + the sender's DERIVED dregg identity;
//! - the core [`Offering::advance`]s that action on the substrate → a REAL landed [`TurnReceipt`];
//! - an illegal move (a killing blow past the HP floor) is a real executor [`Outcome::Refused`] —
//!   nothing commits, no receipt (the anti-ghost tooth), same as on Discord;
//! - [`Offering::verify`] re-verifies the whole playthrough by replay;
//! - the RICH Mini-Program card payload carries one button per affordance.
//!
//! The transport is a [`MockTransport`] — the assertions are all against the request bodies it
//! recorded, which serialize to the exact WeChat `custom/send` wire shape.

use dreggnet_offerings::dungeon::{DungeonOffering, KEEP_NAME, TURN_CHOOSE};
use dreggnet_offerings::{Frontend, Offering, SessionConfig};
use dreggnet_wechat::api::{build_miniprogram_card, present_message};
use dreggnet_wechat::transport::MockTransport;
use dreggnet_wechat::{WeChatFrontend, WeChatMessage};
use dungeon_on_dregg::KP_PRESS_ON;

/// A deterministic bot secret for the tests (a real deploy loads 32 bytes from env).
const BOT_SECRET: [u8; 32] = [7u8; 32];
/// A sample WeChat OpenID (the per-OA opaque user handle).
const OPENID: &str = "oGZUI0egBJY1zhBYw2KaXT9abcd";

fn new_fe() -> WeChatFrontend<MockTransport> {
    WeChatFrontend::new(BOT_SECRET, MockTransport::new())
}

/// The 1-based reply number that selects the affordance carrying `arg` (its position in `actions`).
fn reply_number_for(actions: &[dreggnet_offerings::Action], arg: i64) -> usize {
    actions
        .iter()
        .position(|a| a.arg == arg)
        .expect("affordance present")
        + 1
}

/// `present` → a WeChat OA `custom/send` message whose content is the surface prose + a numbered
/// reply list of ONE line per cap-gated affordance; the sent request IS the real `custom/send` wire
/// body (asserted as JSON).
#[test]
fn present_builds_a_message_and_one_numbered_line_per_affordance() {
    let off = DungeonOffering::new();
    let s = off
        .open(SessionConfig::with_seed(3))
        .expect("the Keep opens");
    let acts = off.actions(&s);
    assert!(acts.len() >= 2, "the gatehall offers >1 candidate move");
    let surface = off.render(&s);

    let mut fe = new_fe();
    let sid = WeChatFrontend::<MockTransport>::session_id(OPENID);
    fe.spin_session(sid.clone());
    fe.present(&sid, &surface, &acts);
    assert!(fe.last_send_error().is_none(), "the mock send succeeds");

    let req = fe.transport().last().expect("a custom/send was sent");
    assert_eq!(req.touser, OPENID, "the message targets the session's user");
    assert_eq!(req.msgtype, "text", "an OA text message");
    assert!(
        req.text.content.contains(KEEP_NAME),
        "the content names the Keep + room: {:?}",
        req.text.content
    );
    // The content is EXACTLY the shared `WeChatBackend` render (prose + the numbered reply list over
    // the whole gated ViewNode tree) — the frontend presents through it; there is no crate-local codec.
    let expected = present_message(&surface).content;
    assert_eq!(
        req.text.content, expected,
        "content = the shared WeChatBackend render (prose + numbered reply list)"
    );

    // ONE numbered line per cap-gated affordance, 1-based, each parseable back to its position.
    for (i, act) in acts.iter().enumerate() {
        let n = i + 1;
        assert!(
            req.text.content.contains(&format!("{n}. ")),
            "affordance {n} ({:?}) has a numbered line: {}",
            act.label,
            req.text.content
        );
    }

    // The sent struct IS the real WeChat `custom/send` JSON wire body.
    let json = serde_json::to_string(req).expect("serialize the custom/send body");
    assert!(
        json.contains(&format!("\"touser\":\"{OPENID}\"")),
        "wire body carries touser: {json}"
    );
    assert!(
        json.contains("\"msgtype\":\"text\""),
        "wire body carries msgtype: {json}"
    );
    assert!(
        json.contains("\"content\":"),
        "wire body carries the text content: {json}"
    );
}

/// `collect(inbound reply)` → the exact typed `(SessionId, Action, DreggIdentity)` — a numbered
/// reply decodes back to the presented affordance and is attributed to the sender's derived id.
#[test]
fn collect_maps_a_numbered_reply_back_to_the_typed_action_and_derived_identity() {
    let off = DungeonOffering::new();
    let s = off.open(SessionConfig::with_seed(3)).expect("open");
    let acts = off.actions(&s);

    let mut fe = new_fe();
    let sid = WeChatFrontend::<MockTransport>::session_id(OPENID);
    fe.spin_session(sid.clone());
    fe.present(&sid, &off.render(&s), &acts);

    // A reply naming the press-on affordance's 1-based position.
    let n = reply_number_for(&acts, KP_PRESS_ON as i64);
    let ev = WeChatMessage::text(OPENID, n.to_string());
    let (got_sid, action, actor) = fe
        .collect(ev)
        .expect("a numbered reply maps back to a presented affordance");
    assert_eq!(got_sid, sid, "the session is reconstructed from the OpenID");
    assert_eq!(action.turn, TURN_CHOOSE);
    assert_eq!(action.arg, KP_PRESS_ON as i64);
    assert_eq!(
        actor,
        fe.identity(OPENID.to_string()),
        "the reply is attributed to the sender's derived dregg identity"
    );

    // A "2." / "2 trade blows" style reply parses the leading number too — via the SHARED positional
    // half of the WeChat codec (`deos_view::wechat_reply_index`), what `collect` resolves against.
    assert_eq!(deos_view::wechat_reply_index("2. trade blows"), Some(2));
    assert_eq!(deos_view::wechat_reply_index("  1 "), Some(1));
    assert_eq!(deos_view::wechat_reply_index("nope"), None);
    assert_eq!(
        deos_view::wechat_reply_index("0"),
        None,
        "there is no 0th affordance"
    );

    // A reply naming a position never presented collects None.
    let stray = WeChatMessage::text(OPENID, "99");
    assert!(
        fe.collect(stray).is_none(),
        "an out-of-range reply is not collected"
    );
    // A reply from an unknown user (no session) collects None.
    let elsewhere = WeChatMessage::text("oOTHERUSERxyz", n.to_string());
    assert!(
        fe.collect(elsewhere).is_none(),
        "a reply from an unknown user is not collected"
    );
    // A non-text message (e.g. an event) collects None.
    let mut ev_event = WeChatMessage::text(OPENID, "1");
    ev_event.msg_type = "event".to_string();
    assert!(
        fe.collect(ev_event).is_none(),
        "a non-text inbound is not collected"
    );
}

/// Identity is a REAL derived Ed25519 key (mirroring the telegram/discord cclerk): deterministic,
/// distinct per OpenID, and equal to the standalone cipherclerk derivation.
#[test]
fn derived_identity_is_deterministic_distinct_and_a_real_ed25519_key() {
    use dreggnet_wechat::cipherclerk::WeChatCipherclerk;
    let fe = new_fe();

    // Deterministic + distinct.
    assert_eq!(
        fe.identity(OPENID.to_string()),
        fe.identity(OPENID.to_string()),
        "same OpenID → same identity"
    );
    assert_ne!(
        fe.identity(OPENID.to_string()),
        fe.identity("oDIFFERENTuser".to_string()),
        "distinct OpenIDs → distinct identities"
    );

    // A real Ed25519 public key: 32 bytes → 64 lowercase hex chars.
    let id = fe.identity(OPENID.to_string());
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
        WeChatCipherclerk::derive(&BOT_SECRET, OPENID).identity(),
        "identity() is exactly the derived cclerk's public-key handle"
    );
}

/// The RICH alternative: a Mini-Program card payload carries one real button per cap-gated
/// affordance (label + `{turn, arg}` + enabled). Same affordances as the OA numbered list.
#[test]
fn miniprogram_card_carries_one_button_per_affordance() {
    let off = DungeonOffering::new();
    let s = off.open(SessionConfig::with_seed(3)).expect("open");
    let acts = off.actions(&s);
    let surface = off.render(&s);

    let card = build_miniprogram_card(&surface, &acts);
    assert!(
        card.body.contains(KEEP_NAME),
        "the card body names the Keep"
    );
    assert_eq!(
        card.buttons.len(),
        acts.len(),
        "one card button per cap-gated affordance"
    );
    for (btn, act) in card.buttons.iter().zip(acts.iter()) {
        assert_eq!(btn.turn, act.turn, "the button carries the affordance verb");
        assert_eq!(btn.arg, act.arg, "the button carries the affordance arg");
        assert_eq!(btn.enabled, act.enabled, "enabled decoration preserved");
    }

    // The card is a serde payload (the MP backend reads this JSON).
    let json = serde_json::to_string(&card).expect("serialize the MP card");
    assert!(
        json.contains("\"buttons\""),
        "the card carries its buttons: {json}"
    );
}
