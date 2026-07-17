//! **The driven MULTI-OFFERING proof — three heterogeneous offerings play through WeChat.**
//!
//! The single-offering `driven.rs` / `dungeon_through_wechat.rs` prove ONE offering plays over the
//! WeChat OA numbered-reply surface. This proves the frontend-agnostic
//! [`OfferingHost`](dreggnet_offerings::OfferingHost) lifted to WeChat: a [`WeChatHost`] registers
//! THREE distinct offerings (a dungeon, a council, a market — heterogeneous `Session` types, one
//! registry) and plays each through the SAME OA numbered-reply surface, with NO WeChat token and NO
//! network (a [`MockTransport`](dreggnet_wechat::transport::MockTransport)):
//!
//! - the host lists ≥ 3 offerings, and an `/offerings` menu (a numbered reply list) opens any of them;
//! - a full winning DUNGEON line plays SOLO (each numbered reply → one real landed `TurnReceipt`);
//! - a COUNCIL propose → vote (two members over a SHARED room) → enact plays, a non-member is a real
//!   refusal;
//! - a MARKET list → sealed bids (two bidders over a SHARED room) → settle clears (value moves,
//!   conservation-checked; the value-taking `list`/`bid` ride a `#turn:value` marked reply);
//! - an unoffered reply is refused BEFORE the substrate;
//! - `verify` re-verifies each committed chain by replay.

use dreggnet_offerings::dungeon::TURN_CHOOSE;
use dreggnet_offerings::{Outcome, SessionId};
use dreggnet_wechat::host::{TURN_OPEN, TURN_VERIFY, WeChatHost, WeChatReply};
use dreggnet_wechat::transport::MockTransport;
use dreggnet_wechat::{WeChatFrontend, WeChatMessage};
use dungeon_on_dregg::{KP_CLAIM_RED, KP_DESCEND, KP_PRESS_ON, KP_SEIZE};

/// A deterministic bot secret (a real deploy loads 32 bytes from env).
const BOT_SECRET: [u8; 32] = [7u8; 32];
/// Two WeChat users registered as the council electorate (their derived identities are the council
/// members), plus a non-member and a second bidder / a seller.
const ALICE: &str = "oALICE_wechat_openid";
const BOB: &str = "oBOB_wechat_openid";
const CAROL: &str = "oCAROL_wechat_openid";
const MALLORY: &str = "oMALLORY_wechat_openid";
const SELLER: &str = "oSELLER_wechat_openid";

/// A fresh host over the three default offerings, with ALICE + BOB as the council electorate.
fn host() -> WeChatHost<MockTransport> {
    WeChatHost::new(BOT_SECRET, MockTransport::new(), &[ALICE, BOB])
}

/// The 1-based reply number selecting the affordance `(turn, arg)` off the surface currently on
/// `openid`'s conversation — exactly what the user reads off the numbered list.
fn reply_number_for(h: &WeChatHost<MockTransport>, openid: &str, turn: &str, arg: i64) -> String {
    let psid = WeChatFrontend::<MockTransport>::session_id(openid);
    let slot = h
        .frontend()
        .session(&psid)
        .expect("a surface is presented to this participant");
    slot.presented
        .options
        .iter()
        .find(|o| o.turn == turn && o.arg == arg)
        .unwrap_or_else(|| panic!("affordance ({turn}, {arg}) is on {openid}'s current surface"))
        .index
        .to_string()
}

/// Assert a reply advanced its offering and landed a real receipt.
fn assert_landed(r: WeChatReply) {
    match r {
        WeChatReply::Advanced { outcome, .. } => {
            assert!(outcome.landed(), "expected a landed turn, got {outcome:?}")
        }
        other => panic!("expected an advance, got {other:?}"),
    }
}

/// The host lists ≥ 3 offerings, and the `/offerings` menu is a numbered reply list of one line per
/// offering — a reply of one's number opens that offering in the user's conversation.
#[test]
fn the_host_lists_at_least_three_offerings_and_the_menu_opens_one() {
    let mut h = host();
    let offs = h.list_offerings();
    assert!(offs.len() >= 3, "the host lists ≥ 3 offerings: {offs:?}");
    let keys: Vec<&str> = offs.iter().map(|o| o.key.as_str()).collect();
    for want in ["dungeon", "council", "market"] {
        assert!(
            keys.contains(&want),
            "offering {want} is registered: {keys:?}"
        );
    }

    // Present the /offerings menu → a custom/send whose numbered list is one open-line per offering.
    let psid = h.present_offerings_menu(ALICE);
    let req = h.frontend().transport().last().expect("the menu was sent");
    assert_eq!(req.touser, ALICE, "the menu targets the user");
    let slot = h
        .frontend()
        .session(&psid)
        .expect("the menu surface is live");
    assert_eq!(
        slot.presented.options.len(),
        offs.len(),
        "one numbered open-line per registered offering"
    );
    for (i, opt) in slot.presented.options.iter().enumerate() {
        assert_eq!(opt.turn, TURN_OPEN, "each option opens an offering");
        assert_eq!(
            opt.arg, i as i64,
            "the option carries the offering catalog index"
        );
    }
    assert!(
        req.text.content.contains("1. "),
        "the menu body is a numbered reply list: {}",
        req.text.content
    );

    // Reply with the market's number → the market opens (solo) in the user's conversation.
    let market_idx = offs.iter().position(|o| o.key == "market").unwrap();
    match h.reply(WeChatMessage::text(ALICE, (market_idx + 1).to_string())) {
        WeChatReply::Opened(k) => assert_eq!(k, "market", "the menu reply opened the market"),
        other => panic!("a menu reply should open the offering, got {other:?}"),
    }
    assert_eq!(
        h.active_offering(ALICE),
        Some("market"),
        "the user is now playing the market"
    );
}

/// A full winning DUNGEON line plays SOLO through the WeChat host — each numbered reply lands one
/// real turn, and the committed chain re-verifies by replay.
#[test]
fn a_winning_dungeon_line_plays_solo_through_the_wechat_host() {
    let mut h = host();
    let room = h.open("dungeon", ALICE).expect("the dungeon opens");
    assert_eq!(h.active_offering(ALICE), Some("dungeon"));

    for arg in [KP_PRESS_ON, KP_CLAIM_RED, KP_DESCEND, KP_SEIZE] {
        let n = reply_number_for(&h, ALICE, TURN_CHOOSE, arg as i64);
        match h.reply(WeChatMessage::text(ALICE, n)) {
            WeChatReply::Advanced { key, outcome } => {
                assert_eq!(key, "dungeon");
                assert!(
                    outcome.landed(),
                    "move {arg} landed a real receipt: {outcome:?}"
                );
            }
            other => panic!("move {arg} should advance the dungeon, got {other:?}"),
        }
    }

    let report = h.verify("dungeon", &room).expect("the session is live");
    assert!(
        report.verified,
        "the winning line re-verifies: {}",
        report.detail
    );
    assert_eq!(report.turns, 5, "genesis + four committed turns");
}

/// A COUNCIL propose → vote (both members, over a SHARED room) → enact plays through the WeChat host
/// — a real quorum vote assembled from two 1:1 conversations, a non-member is a real executor
/// refusal, and the decision chain re-verifies.
#[test]
fn a_council_propose_vote_enact_plays_through_the_wechat_host() {
    let mut h = host();
    // A shared council room — several participants act on ONE host session, each in their own 1:1
    // conversation (their own numbered-reply surface onto the shared council).
    let room = SessionId::new("wx-council-room");
    h.join("council", &room, ALICE).expect("ALICE joins");

    // ALICE proposes catalog item 0 ("Fund the archive").
    assert_landed(h.reply(WeChatMessage::text(
        ALICE,
        reply_number_for(&h, ALICE, "propose", 0),
    )));
    // ALICE approves proposal 0 (her surface re-presented with the vote options).
    assert_landed(h.reply(WeChatMessage::text(
        ALICE,
        reply_number_for(&h, ALICE, "approve", 0),
    )));

    // BOB joins (his conversation refreshes to the current council) and approves (quorum M = 2).
    h.join("council", &room, BOB).expect("BOB joins");
    assert_landed(h.reply(WeChatMessage::text(
        BOB,
        reply_number_for(&h, BOB, "approve", 0),
    )));

    // A non-member (MALLORY holds no ballot cap) is a real executor refusal — nothing commits.
    h.join("council", &room, MALLORY).expect("MALLORY joins");
    match h.reply(WeChatMessage::text(
        MALLORY,
        reply_number_for(&h, MALLORY, "approve", 0),
    )) {
        WeChatReply::Advanced {
            outcome: Outcome::Refused(why),
            ..
        } => assert!(
            why.contains("not a council member"),
            "a non-member is refused: {why}"
        ),
        other => panic!("a non-member vote must be refused, got {other:?}"),
    }

    // Enact — ALICE refreshes (quorum reached → ENACT now enabled) and enacts; the policy effect
    // commits as a real turn.
    h.join("council", &room, ALICE).expect("ALICE refreshes");
    assert_landed(h.reply(WeChatMessage::text(
        ALICE,
        reply_number_for(&h, ALICE, "enact", 0),
    )));

    let report = h.verify("council", &room).expect("the session is live");
    assert!(
        report.verified,
        "the council decision chain re-verifies: {}",
        report.detail
    );
}

/// A MARKET list → sealed bids (two bidders over a SHARED room) → settle clears through the WeChat
/// host — the value moves through the verified per-asset ring settlement, and the cleared chain
/// re-verifies. The value-taking turns (`list` reserve, `bid` value) ride a `#turn:value` marked
/// reply (the general shape a Mini-Program button posts, and the analogue of the Telegram callback
/// carrying the value); `settle` is a plain numbered reply.
#[test]
fn a_market_list_bid_settle_plays_through_the_wechat_host() {
    let mut h = host();
    let room = SessionId::new("wx-market-room");
    h.join("market", &room, SELLER).expect("the seller joins");

    // SELLER lists an item with reserve 100 (a value move → the `#list:100` marked reply).
    assert_landed(h.reply(WeChatMessage::text(SELLER, "#list:100")));

    // Two DISTINCT bidders place sealed bids from their own conversations (distinct OpenIDs →
    // distinct derived identities → distinct commit slots).
    h.join("market", &room, BOB).expect("BOB joins the auction");
    assert_landed(h.reply(WeChatMessage::text(BOB, "#bid:500")));
    h.join("market", &room, CAROL)
        .expect("CAROL joins the auction");
    assert_landed(h.reply(WeChatMessage::text(CAROL, "#bid:300")));

    // SETTLE — the seller refreshes and settles (reveal + clear to the high bid BOB 500 ≥ reserve
    // 100, conservation-checked). It ends the session. `settle` carries no value → a numbered reply.
    h.join("market", &room, SELLER)
        .expect("the seller refreshes");
    match h.reply(WeChatMessage::text(
        SELLER,
        reply_number_for(&h, SELLER, "settle", 0),
    )) {
        WeChatReply::Advanced { key, outcome } => {
            assert_eq!(key, "market");
            assert!(
                matches!(outcome, Outcome::Landed { ended: true, .. }),
                "the auction cleared and ended: {outcome:?}"
            );
        }
        other => panic!("settle should advance the market, got {other:?}"),
    }

    let report = h.verify("market", &room).expect("the session is live");
    assert!(
        report.verified,
        "the cleared market chain re-verifies: {}",
        report.detail
    );
}

/// An unoffered reply is refused BEFORE the substrate (the executor is never reached), and a reply
/// from a participant with nothing open is a no-session miss.
#[test]
fn an_unoffered_reply_is_refused_before_the_substrate() {
    let mut h = host();
    h.open("dungeon", ALICE).expect("the dungeon opens");

    // A reply that names no presented option (an out-of-range number) → refused before the substrate.
    match h.reply(WeChatMessage::text(ALICE, "99")) {
        WeChatReply::NotOffered => {}
        other => {
            panic!("an out-of-range reply must be refused before the substrate, got {other:?}")
        }
    }
    // Ordinary prose is not a press either.
    match h.reply(WeChatMessage::text(ALICE, "hello there")) {
        WeChatReply::NotOffered => {}
        other => panic!("prose is not a press, got {other:?}"),
    }

    // A reply from a participant with nothing open → no session.
    match h.reply(WeChatMessage::text(BOB, "1")) {
        WeChatReply::NoSession => {}
        other => panic!("a reply from an unopened conversation is NoSession, got {other:?}"),
    }
}

/// The RESERVED verify verb: a `#verifychain:0` marked reply routes through `reply()` to the
/// offering's REAL re-verifier — the input a runtime shell binds a "verify" keyword to. It is
/// never on the presented numbered list (surfaces stay byte-stable) and the shared codec fires
/// marked ids off-list, so it works from any conversation with an offering active; while the
/// participant is browsing the offerings menu it is honestly refused.
#[test]
fn the_verify_verb_routes_through_reply_to_the_real_reverifier() {
    let mut h = host();
    h.open("dungeon", ALICE).expect("the dungeon opens");
    let n = reply_number_for(&h, ALICE, TURN_CHOOSE, KP_PRESS_ON as i64);
    assert_landed(h.reply(WeChatMessage::text(ALICE, n)));

    match h.reply(WeChatMessage::text(ALICE, format!("#{TURN_VERIFY}:0"))) {
        WeChatReply::Verified { key, report } => {
            assert_eq!(key, "dungeon", "the report names the active offering");
            let report = report.expect("the dungeon exposes a verifier");
            assert!(
                report.verified,
                "the committed chain re-verifies by replay: {}",
                report.detail
            );
            assert_eq!(report.turns, 2, "genesis + one committed turn");
        }
        other => panic!("a verify reply must hand back the report, got {other:?}"),
    }

    // Verify is read-only: the surface is untouched, so the NEXT numbered reply still resolves.
    let n = reply_number_for(&h, ALICE, TURN_CHOOSE, KP_CLAIM_RED as i64);
    assert_landed(h.reply(WeChatMessage::text(ALICE, n)));

    // While browsing the offerings menu there is nothing to verify — honest refusal.
    h.present_offerings_menu(BOB);
    match h.reply(WeChatMessage::text(BOB, format!("#{TURN_VERIFY}:0"))) {
        WeChatReply::NotOffered => {}
        other => panic!("verify on the menu is refused before the substrate, got {other:?}"),
    }
}
