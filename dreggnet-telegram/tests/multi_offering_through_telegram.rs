//! **The driven MULTI-OFFERING proof — three heterogeneous offerings play through Telegram.**
//!
//! The single-offering `driven.rs` / `dungeon_through_telegram.rs` prove ONE offering plays over
//! Telegram. This proves the frontend-agnostic [`OfferingHost`](dreggnet_offerings::OfferingHost)
//! lifted to Telegram: a [`TelegramHost`] registers THREE distinct offerings (a dungeon, a council,
//! a market — heterogeneous `Session` types, one registry) and plays each through the SAME Telegram
//! inline-keyboard surface, with NO Telegram token and NO network (a
//! [`MockTransport`](dreggnet_telegram::transport::MockTransport)):
//!
//! - the host lists ≥ 3 offerings, and a `/offerings` menu keyboard opens any of them;
//! - a full winning DUNGEON line plays (each press → one real landed `TurnReceipt`);
//! - a COUNCIL propose → vote (two members) → enact plays, a non-member is a real refusal;
//! - a MARKET list → sealed bids → settle clears (value moves, conservation-checked);
//! - an unoffered turn is refused BEFORE the substrate;
//! - `verify` re-verifies each committed chain by replay.

use dreggnet_offerings::Outcome;
use dreggnet_telegram::CallbackQuery;
use dreggnet_telegram::api::encode_callback;
use dreggnet_telegram::host::{HostPress, TURN_OPEN, TelegramHost};
use dreggnet_telegram::transport::MockTransport;
use dungeon_on_dregg::{KP_CLAIM_RED, KP_DESCEND, KP_PRESS_ON, KP_SEIZE};

/// A deterministic bot secret (a real deploy loads 32 bytes from env).
const BOT_SECRET: [u8; 32] = [7u8; 32];
/// Two Telegram users registered as the council electorate (their derived identities are the
/// council members), plus a non-member and a second bidder.
const ALICE: u64 = 1001;
const BOB: u64 = 1002;
const CAROL: u64 = 1003;
const MALLORY: u64 = 9009;

/// A fresh host over the three default offerings, with ALICE + BOB as the council electorate.
fn host() -> TelegramHost<MockTransport> {
    TelegramHost::new(BOT_SECRET, MockTransport::new(), &[ALICE, BOB])
}

/// Assert a press advanced its offering and landed a real receipt.
fn assert_landed(p: HostPress) {
    match p {
        HostPress::Advanced { outcome, .. } => {
            assert!(outcome.landed(), "expected a landed turn, got {outcome:?}")
        }
        other => panic!("expected an advance, got {other:?}"),
    }
}

/// The host lists ≥ 3 offerings, and the `/offerings` menu is a keyboard of one open-button per
/// offering — a press of one opens that offering in the chat.
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

    // Present the /offerings menu → a sendMessage with one open-button per offering.
    let chat: i64 = 5000;
    let sid = h.present_offerings_menu(chat, None);
    let req = h.frontend().transport().last().expect("the menu was sent");
    assert_eq!(req.chat_id, chat, "the menu targets the chat");
    let kb = req
        .reply_markup
        .as_ref()
        .expect("the menu renders as an inline keyboard");
    assert_eq!(
        kb.inline_keyboard.len(),
        offs.len(),
        "one open-button per registered offering"
    );
    for (i, row) in kb.inline_keyboard.iter().enumerate() {
        assert_eq!(row.len(), 1, "one button per row");
        assert_eq!(
            row[0].callback_data,
            encode_callback(TURN_OPEN, i as i64),
            "the button opens the offering at its catalog index"
        );
    }

    // Press the market's open-button → the market opens in the chat.
    let market_idx = offs.iter().position(|o| o.key == "market").unwrap();
    match h.press(CallbackQuery::press(
        chat,
        ALICE,
        encode_callback(TURN_OPEN, market_idx as i64),
    )) {
        HostPress::Opened(k) => assert_eq!(k, "market", "the menu press opened the market"),
        other => panic!("a menu press should open the offering, got {other:?}"),
    }
    assert_eq!(
        h.active_offering(&sid),
        Some("market"),
        "the chat is now playing the market"
    );
}

/// A full winning DUNGEON line plays through the Telegram host — each keyboard press lands one real
/// turn, and the committed chain re-verifies by replay.
#[test]
fn a_winning_dungeon_line_plays_through_the_telegram_host() {
    let mut h = host();
    let chat: i64 = 42; // a positive chat id → single-player DM.
    let sid = h.open("dungeon", chat, None).expect("the dungeon opens");
    assert_eq!(h.active_offering(&sid), Some("dungeon"));

    for arg in [KP_PRESS_ON, KP_CLAIM_RED, KP_DESCEND, KP_SEIZE] {
        let ev = CallbackQuery::press(chat, ALICE, encode_callback("choose", arg as i64));
        match h.press(ev) {
            HostPress::Advanced { key, outcome } => {
                assert_eq!(key, "dungeon");
                assert!(
                    outcome.landed(),
                    "move {arg} landed a real receipt: {outcome:?}"
                );
            }
            other => panic!("move {arg} should advance the dungeon, got {other:?}"),
        }
    }

    let report = h.verify("dungeon", &sid).expect("the session is live");
    assert!(
        report.verified,
        "the winning line re-verifies: {}",
        report.detail
    );
    assert_eq!(report.turns, 5, "genesis + four committed turns");
}

/// A COUNCIL propose → vote (both members) → enact plays through the Telegram host — a real quorum
/// vote, a non-member is a real executor refusal, and the decision chain re-verifies.
#[test]
fn a_council_propose_vote_enact_plays_through_the_telegram_host() {
    let mut h = host();
    let chat: i64 = -1001; // a negative chat id → a group collective.
    let sid = h.open("council", chat, None).expect("the council opens");

    // ALICE proposes catalog item 0 ("Fund the archive").
    assert_landed(h.press(CallbackQuery::press(
        chat,
        ALICE,
        encode_callback("propose", 0),
    )));
    // Both members approve proposal 0 (quorum M = 2).
    assert_landed(h.press(CallbackQuery::press(
        chat,
        ALICE,
        encode_callback("approve", 0),
    )));
    assert_landed(h.press(CallbackQuery::press(
        chat,
        BOB,
        encode_callback("approve", 0),
    )));

    // A non-member (MALLORY holds no ballot cap) is a real executor refusal — nothing commits.
    match h.press(CallbackQuery::press(
        chat,
        MALLORY,
        encode_callback("approve", 0),
    )) {
        HostPress::Advanced {
            outcome: Outcome::Refused(why),
            ..
        } => assert!(
            why.contains("not a council member"),
            "a non-member is refused: {why}"
        ),
        other => panic!("a non-member vote must be refused, got {other:?}"),
    }

    // Enact — quorum reached, the policy effect commits as a real turn.
    assert_landed(h.press(CallbackQuery::press(
        chat,
        ALICE,
        encode_callback("enact", 0),
    )));

    let report = h.verify("council", &sid).expect("the session is live");
    assert!(
        report.verified,
        "the council decision chain re-verifies: {}",
        report.detail
    );
}

/// A MARKET list → sealed bids → settle clears through the Telegram host — the value moves through
/// the verified per-asset ring settlement, and the cleared chain re-verifies. The value-taking
/// turns (`list` reserve, `bid` value) carry their value in the press.
#[test]
fn a_market_list_bid_settle_plays_through_the_telegram_host() {
    let mut h = host();
    let chat: i64 = -2002;
    let sid = h.open("market", chat, None).expect("the market opens");

    // ALICE lists an item with reserve 100.
    assert_landed(h.press(CallbackQuery::press(
        chat,
        ALICE,
        encode_callback("list", 100),
    )));
    // Two DISTINCT bidders place sealed bids (distinct Telegram users → distinct identities →
    // distinct commit slots).
    assert_landed(h.press(CallbackQuery::press(chat, BOB, encode_callback("bid", 500))));
    assert_landed(h.press(CallbackQuery::press(
        chat,
        CAROL,
        encode_callback("bid", 300),
    )));

    // SETTLE — reveal + clear to the high bid (BOB, 500 ≥ reserve 100), conservation-checked. It
    // ends the session.
    match h.press(CallbackQuery::press(
        chat,
        ALICE,
        encode_callback("settle", 0),
    )) {
        HostPress::Advanced { key, outcome } => {
            assert_eq!(key, "market");
            assert!(
                matches!(outcome, Outcome::Landed { ended: true, .. }),
                "the auction cleared and ended: {outcome:?}"
            );
        }
        other => panic!("settle should advance the market, got {other:?}"),
    }

    let report = h.verify("market", &sid).expect("the session is live");
    assert!(
        report.verified,
        "the cleared market chain re-verifies: {}",
        report.detail
    );
}

/// An unoffered turn is refused BEFORE the substrate (the executor is never reached), and a press in
/// a chat with nothing open is a no-session miss.
#[test]
fn an_unoffered_turn_is_refused_before_the_substrate() {
    let mut h = host();
    let chat: i64 = 77;
    h.open("dungeon", chat, None).expect("the dungeon opens");

    // A turn the dungeon surface never offers → refused before the substrate.
    match h.press(CallbackQuery::press(
        chat,
        ALICE,
        encode_callback("not-a-real-turn", 0),
    )) {
        HostPress::NotOffered => {}
        other => panic!("an unoffered turn must be refused before the substrate, got {other:?}"),
    }

    // A press in a chat with nothing open → no session.
    match h.press(CallbackQuery::press(
        999,
        ALICE,
        encode_callback("choose", 1),
    )) {
        HostPress::NoSession => {}
        other => panic!("a press in an unopened chat is NoSession, got {other:?}"),
    }
}
