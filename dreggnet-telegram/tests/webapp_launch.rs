//! **The Mini App LAUNCH tier, driven over `MockTransport`** — no token, no network:
//!
//! - a DM's presented offering surface carries the trailing "🕹 Play in the app" `web_app`
//!   button whose URL is the funnel base + the design-pinned `/tg/offerings/{key}/session/{id}`
//!   deep path — and the button serializes to the Bot API wire shape (a `web_app` field, NO
//!   `callback_data`);
//! - a group chat never gets one (Telegram refuses `web_app` inline buttons outside DMs — the
//!   inline-button tier stays the group's full surface);
//! - `/play` presents the launch menu (one `web_app` button per offering) in a DM and answers
//!   an honest text refusal in a group / on an unarmed host;
//! - a `web_app_data` update (the Mini App's `sendData` round-trip) is parsed + routed without
//!   panic: an affordance-codec payload faces the SAME presented-affordance gate + executor as
//!   a button press; junk is acknowledged and drops nothing on the floor;
//! - the identity master secret resolves through the ONE lib impl, pinned (the token-derived
//!   fixture output must never move — the web Mini App validator derives the same secret).

use dreggnet_telegram::TelegramFrontend;
use dreggnet_telegram::api::encode_callback;
use dreggnet_telegram::cipherclerk::master_secret_from;
use dreggnet_telegram::host::TelegramHost;
use dreggnet_telegram::runtime::{BotEvent, parse_updates, route_text, route_web_app_data};
use dreggnet_telegram::transport::MockTransport;
use dreggnet_telegram::webapp::{
    DEFAULT_WEBAPP_BASE, PLAY_IN_APP_LABEL, play_url, web_app_allowed,
};
use dungeon_on_dregg::KP_PRESS_ON;
use serde_json::json;

const BOT_SECRET: [u8; 32] = [9u8; 32];
const ALICE: u64 = 1001;
const BASE: &str = "https://hbox-dregg.skunk-emperor.ts.net";

/// A fresh in-memory host with the Mini App launch tier ARMED at the funnel base (a trailing
/// slash on purpose — the builder trims it).
fn armed_host() -> TelegramHost<MockTransport> {
    TelegramHost::new(BOT_SECRET, MockTransport::new(), &[]).with_webapp_base(format!("{BASE}/"))
}

/// A DM's presented offering surface carries the trailing `web_app` Play button with the
/// design-pinned deep URL for THAT offering + session — and it serializes to the Bot API wire
/// shape (`web_app` present, `callback_data` absent). A group's surface never carries one.
#[test]
fn a_dm_surface_carries_the_play_button_with_the_offering_session_url() {
    let mut h = armed_host();
    let chat: i64 = 42;
    h.open("dungeon", chat, None, ALICE).expect("dungeon opens");

    let req = h.frontend().transport().last().expect("surface sent");
    let kb = &req.reply_markup.as_ref().expect("keyboard").inline_keyboard;
    let play = &kb.last().expect("at least the play row")[0];
    assert_eq!(play.text, PLAY_IN_APP_LABEL);
    assert_eq!(
        play.web_app.as_ref().expect("a web_app launch button").url,
        format!("{BASE}/tg/offerings/dungeon/session/tg:{chat}"),
        "the Play URL is the funnel base + the pinned /tg deep path for THIS offering+session"
    );
    assert!(
        play.callback_data.is_empty(),
        "a launch button carries no callback"
    );
    // The wire shape: exactly one action field on the button — web_app, never callback_data.
    let wire = serde_json::to_string(play).expect("serializes");
    assert!(wire.contains("\"web_app\""), "web_app on the wire: {wire}");
    assert!(
        !wire.contains("callback_data"),
        "an empty callback_data is OMITTED from the wire: {wire}"
    );
    // Every OTHER row is still an ordinary affordance press button (the fallback tier intact).
    for row in &kb[..kb.len() - 1] {
        assert!(row[0].web_app.is_none() && !row[0].callback_data.is_empty());
    }

    // A GROUP chat (negative id): Telegram refuses web_app inline buttons there — none sent.
    let group: i64 = -777;
    assert!(!web_app_allowed(group, None), "groups are gated out");
    h.open("dungeon", group, None, ALICE).expect("opens");
    let req = h.frontend().transport().last().expect("surface sent");
    for row in &req.reply_markup.as_ref().expect("keyboard").inline_keyboard {
        assert!(
            row.iter().all(|b| b.web_app.is_none()),
            "no web_app button in a group keyboard"
        );
    }
}

/// `/play` presents the launch menu in a DM — one `web_app` button per registered offering,
/// each deep-linking that offering at this chat's session id. A group gets the honest text
/// refusal; an UNARMED host names the missing tier instead of half-working.
#[test]
fn play_command_presents_the_launch_menu_in_a_dm_and_refuses_honestly_elsewhere() {
    let mut h = armed_host();
    let chat: i64 = 43;

    assert_eq!(
        route_text(&mut h, chat, None, ALICE, "/play"),
        None,
        "the launch menu IS the reply"
    );
    let menu = h.frontend().transport().last().expect("menu sent");
    let offerings = h.list_offerings();
    let rows = &menu
        .reply_markup
        .as_ref()
        .expect("keyboard")
        .inline_keyboard;
    assert_eq!(
        rows.len(),
        offerings.len(),
        "one launch button per offering"
    );
    let sid = TelegramFrontend::<MockTransport>::session_id(chat, None);
    for (row, o) in rows.iter().zip(&offerings) {
        assert_eq!(
            row[0].web_app.as_ref().expect("a launch button").url,
            play_url(BASE, &o.key, &sid),
            "each button deep-links ITS offering at this chat's session"
        );
    }

    // A group: refused with the honest Telegram-rule reply (nothing sent).
    let sent_before = h.frontend().transport().sent.len();
    let reply = route_text(&mut h, -50, None, ALICE, "/play").expect("a text refusal");
    assert!(reply.contains("private chat"), "names the rule: {reply}");
    assert_eq!(h.frontend().transport().sent.len(), sent_before);

    // An UNARMED host (no webapp base): /play names the missing tier.
    let mut bare = TelegramHost::new(BOT_SECRET, MockTransport::new(), &[]);
    let reply = route_text(&mut bare, chat, None, ALICE, "/play").expect("a text refusal");
    assert!(
        reply.contains("not configured"),
        "honest about the unarmed tier: {reply}"
    );
    // The default base constant is the deployed funnel (what the bin arms absent the env).
    assert_eq!(
        DEFAULT_WEBAPP_BASE,
        "https://hbox-dregg.skunk-emperor.ts.net"
    );
}

/// A real-shaped `web_app_data` update decodes to the typed event and routes WITHOUT panic:
/// an affordance-codec payload faces the same presented-affordance gate + executor a button
/// press does (untrusted client data can still only fire what the surface offers); junk is
/// acknowledged; a payload for a turn never offered is refused BEFORE the substrate.
#[test]
fn a_web_app_data_update_is_parsed_and_routed_without_panic() {
    let chat: i64 = 44;
    let data = encode_callback("choose", KP_PRESS_ON as i64);
    let result = json!([{
        "update_id": 900,
        "message": {
            "message_id": 5,
            "chat": { "id": chat, "type": "private" },
            "from": { "id": ALICE, "is_bot": false, "first_name": "Alice" },
            "web_app_data": { "data": data, "button_text": "Play" }
        }
    }]);
    let (events, next) = parse_updates(&result);
    assert_eq!(next, Some(901), "the offset is consumed");
    assert_eq!(events.len(), 1);
    let BotEvent::WebAppData {
        chat_id,
        uid,
        data: payload,
        button_text,
        ..
    } = &events[0]
    else {
        panic!(
            "web_app_data decodes to BotEvent::WebAppData, got {:?}",
            events[0]
        );
    };
    assert_eq!((*chat_id, *uid), (chat, ALICE));
    assert_eq!(payload, &data);
    assert_eq!(button_text.as_deref(), Some("Play"));

    // Route it against a live session: the offered affordance LANDS a real turn…
    let mut h = armed_host();
    h.open("dungeon", chat, None, ALICE).expect("opens");
    let reply = route_web_app_data(&mut h, chat, None, ALICE, payload);
    assert!(reply.contains("landed"), "a real substrate turn: {reply}");

    // …a decodable-but-never-offered payload is refused BEFORE the substrate…
    let reply = route_web_app_data(&mut h, chat, None, ALICE, "sudo:999");
    assert!(
        reply.contains("not on the current surface"),
        "the presented-affordance gate holds for client data: {reply}"
    );

    // …and junk is acknowledged, never a crash, nothing landed.
    let reply = route_web_app_data(&mut h, chat, None, ALICE, "🦆 not an affordance");
    assert!(reply.contains("no affordance"), "honest ack: {reply}");

    // A partial web_app_data (no `data`) is skipped, offset still consumed.
    let (events, next) = parse_updates(&json!([{
        "update_id": 901,
        "message": {
            "chat": { "id": chat, "type": "private" },
            "from": { "id": ALICE },
            "web_app_data": { "button_text": "Play" }
        }
    }]));
    assert!(events.is_empty(), "partial update decodes to nothing");
    assert_eq!(next, Some(902));
}

/// **The master-secret pin** — the ONE lib resolver both binaries share. The token-derived
/// fixture output is pinned byte-for-byte: if this moves, every custodial identity a deployed
/// bot ever derived moves with it (and the web Mini App validator forks from the bot).
#[test]
fn master_secret_resolution_is_pinned() {
    // Explicit hex wins, decoded exactly.
    let explicit = "aa".repeat(32);
    assert_eq!(
        master_secret_from("ignored-token", Some(&explicit)).expect("64 hex chars resolve"),
        [0xaa; 32]
    );
    // Malformed explicit values are refused, never silently fallen through.
    assert!(master_secret_from("t", Some("not-hex")).is_err());
    assert!(
        master_secret_from("t", Some("abcd")).is_err(),
        "wrong length refused"
    );
    // Whitespace-only counts as unset (the env-file trap).
    let derived = master_secret_from("123456:TEST-FIXTURE-TOKEN", Some("  ")).expect("derives");
    assert_eq!(
        derived,
        master_secret_from("123456:TEST-FIXTURE-TOKEN", None).expect("derives"),
        "blank explicit value falls through to the token-derived path"
    );
    // THE PIN: the token-derived secret for the fixture token, byte-for-byte.
    assert_eq!(
        hex::encode(derived),
        "8bab9224f0760244ad27d78026ecc5414b99e89305b8bdcfbd5998a7afddf102",
        "the token-derived master secret is pinned (a move here remaps every identity)"
    );
}
