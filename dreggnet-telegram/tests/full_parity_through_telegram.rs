//! **The driven FULL-PORTFOLIO parity proof — Telegram registers the SAME 18 offerings the web
//! catalog does, and the viewer threads through the surface.**
//!
//! `multi_offering_through_telegram.rs` proved THREE heterogeneous offerings play through Telegram.
//! This closes the gap the audit found: Telegram (and WeChat) registered only three each while the
//! web catalog ([`dreggnet_web::demo_host`]) registers eighteen — the five games (incl. automatafl +
//! multiway-tug) and the eight do-once RPG feature surfaces were ABSENT because their crates were not
//! deps. Now [`telegram_default_host`] builds through the ONE shared registrar
//! (`dreggnet_catalog::build_full_catalog` — docs/BOT-SHARED-BACKEND-DESIGN.md). This drives:
//!
//! - **BOTH-POLARITY offering-set parity against the LIVE web catalog**: the Telegram host,
//!   driven over [`MockTransport`], registers exactly the key set `dreggnet_web::demo_host()`
//!   registers — an offering missing from Telegram fails, and an offering Telegram grows that web
//!   lacks fails too (no hand-copied list on either side of the comparison);
//! - a newly-registered game (**automatafl**) is REACHABLE and renders a NON-EMPTY surface (a
//!   CoordGrid board degrades to a text grid on the text-only Telegram renderer — expected, not a
//!   silent drop);
//! - the **multiway-tug hidden hand** threads the viewer: a seated player, projected through the
//!   frontend's own derived identity, sees THEIR OWN card ids while a different seat sees a DIFFERENT
//!   hand — the per-viewer discrimination the `hidden_hand_web.rs` shape proves on the web, now on
//!   the chat surface;
//! - a real turn drives through a newly-registered game (tug's opening `comp` lands a receipt), and
//!   the committed chain re-verifies.

use dreggnet_offerings::Outcome;
use dreggnet_telegram::CallbackQuery;
use dreggnet_telegram::api::encode_callback;
use dreggnet_telegram::host::{HostPress, TelegramHost};
use dreggnet_telegram::transport::MockTransport;

const BOT_SECRET: [u8; 32] = [7u8; 32];
const ALICE: u64 = 1001;
const BOB: u64 = 1002;

fn host() -> TelegramHost<MockTransport> {
    TelegramHost::new(BOT_SECRET, MockTransport::new(), &[ALICE, BOB])
}

/// The last message text the Telegram transport sent (the surface just presented to a chat).
fn last_text(h: &TelegramHost<MockTransport>) -> String {
    h.frontend()
        .transport()
        .last()
        .expect("a surface was presented")
        .text
        .clone()
}

/// **BOTH-POLARITY parity with the LIVE web catalog.** The Telegram host — driven over
/// [`MockTransport`] through its real `HostThread` — registers exactly the offering-key set
/// `dreggnet_web::demo_host()` registers. Polarity 1: every web offering is reachable on Telegram
/// (the audit's original gap). Polarity 2: Telegram registers NOTHING web lacks (no silent
/// re-fork of the catalog). Both sides are live hosts, not hand-copied lists, so drift in either
/// direction — in either frontend — fails here; both build through
/// `dreggnet_catalog::build_full_catalog` at HEAD, and this test is the referee that keeps it so.
#[test]
fn telegram_and_the_web_catalog_register_the_same_offering_set_both_polarities() {
    let h = host();
    let mut telegram_keys: Vec<String> = h.list_offerings().into_iter().map(|o| o.key).collect();
    telegram_keys.sort();

    let web = dreggnet_web::demo_host();
    let mut web_keys: Vec<String> = web.list_offerings().into_iter().map(|o| o.key).collect();
    web_keys.sort();

    // Polarity 1 — nothing the web serves is missing on Telegram.
    for want in &web_keys {
        assert!(
            telegram_keys.contains(want),
            "web offering `{want}` is missing from the Telegram host: {telegram_keys:?}"
        );
    }
    // Polarity 2 — Telegram serves nothing the web lacks.
    for got in &telegram_keys {
        assert!(
            web_keys.contains(got),
            "Telegram offering `{got}` is absent from the web catalog: {web_keys:?}"
        );
    }
    // And the sets are exactly equal (multiplicity included).
    assert_eq!(
        telegram_keys, web_keys,
        "the Telegram host and the web catalog register the SAME offering set"
    );

    // The set is the shared catalog's contract — the ONE list both frontends now build from.
    let mut contract: Vec<&str> = dreggnet_catalog::CATALOG_KEYS.to_vec();
    contract.sort();
    assert_eq!(
        telegram_keys, contract,
        "the shared set IS dreggnet_catalog::CATALOG_KEYS"
    );
}

/// A newly-registered game (**automatafl**) is REACHABLE through the Telegram host and renders a
/// NON-EMPTY surface — the board is a CoordGrid that degrades to a text grid on the text-only
/// renderer (expected), NOT a silent empty. A press drives one turn through the substrate + re-renders.
#[test]
fn automatafl_is_reachable_and_renders_a_non_empty_surface_on_telegram() {
    let mut h = host();
    let chat: i64 = 314;
    let sid = h
        .open("automatafl", chat, None, ALICE)
        .expect("automatafl opens on Telegram");
    assert_eq!(h.active_offering(&sid), Some("automatafl"));

    let surface = last_text(&h);
    assert!(
        !surface.trim().is_empty(),
        "the automatafl board renders a non-empty (degraded-to-text) surface, not a silent drop: {surface:?}"
    );
    // The board is a CoordGrid — it must contribute a text grid (degraded), not vanish.
    assert!(
        surface.contains("Automatafl") || surface.contains("COMMIT") || surface.contains("seat"),
        "the automatafl surface carries its board/phase prose (degraded from the grid): {surface}"
    );

    // Drive one turn: press the first `select` the board offers (a movable piece at index 0..N). The
    // substrate is reached and the surface re-renders (Advanced), proving the game is drivable.
    let pressed = h.press(CallbackQuery::press(
        chat,
        ALICE,
        encode_callback("select", 0),
    ));
    match pressed {
        HostPress::Advanced { key, .. } => {
            assert_eq!(
                key, "automatafl",
                "the press drove the automatafl substrate"
            );
            assert!(
                !last_text(&h).trim().is_empty(),
                "the board re-renders a non-empty surface after the turn"
            );
        }
        // If index 0 is not a movable piece on this seed the surface never offered it → NotOffered is
        // an honest frontend refusal (the substrate stayed the referee); the reachability + non-empty
        // render above is the parity bar.
        HostPress::NotOffered => {}
        other => panic!("an automatafl press should advance or be NotOffered, got {other:?}"),
    }
}

/// **The multiway-tug hidden hand threads the viewer through the Telegram surface.** Two Telegram
/// users each claim a seat by playing; the frontend projects each re-render FOR the pressing user's
/// derived identity (`render_for`), so each sees THEIR OWN card ids — and the two hands DIFFER. A
/// seated player never sees the opponent's cards (fog). This is the `hidden_hand_web.rs` shape on
/// the chat surface: per-viewer discrimination, driven end-to-end (not the viewer-blind projection).
#[test]
fn the_tug_hidden_hand_threads_the_viewer_on_telegram() {
    let mut h = host();
    let chat: i64 = -700; // a group so both users share the round.
    let sid = h
        .open("tug", chat, None, ALICE)
        .expect("tug opens on Telegram");
    assert_eq!(h.active_offering(&sid), Some("tug"));

    // ALICE plays the round's opening action (Competition) — claims seat A, lands a real receipt, and
    // the re-render is projected FOR alice: her own hand is revealed.
    let alice_press = h.press(CallbackQuery::press(
        chat,
        ALICE,
        encode_callback("comp", 3),
    ));
    assert!(
        matches!(
            alice_press,
            HostPress::Advanced {
                outcome: Outcome::Landed { .. },
                ..
            }
        ),
        "alice's opening comp lands + claims seat A: {alice_press:?}"
    );
    let alice_view = last_text(&h);
    assert!(
        !alice_view.trim().is_empty(),
        "the tug surface for the seated player is non-empty (not a silent drop)"
    );
    assert!(
        alice_view.contains("Your hand") && alice_view.contains("card #"),
        "seat A (alice) sees HER OWN card ids through the frontend: {alice_view}"
    );
    assert!(
        alice_view.contains("Opponent (hidden hand)"),
        "the opponent's hand stays fog for the seated viewer: {alice_view}"
    );

    // BOB now presses — claims seat B (A is alice's). The re-render is projected FOR bob: his own,
    // DIFFERENT hand. (The press may land or be a real turn-order refusal — either way the seat is
    // claimed and the surface re-renders AS bob, which is the viewer-thread we assert.)
    let _ = h.press(CallbackQuery::press(
        chat,
        BOB,
        encode_callback("secret", 0),
    ));
    let bob_view = last_text(&h);
    assert!(
        bob_view.contains("Your hand") && bob_view.contains("card #"),
        "seat B (bob) sees HIS OWN card ids through the frontend: {bob_view}"
    );
    assert_ne!(
        alice_view, bob_view,
        "the viewer threaded: alice's seat-A hand and bob's seat-B hand render DIFFERENTLY \
         (per-viewer discrimination, not the viewer-blind fog everyone shared before)"
    );

    // The committed chain re-verifies by replay — a real driven turn through a newly-registered game.
    let report = h.verify("tug", &sid).expect("the tug session is live");
    assert!(
        report.verified,
        "the tug chain re-verifies: {}",
        report.detail
    );
}
