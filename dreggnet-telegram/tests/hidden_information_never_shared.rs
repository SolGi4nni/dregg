//! **The hidden hand never lands in a message a group reads.**
//!
//! ## The bug this file exists for
//! A Telegram session's surface is ONE message per chat, and a re-present EDITS that message in
//! place (`TelegramFrontend::present_result_with` → `Transport::edit_message`). The host used to
//! paint every re-present with `OfferingHost::render_for(viewer)` — the PRESSING player's private
//! projection — including in a group. So in a group chat, alice pressing a button rewrote the one
//! shared message to show alice's card ids, and every other member of the chat read them. Tug and
//! automatafl (both hidden-information games) were unplayable-as-designed anywhere but a DM, and
//! silently so.
//!
//! ## Why the OLD test did not catch it — and what this one does differently
//! `full_parity_through_telegram.rs`'s original tug test asserted, as its SUCCESS condition, that
//! "a different seat sees a DIFFERENT hand" in a group chat, read off `MockTransport::last()`.
//! Both halves of that hid the leak:
//!
//! 1. `last()` is the most recent request in isolation. It models each render as if it went to its
//!    own private place. The reality is that both renders land in the SAME message, so the
//!    difference the old test celebrated is precisely the leak: the group's one message showed
//!    alice's hand, then bob's.
//! 2. `MockTransport` inherited the default `edit_message`, which SENDS instead — so nothing in
//!    the test rig even represented a shared message being rewritten.
//!
//! This file fixes both. `MockTransport` now really edits (stable message id, and every version
//! kept in `sent`, because a group member read each one as it was posted), and every privacy
//! assertion here is over `sent_to(chat)` — **everything that chat's readers ever saw**, not the
//! latest frame. A leak that was edited away a second later still fails these tests.
//!
//! ## What the fix is
//! - **Structural:** in a collective chat the host calls the viewer-blind `render`/`actions`, never
//!   `render_for`. A shared message can only carry the public projection, for ANY offering.
//! - **Declared:** an offering that says `Offering::hidden_information() == true` (tug, automatafl)
//!   is not hosted in a shared chat at all — a public-only projection is not a playable hand — so
//!   it is REFUSED at open with a legible redirect to a DM / the Mini App.
//!
//! The declared signal is load-bearing for the refusal because a render *differential* cannot
//! decide it: at open, before a seat is claimed, tug's per-viewer projection is byte-identical to
//! its public one (`test_the_open_render_differential_would_have_said_safe` proves exactly that).

use dreggnet_offerings::{Offering, Outcome};
use dreggnet_telegram::CallbackQuery;
use dreggnet_telegram::api::{LOCK_GLYPH, encode_callback};
use dreggnet_telegram::host::{HostPress, OpenError, TelegramHost};
use dreggnet_telegram::transport::MockTransport;

const BOT_SECRET: [u8; 32] = [7u8; 32];
const ALICE: u64 = 1001;
const BOB: u64 = 1002;

fn host() -> TelegramHost<MockTransport> {
    TelegramHost::new(BOT_SECRET, MockTransport::new(), &[ALICE, BOB])
}

/// Markers of a PRIVATE tug projection — the strings `render_for` adds for the seat that owns the
/// hand, and that the public `render` never produces (both hands are fog there).
const PRIVATE_MARKERS: [&str; 2] = ["Your hand", "card #"];

/// Assert that NOTHING a chat's readers ever saw carried a private marker — over the chat's WHOLE
/// transcript, including versions an edit later replaced. This is the assertion the old test could
/// not make, because it read only the latest frame.
fn assert_chat_never_showed_private(h: &TelegramHost<MockTransport>, chat: i64) {
    let transcript = h.frontend().transport().sent_to(chat);
    for (i, req) in transcript.iter().enumerate() {
        for marker in PRIVATE_MARKERS {
            assert!(
                !req.text.contains(marker),
                "message version #{i} in shared chat {chat} leaked {marker:?} to every member \
                 of the chat:\n{}",
                req.text
            );
        }
        // A button LABEL is read by the whole chat too — the keyboard is part of the message.
        if let Some(markup) = &req.reply_markup {
            for row in &markup.inline_keyboard {
                for b in row {
                    for marker in PRIVATE_MARKERS {
                        assert!(
                            !b.text.contains(marker),
                            "a keyboard button in shared chat {chat} leaked {marker:?}: {}",
                            b.text
                        );
                    }
                }
            }
        }
    }
}

/// **THE LEAK TEST.** A hidden-information offering opened in a GROUP does not render a per-viewer
/// surface into the shared message: the open is REFUSED with a legible redirect, and the chat's
/// entire transcript is free of private content.
#[test]
fn a_hidden_information_offering_is_refused_in_a_group_and_leaks_nothing() {
    let mut h = host();
    let group: i64 = -700; // a negative chat id → a group: ONE message, many readers.

    let refusal = h
        .open("tug", group, None, ALICE)
        .expect_err("tug hides a hand — a group's shared message must not host it");
    let why = match &refusal {
        OpenError::HiddenInSharedChat { key, why } => {
            assert_eq!(key, "tug");
            why.clone()
        }
        other => panic!("expected the shared-chat privacy refusal, got {other:?}"),
    };

    // LEGIBLE: it names the game, says why, and tells the player where to go instead.
    assert!(
        why.contains("group"),
        "the refusal names the problem: {why}"
    );
    assert!(
        why.contains("/open tug"),
        "the refusal points at the DM path: {why}"
    );
    assert!(
        why.to_lowercase().contains("dm"),
        "the refusal names the private surface: {why}"
    );

    // Nothing was opened: the chat has no tug session and no surface to press.
    assert!(
        h.verify(
            "tug",
            &dreggnet_telegram::TelegramFrontend::<MockTransport>::session_id(group, None)
        )
        .is_none(),
        "a refused open leaves NO host session behind"
    );
    assert!(
        matches!(
            h.press(CallbackQuery::press(
                group,
                ALICE,
                encode_callback("comp", 3)
            )),
            HostPress::NoSession
        ),
        "with nothing opened there is nothing to press"
    );

    // And the whole-transcript check: the group never saw a card.
    assert_chat_never_showed_private(&h, group);
}

/// The same refusal on the **menu-press** path (a `▶ Play` button in `/offerings`), not just
/// `/open` — both entrances go through the one gate, and the presser gets the same legible
/// redirect. A leak fixed on one entrance and left open on the other is not fixed.
#[test]
fn the_offerings_menu_refuses_a_hidden_offering_in_a_group_too() {
    let mut h = host();
    let group: i64 = -701;
    h.present_offerings_menu(group, None);

    let tug_index = h
        .list_offerings()
        .iter()
        .position(|o| o.key == "tug")
        .expect("tug is registered");

    let press = h.press(CallbackQuery::press(
        group,
        ALICE,
        encode_callback("open", tug_index as i64),
    ));
    match press {
        HostPress::OpenRefused { key, why } => {
            assert_eq!(key, "tug");
            assert!(why.contains("/open tug"), "legible redirect: {why}");
        }
        other => panic!("a menu press for tug in a group must be refused, got {other:?}"),
    }
    assert!(
        h.active_offering(
            &dreggnet_telegram::TelegramFrontend::<MockTransport>::session_id(group, None)
        )
        .is_none(),
        "the refused open never became the chat's active offering"
    );
    assert_chat_never_showed_private(&h, group);
}

/// **The structural half, proved on an offering that is NOT declared hidden.** Even for an
/// offering the declaration does not cover, a shared chat's message carries the VIEWER-BLIND
/// projection: the host never calls `render_for` there. The document's per-viewer projection
/// (its cap-dimmed menu) differs from the public one — and what the group's message shows is the
/// public one, byte for byte, no matter who pressed last.
#[test]
fn a_group_message_carries_the_viewer_blind_projection_even_when_undeclared() {
    let mut h = host();
    let group: i64 = -702;
    let dm: i64 = 702;

    // The document's two projections differ observably in ONE way that survives every other
    // difference between two sessions (seeds, commitments, contents): the per-viewer projection
    // DIMS the edit affordances of a viewer who holds no edit cap (`🔒`), while the viewer-blind
    // one — which has no viewer to gate against — leaves them undimmed. So the lock glyph reads
    // out exactly WHICH projection was served, with no circularity.
    h.open("doc", group, None, ALICE).expect("doc opens");
    let group_buttons = button_labels(&h, group);
    assert!(
        !group_buttons.is_empty(),
        "the doc surface really has a keyboard: {group_buttons:?}"
    );
    assert!(
        !group_buttons.iter().any(|b| b.contains(LOCK_GLYPH)),
        "the group's shared message was served the VIEWER-BLIND projection (no per-viewer cap \
         dimming): {group_buttons:?}"
    );

    // Re-presenting as a DIFFERENT member does not swing the shared message to that member's view.
    h.open("doc", group, None, BOB).expect("doc re-presents");
    assert_eq!(
        h.frontend().transport().sent_to(group).len(),
        2,
        "the shared message really was painted a second time (this is not a no-op)"
    );
    assert_eq!(
        h.frontend().transport().messages_in(group).len(),
        1,
        "…into the SAME message — which is exactly why it may not be per-viewer"
    );
    assert!(
        !button_labels(&h, group)
            .iter()
            .any(|b| b.contains(LOCK_GLYPH)),
        "still the viewer-blind projection after another member acted"
    );

    // The SAME offering in a DM is still served per-viewer: alice holds no edit cap on a document
    // she has not been invited to, so HER projection dims those affordances. The rule is about who
    // READS the surface, not about switching projection off.
    h.open("doc", dm, None, ALICE).expect("doc opens in a DM");
    assert!(
        button_labels(&h, dm).iter().any(|b| b.contains(LOCK_GLYPH)),
        "a DM is served the PER-VIEWER projection: {:?}",
        button_labels(&h, dm)
    );
}

/// The inline-keyboard button labels of the last message a chat received.
fn button_labels(h: &TelegramHost<MockTransport>, chat: i64) -> Vec<String> {
    h.frontend()
        .transport()
        .sent_to(chat)
        .last()
        .expect("the chat received a surface")
        .reply_markup
        .as_ref()
        .map(|m| {
            m.inline_keyboard
                .iter()
                .flatten()
                .map(|b| b.text.clone())
                .collect()
        })
        .unwrap_or_default()
}

/// **Non-vacuity: the per-viewer projection still WORKS where it is safe.** The fix is not "delete
/// the hidden hand" — in a DM (one reader) the player sees their OWN cards, exactly as designed.
#[test]
fn a_dm_still_serves_the_player_their_own_hidden_hand() {
    let mut h = host();
    let dm: i64 = 701; // a positive chat id → a DM: one reader.
    let sid = h.open("tug", dm, None, ALICE).expect("tug opens in a DM");

    // ALICE plays the opening move — claims seat A, lands a real receipt, and the re-present is
    // projected FOR her.
    let press = h.press(CallbackQuery::press(dm, ALICE, encode_callback("comp", 3)));
    assert!(
        matches!(
            press,
            HostPress::Advanced {
                outcome: Outcome::Landed { .. },
                ..
            }
        ),
        "alice's opening comp lands + claims seat A: {press:?}"
    );

    let visible = h
        .frontend()
        .transport()
        .sent_to(dm)
        .last()
        .expect("the tug surface was presented")
        .text
        .clone();
    assert!(
        visible.contains("Your hand") && visible.contains("card #"),
        "the seated player sees HER OWN card ids in her DM: {visible}"
    );
    assert!(
        visible.contains("Opponent (hidden hand)"),
        "the opponent's hand stays fog even for the seated viewer: {visible}"
    );

    // The committed chain re-verifies — a real driven turn, not a rendering trick.
    let report = h.verify("tug", &sid).expect("the tug session is live");
    assert!(
        report.verified,
        "the tug chain re-verifies: {}",
        report.detail
    );
}

/// **Why the signal is DECLARED and not inferred from a render differential.** A fresh tug
/// viewer now receives a safe claim affordance, so that projection may differ from the public
/// one before a seat exists. Neither projection contains card ids, however; presentation details
/// still cannot tell a shared frontend whether a later seated projection carries secrets. The
/// explicit declaration remains the policy boundary.
#[test]
fn the_open_claim_surface_is_safe_but_the_offering_still_declares_future_secrets() {
    use dreggnet_offerings::{DreggIdentity, SessionConfig};

    let tug = dreggnet_telegram::seated::SeatedTug::new();
    let session = tug.open(SessionConfig::with_seed(42)).expect("tug opens");
    let viewer = DreggIdentity("a-freshly-arrived-player".to_string());

    let public = format!("{:?}", tug.render(&session).view());
    let per_viewer = format!("{:?}", tug.render_for(&session, &viewer).view());
    assert!(
        !public.contains("card #"),
        "the public opening leaks no hand"
    );
    assert!(
        !per_viewer.contains("card #"),
        "the pre-seat claim surface leaks no hand"
    );
    assert!(
        per_viewer.contains("Competition"),
        "a fresh private viewer gets a usable seat-claim affordance"
    );

    assert!(
        tug.hidden_information(),
        "…but the offering DECLARES that its per-viewer projection will carry secrets, and that \
         declaration is what the shared-surface refusal reads"
    );
}
