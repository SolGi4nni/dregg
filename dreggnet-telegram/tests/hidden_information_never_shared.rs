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
use dreggnet_telegram::api::{LOCK_GLYPH, decode_callback, encode_callback};
use dreggnet_telegram::host::{HostPress, OpenError, TURN_OPEN, TelegramHost};
use dreggnet_telegram::runtime::route_text_decided;
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

/// **The `callback_data` of the first LIVE button on the surface this chat was last presented** —
/// what a person's thumb reaches, derived from the keyboard the bot actually sent.
///
/// ⚑ NEVER `encode_callback("comp", 3)`. `arg` is an INDEX into the acting seat's LIVE
/// `legal_decisions()`, and since the seats CHOOSE (rather than running a fixed per-seat action
/// order) index 3 names whatever the deal put there — so a literal pair is refused, correctly, as a
/// control that is not on the current surface, and every assertion after it is about a turn that
/// never happened. `build_present_request_with_callback_data` sorts LIVE affordances before locked
/// ones and prefixes a locked label with [`LOCK_GLYPH`], so the first un-prefixed, non-`/verify`
/// button is exactly the move this chat is being offered.
fn live_press(h: &TelegramHost<MockTransport>, chat: i64) -> String {
    let sent = h.frontend().transport().sent_to(chat);
    let message = sent.last().expect("the chat was presented a surface");
    let markup = message
        .reply_markup
        .as_ref()
        .expect("an interactive surface carries an inline keyboard");
    markup
        .inline_keyboard
        .iter()
        .flatten()
        .find(|button| {
            !button.text.starts_with(LOCK_GLYPH)
                && !button
                    .callback_data
                    .starts_with(dreggnet_telegram::verify_control::TURN_VERIFY)
        })
        .map(|button| button.callback_data.clone())
        .unwrap_or_else(|| {
            panic!(
                "the presented surface offers no live control: {:?}",
                markup.inline_keyboard
            )
        })
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

// ═════════════════════════════════════════════════════════════════════════════
// ⚑ THE SHELF IS HONEST BEFORE THE PRESS — the menu, not just the open
// ═════════════════════════════════════════════════════════════════════════════
//
// The refusal above is correct and stays. It was also, for a while, the ONLY thing that knew: the
// `/offerings` shelf painted an enabled `▶ Play …` button for all three shipped games in a group
// chat, and two of the three refused on press. Measured by a flow driver on real Telegram traffic;
// a player in a group met a wall of "no" two times out of three, which is the whole of a
// Discord/Telegram bot's home.
//
// It is cheap to fix precisely because `Offering::hidden_information()` needs NO SESSION (the trait
// doc says so outright): the shelf can take the verdict at paint time. So these tests demand the
// menu be honest at paint time — and demand it by READING THE DECLARATION per key, never by
// listing which games are which, because such a list goes stale the first time a game changes its
// mind and the test would then certify the wrong thing.

/// The last message a chat received, as `(button label, callback_data)` pairs.
fn shelf_rows(h: &TelegramHost<MockTransport>, chat: i64) -> Vec<(String, String)> {
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
                .map(|b| (b.text.clone(), b.callback_data.clone()))
                .collect()
        })
        .unwrap_or_default()
}

/// The offering key a shelf button's callback resolves to (its position in the FULL catalog list —
/// which is what a menu button's arg is, and must stay).
fn key_of(h: &TelegramHost<MockTransport>, callback: &str) -> String {
    let (turn, arg) = decode_callback(callback)
        .unwrap_or_else(|| panic!("a shelf button carries a decodable affordance: {callback}"));
    assert_eq!(turn, TURN_OPEN, "a shelf button opens an offering");
    let index = usize::try_from(arg).expect("a catalog index is non-negative");
    h.list_offerings()
        .get(index)
        .unwrap_or_else(|| panic!("callback arg {arg} addresses a registered offering"))
        .key
        .clone()
}

/// **⚑ THE TOOTH. A GROUP'S SHELF PAINTS NO LIVE CONTROL FOR A HIDDEN-INFORMATION OFFERING** — and
/// paints one for every offering that is not. The verdict is read off `hidden_information()` per
/// key, so this tracks whatever the games declare rather than a frozen list of names.
///
/// It also demands the DIMMING BE EXPLAINED: a lock glyph with no sentence beside it is a mystery,
/// and a mystery reads as a broken bot, which is the same failure in a nicer costume.
#[test]
fn a_group_shelf_paints_no_live_control_for_a_hidden_information_offering() {
    let mut h = host();
    let group: i64 = -703;
    h.present_offerings_menu(group, None);

    let rows = shelf_rows(&h, group);
    assert!(
        !rows.is_empty(),
        "the group's shelf painted a keyboard at all — an empty one would pass every assertion \
         below for the wrong reason"
    );
    assert_eq!(
        rows.len(),
        h.list_advertised_offerings().len(),
        "a blocked offering is DIMMED, NOT FILTERED: a game missing from the menu reads as one \
         that does not exist, while a dimmed one teaches the constraint and points at the fix"
    );

    let mut declared_hidden = Vec::new();
    let mut live = Vec::new();
    for (label, callback) in &rows {
        let key = key_of(&h, callback);
        let hidden = h
            .hidden_information(&key)
            .expect("the shelf only paints registered keys");
        let dimmed = label.starts_with(LOCK_GLYPH);
        assert_eq!(
            dimmed,
            hidden,
            "`{key}` declares hidden_information() == {hidden} and its group-chat shelf row is \
             {}dimmed — the menu must agree with the declaration the OPEN gate reads, or a player \
             presses and is refused (label {label:?})",
            if dimmed { "" } else { "NOT " },
        );
        if hidden {
            declared_hidden.push(key);
        } else {
            live.push(key);
        }
    }

    // NON-VACUITY. If nothing on the shelf declared hidden information, every assertion above
    // would hold trivially and this file would certify nothing at all.
    assert!(
        !declared_hidden.is_empty(),
        "no shipped offering declares hidden_information(), so the dimming path was never \
         exercised — this test is vacuous and the shelf gate is unproven"
    );

    // ── The dimmed row must be EXPLAINED. A lock with no sentence beside it is a mystery, and a
    // mystery reads as a broken bot — the same failure in a nicer costume.
    let note = h
        .shelf_note(group, None)
        .expect("a group whose shelf withholds something carries the warning");
    let text = h
        .frontend()
        .transport()
        .sent_to(group)
        .last()
        .expect("the menu went out")
        .text
        .clone();
    assert!(
        text.contains(&note),
        "the /offerings message CARRIES the warning (not merely offers it via an API):\n{text}"
    );
    // Names are derived through the SAME helper the note uses, never re-typed here.
    let titles: std::collections::HashMap<String, String> = h
        .list_offerings()
        .into_iter()
        .map(|o| (o.key, o.title))
        .collect();
    for key in &declared_hidden {
        let name = dreggnet_offerings::shelf::headline(&titles[key]);
        assert!(
            note.contains(name),
            "the warning names the withheld `{name}`, so the player knows WHICH lock is which: \
             {note}"
        );
        assert!(
            note.contains(&format!("/open {key}")),
            "the warning names the exact DM gesture for `{key}` — a constraint without a route is \
             just a no: {note}"
        );
    }
    assert!(
        note.to_lowercase().contains("dm me"),
        "the warning says WHERE that gesture works: {note}"
    );
    // …and it names what DOES still play here, so a row of locks cannot read as a dead shelf. (If
    // `live` is empty this loop is empty — and that case, every shipped game withheld from every
    // group, is what `the_descent_is_not_hidden_information_and_stays_live_in_a_group` fails
    // loudly about rather than letting it pass quietly here.)
    for key in &live {
        let name = dreggnet_offerings::shelf::headline(&titles[key]);
        assert!(
            note.contains(name),
            "the warning names `{name}` as playable right here in the group: {note}"
        );
    }
    // The whole point of the constraint: nothing here leaked while explaining it.
    assert_chat_never_showed_private(&h, group);
}

/// **The other half: a DM offers all of them, live.** The gate is about WHO READS the surface, not
/// about withdrawing a game — so the single-reader chat where these games play properly must lose
/// nothing, and must carry no warning.
#[test]
fn a_dm_shelf_paints_every_shipped_offering_as_a_live_control() {
    let mut h = host();
    let dm: i64 = 704;
    h.present_offerings_menu(dm, None);

    let rows = shelf_rows(&h, dm);
    assert_eq!(
        rows.len(),
        h.list_advertised_offerings().len(),
        "the DM shelf is the whole ship list"
    );
    let mut declared_hidden = 0usize;
    for (label, callback) in &rows {
        let key = key_of(&h, callback);
        assert!(
            !label.starts_with(LOCK_GLYPH),
            "`{key}` is a LIVE control in a DM — one reader, so its own hidden state reaches \
             exactly the player it belongs to (label {label:?})"
        );
        if h.hidden_information(&key) == Some(true) {
            declared_hidden += 1;
        }
    }
    assert!(
        declared_hidden > 0,
        "non-vacuity: a DM shelf offering a hidden-information game live is the claim, and no \
         shipped offering declares one"
    );
    assert!(
        h.shelf_note(dm, None).is_none(),
        "a DM has nothing to warn about: {:?}",
        h.shelf_note(dm, None)
    );
}

/// **⚑ THE DESCENT STILL PLAYS IN A GROUP.** It is a solo crawl and declares nothing hidden (it
/// inherits `hidden_information()`'s `false` default), so the group's shelf must offer it LIVE and
/// the open must actually succeed there.
///
/// This fails loudly if the Descent ever starts declaring hidden information — deliberately. That
/// would mean NOTHING on the shelf plays in a group chat, which changes the whole story a bot's
/// home tells, and it should be a red test rather than a quietly locked menu.
#[test]
fn the_descent_is_not_hidden_information_and_stays_live_in_a_group() {
    // The Telegram catalog binds the Descent to the LIVE verified drand day and REFUSES to open
    // without one — so publish the pinned PUBLISHED round (a genuine BLS-verifiable reveal, and
    // exactly what the bot serves when the transport is down). Without this the open below fails
    // for a reason that has nothing to do with the audience rule under test.
    dreggnet_catalog::publish_pinned_descent_day().expect("the pinned published round verifies");
    let mut h = host();
    let group: i64 = -705;

    assert_eq!(
        h.hidden_information("descent"),
        Some(false),
        "THE DESCENT NOW DECLARES HIDDEN INFORMATION. It is the one shipped game a group chat \
         could host, so if this is intended then no shipped offering plays in a group at all — \
         which is a product decision about every group and every server, not a test to update."
    );

    h.present_offerings_menu(group, None);
    let descent_label = shelf_rows(&h, group)
        .into_iter()
        .find(|(_, callback)| key_of(&h, callback) == "descent")
        .map(|(label, _)| label)
        .expect("the Descent is on the shelf");
    assert!(
        !descent_label.starts_with(LOCK_GLYPH),
        "the Descent is a LIVE control in a group: {descent_label}"
    );

    // …and it really opens there. A live-looking button that refuses is the defect, whichever
    // direction it points.
    let sid = h
        .open("descent", group, None, ALICE)
        .expect("the Descent hosts in a group — it hides nothing per player");
    assert_eq!(
        h.active_offering(&sid),
        Some("descent"),
        "the group is playing the Descent"
    );
}

/// **⚑ THE REFUSAL SURVIVES THE DIMMING.** Dimmed is not removed: the row keeps its
/// `callback_data`, so a press — of the button as painted, of a stale keyboard, of a captured
/// callback — still reaches the same gate and is still refused. The menu became honest; the
/// protection did not move.
#[test]
fn pressing_the_dimmed_row_is_still_refused_by_the_open_gate() {
    let mut h = host();
    let group: i64 = -706;
    h.present_offerings_menu(group, None);

    let dimmed: Vec<(String, String)> = shelf_rows(&h, group)
        .into_iter()
        .filter(|(label, _)| label.starts_with(LOCK_GLYPH))
        .collect();
    assert!(
        !dimmed.is_empty(),
        "non-vacuity: the group shelf dimmed something to press"
    );
    for (label, callback) in dimmed {
        assert!(
            !callback.is_empty(),
            "the dimmed row is still a real pressable button ({label}) — Telegram has no inert \
             inline button, so the gate behind it is what makes the dim honest"
        );
        let key = key_of(&h, &callback);
        match h.press(CallbackQuery::press(group, ALICE, callback.clone())) {
            HostPress::OpenRefused { key: refused, why } => {
                assert_eq!(refused, key);
                assert!(
                    why.contains(&format!("/open {key}")),
                    "the refusal still carries the legible redirect: {why}"
                );
            }
            other => panic!(
                "pressing the dimmed `{key}` row must still hit the open gate, got {other:?} — \
                 the dimming is the WARNING, never the protection"
            ),
        }
    }
    assert_chat_never_showed_private(&h, group);
}

/// **`/help` is a shelf in prose, and it points at `/open <key>` in as many words.** In a group two
/// of those pointers are routes to a refusal, so the same derived warning rides along there. A DM's
/// `/help` is untouched.
#[test]
fn help_carries_the_shared_chat_warning_in_a_group_and_not_in_a_dm() {
    let mut h = host();
    let group: i64 = -707;
    let dm: i64 = 707;

    let (group_help, _) = route_text_decided(&mut h, group, None, ALICE, "/help");
    let group_help = group_help.expect("/help answers in a group");
    let note = h
        .shelf_note(group, None)
        .expect("a group has something to warn about");
    assert!(
        group_help.contains(&note),
        "a group's /help carries the shelf warning:\n{group_help}"
    );

    let (dm_help, _) = route_text_decided(&mut h, dm, None, ALICE, "/help");
    let dm_help = dm_help.expect("/help answers in a DM");
    assert_eq!(
        dm_help,
        dreggnet_telegram::commands::help_text(),
        "a DM's /help is the pure registry rendering — nothing is withheld there, so there is \
         nothing to warn about"
    );
    assert!(
        group_help.chars().count() <= dreggnet_telegram::api::TELEGRAM_TEXT_LIMIT,
        "the warned /help still fits one Telegram message ({} chars)",
        group_help.chars().count()
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
    // projected FOR her. The press is the one her keyboard actually offers (see `live_press`),
    // never a literal `("comp", 3)`.
    let offered = live_press(&h, dm);
    let press = h.press(CallbackQuery::press(dm, ALICE, offered.clone()));
    assert!(
        matches!(
            press,
            HostPress::Advanced {
                outcome: Outcome::Landed { .. },
                ..
            }
        ),
        "alice's opening press ({offered}) lands + claims seat A: {press:?}"
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
