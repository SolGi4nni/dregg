//! # ⚑ THE REFUSAL-COPY GATE — every player-visible "no" the SHIPPED games can say, scanned.
//!
//! ## What this generalises
//!
//! `dreggnet_web::identity_link` already enforces its own refusal copy by hand — three assertions
//! about one module's strings ("the refusal must not blame the player", "never a bare 'invalid'", "a
//! refusal must say nothing happened"). They are the right rules and they caught nothing anywhere
//! else, because they were written as sentences about one page rather than as a *predicate over
//! player-facing text*. An audit of the whole product then found nine failure modes with one root
//! cause: a `Display`/`Debug` written for a log line leaking, unfiltered, into a player-facing string.
//!
//! [`dreggnet_offerings::refusal::audit_player_text`] is that predicate, and this file points it at
//! **strings the shipped surfaces actually produce**, driven through the real HTTP act path:
//!
//! - a raw hex run (a key, a root, a session id) — unreadable, and never the next action;
//! - a `Debug` dump (`Secret { card: 9 }`, `GameSessionBinding { … }`);
//! - a `snake_case` / `SCREAMING_SNAKE` symbol offered as the fix (`game_host_incarnation`,
//!   `DEVNET_API_TOKEN`, `dregg_deleg_admit`) — a player cannot set an env var or call a function;
//! - a system-component name (`executor`, `world-cell`, `teeth`, `oracle`, "bot build");
//! - **no statement of whether anything was lost** — the rule the good refusals in this house never
//!   break and the bad ones never keep;
//! - **no next action** — a refusal with no way forward reads as broken rather than as refused.
//!
//! ## Scope, stated plainly
//!
//! ⚑ **THE WHOLE SHIP LIST** — [`dreggnet_catalog::SHIPPED_KEYS`], today the Descent, Automatafl and
//! Tug — plus the stale-page response every spined act route shares, plus the entire shared refusal
//! vocabulary. Driven from the ship-list constant, so a newly shipped game inherits the gate.
//!
//! What it does NOT cover, named rather than papered over:
//!
//! - **The mounted-but-unshipped keys** (`bazaar`, `dark-pool`, `council`, `market`, `private-raid`,
//!   the eight RPG surfaces). They are reachable by URL and their refusal copy is unaudited; landing
//!   a gate whose reds nobody has read is landing a gate somebody switches off. Widening it one key
//!   at a time, reading each red, is the follow-up.
//! - **Discord's ~200 embeds and Telegram's acks.** Both surfaces now route the conditions this audit
//!   found through shared helpers (`dreggnet_offerings::refusal`,
//!   `discord_bot::embeds::{stale_control_text, store_unavailable_embed}`) whose copy IS gated here —
//!   but a bespoke string typed at a NEW Discord call site is not yet caught.
//!
//! ## Why the scanner takes two switches
//!
//! An offering's `Outcome::Refused(why)` is a CLAUSE, not a message: the host wraps it ("Refused:
//! {why} (nothing committed — anti-ghost)"), and that wrapper — copy the audit VERIFIED as good —
//! states the loss and deliberately gives no next action (the live board is still on screen). So a
//! rendered game refusal is scanned for banned shapes + a loss statement, while the shared vocabulary
//! and the stale-page response, where the audit found the next action missing, are scanned in full.
//! See [`gate`] and [`gate_shapes_and_loss`].

use std::sync::Arc;

use axum::Router;
use axum::body::Body;
use axum::http::{Request, StatusCode};
use dreggnet_offerings::refusal::{
    self, BannedShape, COMMIT_FAILED_NOTHING_CHANGED, STORE_FAILED_NOTHING_CHANGED,
    audit_player_text, belongs_to_another_player, stale_control, stale_control_refresh,
};
use dreggnet_web::{CatalogState, catalog_router};
use tower::ServiceExt;

mod common;

/// The catalog router, with a verified Descent day published.
///
/// ⚑ **THE DAY IS A PRECONDITION OF THE SHIP LIST, not a fixture convenience.** `CatalogState::new`
/// builds its host through `dreggnet_catalog::CatalogConfig::live`, which binds a run's banked-relic
/// provenance to the CURRENT verified beacon day and REFUSES to open a Descent until one is
/// published. `descent` is the first entry in `dreggnet_catalog::SHIPPED_KEYS`, so without this the
/// two legs below never reach a Descent at all: the open is refused and the gate scans the REFUSAL
/// OF THE OPEN instead of the refusal copy it exists to audit. The serving binary publishes the day
/// at boot (`arm_todays_descent_day`, over the network); a test process publishes the pinned,
/// BLS-verifiable reveal, exactly as every other Descent web suite here does (`descent_door`,
/// `game_session_coherence`, `catalog_flow_harness`, `descent_campaign_catalog`).
fn app() -> Router {
    dreggnet_catalog::publish_pinned_descent_day().expect("the pinned published round verifies");
    common::guard(catalog_router(Arc::new(CatalogState::new())))
}

/// The text of the page's own `.notice` banner — what the reader is told just happened, tags out and
/// HTML entities back. `None` when the page carries no notice (a plain GET).
fn notice_text(html: &str) -> Option<String> {
    let (_, after) = html.split_once("class=\"notice")?;
    let (_, inner) = after.split_once('>')?;
    let (text, _) = inner.split_once("</div>")?;
    Some(unescape(&strip_tags(text)))
}

fn strip_tags(html: &str) -> String {
    let mut out = String::new();
    let mut in_tag = false;
    for c in html.chars() {
        match c {
            '<' => in_tag = true,
            '>' => {
                in_tag = false;
                out.push(' ');
            }
            c if !in_tag => out.push(c),
            _ => {}
        }
    }
    out.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// Undo `dreggnet_web`'s `esc` — the scanner judges the SENTENCE, not its transport encoding.
fn unescape(s: &str) -> String {
    s.replace("&quot;", "\"")
        .replace("&lt;", "<")
        .replace("&gt;", ">")
        .replace("&amp;", "&")
}

/// Scan one rendered notice under the FULL rules — banned shapes, a next action, AND a statement of
/// what was lost — and fail loudly, naming every violation.
#[track_caller]
fn gate(what: &str, text: &str) {
    report(what, text, audit_player_text(text, true, true));
}

/// ⚑ **The CALIBRATED rules for a notice wrapped by the anti-ghost family.**
///
/// A game refusal reaches the reader as `"Refused: {why} (nothing committed — anti-ghost)."` — copy the
/// audit explicitly VERIFIED as good and told this pass not to touch. It states the loss ("nothing
/// committed") and, deliberately, gives no next action: the board is still on screen with its live
/// controls, so "reload" would be wrong and "try again" would be a lie. Demanding a next action here
/// would red on good copy, which is how a linter gets switched off.
///
/// So this leg enforces the two rules that are MECHANICAL and unconditional — no banned shape, and say
/// what was lost — and the next-action rule is enforced where the audit found it missing: the
/// stale-page response and the shared vocabulary, both gated in full above.
#[track_caller]
fn gate_shapes_and_loss(what: &str, text: &str) {
    report(what, text, audit_player_text(text, false, true));
}

#[track_caller]
fn report(what: &str, text: &str, violations: Vec<BannedShape>) {
    assert!(
        violations.is_empty(),
        "{what} is not in house style.\n  said: {text}\n  violations:\n{}",
        violations
            .iter()
            .map(|v| format!("    - {v}\n"))
            .collect::<String>()
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// 1. THE SHARED VOCABULARY — the copy every surface now says "no" with.
// ─────────────────────────────────────────────────────────────────────────────

/// Every sentence in [`dreggnet_offerings::refusal`], plus the per-surface `next_step` clauses the
/// shipped frontends pass it. A helper that cannot pass its own gate is worse than the strings it
/// replaced, because it spreads.
#[test]
fn the_shared_refusal_vocabulary_passes_its_own_gate() {
    let mut checked = 0usize;
    let sentences = [
        stale_control_refresh(),
        // The web's clause, verbatim from the server.
        stale_control(dreggnet_web::RELOAD_NEXT_STEP),
        // Telegram's, and Discord's.
        stale_control("Send /offerings for a fresh menu, or /cancel to clear this chat."),
        stale_control(
            "Use the buttons on the newest message for this, or run the command again to get a \
             fresh one.",
        ),
        // The post-restart clause — the strongest one any surface has (it has already reposted the
        // live sessions rather than telling the reader to go find one).
        stale_control(
            "I have reposted your live session(s) below: dungeon. Press there, or /cancel to start \
             clean.",
        ),
        belongs_to_another_player("run"),
        belongs_to_another_player("Descent"),
        belongs_to_another_player("traversal"),
        belongs_to_another_player("errand"),
        belongs_to_another_player("raid"),
        belongs_to_another_player("raid's proof upload"),
        belongs_to_another_player("session"),
        COMMIT_FAILED_NOTHING_CHANGED.to_string(),
        STORE_FAILED_NOTHING_CHANGED.to_string(),
    ];
    for sentence in &sentences {
        gate("a shared refusal sentence", sentence);
        checked += 1;
    }
    assert_eq!(checked, sentences.len());

    // ⚑ AND THE GATE IS NOT VACUOUS. Every string the audit actually found must be RED — otherwise
    // this file is a linter that only ever sees its own good examples, which is the "documented ≠
    // detected" failure in gate form.
    for leak in [
        "method `comp` does not name decision 3 (Secret { card: 9 }, which dispatches under `secret`)",
        "missing or malformed game_host_incarnation",
        "under-gated choice refused: method `select` did not lower fully to executor teeth",
        "world-cell turn refused: the purse is empty",
        "this Descent is bound to \
         3b1f0c9d8e7a6b5c4d3e2f1a0b9c8d7e6f5a4b3c2d1e0f9a8b7c6d5e4f3a2b1c; \
         9a8b7c6d5e4f3a2b1c0d9e8f7a6b5c4d3e2f1a0b9c8d7e6f5a4b3c2d1e0f9a8b cannot move it",
        "turn refused fail-closed — the verified admission oracle (dregg_deleg_admit / \
         Dregg2.Apps.DelegAdmit.delegAdmit) reached NO VERDICT: absent",
        "This governance control is not recognized by this bot build.",
        "Not authorized (HTTP 403). Set `DEVNET_API_TOKEN` for the bot.",
    ] {
        assert!(
            !audit_player_text(leak, true, true).is_empty(),
            "the gate must go RED on a string the audit found, or it is checking nothing: {leak}"
        );
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// 2. THE SHIPPED SURFACES — strings the live server actually renders.
// ─────────────────────────────────────────────────────────────────────────────

/// ⚑ **THE STALE-PAGE RESPONSE, on the real turn handler for every spined game.** A `POST …/act`
/// whose route authority does not resolve used to be answered `(409, error.to_string())` — an
/// unstyled body carrying the form's own wire field names, with no page, no backlink, and nothing
/// telling the reader their move had not landed. Three sites in `lib.rs` and six more across the
/// Discord-activity and Telegram-mini-app twins, all now one wrapper.
///
/// Driven UNGUARDED on purpose: the dark-act tripwire exists to kill exactly this request in an
/// ordinary suite, and here the request IS the subject.
#[tokio::test]
async fn the_stale_page_response_is_in_house_style() {
    let app = catalog_router(Arc::new(CatalogState::new()));
    let response = app
        .oneshot(
            Request::builder()
                .method("POST")
                .uri("/offerings/dungeon/session/copy-gate/act")
                .header("content-type", "application/x-www-form-urlencoded")
                .header("cookie", "dregg_user=copy-gate")
                .body(Body::from("turn=choose&arg=0"))
                .unwrap(),
        )
        .await
        .expect("router responds");
    let status = response.status();
    let body = String::from_utf8_lossy(
        &axum::body::to_bytes(response.into_body(), usize::MAX)
            .await
            .unwrap(),
    )
    .to_string();
    assert_eq!(status, StatusCode::CONFLICT, "{body}");

    let notice = notice_text(&body).expect("the refusal is a styled notice, not a bare body");
    gate("the stale-page refusal", &notice);
    // The two things the bare body had neither of.
    assert!(
        body.contains("notice refused"),
        "a refusal wears the house refusal styling: {body}"
    );
    assert!(
        body.contains("class=\"backlink\""),
        "a refusal gives a way back: {body}"
    );
}

/// ⚑ **THE SHIP LIST'S unoffered-control refusal — every key we put in front of a stranger.** One
/// deliberately-unoffered `{turn, arg}` per shipped key, presented WITH the route authority its own
/// page stamped (so the refusal under test is the affordance gate's, not the spine's), and the
/// rendered notice scanned.
///
/// Driven from [`dreggnet_catalog::SHIPPED_KEYS`] rather than a literal, so **a newly shipped game
/// inherits the gate** — its refusal copy has to be in house style to go on the shelf, which is the
/// right default and the opposite of how this class spread.
///
/// This is the arm that would have caught tug's `{decision:?}` dump and the web's two next-step-less
/// dead ends.
#[tokio::test]
async fn every_shipped_game_refuses_an_unoffered_control_in_house_style() {
    let app = app();
    let mut scanned = 0usize;
    for key in dreggnet_catalog::SHIPPED_KEYS {
        let base = format!("/offerings/{key}/session/copy-gate-{key}");
        // Open the session so the surface (and its route authority) exists.
        let (status, page) =
            common::get_with_cookie(&app, &base, Some("dregg_user=copy-gate")).await;
        assert_eq!(
            status,
            StatusCode::OK,
            "`{key}` is on the ship list, so an ad-hoc session of it must open: {page}"
        );
        let (status, body) = common::post_act(
            &app,
            &format!("{base}/act"),
            "no-such-affordance-copy-gate",
            0,
            "copy-gate",
        )
        .await;
        assert_eq!(status, StatusCode::OK, "{key}: {body}");
        let Some(notice) = notice_text(&body) else {
            panic!("{key}: a refused act must render a notice saying so: {body}");
        };
        // The subject is a REFUSAL. A landed notice carries a 64-character receipt id by design, so
        // scanning one would red on the receipt grammar rather than on any copy — and would mean the
        // unoffered control had been ADMITTED, which is a far worse bug than bad copy.
        assert!(
            notice.starts_with("Refused"),
            "{key}: an unoffered control must be refused, not admitted: {notice}"
        );
        gate_shapes_and_loss(&format!("`{key}`'s unoffered-control refusal"), &notice);
        scanned += 1;
    }
    assert_eq!(
        scanned,
        dreggnet_catalog::SHIPPED_KEYS.len(),
        "the gate must reach every shipped game; a gate that inspects nothing is not a gate"
    );
}

/// ⚑ **THE WRONG-PLAYER REFUSAL on the Descent**, driven as a second browser identity against a run
/// the first one bound. This is the condition that threw **two 64-character Ed25519 keys** at a
/// reader; the gate's hex rule is what makes the repair non-cosmetic.
#[tokio::test]
async fn the_descent_wrong_player_refusal_names_no_key() {
    let app = app();
    let base = "/offerings/descent/session/copy-gate-owner";
    let (status, _) = common::get_with_cookie(&app, base, Some("dregg_user=alice")).await;
    assert_eq!(status, StatusCode::OK);

    // Alice's first real move BINDS the run to her identity.
    let (status, landed) =
        common::post_act(&app, &format!("{base}/act"), "delve", 0, "alice").await;
    assert_eq!(status, StatusCode::OK, "{landed}");
    assert!(
        landed.contains("Turn committed") || landed.contains("floor"),
        "alice's delve must actually land, or the refusal below is about nothing: {landed}"
    );

    // Bob presses the same control. The run is not his.
    let (status, refused) = common::post_act(&app, &format!("{base}/act"), "delve", 0, "bob").await;
    assert_eq!(status, StatusCode::OK, "{refused}");
    let notice = notice_text(&refused).expect("a notice says what happened");
    assert!(
        notice.contains("belongs to a different player"),
        "the shared wrong-player sentence must be what bob reads: {notice}"
    );
    // The wrong-player sentence carries its OWN next action ("switch back to that account"), so this
    // one is gated in full even though it arrives inside the anti-ghost wrapper.
    gate("the Descent's wrong-player refusal", &notice);
    // The gate's hex rule, spelled out at the site it was written for.
    assert!(
        !audit_player_text(&notice, false, false)
            .iter()
            .any(|v| matches!(v, BannedShape::RawHexRun { .. })),
        "neither key may appear: {notice}"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// 3. THE HOUSE STYLE'S OWN EXEMPLARS — the three hand-written assertions, generalised.
// ─────────────────────────────────────────────────────────────────────────────

/// The `identity_link` refusals that the house style was FIRST written down for must pass the
/// generalised predicate too. If the exemplar fails its own generalisation, the generalisation is
/// wrong — this is the calibration leg.
#[test]
fn the_exemplar_pages_pass_the_generalised_gate() {
    // The scanner is deliberately not run over WHOLE pages (a page carries CSS, script and hex ids
    // that are not refusal copy), so the exemplar is checked at the granularity it is written at: the
    // shared sentences it composes with. What this leg pins is that the predicate ACCEPTS the voice
    // the exemplar established — "name the cause, say what was lost, give one next action" — rather
    // than being tuned so tightly to the new copy that only the new copy can pass.
    for exemplar in [
        "That code was not issued by this deployment, so nothing was linked. Ask the bot for a fresh \
         code with /link and try again.",
        "That code has already been used, so nothing was linked. Ask the bot for a fresh code with \
         /link.",
        "This deployment cannot prove a link at all: no such secret is configured on the server. \
         Nothing was changed — an operator setting is missing, and the server log names it.",
    ] {
        gate("an exemplar refusal", exemplar);
    }
    // …and the shapes the exemplar's own three tests were written to forbid are still forbidden.
    assert!(
        audit_player_text("invalid", true, true).contains(&BannedShape::NoNextAction),
        "a bare 'invalid' must still fail"
    );
    assert!(
        audit_player_text(
            "That code is wrong. Ask for a fresh one with /link.",
            true,
            true
        )
        .contains(&BannedShape::NoLossStatement),
        "a refusal that does not say whether anything happened must still fail"
    );
}

/// A guard on the guard: the module path this file scans through is the one the surfaces call, so a
/// future rename cannot leave this suite testing a copy of the vocabulary nobody ships.
#[test]
fn the_gate_scans_the_vocabulary_the_surfaces_actually_call() {
    assert_eq!(
        refusal::stale_control_refresh(),
        refusal::stale_control("Refresh the game to see the moves it offers now.")
    );
    assert!(
        refusal::COMMIT_FAILED_NOTHING_CHANGED.contains("nothing was changed"),
        "the commit-failure sentence must state the loss: {}",
        refusal::COMMIT_FAILED_NOTHING_CHANGED
    );
    assert!(
        refusal::STORE_FAILED_NOTHING_CHANGED.contains("nothing was changed"),
        "the store-failure sentence must state the loss: {}",
        refusal::STORE_FAILED_NOTHING_CHANGED
    );
}
