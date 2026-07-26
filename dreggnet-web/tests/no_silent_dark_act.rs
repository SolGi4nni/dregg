//! **THE GATE ON SILENTLY DARK `/act` TESTS.**
//!
//! A `POST …/act` on a SPINED game key that carries no route authority is answered `409 invalid
//! game reference` BEFORE the executor. Whether a test notices is pure luck of assertion polarity:
//! `assert!(body.contains("Turn committed"))` goes red, `assert!(!body.contains(secret))` goes
//! GREEN having observed nothing. That is how a large part of this suite went dark the day the
//! game-session spine landed, and it is why the repair cannot be "fix the files" alone.
//!
//! Three legs, and each one can go red on its own:
//!
//! 1. **The positive control** — an UNGUARDED router really does refuse a bare act POST, and stamps
//!    the `x-dregg-refusal: missing-game-authority` header the tripwire keys on. It also asserts the
//!    BODY is player copy and carries none of the wire field names it used to be. (This leg used to
//!    key on four prose markers in the body; when the refusal audit made that body a styled player
//!    notice, keying on prose would have silently gone to always-false — see
//!    [`common::is_missing_authority_refusal`].)
//! 2. **The tripwire fires** — the same POST through [`common::guard`] PANICS instead of returning
//!    a body an assertion could skate over. (This test deliberately provokes one panic; the
//!    backtrace printed beneath it is the mechanism working, not a failure.)
//! 3. **Nothing escapes it** — every integration test in this directory that POSTs to an `…/act`
//!    route declares `mod common;`, so a new suite cannot reintroduce the class by hand-rolling
//!    its own bare-body helper.

use std::sync::Arc;

use axum::body::Body;
use axum::http::{Request, StatusCode};
use dreggnet_web::{CatalogState, catalog_router};
use tower::ServiceExt; // oneshot

mod common;

/// A spined key (`game_spine::game_kind("dungeon")` is `Some`) — the refusal below is the SPINE's,
/// not a routing miss.
const SPINED_ACT: &str = "/offerings/dungeon/session/tripwire-control/act";

fn bare_act() -> Request<Body> {
    Request::builder()
        .method("POST")
        .uri(SPINED_ACT)
        .header("content-type", "application/x-www-form-urlencoded")
        .header("cookie", "dregg_user=tripwire")
        .body(Body::from("turn=choose&arg=0"))
        .unwrap()
}

/// **POSITIVE CONTROL.** The class is real and the signal the tripwire keys on is one the server
/// really emits. Without this leg the guard could key on something the server never sends and report a
/// clean suite forever.
///
/// ⚑ The signal is now the `x-dregg-refusal` HEADER, not four prose markers in the body — see
/// [`common::is_missing_authority_refusal`] for why the move is the repair. This leg therefore also
/// asserts the second half of that repair: **the body is player copy**, and carries none of the wire
/// vocabulary it used to be.
#[tokio::test]
async fn a_bare_act_post_really_is_refused_for_a_missing_authority() {
    let app = catalog_router(Arc::new(CatalogState::new()));
    let response = app.oneshot(bare_act()).await.unwrap();
    let status = response.status();
    let headers = response.headers().clone();
    let body = String::from_utf8_lossy(
        &axum::body::to_bytes(response.into_body(), usize::MAX)
            .await
            .unwrap(),
    )
    .to_string();

    assert_eq!(
        status,
        StatusCode::CONFLICT,
        "a bare `turn=&arg=` on a spined key must be refused before the executor: {body}"
    );
    assert!(
        common::is_missing_authority_refusal(status, &headers),
        "the tripwire keys on the server's `{}` header, and it is absent or changed.\n  \
         headers: {headers:?}\n  body: {body}\n  until this is repaired every guarded suite is blind.",
        dreggnet_web::REFUSAL_KIND_HEADER
    );
    // ⚑ AND THE BODY IS COPY. A bare POST used to be answered with the form field's own name — an
    // unstyled `missing or malformed game_host_incarnation` with no page and no way back. A player
    // cannot act on a wire field name, so it is not in the sentence any more; it is in the log.
    for wire in [
        "game_host_incarnation",
        "game_session_generation",
        "game_expected_pre_head",
        "game_form_token",
        "invalid game reference",
    ] {
        assert!(
            !body.contains(wire),
            "the refusal body must not name `{wire}` to a player: {body}"
        );
    }
    assert!(
        body.contains("This page is out of date") && body.contains("Nothing was played"),
        "the styled stale-page notice must be what a reader gets: {body}"
    );
    assert!(
        body.contains("notice refused") && body.contains("/offerings"),
        "…with the house refusal styling and a way back: {body}"
    );
}

/// **THE TRIPWIRE FIRES.** The same request through [`common::guard`] kills the caller instead of
/// handing back a body that a negative assertion would sail straight past.
#[tokio::test]
async fn the_guard_panics_instead_of_returning_a_dark_409() {
    let app = common::guard(catalog_router(Arc::new(CatalogState::new())));
    let outcome = tokio::spawn(async move {
        let response = app.oneshot(bare_act()).await.unwrap();
        let _ = axum::body::to_bytes(response.into_body(), usize::MAX).await;
    })
    .await;

    let error = outcome.expect_err(
        "the guarded router returned a dark 409 instead of tripping — `common::guard` is not \
         actually gating, and every suite that relies on it is back to vacuous green",
    );
    assert!(error.is_panic(), "the tripwire must panic, not cancel");
}

/// **NOTHING ESCAPES IT.** Every test in this directory that POSTs to an `…/act` route routes
/// through `common`, so its router is guarded and its bodies carry the authority. A new suite that
/// hand-rolls a bare `turn=&arg=` helper fails HERE, at review time, instead of going dark for a
/// month.
#[test]
fn every_act_posting_test_routes_through_the_shared_helper() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests");
    let mut scanned = 0usize;
    let mut act_posting = Vec::new();
    let mut offenders = Vec::new();

    for entry in std::fs::read_dir(&dir).expect("the tests directory is readable") {
        let path = entry.expect("a readable directory entry").path();
        if path.extension().and_then(|e| e.to_str()) != Some("rs") {
            continue;
        }
        let name = path
            .file_name()
            .and_then(|n| n.to_str())
            .expect("a UTF-8 test file name")
            .to_string();
        if name == "no_silent_dark_act.rs" {
            continue;
        }
        let source = std::fs::read_to_string(&path).expect("a readable test file");
        scanned += 1;

        // Code lines only: a doc comment naming the route is prose, not a request.
        let posts_an_act = source
            .lines()
            .filter(|line| !line.trim_start().starts_with("//"))
            .any(|line| mentions_act_route(line));
        if !posts_an_act {
            continue;
        }
        act_posting.push(name.clone());
        if !source.lines().any(|line| line.trim() == "mod common;") {
            offenders.push(name);
        }
    }

    assert!(
        scanned > 20,
        "the scan found only {scanned} test files — it is looking in the wrong place ({}), and a \
         gate that inspects nothing is not a gate",
        dir.display()
    );
    assert!(
        act_posting.len() >= 20,
        "only {} act-posting suites matched ({act_posting:?}) — the matcher regressed; the real \
         population is the whole games/catalog surface",
        act_posting.len()
    );
    assert!(
        offenders.is_empty(),
        "these suites POST to an `…/act` route without going through `tests/common/mod.rs`:\n  \
         {offenders:?}\nAdd `mod common;`, build the router with `common::guard(...)`, and post \
         through `common::post_act` / `common::act_body`. A bare `turn=&arg=` on a spined game key \
         is answered `409 invalid game reference` and every assertion after it is vacuous."
    );
}

/// Does this line reference an act route (`…/act`), excluding the independently gated
/// `…/act-signed` seam?
fn mentions_act_route(line: &str) -> bool {
    let mut rest = line;
    while let Some(at) = rest.find("/act") {
        let tail = &rest[at + "/act".len()..];
        if !tail.starts_with("-signed") {
            return true;
        }
        rest = tail;
    }
    false
}
