//! **THE PROGRESSIVE-ENHANCEMENT FRAGMENT PATH, DRIVEN.**
//!
//! The affordance play loop used to be four full page reloads (select → commit → reveal → resolve,
//! each a `<form>` POST that navigated the whole document). This pins the LIVE path added on top —
//! server-authoritative, no-JS-safe:
//!
//! - a POST-act with `X-Fragment: 1` returns JUST the swappable surface FRAGMENT — no `<html>`/
//!   `<head>`/chrome — containing the re-rendered board + the notice;
//! - the SAME POST *without* the header returns the full page, unchanged (the no-JS fallback);
//! - a WHOLE automatafl turn drives through the fragment path (`select → commit ×2 → reveal ×2 →
//!   resolve`), the board fragment updating each step, and `verify` holds;
//! - the fragment is embedded VERBATIM inside the full page (ONE render path: no-JS and JS render
//!   the identical surface);
//! - the inline progressive-enhancement script is present in the page shell.
//!
//! No real network (axum `ServiceExt::oneshot`); the executor stays the sole referee.

use std::sync::Arc;

use axum::body::Body;
use axum::http::{Request, StatusCode};
use dreggnet_web::{CatalogState, catalog_router};
use tower::ServiceExt; // oneshot

/// A GET, optionally asking for JUST the fragment (`X-Fragment: 1`).
async fn get(app: &axum::Router, uri: &str, fragment: bool) -> (StatusCode, String) {
    let mut b = Request::builder().uri(uri);
    if fragment {
        b = b.header("x-fragment", "1");
    }
    let resp = app
        .clone()
        .oneshot(b.body(Body::empty()).unwrap())
        .await
        .unwrap();
    let status = resp.status();
    let bytes = axum::body::to_bytes(resp.into_body(), usize::MAX)
        .await
        .unwrap();
    (status, String::from_utf8(bytes.to_vec()).unwrap())
}

/// POST a `{turn, arg}` affordance as web user `user`, optionally as a progressive-enhancement
/// `fetch` (`X-Fragment: 1`) rather than a classic form navigation.
async fn post(
    app: &axum::Router,
    uri: &str,
    turn: &str,
    arg: i64,
    user: &str,
    fragment: bool,
) -> (StatusCode, String) {
    let mut b = Request::builder()
        .method("POST")
        .uri(uri)
        .header("content-type", "application/x-www-form-urlencoded")
        .header("cookie", format!("dregg_user={user}"));
    if fragment {
        b = b.header("x-fragment", "1");
    }
    let resp = app
        .clone()
        .oneshot(
            b.body(Body::from(format!("turn={turn}&arg={arg}")))
                .unwrap(),
        )
        .await
        .unwrap();
    let status = resp.status();
    let bytes = axum::body::to_bytes(resp.into_body(), usize::MAX)
        .await
        .unwrap();
    (status, String::from_utf8(bytes.to_vec()).unwrap())
}

fn app() -> axum::Router {
    catalog_router(Arc::new(CatalogState::new()))
}

/// The 5×5 board index of `(x, y)`.
fn idx(x: i64, y: i64) -> i64 {
    y * 5 + x
}

/// A fragment response is BARE surface HTML — no document, no head, no shell.
fn assert_is_fragment(body: &str) {
    assert!(
        !body.contains("<html") && !body.contains("<!doctype") && !body.contains("<head"),
        "the X-Fragment response is a bare fragment, not a document: {body}"
    );
    assert!(
        !body.contains("<script"),
        "the fragment carries no page chrome (the script lives in the shell): {body}"
    );
}

/// A full page IS a document — the shell, the head, the inline enhancement script.
fn assert_is_full_page(body: &str) {
    assert!(
        body.contains("<!doctype html>")
            && body.contains("<html lang=\"en\">")
            && body.contains("<head>"),
        "the no-header response is the full page: {}",
        &body[..body.len().min(200)]
    );
}

/// **The fragment contract:** a POST-act with `X-Fragment: 1` returns ONLY the surface fragment
/// (no document), while the same POST without the header returns the full page (the no-JS path).
#[tokio::test]
async fn x_fragment_returns_only_the_surface_full_page_otherwise() {
    let app = app();
    let base = "/offerings/automatafl/session/frag-1";
    let _ = get(&app, base, false).await; // open the session

    // ── With the header: a bare fragment carrying the re-rendered board + the outcome notice.
    let (status, frag) = post(
        &app,
        &format!("{base}/act"),
        "select",
        idx(1, 1),
        "alice",
        true,
    )
    .await;
    assert_eq!(status, StatusCode::OK);
    assert_is_fragment(&frag);
    assert!(
        frag.contains("coordgrid"),
        "the fragment carries the board: {frag}"
    );
    assert!(
        frag.contains("Turn committed"),
        "the fragment carries the outcome notice: {frag}"
    );
    assert!(
        frag.contains("chain re-verified by replay"),
        "the fragment carries the live receipt line: {frag}"
    );

    // ── Without the header: the classic full page (unchanged no-JS behaviour).
    let base2 = "/offerings/automatafl/session/frag-2";
    let _ = get(&app, base2, false).await;
    let (status, page) = post(
        &app,
        &format!("{base2}/act"),
        "select",
        idx(1, 1),
        "alice",
        false,
    )
    .await;
    assert_eq!(status, StatusCode::OK);
    assert_is_full_page(&page);
    assert!(
        page.contains("coordgrid"),
        "the full page carries the board"
    );
    assert!(
        page.contains("Turn committed"),
        "the full page carries the notice"
    );
}

/// **ONE render path:** the fragment is embedded VERBATIM inside the full page — so no-JS (full
/// page) and JS (swapped fragment) render the identical surface. Proven on an unmutated GET (a GET
/// never advances state, so the full-page and fragment renders are of the same state + viewer).
#[tokio::test]
async fn the_fragment_is_embedded_identically_in_the_full_page() {
    let app = app();
    let base = "/offerings/automatafl/session/embed-1";

    let (_, full) = get(&app, base, false).await;
    let (_, frag) = get(&app, base, true).await;

    assert_is_fragment(&frag);
    assert_is_full_page(&full);
    assert!(
        full.contains(&frag),
        "the full page embeds the fragment byte-for-byte (one render path).\n--- fragment ---\n{frag}\n--- full (head) ---\n{}",
        &full[..full.len().min(400)]
    );
    // And the region the script swaps is exactly the one wrapping that fragment.
    assert!(
        full.contains("id=\"live-surface\""),
        "the full page carries the #live-surface swap region"
    );
}

/// **A whole automatafl turn plays through the FRAGMENT path** — the four-reload loop is now
/// four in-place swaps: `select → commit ×2 → reveal ×2 → resolve`, each POST returning an updated
/// board fragment (never a whole document), and the committed chain re-verifies.
#[tokio::test]
async fn a_full_turn_advances_through_the_fragment_path() {
    let app = app();
    let base = "/offerings/automatafl/session/frag-turn";
    let act = format!("{base}/act");
    let _ = get(&app, base, false).await;

    // Each step: a bare fragment, the board present, the turn committed.
    let step = |turn: &'static str, arg: i64, user: &'static str| {
        let app = app.clone();
        let act = act.clone();
        async move { post(&app, &act, turn, arg, user, true).await }
    };

    for (turn, arg, user) in [
        ("select", idx(1, 1), "alice"),
        ("commit", idx(1, 4), "alice"),
        ("select", idx(3, 3), "bob"),
        ("commit", idx(3, 0), "bob"),
        ("reveal", 0, "alice"),
        ("reveal", 0, "bob"),
    ] {
        let (status, frag) = step(turn, arg, user).await;
        assert_eq!(status, StatusCode::OK, "{turn} ok");
        assert_is_fragment(&frag);
        assert!(
            frag.contains("coordgrid"),
            "{turn} re-paints the board fragment: {frag}"
        );
        assert!(
            frag.contains("Turn committed"),
            "{turn} lands a real turn: {frag}"
        );
    }

    // The resolution: the board fragment shows the turn counter advanced.
    let (status, frag) = post(&app, &act, "resolve", 0, "alice", true).await;
    assert_eq!(status, StatusCode::OK);
    assert_is_fragment(&frag);
    assert!(
        frag.contains("Automatafl — turn 1"),
        "the resolved turn counter advanced, via the fragment path: {frag}"
    );
    assert!(
        frag.contains("coordgrid"),
        "the resolved board re-paints in the fragment"
    );

    // The whole committed chain re-verifies by the offering's own proof.
    let (status, body) = get(&app, &format!("{base}/verify"), false).await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        body.contains("\"verified\":true"),
        "the fragment-driven turn verifies: {body}"
    );
}

/// The inline progressive-enhancement script is present in the page shell (and only there) — the
/// one client JS that turns the form POSTs into in-place fragment swaps.
#[tokio::test]
async fn the_enhancement_script_is_present_in_the_shell() {
    let app = app();
    let (_, page) = get(&app, "/offerings/automatafl/session/script-1", false).await;
    assert!(
        page.contains("<script>"),
        "the shell carries an inline script"
    );
    assert!(
        page.contains("X-Fragment") && page.contains("live-surface"),
        "the script drives the fragment swap into the live region"
    );
    assert!(
        page.contains("addEventListener(\"submit\""),
        "the script intercepts affordance form submits"
    );
    // The no-JS floor: the plain POST form is still there (the script only enhances it).
    assert!(
        page.contains("<form class=\"cell") && page.contains("method=\"post\""),
        "the server-rendered form POST (the fallback) is intact"
    );
}
