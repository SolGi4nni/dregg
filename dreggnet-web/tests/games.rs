//! **BOTH PORTFOLIO GAMES, DRIVEN THROUGH THE WEB CATALOG.**
//!
//! `catalog.rs` proved the three heterogeneous offerings (dungeon / council / market) play in the
//! browser. This proves the two GAMES do — with no real network (axum `ServiceExt::oneshot`):
//!
//! - `GET /offerings` lists **tug** and **automatafl** beside the rest;
//! - **automatafl** opens, paints its board as a clickable `CoordGrid` (a real POST button per
//!   affordance-bearing square), and a full simultaneous turn plays through the browser:
//!   `select` → `commit` (both seats) → `reveal` (both) → `resolve` — each POST a real landed turn,
//!   the board visibly moving; an ILLEGAL move (a diagonal) is REFUSED and commits nothing;
//! - **tug** opens and a real play LANDS for a browser user (the seat-claiming adapter), while a
//!   third browser user is refused as a spectator;
//! - `verify` holds for both committed chains.

use std::sync::Arc;

use axum::body::Body;
use axum::http::{Request, StatusCode};
use dreggnet_web::{CatalogState, catalog_router};
use tower::ServiceExt; // oneshot

async fn get(app: &axum::Router, uri: &str) -> (StatusCode, String) {
    let resp = app
        .clone()
        .oneshot(Request::builder().uri(uri).body(Body::empty()).unwrap())
        .await
        .unwrap();
    let status = resp.status();
    let bytes = axum::body::to_bytes(resp.into_body(), usize::MAX)
        .await
        .unwrap();
    (status, String::from_utf8(bytes.to_vec()).unwrap())
}

/// POST a `{turn, arg}` affordance form as web user `user` (a `dregg_user` cookie).
async fn post(
    app: &axum::Router,
    uri: &str,
    turn: &str,
    arg: i64,
    user: &str,
) -> (StatusCode, String) {
    let resp = app
        .clone()
        .oneshot(
            Request::builder()
                .method("POST")
                .uri(uri)
                .header("content-type", "application/x-www-form-urlencoded")
                .header("cookie", format!("dregg_user={user}"))
                .body(Body::from(format!("turn={turn}&arg={arg}")))
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

/// BOTH games appear in the catalog, each with a play link.
#[tokio::test]
async fn the_catalog_lists_both_portfolio_games() {
    let app = app();
    let (status, body) = get(&app, "/offerings").await;
    assert_eq!(status, StatusCode::OK);
    for key in ["tug", "automatafl"] {
        assert!(
            body.contains(&format!("/offerings/{key}/session/")),
            "the catalog lists a play link for {key}"
        );
    }
    assert!(
        body.contains("Automatafl"),
        "the automatafl card is present"
    );
    assert!(body.contains("Multiway-Tug"), "the tug card is present");
}

/// **A full automatafl turn plays in the browser.** The board paints as a clickable CoordGrid; two
/// seats seal a move, both reveal, the turn resolves — every POST a real landed turn — and the board
/// visibly changes. An illegal (diagonal) move is REFUSED, nothing committed.
#[tokio::test]
async fn a_full_automatafl_turn_plays_through_the_catalog() {
    let app = app();
    let base = "/offerings/automatafl/session/auto-1";

    // The board renders: a CoordGrid of clickable squares (a POST button per affordance-bearing
    // cell), the automaton marked, and the goal squares painted.
    let (status, body) = get(&app, base).await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        body.contains("coordgrid"),
        "the board paints as a CoordGrid"
    );
    assert!(
        body.contains("name=\"turn\" value=\"select\""),
        "a board square is a real POST affordance (clickable)"
    );
    assert!(body.contains('@'), "the automaton is painted");
    assert!(
        body.contains("COMMIT (both seats seal a move)"),
        "the match opens in the commit phase"
    );

    // ── Seat A (browser user `alice`): select the attractor at (1,1), seal a move to (1,4).
    let (_, body) = post(&app, &format!("{base}/act"), "select", idx(1, 1), "alice").await;
    assert!(
        body.contains("Turn committed"),
        "the select lands a real turn: {body}"
    );
    // With a piece selected, its ROOK LINE is lit — the legal-move highlight-set reaches the HTML.
    assert!(
        body.contains("highlighted"),
        "the selected piece lights its legal moves in the browser"
    );

    // An ILLEGAL move — (1,1) → (3,3) is a diagonal. REFUSED; nothing commits.
    let (_, body) = post(&app, &format!("{base}/act"), "commit", idx(3, 3), "alice").await;
    assert!(
        body.contains("Refused: illegal move"),
        "a diagonal is refused by the real referee: {body}"
    );
    assert!(
        body.contains("COMMIT (both seats seal a move)"),
        "the refused move committed nothing — still the commit phase"
    );

    // The legal seal lands.
    let (_, body) = post(&app, &format!("{base}/act"), "commit", idx(1, 4), "alice").await;
    assert!(body.contains("Turn committed"), "the seal lands: {body}");
    assert!(
        body.contains("move SEALED"),
        "the sealed move is FOG on the public surface (only the commitment shows)"
    );

    // ── Seat B (browser user `bob`): select (3,3), seal to (3,0).
    let (_, body) = post(&app, &format!("{base}/act"), "select", idx(3, 3), "bob").await;
    assert!(body.contains("Turn committed"), "bob claims seat B: {body}");
    let (_, body) = post(&app, &format!("{base}/act"), "commit", idx(3, 0), "bob").await;
    assert!(body.contains("Turn committed"));
    assert!(
        body.contains("REVEAL (both moves sealed"),
        "both seals in → the reveal phase: {body}"
    );

    // ── The reveals, then the resolution.
    let (_, body) = post(&app, &format!("{base}/act"), "reveal", 0, "alice").await;
    assert!(body.contains("Turn committed"), "alice opens her seal");
    let (_, body) = post(&app, &format!("{base}/act"), "reveal", 0, "bob").await;
    assert!(body.contains("Turn committed"), "bob opens his seal");
    assert!(
        body.contains("RESOLVE (both open"),
        "both open → the resolution is one turn away: {body}"
    );

    let (_, body) = post(&app, &format!("{base}/act"), "resolve", 0, "alice").await;
    assert!(body.contains("Turn committed"), "the resolution lands");
    assert!(
        body.contains("Automatafl — turn 1"),
        "the resolved turn counter advanced in the browser: {body}"
    );
    // The board MOVED: the attractor that was at (1,1) is gone from that square, and the pieces
    // landed. (The reference `apply_turn` decides exactly where; the in-crate tests pin that.)
    assert!(body.contains("coordgrid"), "the resolved board re-paints");

    // The whole committed chain re-verifies by the offering's own proof.
    let (status, body) = get(&app, &format!("{base}/verify")).await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        body.contains("\"verified\":true"),
        "the committed automatafl match verifies: {body}"
    );
}

/// **The server-form automatafl board renders as a POLISHED, clickable grid — not the minimal prior
/// CSS.** This pins the ACTUAL deployed no-JS path (`render_catalog_forms` → `.coordgrid`/`.cell`/
/// `tag-*` + the page `STYLE`): the board is a centered framed grid of SQUARE cells (`aspect-ratio:
/// 1/1`), the clickable squares (`form.cell`) get a hover/lift + pointer cursor, a highlighted legal
/// move gets a green ring, and the role tints paint (automaton = cyan glow, selected = amber, target
/// = green, vacant = dim). The design is ported from deos-view's `.deos-cell`, but onto THIS path —
/// the one the deployed demo actually serves.
#[tokio::test]
async fn the_server_form_automatafl_board_is_polished() {
    let app = app();
    let base = "/offerings/automatafl/session/auto-css";

    // Open the board and light a piece's legal moves (so a `highlighted` legal-move cell is present).
    let (status, body) = get(&app, base).await;
    assert_eq!(status, StatusCode::OK);
    let (_, body_after) = post(&app, &format!("{base}/act"), "select", idx(1, 1), "alice").await;

    // ── THE MARKUP: a coordgrid of square cells, clickable POST forms, tinted + highlighted.
    assert!(
        body.contains("<div class=\"coordgrid\" style=\"grid-template-columns:repeat(5,1fr)\">"),
        "the board is a 5-wide coordgrid: {body}"
    );
    assert!(
        body.contains("<form class=\"cell") && body.contains("<button type=\"submit\">"),
        "clickable squares are POST forms with a submit button"
    );
    assert!(
        body.contains("tag-accent") && body.contains('@'),
        "the automaton paints with the accent tint"
    );
    assert!(
        body_after.contains("cell highlighted")
            || body_after.contains("highlighted good")
            || body_after.contains("tag-good"),
        "a selected piece lights its legal moves (highlighted / good tint): {body_after}"
    );

    // ── THE CSS: the polished board rules are present (NOT the minimal prior stylesheet).
    // The grid frame + square cells.
    assert!(
        body.contains(".coordgrid{display:grid")
            && body.contains("max-width:24rem")
            && body.contains("border-radius:14px"),
        "the board is a centered, framed grid"
    );
    assert!(
        body.contains(".coordgrid .cell{") && body.contains("aspect-ratio:1/1"),
        "cells are square (aspect-ratio:1/1)"
    );
    // Clickable cells: pointer cursor + a hover lift.
    assert!(
        body.contains(".coordgrid form.cell{padding:0;cursor:pointer}"),
        "clickable squares get a pointer cursor"
    );
    assert!(
        body.contains(".coordgrid form.cell:hover{") && body.contains("transform:translateY(-1px)"),
        "clickable squares lift on hover"
    );
    // The highlighted legal-move ring.
    assert!(
        body.contains(".coordgrid .cell.highlighted{")
            && body.contains("box-shadow:inset 0 0 0 1px var(--good)"),
        "a highlighted legal move gets a green ring"
    );
    // The role tints: accent (cyan automaton glow), warn (amber selected), good (green), muted (dim).
    assert!(
        body.contains(".coordgrid .cell.tag-accent{") && body.contains("radial-gradient"),
        "the automaton cell has a cyan radial glow"
    );
    assert!(
        body.contains(".coordgrid .cell.tag-warn{") && body.contains("var(--warn)"),
        "the selected cell tints amber"
    );
    assert!(
        body.contains(".coordgrid .cell.tag-good{") && body.contains(".coordgrid .cell.tag-muted{"),
        "legal-target (green) + vacant (dim) tints are defined"
    );
}

/// **A tug play lands for a browser user.** The seat-claiming adapter seats the first two browser
/// users; a third is a spectator (refused, nothing commits), and the chain verifies.
#[tokio::test]
async fn a_tug_play_lands_for_a_browser_user() {
    let app = app();
    let base = "/offerings/tug/session/tug-1";

    let (status, body) = get(&app, base).await;
    assert_eq!(status, StatusCode::OK);
    assert!(body.contains("Multiway-Tug"), "the tug surface renders");
    assert!(
        body.contains("Guild 0") && body.contains("Guild 6"),
        "the seven guild lanes paint"
    );

    // The scheduled opening action is `comp` (the round's action order is Competition → Gift →
    // Discard → Secret). A browser user CLAIMS seat A by acting — and the play lands a REAL turn
    // (before the adapter, every web play was refused as "actor holds no seat").
    let (_, body) = post(&app, &format!("{base}/act"), "comp", 3, "alice").await;
    assert!(
        body.contains("Turn committed"),
        "a browser user's play lands a real turn: {body}"
    );

    // Seat B is claimed by the next browser user; their scheduled action lands too.
    let (_, body) = post(&app, &format!("{base}/act"), "comp", 3, "bob").await;
    assert!(
        body.contains("Turn committed"),
        "the second browser user claims seat B and plays: {body}"
    );

    // A THIRD browser user is a spectator — refused, nothing commits.
    let (_, body) = post(&app, &format!("{base}/act"), "gift", 2, "carol").await;
    assert!(
        body.contains("Refused"),
        "a third browser user is a spectator: {body}"
    );

    let (status, body) = get(&app, &format!("{base}/verify")).await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        body.contains("\"verified\":true"),
        "the committed tug round verifies: {body}"
    );
}
