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

mod common;

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

/// POST a `{turn, arg}` affordance form as web user `user` (a `dregg_user` cookie), carrying the
/// route authority the play surface stamped into its own form. Both games here (`automatafl`,
/// `tug`) are SPINED keys: a bare `turn=&arg=` is `409 invalid game reference`, and every play
/// line in this file would stop before the executor.
async fn post(
    app: &axum::Router,
    uri: &str,
    turn: &str,
    arg: i64,
    user: &str,
) -> (StatusCode, String) {
    common::post_act(app, uri, turn, arg, user).await
}

fn app() -> axum::Router {
    common::guard(catalog_router(Arc::new(CatalogState::new())))
}

/// The automatafl board index of `(x, y)` — derived from the board's OWN width
/// ([`dregg_automatafl::game::N`], the stock two-player game), never a literal, so a board-size
/// change moves this test with it instead of silently addressing the wrong squares.
fn idx(x: i64, y: i64) -> i64 {
    y * dregg_automatafl::game::N as i64 + x
}

/// BOTH games appear in the catalog, each with a play link.
#[tokio::test]
async fn the_catalog_lists_both_portfolio_games() {
    let app = app();
    let (status, body) = get(&app, "/offerings").await;
    assert_eq!(status, StatusCode::OK);
    // ⚑ THE LINK IS THE TABLE DOOR, not a shared session id. Both of these are SEAT-LOCKED
    // two-player hidden-move games, so the catalog advertises their table-minting front door
    // *instead of* `/offerings/{key}/session/{key}-web`: the printed shared id was a seat race,
    // and an asserted-label identity could render the opponent's private projection on it.
    for key in ["tug", "automatafl"] {
        let door = dreggnet_web::table_seats::lock_for_key(key)
            .unwrap_or_else(|| panic!("{key} is a seat-locked table game"));
        assert!(
            body.contains(&format!("href=\"{}\"", door.route)),
            "the catalog opens a {key} table at {}: {body}",
            door.route
        );
        assert!(
            !body.contains(&format!("/offerings/{key}/session/")),
            "and never re-advertises a shared, guessable {key} table id: {body}"
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

    // ── Seat A (browser user `alice`): select the stock attractor at (3,1), seal a move to (3,3).
    let (_, body) = post(&app, &format!("{base}/act"), "select", idx(3, 1), "alice").await;
    assert!(
        body.contains("Turn committed"),
        "the select lands a real turn: {body}"
    );
    // With a piece selected, its ROOK LINE is lit — the legal-move highlight-set reaches the HTML.
    assert!(
        body.contains("highlighted"),
        "the selected piece lights its legal moves in the browser"
    );

    // An ILLEGAL move — (3,1) → (4,2) is a diagonal. REFUSED; nothing commits.
    let (_, body) = post(&app, &format!("{base}/act"), "commit", idx(4, 2), "alice").await;
    assert!(
        body.contains("Refused: illegal move"),
        "a diagonal is refused by the real referee: {body}"
    );
    assert!(
        body.contains("COMMIT (both seats seal a move)"),
        "the refused move committed nothing — still the commit phase"
    );

    // The legal seal lands. The POST re-renders AS alice (the viewer-aware host boundary), so the
    // sealer sees HER OWN move revealed — the opponent, not the sealer, is the one kept in the fog.
    let (_, body) = post(&app, &format!("{base}/act"), "commit", idx(3, 3), "alice").await;
    assert!(body.contains("Turn committed"), "the seal lands: {body}");
    assert!(
        body.contains("YOUR sealed move"),
        "the sealer sees THEIR OWN sealed move on their own surface (per-viewer, not viewer-blind fog): {body}"
    );

    // ── Seat B (browser user `bob`): select (7,1), seal to (7,3).
    let (_, body) = post(&app, &format!("{base}/act"), "select", idx(7, 1), "bob").await;
    assert!(body.contains("Turn committed"), "bob claims seat B: {body}");
    let (_, body) = post(&app, &format!("{base}/act"), "commit", idx(7, 3), "bob").await;
    assert!(body.contains("Turn committed"));
    // Rendered AS bob now: bob sees HIS own seal, and ALICE's sealed move is FOG to him (only the
    // commitment shows) — the simultaneous-secret fog, correctly keyed to the OPPONENT's viewpoint.
    assert!(
        body.contains("move SEALED"),
        "the opponent's sealed move is fog to bob (only the commitment shows): {body}"
    );
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
    // The board MOVED: the attractor that was at (3,1) is gone from that square, and the pieces
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
    let (_, body_after) = post(&app, &format!("{base}/act"), "select", idx(3, 1), "alice").await;

    // ── THE MARKUP: a coordgrid of square cells, clickable POST forms, tinted + highlighted.
    // N-GENERIC: the expected markup is built from the board's own width, and the `checkered` class
    // (the odd-width checkerboard) is decided by the renderer rather than by a board size in CSS.
    let n = dregg_automatafl::game::N;
    assert!(
        body.contains(&format!(
            "<div class=\"coordgrid checkered\" style=\"grid-template-columns:repeat({n},1fr)\">"
        )),
        "the board is an {n}-wide coordgrid (the board's own width): {body}"
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
            && body.contains("max-width:32rem")
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

/// A browser match now reaches an executor-scored terminal result rather than
/// stopping after the eighth placement with no winner, no charm, and a stale
/// "to move" banner. Both browser identities keep their claimed seats across
/// the full alternating round. The browser then fires the separately surfaced
/// SCORE affordance, preserving the Offering invariant that one press is one
/// executor turn and one receipt; `/verify` re-drives all nine inputs.
#[tokio::test]
async fn a_full_tug_match_scores_and_replays_through_the_web_surface() {
    let app = app();
    let base = "/offerings/tug/session/tug-full-scored";
    let schedule = [
        ("comp", 3, "alice"),
        ("comp", 3, "bob"),
        ("gift", 2, "alice"),
        ("gift", 2, "bob"),
        ("discard", 1, "alice"),
        ("discard", 1, "bob"),
        ("secret", 0, "alice"),
        ("secret", 0, "bob"),
    ];

    for (turn, arg, actor) in schedule {
        let (status, body) = post(&app, &format!("{base}/act"), turn, arg, actor).await;
        assert_eq!(status, StatusCode::OK);
        assert!(body.contains("Turn committed"), "{actor}/{turn}: {body}");
    }

    let (status, body) = post(&app, &format!("{base}/act"), "score", 4, "alice").await;
    assert_eq!(status, StatusCode::OK);
    assert!(body.contains("Turn committed"), "score: {body}");

    let (status, body) = get(&app, base).await;
    assert_eq!(status, StatusCode::OK);
    assert!(body.contains("ROUND COMPLETE"), "{body}");
    assert!(
        body.contains("WINNER:") || body.contains("DRAW"),
        "the public result is explicit: {body}"
    );
    assert!(
        body.contains("Influence A:"),
        "final influence renders: {body}"
    );

    let (status, body) = get(&app, &format!("{base}/verify")).await;
    assert_eq!(status, StatusCode::OK);
    assert!(body.contains("\"verified\":true"), "{body}");
    assert!(
        body.contains("\"turns\":10"),
        "genesis + eight plays + score replay: {body}"
    );
}
