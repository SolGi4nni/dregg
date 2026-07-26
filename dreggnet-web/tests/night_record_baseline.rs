//! **THE SHARED BASELINE — every offering's surface in the Night Record, not just automatafl's.**
//!
//! When the automatafl board landed in dregg's own visual language, the skin that came with it was
//! gated on the offering key (`if key == automatafl_web::KEY { " af-table" }`) and the board's night
//! well was reached only through a guarded `CoordGrid` arm. That was the right scoping for a lane
//! that could screenshot exactly one game — and it left the other twenty-two surfaces on the older
//! catalog theme, which is most of why they read as a debug dump.
//!
//! The skin is game-agnostic — a plaque, a pill, a control, a night ground — so it is now applied to
//! every offering session page, and every non-automatafl `CoordGrid` is recessed in the same well.
//! This file is the tooth on that: it drives REAL sessions of offerings from three different shelves
//! and asserts the baseline reaches them. It is deliberately GET-only, so nothing here depends on
//! the epoch-authenticated act rails.
//!
//! What it pins:
//! - the Night Record skin reaches a game, a feature surface and a service — not one key;
//! - a `CoordGrid` that is NOT automatafl's is painted in the shared well (the descent shaft), with
//!   its column count carried as data rather than hardcoded;
//! - glyph-shape classes are chosen from the glyph, so a symbol and a label paint differently;
//! - automatafl still gets its OWN board painter (`.af-board`), i.e. the shared lift did not eat the
//!   bespoke one.

use std::sync::Arc;

use axum::body::Body;
use axum::http::{Request, StatusCode};
use tower::ServiceExt; // oneshot

mod common;

use dreggnet_web::{CatalogState, catalog_router};

fn app() -> axum::Router {
    common::guard(catalog_router(Arc::new(CatalogState::new())))
}

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
    (status, String::from_utf8_lossy(&bytes).to_string())
}

/// **The skin is not one key's.** A game (`council`), an RPG feature surface (`inventory`) and a
/// service (`doc`) all serve their session page in the Night Record: the page-level `af-table` hook
/// (the night ground hangs off it, outside the swap region) AND the fragment-level one (so a live
/// swap keeps the skin).
#[tokio::test]
async fn every_offering_session_page_is_served_in_the_night_record() {
    let app = app();
    for key in ["council", "market", "tug", "inventory", "doc"] {
        let (status, body) = get(&app, &format!("/offerings/{key}/session/nr-skin-{key}")).await;
        assert_eq!(status, StatusCode::OK, "{key} session page: {body}");
        assert!(
            body.contains("<main class=\"session af-table\">"),
            "`{key}` was not served the Night Record page skin — the shared lift regressed to \
             one key"
        );
        assert!(
            body.contains("<div class=\"af-table\">"),
            "`{key}`'s swappable fragment carries no skin, so a realtime swap would strip it"
        );
    }
}

/// **A non-automatafl board is a BOARD.** The native Descent's shaft is a `CoordGrid`, and it used
/// to render as a bare grid of glyphs on the page floor. It is now recessed in the shared night well
/// — and the well is handed the REAL column count as `--nr-n`, from the node, so no board size is
/// hardcoded anywhere in the renderer or the stylesheet.
#[tokio::test]
async fn a_generic_coordgrid_is_painted_in_the_shared_night_well() {
    let app = app();
    let (status, body) = get(&app, "/offerings/descent/session/nr-well-descent").await;
    assert_eq!(status, StatusCode::OK, "{body}");
    assert!(
        body.contains("class=\"nr-well\""),
        "the descent shaft is not in the shared well: {}",
        &body[..body.len().min(2000)]
    );
    // The well's dimension is DATA. Whatever the shaft's width is, it must arrive as a variable
    // and be a real column count rather than a literal baked into the CSS.
    let n = body
        .split("--nr-n:")
        .nth(1)
        .and_then(|rest| rest.split(['"', ';']).next())
        .expect("the well carries its column count")
        .parse::<usize>()
        .expect("the column count is a number");
    assert!(n >= 1, "a well with {n} columns is not a board");
    assert!(
        body.contains(&format!("grid-template-columns:repeat({n},1fr)")),
        "the grid and its well disagree about the column count"
    );
    // The glyph-shape hint is chosen from the glyph itself — the shaft is full of single symbols
    // (`⚑`, `═`, `☖`), so at least one square must have been classed as a symbol.
    assert!(
        body.contains("nr-sym"),
        "no square was classed by its glyph shape, so a label and a symbol paint identically"
    );
}

/// **The shared lift did not eat the bespoke painter, and the guard is still the KEY.** Driven
/// straight at the renderer with one hand-built `CoordGrid`, so it needs no session and cannot be
/// confused by any game's open path: the same node painted under automatafl's key goes to the
/// bespoke board (`.af-board` + its sprite sheet + rulers), and under any other key goes to the
/// shared well. Neither may produce both — two frames around one board.
#[test]
fn one_coordgrid_two_painters_chosen_by_the_offering_key() {
    use deos_view::{CoordCell, ViewNode};

    let cell = |glyph: &str| CoordCell {
        glyph: glyph.to_string(),
        tag: String::new(),
        turn: String::new(),
        arg: 0,
        highlight: false,
    };
    let board = ViewNode::CoordGrid {
        cols: 3,
        cells: vec![
            cell("R"),
            cell("·"),
            cell("@"),
            cell("A"),
            cell("·"),
            cell("R"),
            cell("·"),
            cell("A"),
            cell("·"),
        ],
    };

    let af = dreggnet_web::render_catalog_forms(&board, "automatafl", "sid");
    assert!(
        af.contains("class=\"af-board\""),
        "automatafl lost its bespoke board painter:\n{af}"
    );
    assert!(
        !af.contains("class=\"nr-well\""),
        "automatafl's board was double-framed by the generic well:\n{af}"
    );

    for key in ["tug", "descent", "some-future-game"] {
        let generic = dreggnet_web::render_catalog_forms(&board, key, "sid");
        assert!(
            generic.contains("class=\"nr-well\" style=\"--nr-n:3\""),
            "`{key}`'s board is not in the shared well with its real column count:\n{generic}"
        );
        assert!(
            !generic.contains("class=\"af-board\""),
            "`{key}` was routed to automatafl's bespoke painter"
        );
        // The glyph decides the shape: a symbol reads large, a vacant square recedes.
        assert!(
            generic.contains("nr-sym") && generic.contains("nr-void"),
            "the glyph-shape classes are not being chosen from the glyph:\n{generic}"
        );
    }

    // And the skin wraps every one of them — the fragment is what a realtime swap replaces.
    for key in ["automatafl", "tug", "doc"] {
        assert!(
            dreggnet_web::render_catalog_forms(&board, key, "sid")
                .starts_with("<div class=\"af-table\">"),
            "`{key}`'s fragment is unskinned"
        );
    }
}
