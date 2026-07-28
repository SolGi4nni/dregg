//! **A DEPLOY REFUSAL IS NOT A STALE PAGE** — the beacon-less Descent open, driven over HTTP.
//!
//! ## The wound
//!
//! `CatalogState::new` builds its host through `dreggnet_catalog::CatalogConfig::live`, whose
//! `DescentDayBinding::Live` resolves today's verified drand day **at every open** and REFUSES when
//! there is none — deliberately, because serving the pre-computable deploy-seed-derived provenance
//! root would make the day's relic ids computable by anyone before the round matured. A serving
//! process arms the day at boot (`arm_todays_descent_day`) and on a timer; between process start and
//! that first fetch, and after every UTC-day roll until the next one, there is no day.
//!
//! The refusal is `HostError::Deploy`, and it fell past `refused_open_response`'s arm into the
//! `Err(error)` catch-all — `refused_game_route_response`, whose body is
//! `STALE_GAME_ROUTE_BODY`: *"This page is out of date … Reload to see the current state."*
//!
//! Every clause of that is false. The page is not out of date — it is the current state of a server
//! that cannot open this game. And the one action it offers cannot work: a reload re-enters the same
//! open, resolves no day, and refuses identically. A player is told to do a thing, forever.
//!
//! ## Both poles
//!
//! * **NO DAY** — 503, the audited deploy copy (*nothing was opened; a fault in how this server was
//!   built, not in what you did; tell an operator, the server log names the missing piece*), and NOT
//!   one word of the stale-page notice.
//! * **DAY PUBLISHED** — the same URL opens and renders. The refusal is the missing day talking, not
//!   this route deciding it dislikes the Descent.
//!
//! ⚠ ONE TEST FN IN ITS OWN BINARY, in that order, on purpose. The published day is a process-wide
//! cell with no un-publish, so the no-day pole must be observed before anything arms one — a second
//! `#[test]` here would race it, and a sibling binary's `publish_pinned_descent_day` cannot reach
//! this process.

use std::sync::Arc;

use axum::http::StatusCode;
use dreggnet_web::{CatalogState, catalog_router};

mod common;

/// The first entry of `dreggnet_catalog::SHIPPED_KEYS` — the flagship, and the one offering whose
/// deploy depends on a fetched beacon.
const DESCENT: &str = "/offerings/descent/session/beaconless-1";

#[tokio::test]
async fn a_descent_open_without_a_verified_day_refuses_honestly_then_opens_once_a_day_is_published()
{
    let app = common::guard(catalog_router(Arc::new(CatalogState::new())));

    // ── POLE 1: no day published in this process ────────────────────────────────────────────────
    let (status, body) = common::get_with_cookie(&app, DESCENT, Some("dregg_user=alice")).await;
    let text = common::without_stylesheets(&body);

    assert_eq!(
        status,
        StatusCode::SERVICE_UNAVAILABLE,
        "a server that cannot build this offering answers 503 — not the 409 of a conflicting route, \
         and not a 500: the request is fine. Body: {text}"
    );
    assert!(
        !text.contains("This page is out of date"),
        "the reader must NOT be told their page is stale: it is current, and the reload that copy \
         asks for re-enters the same refusal. Body: {text}"
    );
    assert!(
        !text.contains("Reload to see the current state"),
        "no next action that cannot work. Body: {text}"
    );
    // The audited deploy copy: what happened, that nothing was lost, and whose problem it is.
    for clause in [
        "could not be opened on this server",
        "Nothing was opened and nothing was recorded",
        "not in anything you did",
        "the server log names the missing piece",
    ] {
        assert!(
            text.contains(clause),
            "the deploy refusal must say {clause:?}. Body: {text}"
        );
    }
    // And it is a rendered refusal NOTICE, not a bare unstyled string — the shape every other
    // refused open on this surface already has, with a way back.
    assert!(
        body.contains("class=\"notice refused\"") && body.contains("Browse all games"),
        "the refusal is a real page with a control that works: {body}"
    );

    // ── POLE 2: arm the day, and the SAME url opens ─────────────────────────────────────────────
    // The pinned published round is a genuine BLS-verifiable drand reveal (what a live surface
    // serves, labeled, when the transport is down), so the whole verify path runs for real.
    dreggnet_catalog::publish_pinned_descent_day().expect("the pinned published round verifies");

    let (status, body) = common::get_with_cookie(&app, DESCENT, Some("dregg_user=alice")).await;
    assert_eq!(
        status,
        StatusCode::OK,
        "with a verified day published the Descent opens — the refusal above was the missing day, \
         not this route: {body}"
    );
    assert!(
        !body.contains("could not be opened on this server"),
        "the deploy refusal must be gone once the day is armed: {body}"
    );
}
