//! Dungeon, Descent, the shielded raid and the Bazaar keep distinct rules but
//! expose one browser interaction grammar: session → action → result/receipt.

use std::sync::Arc;

use axum::body::Body;
use axum::http::{Request, StatusCode};
use dreggnet_web::{CatalogState, catalog_router};
use tower::ServiceExt;

mod common;

async fn response(app: &axum::Router, request: Request<Body>) -> (StatusCode, String) {
    let response = app.clone().oneshot(request).await.expect("router response");
    let status = response.status();
    let body = axum::body::to_bytes(response.into_body(), usize::MAX)
        .await
        .expect("response body");
    (
        status,
        String::from_utf8(body.to_vec()).expect("HTML response"),
    )
}

fn get(path: &str) -> Request<Body> {
    Request::builder()
        .uri(path)
        .header("cookie", "dregg_user=coherence-player")
        .body(Body::empty())
        .unwrap()
}

/// One turn, carrying the route authority the play surface stamped into its own form. All four
/// families driven here (`descent`, `dungeon`, `private-raid`, `bazaar`) are SPINED game keys, so
/// a bare `turn=&arg=` is `409 invalid game reference` — and "the same result/receipt shape"
/// contract this file exists to pin would never have been observed on any of them.
async fn act(app: &axum::Router, path: &str, turn: &str, arg: i64) -> Request<Body> {
    const COOKIE: &str = "dregg_user=coherence-player";
    let act_uri = format!("{path}/act");
    let body = common::act_body(app, &act_uri, turn, arg, Some(COOKIE)).await;
    Request::builder()
        .method("POST")
        .uri(&act_uri)
        .header("content-type", "application/x-www-form-urlencoded")
        .header("cookie", COOKIE)
        .body(Body::from(body))
        .unwrap()
}

#[tokio::test]
async fn four_rule_families_share_the_same_resumable_action_result_contract() {
    // The web catalog registers the Descent against the LIVE verified drand day, and refuses to
    // open on no day at all (a live surface must not serve the pre-computable, seed-derived
    // relic provenance). Publish the pinned PUBLISHED round — a genuine BLS-verifiable reveal,
    // and exactly what the surface serves when the transport is down — so this test drives the
    // real live path with no network.
    dreggnet_catalog::publish_pinned_descent_day().expect("the pinned published round verifies");

    let app = common::guard(catalog_router(Arc::new(CatalogState::new())));
    let cases = [
        ("descent", "descent", "delve", 0),
        ("dungeon", "dungeon", "choose", 0),
        ("private-raid", "tactical-raid", "join-private-raid", 0),
        ("bazaar", "dark-bazaar-crawl", "list", 1),
    ];

    for (key, family, turn, arg) in cases {
        let path = format!("/offerings/{key}/session/coherent-{key}");
        let (status, opened) = response(&app, get(&path)).await;
        assert_eq!(status, StatusCode::OK, "{key}: {opened}");
        for stable in [
            "data-game-session=\"true\"".to_string(),
            format!("data-game-family=\"{family}\""),
            "data-actor-attribution=\"asserted\"".to_string(),
            // The attribution disclosure, in the words the rail now uses. Same claim as the old
            // "Browser actor attribution is asserted, not authenticated." — said so a player can
            // act on it.
            "takes your player name at face value and checks no signature".to_string(),
            "Choose an action".to_string(),
            "Read the result".to_string(),
            "rel=\"bookmark\">Resume here".to_string(),
            "data-result-kind=\"surface-and-receipt\"".to_string(),
            "data-session-action=\"turn\"".to_string(),
            "chain re-verified by replay".to_string(),
        ] {
            assert!(opened.contains(&stable), "{key} lacks {stable:?}: {opened}");
        }
        assert!(
            opened.contains(&format!("href=\"{path}\"")),
            "{key} must resume at the exact game/session address: {opened}"
        );

        let (status, landed) = response(&app, act(&app, &path, turn, arg).await).await;
        assert_eq!(status, StatusCode::OK, "{key}: {landed}");
        assert!(landed.contains("Turn committed"), "{key}: {landed}");
        assert!(
            landed.contains("data-result-kind=\"surface-and-receipt\"")
                && landed.contains("verified turn"),
            "{key} must return the same result/receipt shape: {landed}"
        );
    }
}

#[tokio::test]
async fn service_offerings_are_not_mislabeled_as_games() {
    let app = common::guard(catalog_router(Arc::new(CatalogState::new())));
    let (status, page) = response(&app, get("/offerings/doc/session/not-a-game")).await;
    assert_eq!(status, StatusCode::OK);
    assert!(!page.contains("data-game-session=\"true\""), "{page}");
}
