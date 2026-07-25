//! The player-driven native Descent campaign through the generic web catalog.
//!
//! This is deliberately not the dedicated `/descent/play` presentation. It proves the shared
//! `OfferingHost` mount that web, Telegram, and the catalog registrar all consume: one submitted
//! native move lands, the exact campaign head survives process death by move-log replay, and a
//! second player move continues from that recovered head. No route synthesizes a win or clear.

use std::fs;
use std::path::PathBuf;
use std::sync::Arc;

use axum::body::Body;
use axum::http::{Request, StatusCode};
use dreggnet_web::{CatalogState, catalog_router, demo_host_resumed_from};
use tower::ServiceExt;

mod common;

fn scratch_dir() -> PathBuf {
    use std::sync::atomic::{AtomicU64, Ordering};
    static N: AtomicU64 = AtomicU64::new(0);
    let dir = std::env::temp_dir().join(format!(
        "dreggnet-web-descent-campaign-{}-{}",
        std::process::id(),
        N.fetch_add(1, Ordering::Relaxed)
    ));
    let _ = fs::remove_dir_all(&dir);
    dir
}

fn app_over(dir: PathBuf) -> axum::Router {
    common::guard(catalog_router(Arc::new(CatalogState::with_host(
        move || demo_host_resumed_from(dir),
    ))))
}

async fn get(app: &axum::Router, uri: &str) -> (StatusCode, String) {
    let response = app
        .clone()
        .oneshot(Request::builder().uri(uri).body(Body::empty()).unwrap())
        .await
        .unwrap();
    let status = response.status();
    let bytes = axum::body::to_bytes(response.into_body(), usize::MAX)
        .await
        .unwrap();
    (status, String::from_utf8(bytes.to_vec()).unwrap())
}

/// POST a campaign move, carrying the route authority the surface stamped into its own form.
/// `descent-campaign` is a SPINED key: a bare `turn=&arg=` is `409 invalid game reference`, so
/// nothing would land, nothing would persist, and every resume assertion below would be about a
/// campaign that never moved.
async fn post(app: &axum::Router, uri: &str, turn: &str, arg: i64) -> (StatusCode, String) {
    common::post_act(app, uri, turn, arg, "alice").await
}

#[tokio::test]
async fn campaign_drives_and_resumes_through_the_generic_web_host() {
    // ⚑ THE DAY MUST BE ARMED FIRST. The web catalog registers the Descent (and the campaign over
    // it) against the LIVE verified drand day and REFUSES to open on no day at all, rather than
    // serving the pre-computable deploy-seed-derived relic provenance. This suite predates that
    // rule and had been asking a day-less host to open a campaign — answered `409`, so its very
    // first assertion failed and nothing below it ever ran. Publish the pinned PUBLISHED round
    // (a genuine BLS-verifiable reveal, and exactly what the surface serves when the transport is
    // down), the same arming `game_session_coherence` does.
    dreggnet_catalog::publish_pinned_descent_day().expect("the pinned published round verifies");

    let dir = scratch_dir();
    let base = "/offerings/descent-campaign/session/web-campaign-restart";
    let act = format!("{base}/act");
    let verify = format!("{base}/verify");

    {
        let app = app_over(dir.clone());
        let (status, genesis) = get(&app, base).await;
        assert_eq!(
            status,
            StatusCode::OK,
            "the campaign session must OPEN before anything else is meaningful: {genesis}"
        );
        assert!(genesis.contains("Deepening Ways"), "{genesis}");
        assert!(
            genesis.contains("no scripted completion"),
            "the public surface says the campaign remains player-driven: {genesis}"
        );

        let (status, after) = post(&app, &act, "delve", 0).await;
        assert_eq!(status, StatusCode::OK);
        assert!(after.contains("Turn committed"), "the delve lands: {after}");
        assert!(after.contains("depth 1"), "native state advances: {after}");
        let (status, report) = get(&app, &verify).await;
        assert_eq!(status, StatusCode::OK);
        assert!(report.contains("\"verified\":true"), "{report}");
        assert!(report.contains("\"turns\":2"), "{report}");
    }

    let app = app_over(dir.clone());
    let (status, resumed) = get(&app, base).await;
    assert_eq!(
        status,
        StatusCode::OK,
        "the campaign session reopens: {resumed}"
    );
    assert!(
        resumed.contains("depth 1"),
        "a fresh web host replays the landed native state: {resumed}"
    );
    assert!(
        resumed.contains("campaign revision 1"),
        "the durable campaign revision survives process death: {resumed}"
    );
    assert!(
        resumed.contains("Strike the guardian"),
        "the recovered state presents its actual next move: {resumed}"
    );
    let (status, recovered_report) = get(&app, &verify).await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        recovered_report.contains("\"verified\":true"),
        "{recovered_report}"
    );
    assert!(
        recovered_report.contains("\"turns\":2"),
        "{recovered_report}"
    );

    let (status, after_smite) = post(&app, &act, "smite", 0).await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        after_smite.contains("Turn committed"),
        "the recovered campaign accepts the next presented move: {after_smite}"
    );
    let (_, report) = get(&app, &verify).await;
    assert!(report.contains("\"verified\":true"), "{report}");
    assert!(report.contains("\"turns\":3"), "{report}");

    let _ = fs::remove_dir_all(&dir);
}
