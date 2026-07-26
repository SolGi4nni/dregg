//! The Lean-authored Descent through the ordinary web catalog, including a
//! process-style restart from the public move journal.

use std::fs;
use std::path::PathBuf;
use std::sync::Arc;

use axum::Router;
use axum::body::Body;
use axum::http::{Request, StatusCode, header};
use dreggnet_offerings::native_descent::NativeDescentOffering;
use dreggnet_offerings::{FileResumeStore, OfferingHost};
use dreggnet_web::{CatalogState, catalog_router};
use dungeon_on_dregg::descent::FLOORS;
use tower::ServiceExt;

mod common;

const KEY: &str = "descent";
const SESSION: &str = "native-web-run";

fn scratch_dir() -> PathBuf {
    use std::sync::atomic::{AtomicU64, Ordering};
    static N: AtomicU64 = AtomicU64::new(0);
    let n = N.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!(
        "dreggnet-native-descent-web-{}-{n}",
        std::process::id()
    ));
    let _ = fs::remove_dir_all(&dir);
    dir
}

fn native_host_over(dir: PathBuf) -> OfferingHost {
    let store = FileResumeStore::open(dir).expect("native Descent store opens");
    let mut host = OfferingHost::new().with_resume_store(Box::new(store));
    host.register(KEY, "The Descent", NativeDescentOffering::new());
    let resumed = host.resume_all();
    assert!(
        resumed.iter().all(|(_, result)| result.is_ok()),
        "every authentic native run resumes: {resumed:?}"
    );
    host
}

fn app_over(dir: PathBuf) -> (Router, Arc<CatalogState>) {
    let catalog = Arc::new(CatalogState::with_host(move || native_host_over(dir)));
    (common::guard(catalog_router(Arc::clone(&catalog))), catalog)
}

async fn response(app: &Router, request: Request<Body>) -> (StatusCode, String) {
    let (status, _, body) = response_with_set_cookie(app, request).await;
    (status, body)
}

async fn response_with_set_cookie(
    app: &Router,
    request: Request<Body>,
) -> (StatusCode, Option<String>, String) {
    let response = app.clone().oneshot(request).await.expect("router responds");
    let status = response.status();
    let set_cookie = response
        .headers()
        .get(header::SET_COOKIE)
        .and_then(|value| value.to_str().ok())
        .map(str::to_string);
    let bytes = axum::body::to_bytes(response.into_body(), usize::MAX)
        .await
        .expect("bounded response body");
    (
        status,
        set_cookie,
        String::from_utf8(bytes.to_vec()).expect("utf-8 surface"),
    )
}

async fn get(app: &Router, suffix: &str, cookie: &str) -> (StatusCode, String) {
    response(
        app,
        Request::builder()
            .uri(format!("/offerings/{KEY}/session/{SESSION}{suffix}"))
            .header(header::COOKIE, cookie)
            .body(Body::empty())
            .unwrap(),
    )
    .await
}

/// One native Descent move, carrying the route authority the surface stamped into its own form.
/// `descent` is a SPINED game key: a bare `turn=&arg=` is `409 invalid game reference`, so the
/// journal would stay empty and the restart legs below would be proving that nothing resumes to
/// nothing.
async fn act(app: &Router, turn: &str, arg: i64, cookie: &str) -> (StatusCode, String) {
    let uri = format!("/offerings/{KEY}/session/{SESSION}/act");
    let body = common::act_body(app, &uri, turn, arg, Some(cookie)).await;
    response(
        app,
        Request::builder()
            .method("POST")
            .uri(&uri)
            .header("content-type", "application/x-www-form-urlencoded")
            .header(header::COOKIE, cookie)
            .body(Body::from(body))
            .unwrap(),
    )
    .await
}

#[tokio::test]
async fn browser_drives_and_restarts_the_native_descent_without_a_state_blob() {
    let dir = scratch_dir();
    let (app, catalog) = app_over(dir.clone());

    let (status, set_cookie, genesis) = response_with_set_cookie(
        &app,
        Request::builder()
            .uri(format!("/offerings/{KEY}/session/{SESSION}"))
            .body(Body::empty())
            .unwrap(),
    )
    .await;
    assert_eq!(status, StatusCode::OK);
    let set_cookie = set_cookie.expect("a cookie-less native player receives a visitor pseudonym");
    let player_cookie = set_cookie
        .split(';')
        .next()
        .expect("Set-Cookie starts with the cookie pair")
        .to_string();
    assert!(player_cookie.starts_with("dregg_user=visitor-"));

    let (_, other_set_cookie, _) = response_with_set_cookie(
        &app,
        Request::builder()
            .uri(format!("/offerings/{KEY}/session/{SESSION}"))
            .body(Body::empty())
            .unwrap(),
    )
    .await;
    let other_cookie = other_set_cookie
        .expect("an independent browser receives its own visitor pseudonym")
        .split(';')
        .next()
        .expect("Set-Cookie starts with the cookie pair")
        .to_string();
    assert_ne!(player_cookie, other_cookie);

    assert!(genesis.contains("The Descent"), "{genesis}");
    for native_field in ["light", "carried", "banked", "delve"] {
        assert!(
            genesis.contains(native_field),
            "native field `{native_field}` reaches the browser: {genesis}"
        );
    }

    let (status, landed) = act(&app, "delve", 0, &player_cookie).await;
    assert_eq!(status, StatusCode::OK);
    assert!(landed.contains("Turn committed"), "{landed}");
    // ⚑ THE STALE LITERAL. This read `"depth 1"` — the counter dump the surface emitted before the
    // vitals painter was unified (`native_descent.rs`'s own note: it "used to render a flat
    // `depth 2 · light spent 9 · wounds 1` counter dump beside a menu"). The surface has said
    // "floor 1 of 4" since, so the test had been red at HEAD ever since. Derived from `FLOORS` now,
    // so re-shaping the shaft moves the expectation with it.
    assert!(
        landed.contains(&format!("floor 1 of {FLOORS}")),
        "the landed page must name the floor the delve reached: {landed}"
    );

    // Actor ownership is enforced below HTML: another asserted browser actor
    // cannot move the first visitor's run, and the refusal extends no journal. This is
    // continuity/ownership inside the game, not web authentication.
    let (status, refused) = act(&app, "delve", 0, &other_cookie).await;
    assert_eq!(status, StatusCode::OK);
    assert!(refused.contains("Refused"), "{refused}");

    let (status, verified) = get(&app, "/verify", &player_cookie).await;
    assert_eq!(status, StatusCode::OK);
    assert!(verified.contains("\"verified\":true"), "{verified}");

    drop(app);
    drop(catalog);

    // A fresh host gets only the durable public-input journal. It re-deploys
    // the Lean program and re-drives the admitted command; no serialized game
    // state is trusted.
    let (restarted, restarted_catalog) = app_over(dir.clone());
    let (status, after_restart) = get(&restarted, "", &player_cookie).await;
    assert_eq!(status, StatusCode::OK);
    // Same stale literal as above: the surface names the FLOOR, not a `depth N` counter.
    assert!(
        after_restart.contains(&format!("floor 1 of {FLOORS}")),
        "the re-driven run stands where the journal says it stood: {after_restart}"
    );
    assert!(after_restart.contains("revision 1"), "{after_restart}");
    let (status, verified_again) = get(&restarted, "/verify", &player_cookie).await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        verified_again.contains("\"verified\":true"),
        "{verified_again}"
    );

    drop(restarted);
    drop(restarted_catalog);
    let _ = fs::remove_dir_all(dir);
}
