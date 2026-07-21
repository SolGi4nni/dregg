//! The Lean-authored Descent through the ordinary web catalog, including a
//! process-style restart from the public move journal.

use std::fs;
use std::path::PathBuf;
use std::sync::Arc;

use axum::Router;
use axum::body::Body;
use axum::http::{Request, StatusCode};
use dreggnet_offerings::native_descent::NativeDescentOffering;
use dreggnet_offerings::{FileResumeStore, OfferingHost};
use dreggnet_web::{CatalogState, catalog_router};
use tower::ServiceExt;

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
    (catalog_router(Arc::clone(&catalog)), catalog)
}

async fn response(app: &Router, request: Request<Body>) -> (StatusCode, String) {
    let response = app.clone().oneshot(request).await.expect("router responds");
    let status = response.status();
    let bytes = axum::body::to_bytes(response.into_body(), usize::MAX)
        .await
        .expect("bounded response body");
    (
        status,
        String::from_utf8(bytes.to_vec()).expect("utf-8 surface"),
    )
}

async fn get(app: &Router, suffix: &str, user: &str) -> (StatusCode, String) {
    response(
        app,
        Request::builder()
            .uri(format!("/offerings/{KEY}/session/{SESSION}{suffix}"))
            .header("cookie", format!("dregg_user={user}"))
            .body(Body::empty())
            .unwrap(),
    )
    .await
}

async fn act(app: &Router, turn: &str, arg: i64, user: &str) -> (StatusCode, String) {
    response(
        app,
        Request::builder()
            .method("POST")
            .uri(format!("/offerings/{KEY}/session/{SESSION}/act"))
            .header("content-type", "application/x-www-form-urlencoded")
            .header("cookie", format!("dregg_user={user}"))
            .body(Body::from(format!("turn={turn}&arg={arg}")))
            .unwrap(),
    )
    .await
}

#[tokio::test]
async fn browser_drives_and_restarts_the_native_descent_without_a_state_blob() {
    let dir = scratch_dir();
    let (app, catalog) = app_over(dir.clone());

    let (status, genesis) = get(&app, "", "alice").await;
    assert_eq!(status, StatusCode::OK);
    assert!(genesis.contains("The Descent"), "{genesis}");
    for native_field in ["light", "carried", "banked", "delve"] {
        assert!(
            genesis.contains(native_field),
            "native field `{native_field}` reaches the browser: {genesis}"
        );
    }

    let (status, landed) = act(&app, "delve", 0, "alice").await;
    assert_eq!(status, StatusCode::OK);
    assert!(landed.contains("Turn committed"), "{landed}");
    assert!(landed.contains("depth 1"), "{landed}");

    // Actor ownership is enforced below HTML: another browser identity cannot
    // move Alice's run, and the refusal extends no journal.
    let (status, refused) = act(&app, "delve", 0, "bob").await;
    assert_eq!(status, StatusCode::OK);
    assert!(refused.contains("Refused"), "{refused}");

    let (status, verified) = get(&app, "/verify", "alice").await;
    assert_eq!(status, StatusCode::OK);
    assert!(verified.contains("\"verified\":true"), "{verified}");

    drop(app);
    drop(catalog);

    // A fresh host gets only the durable public-input journal. It re-deploys
    // the Lean program and re-drives the admitted command; no serialized game
    // state is trusted.
    let (restarted, restarted_catalog) = app_over(dir.clone());
    let (status, after_restart) = get(&restarted, "", "alice").await;
    assert_eq!(status, StatusCode::OK);
    assert!(after_restart.contains("depth 1"), "{after_restart}");
    assert!(after_restart.contains("revision 1"), "{after_restart}");
    let (status, verified_again) = get(&restarted, "/verify", "alice").await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        verified_again.contains("\"verified\":true"),
        "{verified_again}"
    );

    drop(restarted);
    drop(restarted_catalog);
    let _ = fs::remove_dir_all(dir);
}
