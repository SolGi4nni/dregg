//! The primary web catalog consumes the same authority-bound game spine as the
//! chat adapters: restart retains one exact route, close/reopen advances it,
//! and a foreign host incarnation cannot inspect the live world.

use std::fs;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use axum::body::Body;
use axum::http::{Request, StatusCode};
use dreggnet_catalog::{
    GameAudience, GameEpochLedger, GameHostIncarnation, GameSessionRef, PlayerWorlds,
};
use dreggnet_offerings::{DreggIdentity, SessionId};
use dreggnet_web::{CatalogState, catalog_router, demo_host_resumed_from};
use tower::ServiceExt;

fn scratch_dir(tag: &str) -> PathBuf {
    use std::sync::atomic::{AtomicU64, Ordering};
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let dir = std::env::temp_dir().join(format!(
        "dreggnet-web-game-epoch-{}-{tag}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed),
    ));
    let _ = fs::remove_dir_all(&dir);
    dir
}

fn state_over(root: &Path) -> Arc<CatalogState> {
    let sessions = root.join("sessions");
    let epochs = GameEpochLedger::open(root.join("epochs")).expect("open durable game epochs");
    Arc::new(CatalogState::with_hosts_and_game_epochs(
        move || demo_host_resumed_from(sessions),
        PlayerWorlds::new,
        epochs,
    ))
}

async fn response(app: &axum::Router, request: Request<Body>) -> (StatusCode, String) {
    let response = app.clone().oneshot(request).await.expect("router response");
    let status = response.status();
    let body = axum::body::to_bytes(response.into_body(), usize::MAX)
        .await
        .expect("response body");
    (
        status,
        String::from_utf8(body.to_vec()).expect("UTF-8 response"),
    )
}

fn get(path: &str) -> Request<Body> {
    Request::builder()
        .uri(path)
        .header("cookie", "dregg_user=epoch-player")
        .body(Body::empty())
        .unwrap()
}

fn act(path: &str, turn: &str, arg: i64) -> Request<Body> {
    Request::builder()
        .method("POST")
        .uri(format!("{path}/act"))
        .header("content-type", "application/x-www-form-urlencoded")
        .header("cookie", "dregg_user=epoch-player")
        .body(Body::from(format!("turn={turn}&arg={arg}")))
        .unwrap()
}

#[tokio::test]
async fn web_game_epoch_survives_restart_and_close_reopen_retires_old_route() {
    let root = scratch_dir("restart-close");
    let path = "/offerings/dungeon/session/epoch-run";
    let sid = SessionId::new("epoch-run");
    let viewer = DreggIdentity("epoch-player".to_string());

    let state = state_over(&root);
    let app = catalog_router(Arc::clone(&state));
    assert_eq!(response(&app, get(path)).await.0, StatusCode::OK);
    let generation_one = state
        .bound_game_session("dungeon", &sid)
        .expect("first bound route");

    let (status, landed) = response(&app, act(path, "choose", 0)).await;
    assert_eq!(status, StatusCode::OK, "{landed}");
    assert!(
        landed.contains("publication") && landed.contains("Verified dungeon receipt"),
        "the actual web turn returns only the common public receipt grammar: {landed}"
    );

    assert!(
        state
            .close_game_session("dungeon", &sid, &viewer)
            .expect("retire generation one")
    );
    assert_eq!(response(&app, get(path)).await.0, StatusCode::OK);
    let generation_two = state
        .bound_game_session("dungeon", &sid)
        .expect("reopened bound route");
    assert_ne!(generation_one, generation_two);
    assert!(
        state
            .inspect_game_session(generation_one, GameAudience::Shared)
            .is_err(),
        "the exact pre-close route must not inspect the reopened world"
    );

    drop(app);
    drop(state);

    let restarted = state_over(&root);
    let restarted_app = catalog_router(Arc::clone(&restarted));
    assert_eq!(response(&restarted_app, get(path)).await.0, StatusCode::OK);
    assert_eq!(
        restarted
            .bound_game_session("dungeon", &sid)
            .expect("restart route"),
        generation_two,
        "ordinary restart retains incarnation and live generation"
    );

    let foreign = GameSessionRef::bound(
        "dungeon",
        sid,
        GameHostIncarnation::new([0xa5; 32]).unwrap(),
        2,
    )
    .unwrap();
    assert!(
        restarted
            .inspect_game_session(foreign, GameAudience::Shared)
            .is_err(),
        "a foreign host incarnation must not inspect this deployment's world"
    );

    let _ = fs::remove_dir_all(root);
}
