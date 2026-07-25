#![cfg(feature = "hosted-binary-operations")]

//! Browser-level proof that the shared catalog's Ash Gate raid is a playable
//! game, not only a discoverable proof-upload panel.

use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

use axum::Router;
use axum::body::Body;
use axum::http::{Request, StatusCode};
use dreggnet_catalog::{CatalogConfig, full_catalog_host};
use dreggnet_offerings::{FileResumeStore, SessionId, seed_from_id};
use dreggnet_surfaces::party::{
    TURN_ACT, TURN_CLAIM, TURN_FORK, TURN_LAUNCH, TURN_READY, TURN_RESOLVE_FORK,
};
use dreggnet_surfaces::private_raid::{
    ASSIGN_MEDIA_TYPE, ASSIGN_OPERATION, KEY, TURN_JOIN_RAID, TURN_PRIME_TACTIC,
    proof_session_for_seed,
};
use dreggnet_web::{CatalogState, catalog_router, fhegg_operation};
use dungeon_on_dregg::combat::{Arena, is_hero};
use dungeon_on_dregg::private_raid::prove_private_assignment;
use tower::ServiceExt;

mod common;

const USERS: [&str; 4] = ["alice", "bob", "cara", "devi"];

fn scores() -> [[u8; 4]; 4] {
    [[3, 2, 0, 0], [3, 0, 1, 0], [0, 0, 3, 1], [0, 1, 0, 3]]
}

fn arena_seed(seed: u64) -> u8 {
    seed.to_le_bytes().into_iter().fold(0u8, u8::wrapping_add)
}

fn hero_first_session() -> String {
    (0u64..)
        .map(|candidate| format!("browser-private-raid-{candidate}"))
        .find(|id| is_hero(Arena::deploy(arena_seed(seed_from_id(id))).active()))
        .expect("some deterministic browser session begins on a hero turn")
}

fn scratch_dir() -> PathBuf {
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let dir = std::env::temp_dir().join(format!(
        "dreggnet-web-private-raid-player-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    let _ = std::fs::remove_dir_all(&dir);
    dir
}

fn state(dir: &Path) -> Arc<CatalogState> {
    let dir = dir.to_path_buf();
    Arc::new(CatalogState::with_host(move || {
        let store = FileResumeStore::open(dir).expect("the browser raid journal opens");
        let mut host =
            full_catalog_host(&CatalogConfig::default()).with_resume_store(Box::new(store));
        let resumed = host.resume_all();
        assert!(
            resumed.iter().all(|(_, result)| result.is_ok()),
            "the shared catalog must fail closed rather than partially resume: {resumed:?}"
        );
        host
    }))
}

fn app(state: Arc<CatalogState>) -> Router {
    common::guard(catalog_router(Arc::clone(&state)).merge(fhegg_operation::router(state)))
}

async fn response(app: &Router, request: Request<Body>) -> (StatusCode, String) {
    let response = app.clone().oneshot(request).await.expect("router response");
    let status = response.status();
    let body = axum::body::to_bytes(response.into_body(), usize::MAX)
        .await
        .expect("response body");
    (
        status,
        String::from_utf8(body.to_vec()).expect("HTML/JSON response"),
    )
}

/// One raid move, carrying the route authority the play surface stamped into its own form.
/// `private-raid` is a SPINED game key, so a bare `turn=&arg=` is `409 invalid game reference` —
/// nobody joins, nothing is journalled, and the restart legs prove nothing.
async fn act(app: &Router, base: &str, user: &str, turn: &str, arg: i64) -> Request<Body> {
    let act_uri = format!("{base}/act");
    let cookie = format!("dregg_user={user}");
    let body = common::act_body(app, &act_uri, turn, arg, Some(&cookie)).await;
    Request::builder()
        .method("POST")
        .uri(&act_uri)
        .header("content-type", "application/x-www-form-urlencoded")
        .header("cookie", &cookie)
        .body(Body::from(body))
        .expect("valid action request")
}

fn upload(base: &str, user: &str, proof: Vec<u8>) -> Request<Body> {
    Request::builder()
        .method("POST")
        .uri(format!("{base}/operations/{ASSIGN_OPERATION}"))
        .header("content-type", ASSIGN_MEDIA_TYPE)
        .header("cookie", format!("dregg_user={user}"))
        .body(Body::from(proof))
        .expect("valid proof request")
}

async fn lands(app: &Router, request: Request<Body>, context: &str) -> String {
    let (status, body) = response(app, request).await;
    assert_eq!(status, StatusCode::OK, "{context}: {body}");
    assert!(body.contains("Turn committed"), "{context}: {body}");
    body
}

#[tokio::test]
async fn shared_catalog_browser_raid_spends_the_proof_in_arena_and_restarts() {
    let dir = scratch_dir();
    let session = hero_first_session();
    let seed = seed_from_id(&session);
    let proof = prove_private_assignment(
        proof_session_for_seed(seed),
        scores(),
        [
            [false, true, true, true],
            [true, true, true, true],
            [true, true, true, true],
            [true, true, true, true],
        ],
    )
    .expect("the private optimizer produces a real HidingFri proof")
    .to_postcard()
    .expect("the proof has its canonical upload image");
    let base = format!("/offerings/{KEY}/session/{session}");

    let before_restart_turns = {
        let catalog = state(&dir);
        let app = app(Arc::clone(&catalog));

        for user in USERS {
            lands(
                &app,
                act(&app, &base, user, TURN_JOIN_RAID, 0).await,
                &format!("{user} joins with the asserted browser actor"),
            )
            .await;
        }

        let (status, body) = response(&app, upload(&base, "bob", proof.clone())).await;
        assert_eq!(status, StatusCode::CONFLICT, "wrong proof seat: {body}");
        assert!(body.contains("only public seat 0"), "{body}");

        let (status, body) = response(&app, upload(&base, "alice", proof)).await;
        assert_eq!(status, StatusCode::OK, "seat-zero proof upload: {body}");
        assert!(body.contains("\"status\":\"applied\""), "{body}");

        // Proof roles Striker/Bulwark/Mender/Pathfinder map to the real party's
        // Mage/Tank/Healer/Scout capability indices 2/0/3/1.
        for (user, role) in [("alice", 2), ("bob", 0), ("cara", 3), ("devi", 1)] {
            lands(
                &app,
                act(&app, &base, user, TURN_CLAIM, role).await,
                &format!("{user} claims only the proof-selected capability"),
            )
            .await;
        }
        for user in USERS {
            lands(
                &app,
                act(&app, &base, user, TURN_READY, 0).await,
                &format!("{user} readies"),
            )
            .await;
        }
        lands(
            &app,
            act(&app, &base, "alice", TURN_LAUNCH, 0).await,
            "leader launches",
        )
        .await;
        for user in ["alice", "bob", "cara"] {
            lands(
                &app,
                act(&app, &base, user, TURN_FORK, 0).await,
                &format!("{user} votes for the Warden"),
            )
            .await;
        }
        lands(
            &app,
            act(&app, &base, "alice", TURN_RESOLVE_FORK, 0).await,
            "leader resolves the real target ballot",
        )
        .await;

        let (status, unprimed) = response(
            &app,
            Request::builder()
                .uri(&base)
                .header("cookie", "dregg_user=alice")
                .body(Body::empty())
                .unwrap(),
        )
        .await;
        assert_eq!(status, StatusCode::OK);
        assert!(unprimed.contains(TURN_PRIME_TACTIC), "{unprimed}");
        assert!(
            !unprimed.contains(&format!("name=\"turn\" value=\"{TURN_ACT}\"")),
            "an unprimed Arena action must not be painted into the browser: {unprimed}"
        );

        let (status, crafted) = response(&app, act(&app, &base, "alice", TURN_ACT, 0).await).await;
        assert_eq!(status, StatusCode::OK);
        assert!(
            crafted.contains("not on the current surface"),
            "a stale/crafted unprimed act is refused before Arena: {crafted}"
        );

        lands(
            &app,
            act(&app, &base, "alice", TURN_PRIME_TACTIC, 2).await,
            "Alice burns her proof-minted Mage sigil",
        )
        .await;
        let acted = lands(
            &app,
            act(&app, &base, "alice", TURN_ACT, 0).await,
            "the primed Mage contributes a real Arena turn",
        )
        .await;
        assert!(acted.contains("Tactical Arena"), "{acted}");

        let report = catalog
            .verify(KEY, &SessionId::new(session.clone()))
            .expect("the shared catalog retains the raid session");
        assert!(report.verified, "{}", report.detail);
        report.turns
    };

    let rebooted = state(&dir);
    assert!(
        rebooted.is_open(KEY, &SessionId::new(session.clone())),
        "the shared catalog boot-replays the browser raid"
    );
    let report = rebooted
        .verify(KEY, &SessionId::new(session.clone()))
        .expect("the replayed raid remains live");
    assert!(report.verified, "{}", report.detail);
    assert_eq!(report.turns, before_restart_turns);

    let rebooted_app = app(rebooted);
    let (status, page) = response(
        &rebooted_app,
        Request::builder()
            .uri(&base)
            .header("cookie", "dregg_user=alice")
            .body(Body::empty())
            .unwrap(),
    )
    .await;
    assert_eq!(status, StatusCode::OK);
    assert!(page.contains("HIDING PROOF VERIFIED"), "{page}");
    assert!(page.contains("Tactical Arena"), "{page}");

    let _ = std::fs::remove_dir_all(dir);
}
