//! **Live game sessions survive a restart — the durable session-resume weld, driven end-to-end.**
//!
//! `demo_host_resumed_from(dir)` builds the demo catalog host over a durable
//! [`FileResumeStore`](dreggnet_offerings::FileResumeStore) and boot-resumes every persisted
//! move-log by REPLAY. These tests drive that weld through the REAL catalog router (axum
//! `oneshot`, no network), across a simulated restart (a brand-new app/host over the SAME
//! directory), in both polarities:
//! - a played session's state SURVIVES the restart — the resumed session renders the identical
//!   surface and re-verifies at the same turn count (and the pre-restart surface provably differs
//!   from genesis, so the equality is non-vacuous);
//! - a session whose persisted log is TAMPERED (one byte) REFUSES to reopen (fail-closed, its
//!   file kept on disk) while the intact sessions still resume.

use std::fs;
use std::path::PathBuf;
use std::sync::Arc;

use axum::body::Body;
use axum::http::{Request, StatusCode};
use dreggnet_offerings::SessionId;
use dreggnet_web::{CatalogState, catalog_router, demo_host_resumed_from};
use dungeon_on_dregg::{KP_CLAIM_RED, KP_DESCEND, KP_PRESS_ON};
use tower::ServiceExt; // oneshot

mod common;

/// A unique scratch directory for one test (process id + a monotone counter), created by the
/// store itself on first open.
fn scratch_dir(tag: &str) -> PathBuf {
    use std::sync::atomic::{AtomicU64, Ordering};
    static N: AtomicU64 = AtomicU64::new(0);
    let n = N.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!(
        "dreggnet-web-session-resume-{}-{}-{}",
        std::process::id(),
        tag,
        n
    ));
    let _ = fs::remove_dir_all(&dir);
    dir
}

/// The catalog app over a durable session store rooted at `dir` — one "server process". Building
/// a second one over the SAME dir is the simulated restart (the boot resume runs on the host
/// thread inside `demo_host_resumed_from`).
fn app_over(dir: PathBuf) -> axum::Router {
    common::guard(catalog_router(Arc::new(CatalogState::with_host(
        move || demo_host_resumed_from(dir),
    ))))
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
    (status, String::from_utf8(bytes.to_vec()).unwrap())
}

/// POST a `{turn, arg}` affordance form to `uri` as web user `user` (a `dregg_user` cookie),
/// carrying the route authority the surface stamped into its own form. `dungeon` is a SPINED key,
/// so a bare `turn=&arg=` never lands and there would be nothing durable to resume.
async fn post(
    app: &axum::Router,
    uri: &str,
    turn: &str,
    arg: i64,
    user: &str,
) -> (StatusCode, String) {
    common::post_act(app, uri, turn, arg, user).await
}

/// A played dungeon session SURVIVES a restart: three landed moves through the real router, then
/// a brand-new app/host over the SAME store dir renders the IDENTICAL surface at the SAME
/// re-verified turn count — not a fresh genesis (the genesis surface provably differs).
#[tokio::test]
async fn a_played_session_survives_a_restart_from_the_same_dir() {
    let dir = scratch_dir("survive");
    let app = app_over(dir.clone());
    let base = "/offerings/dungeon/session/persist-1";
    let act = format!("{base}/act");
    let verify = format!("{base}/verify");

    // Open at genesis (the lazy open records the seed into the store) and keep its surface — the
    // non-vacuity witness for the equality assertion after the restart.
    let (status, genesis_body) = get(&app, base).await;
    assert_eq!(status, StatusCode::OK);

    // Land three real turns.
    for arg in [KP_PRESS_ON, KP_CLAIM_RED, KP_DESCEND] {
        let (s, body) = post(&app, &act, "choose", arg as i64, "alice").await;
        assert_eq!(s, StatusCode::OK);
        assert!(body.contains("Turn committed"), "move {arg} landed: {body}");
    }

    // The pre-restart observables: the rendered surface + the replay-verified turn count.
    let (_s, before_body) = get(&app, base).await;
    let (_s, before_verify) = get(&app, &verify).await;
    assert!(
        before_verify.contains("\"verified\":true"),
        "the played chain re-verifies before the restart: {before_verify}"
    );
    assert!(
        before_verify.contains("\"turns\":4"),
        "genesis + three landed turns: {before_verify}"
    );
    assert_ne!(
        before_body, genesis_body,
        "three landed moves changed the rendered surface — the survival equality below is non-vacuous"
    );

    // THE RESTART: a brand-new app + host over the SAME directory. Nothing in-memory survives;
    // the session must come back from the persisted move-log, by replay.
    let app2 = app_over(dir.clone());
    let (status, after_body) = get(&app2, base).await;
    assert_eq!(status, StatusCode::OK);
    assert_eq!(
        after_body, before_body,
        "the resumed session renders the IDENTICAL surface (not a fresh genesis)"
    );
    let (_s, after_verify) = get(&app2, &verify).await;
    assert!(
        after_verify.contains("\"verified\":true"),
        "the resumed chain re-verifies: {after_verify}"
    );
    assert!(
        after_verify.contains("\"turns\":4"),
        "the resumed session is at the SAME committed turn count: {after_verify}"
    );

    let _ = fs::remove_dir_all(&dir);
}

/// A TAMPERED persisted log (one byte flipped in its landed move) REFUSES to reopen on restart —
/// fail-closed, the file kept on disk — while the intact session in the same store still resumes
/// to its advanced (non-genesis) state.
#[tokio::test]
async fn a_tampered_log_refuses_to_reopen_and_the_rest_still_resume() {
    let dir = scratch_dir("tamper");
    {
        let app = app_over(dir.clone());
        for sid in ["t-good", "t-bad"] {
            let base = format!("/offerings/dungeon/session/{sid}");
            let (s, _) = get(&app, &base).await;
            assert_eq!(s, StatusCode::OK);
            let (s, body) = post(
                &app,
                &format!("{base}/act"),
                "choose",
                KP_PRESS_ON as i64,
                "alice",
            )
            .await;
            assert_eq!(s, StatusCode::OK);
            assert!(
                body.contains("Turn committed"),
                "{sid}'s move landed: {body}"
            );
        }
    }

    // Find t-bad's log file by its header line (`key \t id \t seed`) — file names are hashes.
    let mut bad_path: Option<PathBuf> = None;
    let mut n_logs = 0;
    for e in fs::read_dir(&dir).unwrap().flatten() {
        let p = e.path();
        if p.extension().and_then(|s| s.to_str()) != Some("log") {
            continue;
        }
        n_logs += 1;
        let text = fs::read_to_string(&p).unwrap();
        if text.lines().next().unwrap().split('\t').nth(1) == Some("t-bad") {
            bad_path = Some(p);
        }
    }
    assert_eq!(n_logs, 2, "both sessions persisted a log");
    let bad_path = bad_path.expect("t-bad's log file is identifiable by its header");

    // Tamper ONE byte: the landed move's turn verb (`\tchoose\t` → `\tchooze\t`, tab-delimited so
    // the flip is in the turn field, not the label). Structurally still a valid log line — the
    // refusal must come from the executor on re-drive, not from the codec.
    let text = fs::read_to_string(&bad_path).unwrap();
    let tampered = text.replacen("\tchoose\t", "\tchooze\t", 1);
    assert_ne!(tampered, text, "one byte flipped in the persisted move");
    fs::write(&bad_path, tampered).unwrap();

    // THE RESTART: build the resumed host directly, so the resume outcomes are observable.
    let host = demo_host_resumed_from(dir.clone());
    assert!(
        !host.is_open("dungeon", &SessionId::new("t-bad")),
        "the tampered log REFUSED to reopen (fail-closed) — no session left live under its id"
    );
    assert!(
        host.is_open("dungeon", &SessionId::new("t-good")),
        "the intact log still resumed"
    );
    assert!(
        bad_path.exists(),
        "the refused log file is KEPT on disk (evidence, never deleted by the boot resume)"
    );

    // The intact session resumed to its ADVANCED state (genesis + its landed move), verified.
    let report = host
        .verify("dungeon", &SessionId::new("t-good"))
        .expect("the resumed session re-verifies");
    assert!(report.verified, "the resumed chain verifies by replay");
    assert_eq!(report.turns, 2, "genesis + the one landed move survived");

    let _ = fs::remove_dir_all(&dir);
}
