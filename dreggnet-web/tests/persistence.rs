//! DRIVEN persistence + run-ingest tests for the public-demo Descent board — the Phase-0 finish.
//!
//! The committed `tests/server.rs` proves the in-RAM demo. This drives the two new deliverables end
//! to end, node-free (axum `ServiceExt::oneshot`):
//!  1. **SQLITE PERSISTENCE** — a submitted run SURVIVES a simulated restart: the store is dropped
//!     and reopened over the SAME file, and the run re-loads, re-verifies by replay, and still
//!     ranks. A TAMPERED row (a persisted move line that no longer re-executes to the win) is
//!     DROPPED on boot — it cannot resurrect a cheat, while the honest run survives (non-vacuous).
//!  2. **THE HTTP RUN-INGEST ENDPOINT** — `POST /descent/submit` accepts an honest run (verify-gated
//!     — it then appears on the leaderboard) and REJECTS a forged / incomplete run (`400`, never
//!     ranked). Fail-closed.

use axum::body::Body;
use axum::http::{Request, StatusCode};
use dreggnet_web::descent_store::{DescentRunStore, SqliteDescentRunStore, StoredRun};
use dreggnet_web::{DescentState, build_demo_descent, demo_win, make_app_with_descent};
use std::sync::Arc;
use tower::ServiceExt; // oneshot

// ── HTTP driving helpers (no real network) ────────────────────────────────────────────

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

/// **Does `player` actually RANK on this leaderboard?** — i.e. does the board carry a ranked row
/// whose player cell is that name.
///
/// A bare `board.contains("eve")` cannot answer that: the page is a whole HTML document, so the
/// name only has to appear *somewhere* — and `eve` is a substring of ordinary English ("every",
/// "never") and of the CSS property `pointer-events`, both of which legitimately occur in the
/// inlined stylesheet. That made the negative assertion pass for a reason unrelated to ranking, and
/// fail the moment the page's prose or CSS changed. Matching the rendered player cell asks the
/// question the test means to ask, and cannot be satisfied by the page's chrome.
fn ranks(board: &str, player: &str) -> bool {
    board.contains(&format!("class=\"player\">{player}<"))
}

async fn post_json(app: &axum::Router, uri: &str, body: serde_json::Value) -> (StatusCode, String) {
    let resp = app
        .clone()
        .oneshot(
            Request::builder()
                .method("POST")
                .uri(uri)
                .header("content-type", "application/json")
                .body(Body::from(body.to_string()))
                .unwrap(),
        )
        .await
        .unwrap();
    let status = resp.status();
    let bytes = axum::body::to_bytes(resp.into_body(), usize::MAX)
        .await
        .unwrap();
    (status, String::from_utf8(bytes.to_vec()).unwrap())
}

/// A unique temp sqlite path (removed if a stale one exists), for the survives-restart tests.
fn temp_db(tag: &str) -> String {
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let path = std::env::temp_dir().join(format!(
        "dreggnet-web-{tag}-{}-{nanos}.db",
        std::process::id()
    ));
    let _ = std::fs::remove_file(&path);
    path.to_string_lossy().into_owned()
}

// ── 1. SQLITE PERSISTENCE — survives restart, re-verified on boot, tamper-safe ─────────

/// A submitted run round-trips through sqlite and SURVIVES a simulated restart: boot-1 opens the
/// day + submits a real winning run (persisted), the store is dropped, and a FRESH boot-2 state
/// (over the SAME file) reconstructs + re-verifies it by replay — it re-loads and still ranks.
#[tokio::test]
async fn a_persisted_run_survives_restart_and_reverifies_on_boot() {
    let url = temp_db("survive");
    let (win_moves, _lvl, _cls) = demo_win();

    // ── boot 1 — seed the demo board over a durable store, then submit a real winning run.
    {
        let store = Arc::new(SqliteDescentRunStore::open(&url).unwrap());
        let state = build_demo_descent(Some(store)); // opens + persists "today" + the demo winner
        let turns = state
            .submit_run("today", "alice-run", "alice", 5, 2, &win_moves)
            .expect("the honest winning run is accepted + persisted");
        assert!(turns > 0, "the run verified to a positive turn count");
        // state (and its store handle) drop here — the process "restarts".
    }

    // ── boot 2 — a FRESH, EMPTY state over a NEW store on the SAME file: load ONLY.
    let store2 = Arc::new(SqliteDescentRunStore::open(&url).unwrap());
    let state2 = Arc::new(DescentState::with_store(store2));
    state2.load_from_store(); // reconstruct the day + re-verify the persisted runs by replay
    let app = make_app_with_descent(state2);

    let (status, board) = get(&app, "/descent/leaderboard?day=today").await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        board.contains("alice"),
        "the submitted run SURVIVED the restart + re-verified + ranks: {board}"
    );
    assert!(
        board.contains("ember"),
        "the seeded demo winner also survived: {board}"
    );
    let _ = std::fs::remove_file(&url);
}

/// A TAMPERED row (a persisted move line that no longer re-executes to the win) is DROPPED on boot,
/// while the honest run survives — non-vacuous: the honest player is present, the cheat is not.
#[tokio::test]
async fn a_tampered_row_is_dropped_on_boot() {
    let url = temp_db("tamper");
    let (win_moves, _lvl, _cls) = demo_win();

    // ── boot 1 — a valid board (day + honest winner persisted), then INJECT a bad row straight
    // into the DB: an incomplete move line that never re-executes to the hoard (as a tampered /
    // forged row that bypassed the verify-gate would look).
    {
        let store = Arc::new(SqliteDescentRunStore::open(&url).unwrap());
        let _state = build_demo_descent(Some(store.clone())); // persists "today" + demo winner
        let mut losing = win_moves.clone();
        losing.pop(); // drop the final seizing move — reaches the hoard-gate but never wins
        store
            .persist_run(&StoredRun {
                run_id: "cheat".to_string(),
                day_key: "today".to_string(),
                player: "cheater".to_string(),
                level: 1,
                class: 0,
                moves_json: serde_json::to_string(&losing).unwrap(),
            })
            .unwrap();
    }

    // ── boot 2 — reconstruct + re-verify from the tampered DB.
    let store2 = Arc::new(SqliteDescentRunStore::open(&url).unwrap());
    let state2 = Arc::new(DescentState::with_store(store2));
    state2.load_from_store();
    let app = make_app_with_descent(state2);

    let (status, board) = get(&app, "/descent/leaderboard?day=today").await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        !board.contains("cheater"),
        "the tampered row was DROPPED on boot — it cannot resurrect a cheat: {board}"
    );
    assert!(
        board.contains("ember"),
        "the honest run survived the tamper-drop (non-vacuous): {board}"
    );
    let _ = std::fs::remove_file(&url);
}

// ── 2. THE HTTP RUN-INGEST ENDPOINT — verify-gated, fail-closed ────────────────────────

/// `POST /descent/submit` accepts an HONEST run (verify-gated) — it ingests, ranks, and persists —
/// and REJECTS a forged / incomplete run (`400`, never ranked). The whole point: a stranger can add
/// a run to the no-cheat board over HTTP, but only a run that provably reaches the hoard.
#[tokio::test]
async fn the_run_ingest_endpoint_accepts_honest_and_rejects_forged() {
    let store = Arc::new(SqliteDescentRunStore::open(":memory:").unwrap());
    let state = build_demo_descent(Some(store));
    let app = make_app_with_descent(state);
    let (win_moves, _lvl, _cls) = demo_win();

    // ── an HONEST run — the full winning line — is accepted + ranks.
    let (status, body) = post_json(
        &app,
        "/descent/submit",
        serde_json::json!({
            "day": "today",
            "player": "zoe",
            "level": 3,
            "class": 1,
            "moves": win_moves,
        }),
    )
    .await;
    assert_eq!(status, StatusCode::OK, "an honest run is ingested: {body}");
    assert!(
        body.contains("\"ranked\":true"),
        "the honest run is ranked: {body}"
    );
    assert!(
        body.contains("sub-"),
        "a shareable run id is returned: {body}"
    );

    let (_, board) = get(&app, "/descent/leaderboard?day=today").await;
    assert!(
        ranks(&board, "zoe"),
        "the ingested honest run now appears on the leaderboard: {board}"
    );

    // ── a FORGED / incomplete run — the winning line minus its final move — is REJECTED 4xx.
    let mut incomplete = win_moves.clone();
    incomplete.pop();
    let (status, body) = post_json(
        &app,
        "/descent/submit",
        serde_json::json!({
            "day": "today",
            "player": "mallory",
            "moves": incomplete,
        }),
    )
    .await;
    assert_eq!(
        status,
        StatusCode::BAD_REQUEST,
        "an incomplete run is rejected 4xx: {body}"
    );
    assert!(
        body.contains("\"ranked\":false"),
        "the rejected run is not ranked: {body}"
    );

    // ── an ILLEGAL move (an out-of-range choice index) is also refused before it can rank.
    let mut illegal = win_moves.clone();
    illegal.push(99);
    let (status, _body) = post_json(
        &app,
        "/descent/submit",
        serde_json::json!({ "day": "today", "player": "eve", "moves": illegal }),
    )
    .await;
    assert_eq!(
        status,
        StatusCode::BAD_REQUEST,
        "an illegal move is refused by the real executor on replay"
    );

    // ── the forgers never made it onto the no-cheat board.
    let (_, board) = get(&app, "/descent/leaderboard?day=today").await;
    assert!(
        !ranks(&board, "mallory") && !ranks(&board, "eve"),
        "no forged run ranks (fail-closed): {board}"
    );
}

/// `make_app_with_descent` over a sqlite-backed state serves the persisted, re-verified leaderboard
/// through the full merged app (the honest demo winner ranks; the seeded forgery is excluded).
#[tokio::test]
async fn make_app_over_a_sqlite_store_serves_the_persisted_board() {
    let store = Arc::new(SqliteDescentRunStore::open(":memory:").unwrap());
    let app = make_app_with_descent(build_demo_descent(Some(store)));

    let (status, board) = get(&app, "/descent/leaderboard").await;
    assert_eq!(status, StatusCode::OK);
    assert!(
        board.contains("ember"),
        "the verified winner ranks: {board}"
    );
    assert!(
        !board.contains("a-forger"),
        "the forgery is excluded from the no-cheat board: {board}"
    );
}
