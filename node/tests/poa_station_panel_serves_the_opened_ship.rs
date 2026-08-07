//! END-TO-END EXHIBIT: a crew member opens the crate through the WRITE route, and the public
//! READ route then serves THE SAME SHIP.
//!
//! # The gap this closes, measured
//!
//! Until 2026-08-07 the two halves disagreed over HTTP. `POST …/crate/open` served
//! `exact_total: 1, observed: 2`; `GET …/panel` served `exact_total: 0, observed: 0`, because
//! `POA-STATION-DAILY-1` had no field for the node's durable open log and so `servedState` had
//! nothing to fold. A player could open the crate and the page they looked at still said zero.
//!
//! Lean's `the_served_ship_has_not_been_moved` was advertised as the assertion that would go RED
//! the day a judged opening could be folded in. It did not, because it was never about
//! reachability — it was about the request type. It is retired, and
//! `the_served_ship_moves_when_the_log_records_an_opening` plus
//! `StationCrateOpenRuntime.the_station_read_serves_the_ship_this_write_published` replace it.
//! This file is the same claim against the REAL router, the REAL store and native Lean.
//!
//! # What makes this an exhibit rather than a coincidence
//!
//! Every assertion below is a comparison between two SERVED documents, not against numbers
//! written here. The read's gauges are asserted EQUAL to the write's gauges. A test that pinned
//! both to `1` would still pass if both organs were wrong in the same way; a test that pins them
//! to EACH OTHER is the loop.
//!
//! And the mutation is asserted before the verdict: the panel read BEFORE the open is captured
//! and required to differ from the one after it, so a read that ignored the log entirely (the
//! defect itself) cannot pass by serving a constant.
//!
//! # If this cannot run
//!
//! Both routes refuse with `503` when the linked archive lacks `dregg_poa_station_daily_read` or
//! `dregg_poa_crate_open`. That is a REAL failure of this exhibit, not a skip: there is no Rust
//! projection to fall back to and the assertions would be measuring nothing.

use axum::Router;
use axum::body::Body;
use axum::extract::ConnectInfo;
use axum::http::{Request, StatusCode, header};
use dregg_node::api::router;
use dregg_node::state::NodeState;
use dregg_types::hex_encode;
use http_body_util::BodyExt;
use tower::ServiceExt;

/// `SalvageCrateExamples.digest 41` — the crew key Lean proves draws the communal salvage on the
/// installed period.
const CREW_41: [u8; 32] = [0x29; 32];
/// `digest 40` — an authored row whose contribution is `Contribution.zero`.
const CREW_40: [u8; 32] = [0x28; 32];

const TEST_AUTHORITY: [u8; 32] = [0x41; 32];

async fn live_router() -> (Router, tempfile::TempDir) {
    let tmp = tempfile::tempdir().expect("tempdir");
    let state = NodeState::new(tmp.path(), vec![]).expect("node state");
    {
        let mut s = state.write().await;
        s.federation_id = TEST_AUTHORITY;
        s.federation_configured = true;
    }
    let recorder = metrics_exporter_prometheus::PrometheusBuilder::new().build_recorder();
    (router(state, false, recorder.handle()), tmp)
}

fn connect_info() -> ConnectInfo<std::net::SocketAddr> {
    ConnectInfo(
        "127.0.0.1:4444"
            .parse::<std::net::SocketAddr>()
            .expect("test client address"),
    )
}

async fn open_crate(app: &Router, opener: &[u8; 32]) -> (StatusCode, serde_json::Value) {
    let authority = hex_encode(&TEST_AUTHORITY);
    let body = format!(r#"{{"opener":"{}"}}"#, hex_encode(opener));
    let response = app
        .clone()
        .oneshot(
            Request::builder()
                .method("POST")
                .uri(format!("/api/poa/station/{authority}/crate/open"))
                .header(header::CONTENT_TYPE, "application/json")
                .extension(connect_info())
                .body(Body::from(body))
                .expect("request"),
        )
        .await
        .expect("response");
    collect(response).await
}

/// `GET /api/poa/station/{authority}/panel` — the public, unauthenticated read a page calls.
async fn read_panel(app: &Router) -> (StatusCode, serde_json::Value) {
    let authority = hex_encode(&TEST_AUTHORITY);
    let response = app
        .clone()
        .oneshot(
            Request::builder()
                .method("GET")
                .uri(format!("/api/poa/station/{authority}/panel"))
                .extension(connect_info())
                .body(Body::empty())
                .expect("request"),
        )
        .await
        .expect("response");
    collect(response).await
}

async fn collect(response: axum::response::Response) -> (StatusCode, serde_json::Value) {
    let status = response.status();
    let bytes = response
        .into_body()
        .collect()
        .await
        .expect("body")
        .to_bytes();
    let json = serde_json::from_slice(&bytes).unwrap_or(serde_json::Value::Null);
    (status, json)
}

/// ⭐ THE LOOP, END TO END. The crate is opened over HTTP and the public panel read then serves
/// the SAME gauges the open published — compared against each other, not against constants.
#[tokio::test]
async fn the_panel_serves_the_ship_the_crate_open_moved() {
    let (app, _tmp) = live_router().await;

    // ── BEFORE: the installed ship, and the log is empty ─────────────────────────────────────
    let (status, before) = read_panel(&app).await;
    assert_eq!(status, StatusCode::OK, "installed panel; body: {before}");
    println!(
        "PANEL BEFORE →\n{}",
        serde_json::to_string_pretty(&before).expect("pretty")
    );
    assert_eq!(before["format"], "POA-STATION-VIEW-1");
    assert_eq!(
        before["log_rows_folded"], 0,
        "the node has no open log yet, so the read folds nothing"
    );
    let installed = &before["station"];
    assert_eq!(installed["format"], "POA-STATION-DAILY-OUT-1");
    assert_eq!(installed["gauges"][0]["exact_total"], 0);
    assert_eq!(installed["gauges"][0]["shown"], 0);
    assert_eq!(installed["observed"], 0);
    assert_eq!(installed["admitted"], 0);
    assert_eq!(installed["recovered_kinds"], 0);

    // ── THE WRITE ────────────────────────────────────────────────────────────────────────────
    let (status, opened) = open_crate(&app, &CREW_41).await;
    assert_eq!(status, StatusCode::OK, "the open; body: {opened}");
    assert_eq!(opened["crate_open"]["opened"], true);
    assert_eq!(
        opened["log_appended"], true,
        "nothing was appended, so the read below would have nothing to fold and this test would \
         be measuring the installed ship twice"
    );
    let written = &opened["crate_open"]["panel"];
    println!(
        "WRITE PUBLISHED →\n{}",
        serde_json::to_string_pretty(written).expect("pretty")
    );

    // ── AFTER: the same public read, and it has MOVED ────────────────────────────────────────
    let (status, after) = read_panel(&app).await;
    assert_eq!(
        status,
        StatusCode::OK,
        "panel after the open; body: {after}"
    );
    println!(
        "PANEL AFTER →\n{}",
        serde_json::to_string_pretty(&after).expect("pretty")
    );
    let served = &after["station"];

    // The mutation is present and it is the log: one row folded, where there were none.
    assert_eq!(
        after["log_rows_folded"], 1,
        "the read must fold the row the open appended, or nothing below proves anything"
    );

    // ⭐ THE BAR. The read's communal figures ARE the write's, field for field. Neither side is
    // compared to a number written in this file.
    assert_eq!(
        served["gauges"], written["gauges"],
        "the panel read serves different gauges from the ones the open published"
    );
    assert_eq!(served["observed"], written["observed"]);
    assert_eq!(served["admitted"], written["admitted"]);
    assert_eq!(served["recovered_kinds"], written["recovered_kinds"]);

    // And it is a MOVE, not two agreeing zeros — the read genuinely differs from the ship it
    // served before the open, which is the whole defect this closes.
    assert_ne!(
        served["gauges"], installed["gauges"],
        "the panel served the same gauges before and after an accepted open: the read is not \
         folding the log"
    );
    assert_eq!(served["gauges"][0]["exact_total"], 1);
    assert_eq!(served["gauges"][0]["shown"], 1);
    assert_eq!(served["observed"], 1);
    assert_eq!(served["admitted"], 1);
    assert_eq!(served["recovered_kinds"], 1);

    // The read stays COMMUNAL: no per-player field appears because one crew member opened.
    assert!(
        served["crew"].is_null(),
        "the communal panel named a crew member"
    );

    // The standing claim no longer says openings are impossible.
    let write_path = after["write_path"].as_str().expect("write path claim");
    assert!(
        write_path.contains("DURABLE OPEN LOG"),
        "the served claim does not say the gauges are a fold of the log: {write_path}"
    );
    assert!(
        !write_path.contains("no judged opening exists"),
        "the served claim still says no judged opening exists: {write_path}"
    );
}

/// ⭐ THE SHIP ACCUMULATES ON THE PUBLIC READ TOO. Two crew members open; the panel a page reads
/// shows two arrivals and the one salvage draw — the communal aggregate, still unattributed.
#[tokio::test]
async fn the_panel_accumulates_the_whole_crew() {
    let (app, _tmp) = live_router().await;

    let (_, first) = open_crate(&app, &CREW_41).await;
    assert_eq!(first["crate_open"]["opened"], true);
    let (_, second) = open_crate(&app, &CREW_40).await;
    assert_eq!(second["crate_open"]["opened"], true);
    let written = &second["crate_open"]["panel"];

    let (status, after) = read_panel(&app).await;
    assert_eq!(status, StatusCode::OK, "body: {after}");
    println!(
        "PANEL AFTER TWO OPENS →\n{}",
        serde_json::to_string_pretty(&after).expect("pretty")
    );
    let served = &after["station"];

    assert_eq!(after["log_rows_folded"], 2);
    assert_eq!(served["gauges"], written["gauges"]);
    assert_eq!(served["observed"], written["observed"]);
    assert_eq!(served["admitted"], written["admitted"]);
    // Two arrivals, one draw: crew 40's authored row contributes zero.
    assert_eq!(served["observed"], 2);
    assert_eq!(served["admitted"], 2);
    assert_eq!(served["gauges"][0]["exact_total"], 1);
    assert!(served["crew"].is_null());
}

/// The fold is durable: a fresh router over the SAME data directory serves the moved ship, because
/// the ship is not held in memory anywhere — it is recomputed from the log every read.
#[tokio::test]
async fn the_served_ship_survives_a_restart() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let recorder = metrics_exporter_prometheus::PrometheusBuilder::new().build_recorder();

    let published = {
        let state = NodeState::new(tmp.path(), vec![]).expect("node state");
        {
            let mut s = state.write().await;
            s.federation_id = TEST_AUTHORITY;
            s.federation_configured = true;
        }
        let app = router(state, false, recorder.handle());
        let (status, opened) = open_crate(&app, &CREW_41).await;
        assert_eq!(status, StatusCode::OK, "body: {opened}");
        assert_eq!(opened["crate_open"]["opened"], true);
        assert_eq!(opened["log_appended"], true);
        opened["crate_open"]["panel"].clone()
    };

    // A second NodeState over the same directory — the store is reopened from disk.
    let state = NodeState::new(tmp.path(), vec![]).expect("reopened node state");
    {
        let mut s = state.write().await;
        s.federation_id = TEST_AUTHORITY;
        s.federation_configured = true;
    }
    let recorder = metrics_exporter_prometheus::PrometheusBuilder::new().build_recorder();
    let app = router(state, false, recorder.handle());

    let (status, after) = read_panel(&app).await;
    assert_eq!(status, StatusCode::OK, "body: {after}");
    println!(
        "PANEL AFTER REOPEN →\n{}",
        serde_json::to_string_pretty(&after).expect("pretty")
    );
    assert_eq!(after["log_rows_folded"], 1);
    assert_eq!(after["station"]["gauges"], published["gauges"]);
    assert_eq!(after["station"]["observed"], published["observed"]);
}

/// ⚠ A LOG THIS NODE DID NOT WRITE IS A REFUSAL, NEVER A PAGE OF ZEROS.
///
/// The two readings are indistinguishable to a player — both say "nothing has moved the ship" —
/// so the route must not serve the installed ship when the durable blob is unreadable. The
/// mutation is asserted to be one: the same store serves a real panel before the blob is
/// corrupted.
#[tokio::test]
async fn a_corrupt_open_log_refuses_rather_than_serving_the_installed_ship() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let state = NodeState::new(tmp.path(), vec![]).expect("node state");
    let store = {
        let mut s = state.write().await;
        s.federation_id = TEST_AUTHORITY;
        s.federation_configured = true;
        s.store.clone()
    };
    let recorder = metrics_exporter_prometheus::PrometheusBuilder::new().build_recorder();
    let app = router(state, false, recorder.handle());

    // The honest pole: this store serves a document.
    let (status, honest) = read_panel(&app).await;
    assert_eq!(status, StatusCode::OK, "body: {honest}");
    assert_eq!(honest["station"]["gauges"][0]["exact_total"], 0);

    // The mutation, applied and asserted: a blob under the log's own key that this node could
    // not have written.
    let key = format!("poa_crate_open_log:v1:{}", hex_encode(&TEST_AUTHORITY));
    store
        .set_config(&key, b"NOTALOG1garbage")
        .expect("write the corrupt blob");
    assert_eq!(
        store
            .get_config(&key)
            .expect("read back")
            .expect("the blob is present"),
        b"NOTALOG1garbage".to_vec(),
        "the mutation did not land, so the refusal below would prove nothing"
    );

    let (status, refused) = read_panel(&app).await;
    println!(
        "PANEL OVER A CORRUPT LOG →\n{}",
        serde_json::to_string_pretty(&refused).expect("pretty")
    );
    assert_eq!(
        status,
        StatusCode::INTERNAL_SERVER_ERROR,
        "a corrupt log was served as a readable panel: {refused}"
    );
    assert_eq!(refused["refused"], "log-unreadable");
    // Not a single gauge is published on the refusal path.
    assert!(refused["station"].is_null());
}
