//! END-TO-END EXHIBIT: a crew member opens the daily salvage crate THROUGH THE ROUTE, the communal
//! gauges move, and a second open of the same period is REFUSED.
//!
//! This drives the REAL axum router (`dregg_node::api::router`), the real bearer layer, the real
//! `PersistentStore`, and native Lean. Nothing here is a re-implementation: every number asserted
//! below is a field of the exact `POA-CRATE-OPEN-OUT-1` document
//! `Dregg2.Games.PathOfAngels.StationCrateOpenRuntime` emitted.
//!
//! # The mutation is asserted before the verdict is read
//!
//! The ONLY difference between the two requests is the node's durable open log: empty for the
//! first, one row for the second. The test asserts that the first open actually appended
//! (`log_appended: true`) and that the second replayed a one-row log (`log_rows_replayed: 1`)
//! BEFORE it looks at the refusal — so a refusal that came from a broken transport rather than from
//! `SalvageCrate`'s append-only `consumed` set cannot pass.
//!
//! # If this cannot run
//!
//! The crate-open route refuses with `503 lean-crate-open-absent` when the linked archive has no
//! `dregg_poa_crate_open`. That is a REAL failure of this exhibit, not a skip: there is no Rust
//! ceremony to fall back to and the assertions below would be measuring nothing.

use axum::Router;
use axum::body::Body;
use axum::extract::ConnectInfo;
use axum::http::{Request, StatusCode, header};
use dregg_node::api::router;
use dregg_node::state::NodeState;
use dregg_types::hex_encode;
use http_body_util::BodyExt;
use tower::ServiceExt;

/// The authored crew: `SalvageCrateExamples.digest 41` is 32 bytes of `41 % 256 = 0x29`, and it is
/// the crew key `StationCrateOpen.an_honest_salvage_open_moves_the_supplies_gauge` proves draws the
/// communal salvage on the installed period.
const CREW_41: [u8; 32] = [0x29; 32];
/// `digest 40` — the crew key whose authored row carries `Contribution.zero`.
const CREW_40: [u8; 32] = [0x28; 32];
/// Not on the curator's roster (`{digest 40, digest 41, digest 42}`).
const STOWAWAY: [u8; 32] = [0x4d; 32];

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
                .extension(ConnectInfo(
                    "127.0.0.1:4444"
                        .parse::<std::net::SocketAddr>()
                        .expect("test client address"),
                ))
                .body(Body::from(body))
                .expect("request"),
        )
        .await
        .expect("response");
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

/// ⭐ THE RITUAL, END TO END. Crew 41 opens the crate through the authenticated route and the
/// communal supplies gauge advances by exactly the drawn contribution; the same crew member opening
/// the same period again is REFUSED, with no gauge in the refusal.
#[tokio::test]
async fn a_crate_opened_through_the_route_moves_the_gauges_and_refuses_the_second_open() {
    let (app, _tmp) = live_router().await;

    // ── POLE ONE: the open ────────────────────────────────────────────────────────────────────
    let (status, first) = open_crate(&app, &CREW_41).await;
    assert_eq!(
        status,
        StatusCode::OK,
        "the crate open must reach Lean; body: {first}"
    );
    println!(
        "FIRST OPEN →\n{}",
        serde_json::to_string_pretty(&first).expect("pretty")
    );

    assert_eq!(first["format"], "POA-CRATE-OPEN-VIEW-1");
    assert_eq!(first["authority_id"], hex_encode(&TEST_AUTHORITY));
    // The mutation, asserted before the verdict below is read: the first open replayed an EMPTY log
    // and the node really did append its row.
    assert_eq!(first["log_rows_replayed"], 0);
    assert_eq!(first["log_appended"], true);

    let opened = &first["crate_open"];
    assert_eq!(opened["format"], "POA-CRATE-OPEN-OUT-1");
    assert_eq!(opened["opened"], true);
    assert!(opened["refusal"].is_null());
    assert_eq!(opened["opener"], hex_encode(&CREW_41));
    // The period is the INSTALLED one — the first authored beacon — and it came from the crate
    // state, not from the request (the wire has no period field at all).
    assert_eq!(opened["period"], 31);

    // The drawn row: the communal-salvage entry of the authored table, one supply.
    assert_eq!(opened["entry"]["id"], 13);
    assert_eq!(opened["entry"]["prize"], "communal-salvage:55");
    assert_eq!(opened["entry"]["supplies"], 1);

    // ⭐ THE SHIP MOVED. One dial, exact total 1, one recovered kind, one observed receipt.
    let panel = &opened["panel"];
    assert_eq!(panel["gauges"][0]["gauge"], 1);
    assert_eq!(panel["gauges"][0]["meter"], "supplies");
    assert_eq!(panel["gauges"][0]["exact_total"], 1);
    assert_eq!(panel["gauges"][0]["full_at"], 64);
    assert_eq!(panel["gauges"][0]["shown"], 1);
    assert_eq!(panel["gauges"][0]["at_full"], false);
    assert_eq!(panel["recovered_kinds"], 1);
    assert_eq!(panel["observed"], 1);
    assert_eq!(panel["admitted"], 1);

    // ── POLE TWO: the replay ──────────────────────────────────────────────────────────────────
    let (status, second) = open_crate(&app, &CREW_41).await;
    assert_eq!(
        status,
        StatusCode::OK,
        "the refusal is a document, not a 5xx"
    );
    println!(
        "SECOND OPEN (same crew, same period) →\n{}",
        serde_json::to_string_pretty(&second).expect("pretty")
    );

    // The mutation is present: this open replayed the ONE row the first open appended.
    assert_eq!(
        second["log_rows_replayed"], 1,
        "the second open must replay the row the first appended, or the refusal proves nothing"
    );
    assert_eq!(second["log_appended"], false);

    let refused = &second["crate_open"];
    assert_eq!(refused["format"], "POA-CRATE-OPEN-OUT-1");
    assert_eq!(refused["opened"], false);
    assert_eq!(refused["refusal"], "already-opened-this-period");
    assert_eq!(refused["period"], 31);
    // ⭐ A refusal carries NO gauge and NO entry — Lean's
    // `a_refused_open_publishes_no_gauge_and_no_entry`, on the wire.
    assert!(refused["panel"].is_null());
    assert!(refused["entry"].is_null());
}

/// ⭐ The ship is COMMUNAL and it ACCUMULATES: a second crew member opening the same period is
/// admitted, is counted, and sees the salvage the first crew member drew — which they did not draw
/// themselves.
#[tokio::test]
async fn a_second_crew_member_sees_the_ship_the_first_one_moved() {
    let (app, _tmp) = live_router().await;

    let (status, first) = open_crate(&app, &CREW_41).await;
    assert_eq!(status, StatusCode::OK, "first open; body: {first}");
    assert_eq!(first["crate_open"]["opened"], true);
    assert_eq!(first["crate_open"]["panel"]["gauges"][0]["exact_total"], 1);
    assert_eq!(first["log_appended"], true);

    let (status, second) = open_crate(&app, &CREW_40).await;
    assert_eq!(status, StatusCode::OK, "second crew member; body: {second}");
    println!(
        "SECOND CREW MEMBER →\n{}",
        serde_json::to_string_pretty(&second).expect("pretty")
    );

    let opened = &second["crate_open"];
    assert_eq!(opened["opened"], true);
    // Their OWN draw is an ordinary one: an account record, zero supplies.
    assert_eq!(opened["entry"]["supplies"], 0);
    // And yet the ship they see carries the salvage crew 41 drew. Two arrivals, one draw.
    assert_eq!(opened["panel"]["gauges"][0]["exact_total"], 1);
    assert_eq!(opened["panel"]["recovered_kinds"], 1);
    assert_eq!(opened["panel"]["observed"], 2);
    assert_eq!(opened["panel"]["admitted"], 2);
    assert_eq!(second["log_rows_replayed"], 1);
    assert_eq!(second["log_appended"], true);
}

/// A crew key the curator never enrolled is refused BY NAME, and nothing is appended. The poles
/// above show the same empty log admits an enrolled crew key, so this is the roster refusing rather
/// than the transport failing.
#[tokio::test]
async fn a_stowaway_is_refused_and_never_reaches_the_log() {
    let (app, _tmp) = live_router().await;

    let (status, body) = open_crate(&app, &STOWAWAY).await;
    assert_eq!(status, StatusCode::OK, "body: {body}");
    println!(
        "STOWAWAY →\n{}",
        serde_json::to_string_pretty(&body).expect("pretty")
    );
    assert_eq!(body["crate_open"]["opened"], false);
    assert_eq!(body["crate_open"]["refusal"], "ineligible-crew");
    assert!(body["crate_open"]["panel"].is_null());
    assert_eq!(body["log_appended"], false);

    // The log is untouched, so an enrolled crew member still opens against an EMPTY log.
    let (status, honest) = open_crate(&app, &CREW_41).await;
    assert_eq!(status, StatusCode::OK, "body: {honest}");
    assert_eq!(honest["log_rows_replayed"], 0);
    assert_eq!(honest["crate_open"]["opened"], true);
}

/// The durable log really is durable: a fresh router over the SAME data directory replays the row
/// the first process appended, and refuses the replay. This is the half of
/// `the_replay_guard_is_exactly_as_strong_as_the_node_log` that lives in storage rather than in
/// Lean.
#[tokio::test]
async fn the_open_log_survives_a_restart_and_still_refuses_the_replay() {
    let tmp = tempfile::tempdir().expect("tempdir");

    {
        let state = NodeState::new(tmp.path(), vec![]).expect("node state");
        {
            let mut s = state.write().await;
            s.federation_id = TEST_AUTHORITY;
            s.federation_configured = true;
        }
        let recorder = metrics_exporter_prometheus::PrometheusBuilder::new().build_recorder();
        let app = router(state, false, recorder.handle());
        let (status, first) = open_crate(&app, &CREW_41).await;
        assert_eq!(status, StatusCode::OK, "body: {first}");
        assert_eq!(first["crate_open"]["opened"], true);
        assert_eq!(first["log_appended"], true);
    }

    // A second NodeState over the same directory — the store is reopened from disk.
    let state = NodeState::new(tmp.path(), vec![]).expect("reopened node state");
    {
        let mut s = state.write().await;
        s.federation_id = TEST_AUTHORITY;
        s.federation_configured = true;
    }
    let recorder = metrics_exporter_prometheus::PrometheusBuilder::new().build_recorder();
    let app = router(state, false, recorder.handle());

    let (status, after) = open_crate(&app, &CREW_41).await;
    assert_eq!(status, StatusCode::OK, "body: {after}");
    println!(
        "AFTER REOPEN →\n{}",
        serde_json::to_string_pretty(&after).expect("pretty")
    );
    assert_eq!(
        after["log_rows_replayed"], 1,
        "the reopened store must still hold the appended row"
    );
    assert_eq!(after["crate_open"]["opened"], false);
    assert_eq!(after["crate_open"]["refusal"], "already-opened-this-period");
}

/// Malformed selectors are refused before anything is replayed, and the refusal body never mirrors
/// unparsed path or body bytes back.
#[tokio::test]
async fn malformed_selectors_are_refused_without_touching_the_log() {
    let (app, _tmp) = live_router().await;
    let authority = hex_encode(&TEST_AUTHORITY);

    // ⚑ The mutation must BE one. `CREW_41` is `0x29` repeated, which spells `29…` — all digits,
    // nothing to upper-case — so casing it is a no-op and the "hostile" request is the honest one.
    // `STOWAWAY` is `0x4d`, which spells `4d…` and really does change.
    let lowercase = hex_encode(&STOWAWAY);
    let uppercase = lowercase.to_uppercase();
    assert_ne!(
        uppercase, lowercase,
        "the upper-case mutation must actually change the wire"
    );
    let response = app
        .clone()
        .oneshot(
            Request::builder()
                .method("POST")
                .uri(format!("/api/poa/station/{authority}/crate/open"))
                .header(header::CONTENT_TYPE, "application/json")
                .extension(ConnectInfo(
                    "127.0.0.1:4444"
                        .parse::<std::net::SocketAddr>()
                        .expect("test client address"),
                ))
                .body(Body::from(format!(r#"{{"opener":"{uppercase}"}}"#)))
                .expect("request"),
        )
        .await
        .expect("response");
    assert_eq!(response.status(), StatusCode::BAD_REQUEST);

    // An unknown body field — the shape an attempt to smuggle a period or a contribution takes.
    let response = app
        .clone()
        .oneshot(
            Request::builder()
                .method("POST")
                .uri(format!("/api/poa/station/{authority}/crate/open"))
                .header(header::CONTENT_TYPE, "application/json")
                .extension(ConnectInfo(
                    "127.0.0.1:4444"
                        .parse::<std::net::SocketAddr>()
                        .expect("test client address"),
                ))
                .body(Body::from(format!(
                    r#"{{"opener":"{}","period":31}}"#,
                    hex_encode(&CREW_41)
                )))
                .expect("request"),
        )
        .await
        .expect("response");
    assert_eq!(
        response.status(),
        StatusCode::UNPROCESSABLE_ENTITY,
        "the request body denies unknown fields"
    );

    // After both refusals the log is still empty.
    let (status, honest) = open_crate(&app, &CREW_41).await;
    assert_eq!(status, StatusCode::OK, "body: {honest}");
    assert_eq!(honest["log_rows_replayed"], 0);
    assert_eq!(honest["crate_open"]["opened"], true);
}
