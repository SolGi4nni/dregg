//! discharge_replay_e2e.rs — DOES `/api/discharge` REFUSE WHEN IT CANNOT KNOW?
//!
//! The discharge gateway's only defence against a reused third-party ticket is
//! its replay set, and that set lives under a store config key
//! (`discharge_issued_set`). Two silent fail-opens sat on that key until
//! 2026-08-05, three lines apart, both of them able to hand out a discharge the
//! node could not account for:
//!
//!   [1] **the load** was `if let Ok(Some(data)) = s.store.get_config(..)` with
//!       NO `else`. A store *error* — no answer at all — took the same branch as
//!       "nothing has ever been persisted", so the gateway was built with an
//!       EMPTY replay set and every ticket this node ever discharged became
//!       discharge-able again. Nothing was logged; nothing was metered.
//!
//!   [2] **the store** warned and returned `success: true`, under a comment that
//!       named the hazard itself: *"A crash between discharge issuance and
//!       shutdown would otherwise lose the replay set, enabling ticket reuse."*
//!       The discharge went out over a burn that was never made durable.
//!
//!   [2b] and the burn was only persisted on the SUCCESS arm, while
//!        `DischargeGateway::process_request` burns a ticket on PRESENTATION —
//!        before any condition is evaluated. A ticket denied for a bad proof was
//!        burned in RAM and not on disk, so a restart resurrected it.
//!
//! A third sat one layer down: `load_issued_set` returned `()` and, per its own
//! docstring, "silently ignored" a blob whose length was not a multiple of 32 —
//! leaving the set empty for exactly the corrupted-store case that most needs it
//! to be complete.
//!
//! These tests drive the REAL router and force each failure through the
//! `fail_config_io` seam on `PersistentStore`. Every one asserts the refusal
//! FIRES (503, no discharge in the body), and every one is paired with the
//! honest path still working — a fail-closed gate that also refuses the happy
//! case is not a gate, it is an outage.
//!
//! The canary: delete either refusal and the matching test goes red on a
//! `200 OK` carrying a discharge macaroon, not on a log line.

#![cfg(test)]

use axum::body::Body;
use axum::extract::ConnectInfo;
use axum::http::{Request, StatusCode};
use http_body_util::BodyExt;
use tower::ServiceExt;

use base64::Engine;

use crate::state::NodeState;

/// Stand up a node + the real router, and return the pieces a discharge test
/// needs: the state, the app, the gateway's shared key + location (derived
/// exactly as `post_discharge` derives them), and the store to fault-inject on.
async fn discharge_node() -> (
    axum::Router,
    [u8; 32],
    String,
    std::sync::Arc<dregg_persist::PersistentStore>,
    tempfile::TempDir,
) {
    let _ = rustls::crypto::ring::default_provider().install_default();
    let _ = crate::install_mldsa_verified_keygen_core_real();
    let _ = crate::install_mldsa_verified_sign_core_real();
    let _ = crate::install_mldsa_verified_verify_core();
    let tmp = tempfile::tempdir().expect("tempdir");
    let state = NodeState::new(tmp.path(), vec![]).expect("build NodeState");

    let (gateway_key, location, store) = {
        let mut s = state.write().await;
        // `/api/discharge` returns 403 unless the node is unlocked.
        s.unlocked = true;
        let key = s.cclerk.derive_symmetric_key("dregg-discharge-gateway-v1");
        let location = format!(
            "dregg-node://{}",
            dregg_types::hex_encode(&s.cclerk.public_key().0)
        );
        (key, location, s.store.clone())
    };

    let recorder = metrics_exporter_prometheus::PrometheusBuilder::new().build_recorder();
    let app = crate::api::router(state.clone(), false, recorder.handle());
    (app, gateway_key, location, store, tmp)
}

/// Mint a fresh third-party ticket addressed to this node's gateway. Each call
/// uses a fresh root key, so each ticket is a DISTINCT entry in the replay set.
fn fresh_ticket(shared_key: &[u8; 32], location: &str) -> String {
    let root_key = [7u8; 32];
    let mut mac = dregg_macaroon::Macaroon::new(
        &root_key,
        // The kid varies per call so the derived ticket does too.
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("clock")
            .as_nanos()
            .to_le_bytes()
            .to_vec(),
        "https://issuer.test".into(),
    );
    mac.add_third_party(location, shared_key, dregg_macaroon::CaveatSet::new())
        .expect("add 3P caveat");
    let tp_caveats = mac.caveats.third_party_caveats();
    let tp = dregg_macaroon::ThirdPartyCaveat::decode_body(&tp_caveats[0].body).expect("3P body");
    base64::engine::general_purpose::STANDARD.encode(&tp.ticket)
}

/// `POST /api/discharge` through the real router; returns (status, parsed body).
/// The body is `None` for a non-200 (the refusals carry no JSON).
async fn post_discharge(
    app: &axum::Router,
    ticket_b64: &str,
) -> (StatusCode, Option<serde_json::Value>) {
    let addr: std::net::SocketAddr = "127.0.0.1:4545".parse().unwrap();
    let body = serde_json::json!({
        "ticket": ticket_b64,
        // The default evaluator is `ProofRequiredEvaluator`: a non-empty proof
        // blob is what makes the HONEST path succeed, so every one of these
        // requests is one that WOULD be served if the store were healthy.
        "proof": base64::engine::general_purpose::STANDARD.encode([0xABu8; 96]),
    });
    let response = app
        .clone()
        .oneshot(
            Request::builder()
                .method("POST")
                .uri("/api/discharge")
                .header("content-type", "application/json")
                .extension(ConnectInfo(addr))
                .body(Body::from(serde_json::to_vec(&body).unwrap()))
                .expect("discharge request"),
        )
        .await
        .expect("discharge response");
    let status = response.status();
    if status != StatusCode::OK {
        return (status, None);
    }
    let bytes = response
        .into_body()
        .collect()
        .await
        .expect("body")
        .to_bytes();
    (status, Some(serde_json::from_slice(&bytes).expect("json")))
}

/// [1] An UNREADABLE replay set must refuse, not start from empty.
///
/// This is the one with the named, reachable consequence. The gateway is
/// constructed lazily on the first request, and that is the only moment the
/// persisted set is read — so a store error there decided the replay set for the
/// whole process lifetime.
#[tokio::test]
async fn unreadable_replay_set_refuses_instead_of_discharging_on_an_empty_one() {
    let (app, key, location, store, _tmp) = discharge_node().await;

    // ── THE REFUSAL FIRES: the store cannot answer, so the node does not serve.
    store.set_fail_config_io(true);
    let (status, body) = post_discharge(&app, &fresh_ticket(&key, &location)).await;
    assert_eq!(
        status,
        StatusCode::SERVICE_UNAVAILABLE,
        "a gateway that cannot read its replay set must refuse; it answered {body:?}"
    );

    // ── COMPLETENESS: with the store healthy, the same request is served.
    store.set_fail_config_io(false);
    let (status, body) = post_discharge(&app, &fresh_ticket(&key, &location)).await;
    assert_eq!(status, StatusCode::OK, "the honest path must still work");
    let body = body.expect("200 carries a body");
    assert_eq!(
        body["success"], true,
        "a real ticket with a real proof must still be discharged: {body}"
    );
    assert!(
        body["discharge"].as_str().is_some_and(|d| !d.is_empty()),
        "the honest path must return an actual discharge macaroon: {body}"
    );
}

/// [1b] A MALFORMED persisted blob must refuse too.
///
/// `load_issued_set` used to `return` silently on a length that was not a
/// multiple of 32, which is indistinguishable — from the caller — from a clean
/// load of an empty set. Store a truncated blob and watch the gateway refuse to
/// be built on it.
#[tokio::test]
async fn malformed_persisted_replay_set_refuses_instead_of_loading_nothing() {
    let (app, key, location, store, _tmp) = discharge_node().await;

    // 33 bytes: one whole hash plus a byte. At least one entry is unrecoverable.
    store
        .set_config("discharge_issued_set", &[0x5Au8; 33])
        .expect("seed a malformed replay set");

    let (status, body) = post_discharge(&app, &fresh_ticket(&key, &location)).await;
    assert_eq!(
        status,
        StatusCode::SERVICE_UNAVAILABLE,
        "a malformed replay set is not an empty one; it answered {body:?}"
    );

    // ── COMPLETENESS: a well-formed set of the same shape loads and serves.
    store
        .set_config("discharge_issued_set", &[0x5Au8; 32])
        .expect("seed a well-formed replay set");
    let (status, body) = post_discharge(&app, &fresh_ticket(&key, &location)).await;
    assert_eq!(status, StatusCode::OK, "a valid replay set must load");
    assert_eq!(
        body.expect("200 carries a body")["success"],
        true,
        "a ticket absent from the loaded set is still discharge-able"
    );
}

/// [2] An UNPERSISTABLE burn must refuse, not answer `success: true`.
///
/// The gateway is already built and cached at this point (so the read seam is
/// out of the picture); what fails is the write that makes the burn durable.
/// Before this fix the handler warned and handed the discharge over anyway.
#[tokio::test]
async fn unpersistable_burn_refuses_instead_of_issuing_an_unrecorded_discharge() {
    let (app, key, location, store, _tmp) = discharge_node().await;

    // Build + cache the gateway on a healthy store, and prove the honest path.
    let (status, body) = post_discharge(&app, &fresh_ticket(&key, &location)).await;
    assert_eq!(status, StatusCode::OK);
    assert_eq!(body.expect("body")["success"], true);
    let after_first = store
        .get_config("discharge_issued_set")
        .expect("read")
        .expect("the first discharge persisted its burn");
    assert_eq!(after_first.len(), 32, "exactly one ticket hash is durable");

    // ── THE REFUSAL FIRES: the burn cannot be made durable, so nothing is issued.
    store.set_fail_config_io(true);
    let (status, body) = post_discharge(&app, &fresh_ticket(&key, &location)).await;
    assert_eq!(
        status,
        StatusCode::SERVICE_UNAVAILABLE,
        "a discharge whose burn is not durable must not be handed out; it answered {body:?}"
    );

    // ── COMPLETENESS: the store recovers and issuance resumes, still recorded.
    store.set_fail_config_io(false);
    let (status, body) = post_discharge(&app, &fresh_ticket(&key, &location)).await;
    assert_eq!(
        status,
        StatusCode::OK,
        "issuance resumes once the store does"
    );
    assert_eq!(body.expect("body")["success"], true);
    let after_recovery = store
        .get_config("discharge_issued_set")
        .expect("read")
        .expect("still persisted");
    assert_eq!(
        after_recovery.len() % 32,
        0,
        "the persisted set stays a whole number of hashes"
    );
    assert!(
        after_recovery.len() >= 32 * 3,
        "the REFUSED request's ticket stays burned in RAM and is flushed on the next \
         successful write — the burn is never rolled back to buy liveness (got {} bytes)",
        after_recovery.len()
    );
}

/// [2b] A DENIED request burns the ticket too, so it must be persisted too.
///
/// `process_request` inserts the ticket hash before evaluating conditions, so a
/// request denied for a missing proof still mutates the replay set. Persisting
/// only the success arm meant a restart resurrected every denied ticket — the
/// durable set was strictly weaker than the in-RAM one it is supposed to mirror.
#[tokio::test]
async fn a_denied_request_persists_its_burn_so_a_restart_cannot_resurrect_the_ticket() {
    let (app, key, location, store, _tmp) = discharge_node().await;
    let ticket = fresh_ticket(&key, &location);

    // Present the ticket WITHOUT a proof: `ProofRequiredEvaluator` denies it,
    // but the gateway has already burned it.
    let addr: std::net::SocketAddr = "127.0.0.1:4546".parse().unwrap();
    let response = app
        .clone()
        .oneshot(
            Request::builder()
                .method("POST")
                .uri("/api/discharge")
                .header("content-type", "application/json")
                .extension(ConnectInfo(addr))
                .body(Body::from(
                    serde_json::to_vec(&serde_json::json!({ "ticket": ticket })).unwrap(),
                ))
                .expect("discharge request"),
        )
        .await
        .expect("discharge response");
    assert_eq!(response.status(), StatusCode::OK);
    let bytes = response.into_body().collect().await.expect("b").to_bytes();
    let body: serde_json::Value = serde_json::from_slice(&bytes).expect("json");
    assert_eq!(body["success"], false, "no proof ⇒ denied: {body}");

    let persisted = store
        .get_config("discharge_issued_set")
        .expect("read")
        .expect("a DENIED presentation must still persist its burn");
    assert_eq!(
        persisted.len(),
        32,
        "the denied ticket's hash is durable, so a restart still refuses it"
    );

    // And the burn is real: the same ticket, now WITH a valid proof, is refused
    // as a replay rather than discharged.
    let (status, body) = post_discharge(&app, &ticket).await;
    assert_eq!(status, StatusCode::OK);
    let body = body.expect("body");
    assert_eq!(
        body["success"], false,
        "a presented ticket is spent: {body}"
    );
    assert!(
        body["error"].as_str().is_some_and(|e| e.contains("replay")),
        "the refusal names replay, not the condition: {body}"
    );
}
