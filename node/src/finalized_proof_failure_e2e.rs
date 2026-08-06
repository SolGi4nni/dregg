//! finalized_proof_failure_e2e.rs — WHAT DOES A FAILED FULL-TURN PROOF LEAVE?
//!
//! `blocklace_sync::execute_finalized_turn` calls a finalized turn whose
//! full-turn proof will not generate or verify *"a serious event"* in its own
//! comment — and then commits the turn anyway. Whether that is right is a
//! **genuine design fork** (refusing would wedge this node at a height the rest
//! of the committee has already passed), and this test does NOT settle it. It
//! pins the half that was never a fork:
//!
//!   **the failure has to be findable.** Before 2026-08-05 it left exactly one
//!   `error!` line. The activity feed published the turn as `ProofPending` —
//!   the same status a turn still being proven carries, so a reader waits
//!   forever for an attestation that will never come — and `full_turn_proof:{h}`
//!   was simply absent, which is also what proving-disabled looks like. Three
//!   different facts, one observable.
//!
//! So this drives a REAL faucet grant to REAL finalization with proving on and
//! the prover faulted, and asserts:
//!
//!   [1] the turn still commits and the recipient is still credited — the
//!       current answer to the fork, asserted so that changing it is a visible
//!       decision and not a drift;
//!   [2] `full_turn_proof_failed:{turn_hash}` is durable and names the reason;
//!   [3] `GET /api/turn/{hash}/proof` answers `410 Gone` +
//!       `proof_status: "generation_failed"`, not a bare 404 a poller reads as
//!       "not yet";
//!   [4] the activity event says `ProofGenerationFailed`, not `ProofPending`;
//!   [5] and with no fault, none of that is written — the record is not a
//!       decoration that fires on every turn.
//!
//! The canary: delete the `full_turn_proof_failure` carrier in `blocklace_sync`
//! and [2]/[3]/[4] go red on the absence of a durable fact, not on a log line.

#![cfg(test)]

use std::time::Duration;

use axum::body::Body;
use axum::extract::ConnectInfo;
use axum::http::{Request, StatusCode};
use http_body_util::BodyExt;
use tower::ServiceExt;

use dregg_types::hex_encode;

use crate::faucet_grant_e2e::{await_balance, faucet_node, post_faucet};
use crate::state::NodeState;

/// `GET /api/turn/{hash}/proof` through the real router.
async fn get_turn_proof(
    app: &axum::Router,
    turn_hash_hex: &str,
) -> (StatusCode, serde_json::Value) {
    let addr: std::net::SocketAddr = "127.0.0.1:4747".parse().unwrap();
    let response = app
        .clone()
        .oneshot(
            Request::builder()
                .method("GET")
                .uri(format!("/api/turn/{turn_hash_hex}/proof"))
                .extension(ConnectInfo(addr))
                .body(Body::empty())
                .expect("proof request"),
        )
        .await
        .expect("proof response");
    let status = response.status();
    let bytes = response.into_body().collect().await.expect("b").to_bytes();
    (
        status,
        serde_json::from_slice(&bytes).unwrap_or(serde_json::Value::Null),
    )
}

/// Poll until the durable proving-failure record for `turn_hash` appears.
async fn await_proof_failure_record(
    state: &NodeState,
    turn_hash_hex: &str,
    within: Duration,
) -> Option<String> {
    let key = crate::turn_proving::turn_proof_failure_config_key(turn_hash_hex);
    let deadline = std::time::Instant::now() + within;
    loop {
        {
            let s = state.read().await;
            if let Ok(Some(bytes)) = s.store.get_config(&key) {
                return Some(String::from_utf8_lossy(&bytes).into_owned());
            }
        }
        if std::time::Instant::now() >= deadline {
            return None;
        }
        tokio::time::sleep(Duration::from_millis(100)).await;
    }
}

/// Latest committed-activity proof status for a turn, from the node's own ring
/// buffer (the same values `/api/events` serves).
async fn activity_proof_status(
    state: &NodeState,
    turn_hash_hex: &str,
) -> Option<crate::state::ActivityProofStatus> {
    let s = state.read().await;
    s.event_log
        .iter()
        .rev()
        .find(|e| e.turn_hash.eq_ignore_ascii_case(turn_hash_hex))
        .map(|e| e.proof_status)
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_finalized_turn_whose_proof_failed_is_recorded_durably_and_served_as_gone() {
    let (state, app, _faucet_cell_id, _tmp) = faucet_node().await;

    // Turn proving ON (it is OFF by default — `--prove-turns` only), then FAULT
    // the prover so the SOUNDNESS arm of `execute_finalized_turn` is the one that
    // runs. `INJECT_PROVING_FAULT` is a process-global; nextest gives each test
    // its own process, which is what keeps this from leaking into a sibling.
    {
        let mut s = state.write().await;
        s.full_turn_proving_enabled = true;
    }
    crate::turn_proving::set_inject_proving_fault(true);

    let recipient = dregg_cell::CellId([0x5Cu8; 32]);
    let recipient_hex = hex_encode(&recipient.0);
    let amount = 1_000u64;

    let json = post_faucet(&app, &recipient_hex, amount).await;
    assert_eq!(
        json["success"], true,
        "faucet must accept the grant: {json}"
    );
    let turn_hash = json["turn_hash"]
        .as_str()
        .expect("a committed faucet turn carries its turn hash")
        .to_string();

    // ── [1] THE FORK'S CURRENT ANSWER, ASSERTED. The proof failed and the turn
    //        committed regardless: the recipient really is credited. Changing
    //        this to a refusal is a decision someone has to make on purpose.
    let credited = await_balance(&state, &recipient, amount as i64, Duration::from_secs(30)).await;
    assert_eq!(
        credited,
        Some(amount as i64),
        "the finalized turn COMMITS UNPROVEN today; if this ever goes red, the \
         commit-anyway/refuse fork was decided — say so in the commit"
    );

    // ── [2] THE FAILURE IS DURABLE, and names why.
    let reason = await_proof_failure_record(&state, &turn_hash, Duration::from_secs(20)).await;
    let reason = reason.expect(
        "a finalized turn whose proof FAILED must leave a durable, per-turn record — an \
         error! line is not a detection",
    );
    assert!(
        reason.contains("fault injected"),
        "the record must carry the proving error, not a placeholder: {reason}"
    );

    // ── [3] AND IT IS SERVED AS DEFINITIVE, not as "not yet".
    let (status, body) = get_turn_proof(&app, &turn_hash).await;
    assert_eq!(
        status,
        StatusCode::GONE,
        "a proof that failed is never coming; 404 tells a poller to keep polling: {body}"
    );
    assert_eq!(body["proof_status"], "generation_failed", "{body}");
    assert!(
        body["error"].as_str().is_some_and(|e| !e.is_empty()),
        "the served failure must carry the reason: {body}"
    );

    // ── [4] AND OBSERVERS ARE NOT TOLD IT IS PENDING.
    let status = activity_proof_status(&state, &turn_hash).await;
    assert_eq!(
        status,
        Some(crate::state::ActivityProofStatus::ProofGenerationFailed),
        "the activity feed must not report a failed proof as ProofPending — that is a \
         claim which resolves itself as success in the reader's head"
    );
}

/// COMPLETENESS: with no fault, an honest finalized turn writes NO failure
/// record and the endpoint answers `absent`, not `generation_failed`. A marker
/// that fires on every turn detects nothing.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn an_honest_finalized_turn_leaves_no_proving_failure_record() {
    let (state, app, _faucet_cell_id, _tmp) = faucet_node().await;
    crate::turn_proving::set_inject_proving_fault(false);

    let recipient = dregg_cell::CellId([0x6Du8; 32]);
    let recipient_hex = hex_encode(&recipient.0);
    let amount = 1_000u64;

    let json = post_faucet(&app, &recipient_hex, amount).await;
    assert_eq!(
        json["success"], true,
        "faucet must accept the grant: {json}"
    );
    let turn_hash = json["turn_hash"].as_str().expect("turn hash").to_string();

    let credited = await_balance(&state, &recipient, amount as i64, Duration::from_secs(30)).await;
    assert_eq!(credited, Some(amount as i64), "the honest grant must land");

    let key = crate::turn_proving::turn_proof_failure_config_key(&turn_hash);
    let recorded = {
        let s = state.read().await;
        s.store.get_config(&key).expect("store readable")
    };
    assert!(
        recorded.is_none(),
        "no proving failure occurred, so nothing may be recorded (got {recorded:?})"
    );

    let (status, body) = get_turn_proof(&app, &turn_hash).await;
    assert_eq!(
        status,
        StatusCode::NOT_FOUND,
        "proving is OFF by default, so this turn has no proof and no failure: {body}"
    );
    assert_eq!(body["proof_status"], "absent", "{body}");
}
