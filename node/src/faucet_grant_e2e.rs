//! faucet_grant_e2e.rs — DOES THE FAUCET MOVE THE MONEY?
//!
//! `POST /api/faucet` answers `success: true` at SUBMISSION time, but submission
//! is admission staging only: the handler executes the grant against an undo
//! journal and rolls it back, and consensus FINALIZATION is the sole durable
//! application (`blocklace_sync::execute_finalized_turn`). So every assertion
//! that stops at the HTTP response — "success":true, a `turn_hash`, a committed
//! activity event, a turn-bearing block — is compatible with the recipient never
//! being credited at all. That is exactly what shipped between 2026-07-21 and
//! 2026-07-25: the faucet cell was minted in the all-zero asset while
//! `signed_turn_validation::validate_signed_turn` requires a turn's agent to be
//! `derive_raw(signer, blake3("default"))`, so the finalized executor threw every
//! faucet turn away as `agent-signer-mismatch` — silently, after the caller had
//! already been told it worked.
//!
//! This test therefore asserts on the AUTHORITATIVE LEDGER after finalization,
//! never on the response:
//!
//!   [1] a faucet grant CREDITS the recipient and DEBITS the faucet, applied by
//!       the finalized executor, and no durable rejection record was written for
//!       the block that carried it;
//!   [2] a SECOND grant in the same process also lands — the pipelined faucet
//!       nonce advances and the action signature is bound to the nonce the turn
//!       actually carries (`dregg-action-sig-v3`). Before the fix the second call
//!       per boot always failed "Ed25519 (classical) signature half failed",
//!       because the per-request cipherclerk's `next_turn_nonce()` is always 0
//!       while the reservation had moved on.
//!
//! The canary that proves [1] can fail: change the faucet Transfer's amount (or
//! the asset the destination stub is minted in, or the faucet cell's token
//! domain) and this test goes red on the balance, not on a status code.

#![cfg(test)]

use std::time::{Duration, Instant};

use axum::body::Body;
use axum::extract::ConnectInfo;
use axum::http::Request;
use http_body_util::BodyExt;
use tower::ServiceExt;

use dregg_types::hex_encode;

use crate::blocklace_sync::run_blocklace_sync_with_policy;
use crate::state::NodeState;

/// The genesis faucet supply this fixture mints, mirroring `genesis.rs`
/// (`recipients` gives the faucet cell 1_000_000 in the default asset).
const FAUCET_SUPPLY: i64 = 1_000_000;

/// Stand up a real solo node: NodeState + the genesis faucet cell + the live
/// blocklace/finality machinery, plus the HTTP router with the faucet enabled.
async fn faucet_node() -> (
    NodeState,
    axum::Router,
    dregg_cell::CellId,
    tempfile::TempDir,
) {
    let _ = rustls::crypto::ring::default_provider().install_default();
    let tmp = tempfile::tempdir().expect("tempdir");
    let state = NodeState::new(tmp.path(), vec![]).expect("build NodeState");

    // The genesis faucet cell, materialized exactly as `genesis.rs` +
    // `materialize_genesis_cells` build it: same key, same asset, and the
    // COMMITTED ML-DSA identity the faucet's own cipherclerk signs with (hybrid
    // admission anchors the carried PQ key in the agent cell, so a faucet cell
    // without it cannot act).
    let faucet_cell_id = {
        let mut s = state.write().await;
        s.unlocked = true;
        let faucet_seed = crate::api::faucet_signing_key().to_bytes();
        let ml_dsa_public_key =
            dregg_turn::pq::MlDsaTurnKey::from_ed25519_seed(&faucet_seed).public_bytes();
        let faucet = dregg_cell::Cell::with_hybrid_balance(
            crate::api::faucet_public_key(),
            &ml_dsa_public_key,
            crate::api::faucet_token_id(),
            FAUCET_SUPPLY,
        )
        .expect("canonical ML-DSA-65 faucet identity");
        let id = faucet.id();
        s.ledger.insert_cell(faucet).expect("insert faucet cell");
        id
    };

    let handle = run_blocklace_sync_with_policy(
        state.clone(),
        0,      // gossip_port 0 ⇒ OS-assigned ephemeral
        true,   // auto_approve_joins (irrelevant solo)
        100,    // blocklace_checkpoint_interval
        10_000, // constitution wave timeout ms
        50,     // block_cadence_ms
        2_000,  // idle_heartbeat_ms
        0,      // min_block_interval_ms
        None,   // advertise_addr
        dregg_blocklace::finality::ConsensusTimePolicyV1::new(1_700_000_000),
    )
    .await
    .expect("run_blocklace_sync must return a handle in solo mode");
    state.set_blocklace(handle).await;

    let recorder = metrics_exporter_prometheus::PrometheusBuilder::new().build_recorder();
    let app = crate::api::router(state.clone(), true, recorder.handle());
    (state, app, faucet_cell_id, tmp)
}

/// `POST /api/faucet` through the real router; returns the parsed JSON body.
async fn post_faucet(app: &axum::Router, recipient_hex: &str, amount: u64) -> serde_json::Value {
    let addr: std::net::SocketAddr = "127.0.0.1:4444".parse().unwrap();
    let body = serde_json::json!({ "recipient": recipient_hex, "amount": amount });
    let response = app
        .clone()
        .oneshot(
            Request::builder()
                .method("POST")
                .uri("/api/faucet")
                .header("content-type", "application/json")
                .extension(ConnectInfo(addr))
                .body(Body::from(serde_json::to_vec(&body).unwrap()))
                .expect("faucet request"),
        )
        .await
        .expect("faucet response");
    assert_eq!(response.status(), axum::http::StatusCode::OK);
    let bytes = response
        .into_body()
        .collect()
        .await
        .expect("body")
        .to_bytes();
    serde_json::from_slice(&bytes).expect("faucet json")
}

/// Poll the AUTHORITATIVE ledger until `cell` holds `want`, or time out.
/// Returns the last observed balance (`None` when the cell never appeared).
async fn await_balance(
    state: &NodeState,
    cell: &dregg_cell::CellId,
    want: i64,
    within: Duration,
) -> Option<i64> {
    let deadline = Instant::now() + within;
    let mut seen = None;
    loop {
        {
            let s = state.read().await;
            seen = s.ledger.get(cell).map(|c| c.state.balance()).or(seen);
            if seen == Some(want) {
                return seen;
            }
        }
        if Instant::now() >= deadline {
            return seen;
        }
        tokio::time::sleep(Duration::from_millis(100)).await;
    }
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn faucet_grant_credits_the_recipient_after_finalization() {
    let (state, app, faucet_cell_id, _tmp) = faucet_node().await;

    let recipient = dregg_cell::CellId([0x7Au8; 32]);
    let recipient_hex = hex_encode(&recipient.0);
    let amount = 10_000u64;

    let json = post_faucet(&app, &recipient_hex, amount).await;
    assert_eq!(
        json["success"], true,
        "faucet must accept the grant: {json}"
    );

    // THE ASSERTION THAT BITES: the authoritative ledger, after finalization.
    let credited = await_balance(&state, &recipient, amount as i64, Duration::from_secs(30)).await;
    assert_eq!(
        credited,
        Some(amount as i64),
        "the finalized executor must credit the faucet recipient — response said {json}, ledger \
         says {credited:?}. A grant that commits into a block but never moves value is the exact \
         success-that-is-not-one this test exists to catch."
    );

    // The faucet is debited by the grant plus the turn's (burned) fee.
    let faucet_after = {
        let s = state.read().await;
        s.ledger
            .get(&faucet_cell_id)
            .expect("faucet cell present")
            .state
            .balance()
    };
    assert!(
        faucet_after <= FAUCET_SUPPLY - amount as i64,
        "the faucet must be debited at least the granted amount (supply={FAUCET_SUPPLY}, \
         after={faucet_after})"
    );

    // And nothing was thrown away at finalization: a deterministic rejection is
    // recorded durably per block, so its ABSENCE is a real check.
    let rejected: Vec<String> = {
        let s = state.read().await;
        let blocklace = state.blocklace().await.expect("blocklace handle");
        let block_ids: Vec<[u8; 32]> = blocklace
            .lace
            .read()
            .await
            .all_blocks()
            .iter()
            .map(|block| block.id().0)
            .collect();
        block_ids
            .into_iter()
            .filter_map(|id| {
                let key =
                    crate::signed_turn_validation::FinalizedPayloadRejectionRecord::storage_key(
                        &id,
                    );
                s.store.get_config(&key).ok().flatten().and_then(|bytes| {
                    postcard::from_bytes::<
                        crate::signed_turn_validation::FinalizedPayloadRejectionRecord,
                    >(&bytes)
                    .ok()
                    .map(|record| record.reason_code)
                })
            })
            .collect()
    };
    assert!(
        rejected.is_empty(),
        "no finalized faucet payload may be deterministically rejected; got {rejected:?}"
    );
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_second_faucet_grant_in_the_same_process_also_lands() {
    let (state, app, _faucet_cell_id, _tmp) = faucet_node().await;

    // Two DISTINCT recipients so the per-cell rate limiter is not the thing
    // under test; the failure this catches is the faucet's own signing path.
    let first = dregg_cell::CellId([0x11u8; 32]);
    let second = dregg_cell::CellId([0x22u8; 32]);
    let amount = 1_000u64;

    let json = post_faucet(&app, &hex_encode(&first.0), amount).await;
    assert_eq!(json["success"], true, "first grant: {json}");
    // Let the first grant finalize so the faucet's authoritative nonce advances;
    // the reservation and the on-ledger nonce must reconcile, not diverge.
    let first_credited =
        await_balance(&state, &first, amount as i64, Duration::from_secs(30)).await;
    assert_eq!(first_credited, Some(amount as i64), "first grant must land");

    let json = post_faucet(&app, &hex_encode(&second.0), amount).await;
    assert_eq!(
        json["success"], true,
        "the SECOND faucet call per boot must succeed — a failure here reads \
         'Ed25519 (classical) signature half failed' when the action signature is not bound to \
         the turn nonce the faucet actually reserved: {json}"
    );
    let second_credited =
        await_balance(&state, &second, amount as i64, Duration::from_secs(30)).await;
    assert_eq!(
        second_credited,
        Some(amount as i64),
        "the second grant must be credited too (got {second_credited:?})"
    );
}
