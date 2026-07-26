//! operator_turn_receipt_head_e2e.rs — CAN THE OPERATOR ACT AFTER SOMEBODY ELSE ACTED?
//!
//! `dregg demo` funds the operator cell (step 3) and then writes a name into it
//! (step 4). Until 2026-07-26 those two steps were MUTUALLY EXCLUSIVE. Step 4
//! came back:
//!
//! ```text
//! ERROR: Registration rejected: rejected: receipt chain mismatch: expected None, got Some(d924...)
//! ```
//!
//! WHY. `api::post_submit_turn` — the thin JSON ingress behind `/turn/submit`
//! and `/api/turns/submit`, the one every `dregg name …` command and the whole
//! demo ride on — stamped the turn's `previous_receipt_hash` from
//! `cclerk.receipt_chain().last()`. That is the last entry in the node-WIDE
//! observation log, which interleaves every agent the node has ever committed
//! for. Its own doc comment says so and points at `agent_receipt_head_hash`.
//! The executor compares against the agent's OWN causal head. So the moment any
//! other agent committed anything, the operator's next turn carried a stranger's
//! receipt as its predecessor and was refused.
//!
//! The faucet grant is the first foreign commit every newcomer triggers, one step
//! before their first turn. The failure was therefore not an edge case: it was the
//! default path, and it made a second `dregg demo` on a live node impossible.
//!
//! THE CANARY (run it, it is cheap): put `s.cclerk.receipt_chain().last().map(|r|
//! r.receipt_hash())` back in `api.rs::post_submit_turn` and this test goes RED on
//! `accepted`, naming the mismatch. Nothing else in the suite noticed — every
//! other thin-path test committed the operator's turn on a log the operator alone
//! had written to, where the global head and the agent head are the same value.

#![cfg(test)]

use std::time::Duration;

use axum::body::Body;
use axum::extract::ConnectInfo;
use axum::http::Request;
use http_body_util::BodyExt;
use tower::ServiceExt;

use dregg_types::hex_encode;

use crate::faucet_grant_e2e::{await_balance, faucet_node, post_faucet};
use crate::state::NodeState;

/// The operator's own agent cell — what `post_submit_turn` derives from the
/// node's cipherclerk pubkey and acts on by default (`/api/node/identity`
/// publishes the same value as `agent_cell`).
async fn operator_agent_cell(state: &NodeState) -> dregg_cell::CellId {
    let s = state.read().await;
    let default_token_id = *blake3::hash(b"default").as_bytes();
    dregg_cell::CellId::derive_raw(&s.cclerk.public_key().0, &default_token_id)
}

/// `POST /api/turns/submit` through the real router — byte-for-byte the request
/// `dregg name register` builds (`cli/src/commands/name.rs::submit_effects`),
/// including its `"agent": "00"*32` placeholder and `"nonce": 0`.
async fn post_thin_turn(app: &axum::Router, body: serde_json::Value) -> serde_json::Value {
    let addr: std::net::SocketAddr = "127.0.0.1:4444".parse().unwrap();
    let response = app
        .clone()
        .oneshot(
            Request::builder()
                .method("POST")
                .uri("/api/turns/submit")
                .header("content-type", "application/json")
                .extension(ConnectInfo(addr))
                .body(Body::from(serde_json::to_vec(&body).unwrap()))
                .expect("submit request"),
        )
        .await
        .expect("submit response");
    let status = response.status();
    let bytes = response
        .into_body()
        .collect()
        .await
        .expect("body")
        .to_bytes();
    assert_eq!(
        status,
        axum::http::StatusCode::OK,
        "/api/turns/submit answered {status}: {}",
        String::from_utf8_lossy(&bytes)
    );
    serde_json::from_slice(&bytes).expect("submit json")
}

/// THE DEMO'S STEP 3 → STEP 4, end to end: faucet the operator cell, wait for the
/// grant to land on the authoritative ledger (which appends the FAUCET's receipt
/// to the node-wide log), then take the operator's own turn through the thin
/// ingress and require that it commits.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn the_operator_can_take_a_turn_after_the_faucet_receipt_lands() {
    let (state, app, _faucet_cell_id, _tmp) = faucet_node().await;

    let operator = operator_agent_cell(&state).await;
    let operator_hex = hex_encode(&operator.0);
    let grant = 10_000u64;

    let faucet = post_faucet(&app, &operator_hex, grant).await;
    assert_eq!(
        faucet["success"].as_bool(),
        Some(true),
        "faucet submission refused: {faucet}"
    );

    let credited = await_balance(
        &state,
        &operator,
        i64::try_from(grant).unwrap(),
        Duration::from_secs(30),
    )
    .await;
    assert_eq!(
        credited,
        Some(i64::try_from(grant).unwrap()),
        "the grant never reached the authoritative ledger; nothing downstream is meaningful"
    );

    // The precondition that broke the door: the node-wide log head now belongs to
    // the FAUCET, while the operator's own causal head is still genesis (`None`).
    // Those two disagreeing is the whole bug.
    {
        let s = state.read().await;
        assert!(
            s.cclerk.receipt_log_length() > 0,
            "the faucet grant must have appended a receipt to the node-wide log"
        );
        assert_ne!(
            s.cclerk.receipt_log().last().map(|r| r.agent),
            Some(operator),
            "the node-wide log head must belong to the faucet, not the operator — \
             otherwise this test cannot distinguish the two accessors"
        );
        assert_eq!(
            s.cclerk.agent_receipt_head_hash(&operator),
            None,
            "the operator has taken no turn yet, so its causal head is genesis"
        );
    }

    // Step 4: the operator writes a field into its own cell. Same JSON the CLI
    // sends, placeholder agent and all.
    let submitted = post_thin_turn(
        &app,
        serde_json::json!({
            "agent": "00".repeat(32),
            "nonce": 0,
            "fee": 1000,
            "memo": serde_json::Value::Null,
            "actions": [{
                "target": operator_hex,
                "method": "register_name",
                "effects": [
                    { "kind": "set_field", "index": 2, "value": "ab".repeat(32) }
                ],
            }],
        }),
    )
    .await;

    assert_eq!(
        submitted["accepted"].as_bool(),
        Some(true),
        "the operator's own turn was refused right after being funded: {}",
        submitted["error"].as_str().unwrap_or("(no error field)")
    );

    // And the chain MOVED. `accepted: true` is the turn being admitted and
    // ordered, not applied — application is finalization's job, and a turn can be
    // refused there after the HTTP surface has answered. Poll the authoritative
    // ledger, the way `dregg demo` now does between its steps.
    let deadline = tokio::time::Instant::now() + Duration::from_secs(30);
    loop {
        {
            let s = state.read().await;
            let head = s.cclerk.agent_receipt_head_hash(&operator);
            let field = s
                .ledger
                .get(&operator)
                .and_then(|c| c.state.get_field(2).copied());
            if head.is_some() && field == Some([0xab; 32]) {
                break;
            }
            if tokio::time::Instant::now() >= deadline {
                panic!(
                    "the turn was accepted but never applied within 30s: \
                     operator receipt head = {head:?}, slot 2 = {field:?}. \
                     A turn admitted and then refused at finalization looks exactly like this."
                );
            }
        }
        tokio::time::sleep(Duration::from_millis(100)).await;
    }
}
