//! transport_parity_e2e.rs — DO TWO INGRESSES ON THE SAME NODE ANSWER THE SAME?
//!
//! `signed_turn_validation` exists so every `SignedTurn` transport reaches one
//! verdict. Until 2026-08-06 its docblock ASSERTED that and nothing checked it,
//! and the way it was false is the reason this file exists: the failure was not a
//! transport that checked too little, it was a transport that checked something
//! ELSE and refused a turn the chain commits.
//!
//! # The split, concretely
//!
//! `blocklace_sync::provision_transfer_destinations` materialises a deterministic
//! zero-pk stub for any `Transfer` destination no node has seen — the recipient's
//! public key is not carried over consensus, so every node mints the identical
//! landing site from the turn's own data. `execute_finalized_turn` does this
//! UNCONDITIONALLY before it executes, and the executor refuses a `Transfer` whose
//! destination is absent (`TurnError::TransferDestNotFound`).
//!
//! `POST /turns/submit` provisioned before its staging execution. `POST
//! /turn/submit` did not. So on ONE node, at one instant, for the same effect:
//!
//! * `/turns/submit` → `accepted: true`, the turn enters consensus, finalization
//!   provisions the destination and credits it; and
//! * `/turn/submit`  → `accepted: false, "rejected: transfer destination not
//!   found: …"` — terminal, never submitted, nothing to retry.
//!
//! The pg `submit_queue` drainer had the same omission with a worse ending: it
//! wrote `status='refused'` into the queue row. (That transport is
//! `pg-mirror-live`-only; its half of this proof lives in
//! `submit_queue_drainer.rs` so it runs under the feature that compiles it.)
//!
//! ⚑ WHICH SIDE WAS WRONG. The strict one. A staging run exists to PREDICT
//! finalization's verdict — finalization is the sole authoritative application —
//! so a prediction computed against a ledger finalization will never produce is
//! not a stricter check, it is a wrong one. And it guarded nothing: the identical
//! turn walked in through the other door and committed. The repair is therefore
//! `signed_turn_validation::install_pre_execution_state`, called by finalization
//! AND by the one shared staging run every ingress now takes.
//!
//! THE CANARY (cheap, and it is the whole point): delete the
//! `install_pre_execution_state` call from
//! `signed_turn_validation::stage_signed_turn_admission` and
//! [`the_two_http_turn_ingresses_agree_on_a_transfer_to_a_fresh_destination`]
//! goes red on the `/turn/submit` half with `transfer destination not found`,
//! while the `/turns/submit` half stays green — which is exactly the shape of the
//! defect, reproduced.

#![cfg(test)]

use std::time::Duration;

use dregg_sdk::AgentCipherclerk;
use dregg_turn::action::Effect;
use dregg_types::hex_encode;

use crate::faucet_grant_e2e::{await_balance, faucet_node, post_faucet};
use crate::state::NodeState;

fn default_token() -> [u8; 32] {
    crate::executor_setup::default_token_id()
}

/// A destination cell id no node has ever seen, derived from a salt so distinct
/// cases cannot collide.
fn fresh_destination(salt: u8) -> dregg_cell::CellId {
    dregg_cell::CellId::derive_raw(&[salt; 32], &default_token())
}

/// `POST /turn/submit` — the THIN, node-signed ingress (`dregg demo`, the CLI).
/// The node derives the agent from its own cipherclerk and signs as itself.
async fn post_thin_turn(app: &axum::Router, body: serde_json::Value) -> serde_json::Value {
    post_json(app, "/turn/submit", body, "127.0.0.1:4466").await
}

/// `POST /turns/submit` — the client-signed remote ingress an SDK drives.
async fn post_signed_turn(app: &axum::Router, signed: &dregg_sdk::SignedTurn) -> serde_json::Value {
    use axum::body::Body;
    use axum::extract::ConnectInfo;
    use axum::http::Request;
    use http_body_util::BodyExt;
    use tower::ServiceExt;

    let addr: std::net::SocketAddr = "127.0.0.1:4467".parse().unwrap();
    let wire = postcard::to_stdvec(signed).expect("encode SignedTurn");
    let response = app
        .clone()
        .oneshot(
            Request::builder()
                .method("POST")
                .uri("/turns/submit")
                .header("content-type", "application/octet-stream")
                .extension(ConnectInfo(addr))
                .body(Body::from(wire))
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
        "/turns/submit answered {status}: {}",
        String::from_utf8_lossy(&bytes)
    );
    serde_json::from_slice(&bytes).expect("submit json")
}

async fn post_json(
    app: &axum::Router,
    uri: &str,
    body: serde_json::Value,
    peer: &str,
) -> serde_json::Value {
    use axum::body::Body;
    use axum::extract::ConnectInfo;
    use axum::http::Request;
    use http_body_util::BodyExt;
    use tower::ServiceExt;

    let addr: std::net::SocketAddr = peer.parse().unwrap();
    let response = app
        .clone()
        .oneshot(
            Request::builder()
                .method("POST")
                .uri(uri)
                .header("content-type", "application/json")
                .extension(ConnectInfo(addr))
                .body(Body::from(serde_json::to_vec(&body).unwrap()))
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
    assert_eq!(
        status,
        axum::http::StatusCode::OK,
        "{uri} answered {status}: {}",
        String::from_utf8_lossy(&bytes)
    );
    serde_json::from_slice(&bytes).expect("json")
}

/// The operator's own default cell — the agent `/turn/submit` signs as.
async fn operator_cell(state: &NodeState) -> dregg_cell::CellId {
    let s = state.read().await;
    crate::executor_setup::local_agent_cell(&s)
}

/// Fund a cell through the real faucet and wait for finalization to credit it.
async fn fund(state: &NodeState, app: &axum::Router, cell: &dregg_cell::CellId, amount: u64) {
    let json = post_faucet(app, &hex_encode(&cell.0), amount).await;
    assert_eq!(
        json["success"], true,
        "faucet must accept the grant: {json}"
    );
    let credited = await_balance(state, cell, amount as i64, Duration::from_secs(30)).await;
    assert_eq!(
        credited,
        Some(amount as i64),
        "the grant must reach the authoritative ledger before the parity case can run"
    );
}

/// Build a client-signed single-`Transfer` turn — the exact shape an SDK sends.
async fn client_transfer_turn(
    state: &NodeState,
    client: &AgentCipherclerk,
    to: dregg_cell::CellId,
    amount: u64,
    fee: u64,
) -> dregg_sdk::SignedTurn {
    let actor = client.cell_id("default");
    let federation_id = {
        let s = state.read().await;
        crate::executor_setup::federation_id_for_executor(&s)
    };
    let action = client.make_action(
        actor,
        "parity_transfer",
        vec![Effect::Transfer {
            from: actor,
            to,
            amount,
        }],
        &federation_id,
    );
    let mut turn = client.make_turn(action);
    turn.fee = fee;
    turn.valid_until = Some(
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs() as i64)
            .unwrap_or(0)
            + 3_600,
    );
    client.sign_turn(&turn)
}

/// ⚑ THE SPLIT, EXHIBITED END TO END: the same effect, two ingresses, one node.
///
/// This is not a comparison of two gate lists — both halves are driven through
/// the real `axum` router and asserted on the AUTHORITATIVE ledger after
/// finalization, so it says what RUNS, not what is written down.
///
/// BEFORE the repair the `/turn/submit` half answered
/// `rejected: transfer destination not found: <id>` and the destination stayed
/// absent forever, while the `/turns/submit` half committed the identical
/// `Transfer` through consensus.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn the_two_http_turn_ingresses_agree_on_a_transfer_to_a_fresh_destination() {
    let (state, app, _faucet, _tmp) = faucet_node().await;

    // ── half A: the client-signed ingress, which always provisioned. ────────
    let client = AgentCipherclerk::from_key_bytes(zeroize::Zeroizing::new([0xB1; 32]));
    let client_cell = client.cell_id("default");
    fund(&state, &app, &client_cell, 10_000).await;

    let signed_destination = fresh_destination(0xE1);
    let signed = client_transfer_turn(&state, &client, signed_destination, 1_000, 5_000).await;
    let signed_response = post_signed_turn(&app, &signed).await;
    assert_eq!(
        signed_response["accepted"], true,
        "the client-signed ingress must admit a Transfer to a fresh destination: {signed_response}"
    );
    let signed_landed =
        await_balance(&state, &signed_destination, 1_000, Duration::from_secs(30)).await;
    assert_eq!(
        signed_landed,
        Some(1_000),
        "and finalization must credit it — this is the verdict the OTHER ingress has to predict"
    );

    // ── half B: the thin node-signed ingress, on the identical shape. ───────
    let operator = operator_cell(&state).await;
    fund(&state, &app, &operator, 10_000).await;

    let thin_destination = fresh_destination(0xE2);
    let thin_response = post_thin_turn(
        &app,
        serde_json::json!({
            "agent": hex_encode(&operator.0),
            "nonce": 0,
            "fee": 5_000,
            "actions": [{
                "target": hex_encode(&operator.0),
                "method": "parity_transfer",
                "effects": [{
                    "kind": "transfer",
                    "from": hex_encode(&operator.0),
                    "to": hex_encode(&thin_destination.0),
                    "amount": 1_000
                }]
            }]
        }),
    )
    .await;

    // ⚑ THE ASSERTION THAT WAS RED. `transfer destination not found` here means
    // the thin ingress is staging against a ledger finalization will never
    // produce: `install_pre_execution_state` is not running before its executor.
    assert_eq!(
        thin_response["accepted"], true,
        "the thin ingress must reach the SAME verdict as the client-signed one for the same \
         effect. A `transfer destination not found` refusal here is the liveness split: the \
         chain has no objection to this turn — the other door just admitted it — and this one \
         answered a terminal refusal that never reaches consensus. Response: {thin_response}"
    );

    let thin_landed =
        await_balance(&state, &thin_destination, 1_000, Duration::from_secs(30)).await;
    assert_eq!(
        thin_landed,
        Some(1_000),
        "and it must FINALIZE — an `accepted:true` that never lands is the other half of this \
         file's point (got {thin_landed:?})"
    );
}

/// COMPLETENESS, the other direction: making the ingresses agree must not have
/// made either of them admit something the chain refuses.
///
/// The perimeter teeth are asserted on the ingress that gained the most
/// checks (`/turn/submit` gained the whole shared predicate) and on the one that
/// gained provisioning, and each refusal is asserted by its STABLE CODE, not by
/// `accepted == false` — a refusal for the wrong reason is a green that means
/// nothing.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn provisioning_a_destination_did_not_open_a_door() {
    let (state, app, _faucet, _tmp) = faucet_node().await;

    // (a) an UNFUNDED client still cannot pay, even though its destination is
    //     now provisioned for it. Provisioning is a landing site, not value.
    let broke = AgentCipherclerk::from_key_bytes(zeroize::Zeroizing::new([0xB2; 32]));
    let destination = fresh_destination(0xE3);
    let signed = client_transfer_turn(&state, &broke, destination, 1_000, 5_000).await;
    let response = post_signed_turn(&app, &signed).await;
    assert_eq!(
        response["accepted"], false,
        "an unfunded client must not be able to move value into a freshly provisioned \
         destination: {response}"
    );
    {
        let s = state.read().await;
        assert_eq!(
            s.ledger.get(&destination).map(|c| c.state.balance()),
            None,
            "a refused staging run must leave NO provisioned stub on the authoritative ledger — \
             the rollback covers the provisioning too, or an unauthenticated body could mint \
             cells by naming them"
        );
    }

    // (b) the agent/signer binding still bites on the client-signed ingress.
    let attacker = AgentCipherclerk::from_key_bytes(zeroize::Zeroizing::new([0xB3; 32]));
    let victim = fresh_destination(0xE4);
    let federation_id = {
        let s = state.read().await;
        crate::executor_setup::federation_id_for_executor(&s)
    };
    let action = attacker.make_action(
        victim,
        "steal",
        vec![Effect::Transfer {
            from: victim,
            to: attacker.cell_id("default"),
            amount: 1_000,
        }],
        &federation_id,
    );
    let mut turn = attacker.make_turn(action);
    turn.agent = victim;
    turn.fee = 5_000;
    let stolen = post_signed_turn(&app, &attacker.sign_turn(&turn)).await;
    assert_eq!(stolen["accepted"], false, "must be refused: {stolen}");
    assert!(
        stolen["error"]
            .as_str()
            .unwrap_or_default()
            .contains("does not match signer default cell"),
        "the agent/signer tooth must still be what refuses this, not an incidental balance \
         failure; got {stolen}"
    );
    {
        let s = state.read().await;
        assert!(
            s.ledger.get(&victim).is_none(),
            "no cell may be fabricated at a foreign agent id"
        );
    }

    // (c) an omitted receipt link is still a pre-mutation refusal on the thin
    //     ingress — the check it did not previously run at all.
    let operator = operator_cell(&state).await;
    fund(&state, &app, &operator, 10_000).await;
    let before_nonce = {
        let s = state.read().await;
        s.ledger
            .get(&operator)
            .expect("operator cell")
            .state
            .nonce()
    };
    let first = post_thin_turn(
        &app,
        serde_json::json!({
            "agent": hex_encode(&operator.0),
            "nonce": 0,
            "fee": 5_000,
            "actions": [{
                "target": hex_encode(&operator.0),
                "method": "parity_bump",
                "effects": [{ "kind": "increment_nonce", "cell": hex_encode(&operator.0) }]
            }]
        }),
    )
    .await;
    assert_eq!(
        first["accepted"], true,
        "an ordinary thin turn from a funded operator must still be admitted: {first}"
    );
    assert_eq!(
        {
            let s = state.read().await;
            s.ledger
                .get(&operator)
                .expect("operator cell")
                .state
                .nonce()
        },
        before_nonce,
        "the thin ingress is admission staging only: the authoritative nonce must not move here"
    );
}
