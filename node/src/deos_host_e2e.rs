//! deos_host_e2e.rs — THE DEOS-HOST KEYSTONE, PROVEN BY RUNNING.
//!
//! The architecture this proves: the dregg node (`./node`, headless, NO gpui) HOSTS a
//! userspace deos-js "private server" program (a gamemaster) that holds state + offers
//! cap-gated affordances; a CLIENT connects, DISCOVERS an affordance, and FIRES it →
//! a real verified turn on the node's ledger. The node is a headless deos-js-server-host;
//! the cockpit is just one client of this.
//!
//! THE FLOW (each step is a hard assertion; DONE = ran):
//!   1. boot a headless `NodeState` (NO gpui anywhere — `node` + deos-js only);
//!   2. mint an OPEN door cell + an OPEN, funded player cell, and self-grant the player
//!      a capability over the door (the GM's setup of its world — real verified turns);
//!   3. HOST the `gm.js` private server: its setup spawns a lever cell (a GM superpower —
//!      a real CreateCell turn) and registers a cap-gated `knock` affordance carrying a
//!      real `SetField` on the door cell — published into the node's discovery surface;
//!   4. a CLIENT GETs `/api/server/{gm}/affordances?viewer=signature` → sees `knock`;
//!   5. the CLIENT builds a `Turn` carrying knock's `SetField`, signs it as the PLAYER's
//!      OWN cell, POSTs the postcard `SignedTurn` to `/turns/submit` (the genuine remote
//!      ingress, `post_submit_signed_turn`);
//!   6. ASSERT: the door cell's field changed (0 → 1), a real `TurnReceipt` landed
//!      (receipt count grew, `agent == player`), the HTTP response is `accepted: true`.
#![cfg(all(test, feature = "deos-host"))]

use std::collections::HashSet;

use axum::body::Body;
use axum::http::{Request, StatusCode};
use dregg_cell::{AuthRequired, CapabilityRef, Cell, CellId, Permissions};
use dregg_turn::action::Effect;
use dregg_turn::{CallForest, Turn};
use http_body_util::BodyExt;
use tower::ServiceExt;
use zeroize::Zeroizing;

use crate::state::NodeState;

fn open_permissions() -> Permissions {
    Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

fn default_token_id() -> [u8; 32] {
    *blake3::hash(b"default").as_bytes()
}

/// Pack a u64 into a `FieldElement` (LE low 8 bytes) — matches deos-js `pack_u64`, the
/// shape the `deos.server.defineAffordance` SetField effect carries.
fn pack_u64(v: u64) -> dregg_cell::state::FieldElement {
    dregg_cell::field_from_u64(v)
}

/// Read a u64 back out of a `FieldElement` (LE low 8 bytes).
fn unpack_u64(fe: &dregg_cell::state::FieldElement) -> u64 {
    dregg_cell::field_to_u64(fe)
}

fn hex_of(id: &CellId) -> String {
    dregg_types::hex_encode(id.as_bytes())
}

/// Derive an agent cell id the way the node's signed-turn ingress does.
fn agent_cell_for(pubkey: &[u8; 32]) -> CellId {
    CellId(dregg_cell::CellId::derive_raw(pubkey, &default_token_id()).0)
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn headless_node_hosts_deos_server_client_discovers_and_fires() {
    let _ = rustls::crypto::ring::default_provider().install_default();

    // ── (1) a headless NodeState (NO gpui — node + deos-js only) ────────────────
    let tmp = tempfile::tempdir().expect("tempdir");
    let state = NodeState::new(tmp.path(), vec![]).expect("build NodeState");
    {
        let mut s = state.write().await;
        s.unlocked = true; // the signed-turn ingress requires an unlocked node
    }

    // The PLAYER — its own cipherclerk + cell (the client identity that fires).
    let player_cclerk = dregg_sdk::AgentCipherclerk::from_key_bytes(Zeroizing::new(
        *blake3::hash(b"deos-host-player").as_bytes(),
    ));
    let player_pubkey = player_cclerk.public_key().0;
    let player_cell = agent_cell_for(&player_pubkey);

    // ── (2) mint the OPEN door + OPEN funded player cell; grant the player a cap
    //        over the door (a real GrantCapability self-grant from the door) ──────
    let door_cell = {
        let mut s = state.write().await;
        let token = default_token_id();

        // Door: an OPEN, funded cell on the node ledger (the GM's resource; funded so
        // the self-grant turn's computron fee is covered).
        let door_pubkey = *blake3::hash(b"gm-door").as_bytes();
        let mut door = Cell::with_balance(door_pubkey, token, 1_000_000);
        door.permissions = open_permissions();
        let door_id = door.id();
        s.ledger.insert_cell(door).expect("insert door cell");

        // Player: an OPEN, funded cell so its signed turn passes the budget gate.
        let mut player = Cell::with_balance(player_pubkey, token, 1_000_000);
        player.permissions = open_permissions();
        // ⚑ COMMIT THE PLAYER'S ML-DSA ANCHOR. Step (5) fires through the GENUINE remote ingress
        // (`post_submit_signed_turn` → `signed_turn_validation`), which requires the signer's
        // post-quantum identity to be Cell-committed or independently enrolled — a real client's
        // account has one (`first_turn_e2e` asserts the first claim commits it). Seeding this cell
        // with the ed25519 half ALONE made the whole client-fires leg unreachable behind
        // `pq-identity-not-enrolled`, and that was invisible while the turn before it was being
        // vetoed by the verified kernel.
        player
            .install_pq_identity(&player_cclerk.ml_dsa_public_bytes())
            .expect("install the player's epoch-0 ML-DSA anchor");
        assert_eq!(
            player.id(),
            player_cell,
            "player cell id must match derivation"
        );
        s.ledger.insert_cell(player).expect("insert player cell");

        // GRANT: a self-grant FROM the door TO the player (a real verified turn
        // committed AS the door — authorized because cap.target == from == door).
        // Now the player HOLDS a capability over the door, so its cross-cell knock
        // SetField is authorized (cap held + door set_state == None).
        let cap = CapabilityRef {
            target: door_id,
            slot: 0,
            permissions: AuthRequired::None,
            breadstuff: None,
            expires_at: None,
            allowed_effects: None,
            stored_epoch: None,
            provenance: dregg_cell::derivation::cap_provenance(
                &(door_id),
                (0),
                &dregg_cell::derivation::mint_provenance(),
                &[0u8; 32],
            ),
        };
        let grant = Effect::GrantCapability {
            from: door_id,
            to: player_cell,
            cap,
        };
        crate::executor_setup::commit_effects_as(&mut s, door_id, "grant", vec![grant])
            .expect("self-grant from the door to the player commits");

        door_id
    };
    let door_hex = hex_of(&door_cell);

    let receipts_before = {
        let s = state.read().await;
        s.cclerk.receipt_chain_length()
    };

    // ── (3) HOST the gm.js private server (headless, dedicated SpiderMonkey thread).
    //        Substitute the real door id into the fixture; its setup spawns a lever
    //        cell (a GM superpower turn) + registers the `knock` affordance. ────────
    let program = include_str!("../tests/fixtures/gm.js").replace("__DOOR__", &door_hex);
    let gm_cell =
        crate::deos_host::host_server_program(&state, "gamemaster", AuthRequired::None, program)
            .await
            .expect("host the gm.js private server");
    let gm_hex = hex_of(&gm_cell);

    // The host published the affordance surface for discovery.
    {
        let s = state.read().await;
        let specs = s
            .deos_server_surfaces
            .get(&gm_cell)
            .expect("the gm server's surface is published");
        assert!(
            specs.iter().any(|(n, _)| n == "knock"),
            "the published surface carries the knock affordance"
        );
    }

    // Build the router ONCE (the genuine node HTTP surface) for both discovery + fire.
    let metrics_handle = crate::metrics::install_recorder();
    let make_router = || {
        crate::api::router_with_cors(state.clone(), false, metrics_handle.clone(), HashSet::new())
    };

    // ── (4) the CLIENT DISCOVERS the affordance via the node's HTTP route ─────────
    let disco_uri = format!("/api/server/{gm_hex}/affordances?viewer=signature");
    let disco_resp = make_router()
        .oneshot(
            Request::builder()
                .uri(&disco_uri)
                .body(Body::empty())
                .unwrap(),
        )
        .await
        .expect("discovery request");
    assert_eq!(
        disco_resp.status(),
        StatusCode::OK,
        "discovery route returns OK"
    );
    let disco_body = disco_resp.into_body().collect().await.unwrap().to_bytes();
    let disco: serde_json::Value = serde_json::from_slice(&disco_body).unwrap();
    let names: Vec<String> = disco["affordances"]
        .as_array()
        .unwrap()
        .iter()
        .map(|a| a["name"].as_str().unwrap().to_string())
        .collect();
    assert!(
        names.contains(&"knock".to_string()),
        "a signature-holding client discovers the knock affordance; got {names:?}"
    );

    // ── (5) the CLIENT BUILDS + SIGNS + FIRES the knock turn ──────────────────────
    let door_field_before = {
        let s = state.read().await;
        s.ledger
            .get(&door_cell)
            .expect("door cell present")
            .state
            .get_field(0)
            .map(unpack_u64)
            .unwrap_or(0)
    };
    assert_eq!(door_field_before, 0, "door starts closed (field 0 == 0)");

    // The knock effect = the affordance's published effect: SetField(door, 0, 1).
    let knock = Effect::SetField {
        cell: door_cell,
        index: 0,
        value: pack_u64(1),
    };

    let signed_bytes = {
        let s = state.read().await;
        let exec_fed = crate::executor_setup::federation_id_for_executor(&s);
        let nonce = s
            .ledger
            .get(&player_cell)
            .map(|c| c.state.nonce())
            .unwrap_or(0);
        // The PLAYER's own causal head — the value `post_submit_signed_turn` checks
        // (`agent_receipt_head_hash(&signed.turn.agent)`). The node-wide log head is a
        // different question and only agrees here because the fixture's earlier commits
        // happen to be the player's.
        let prev = s.cclerk.agent_receipt_head_hash(&player_cell);

        let action = player_cclerk.make_action(player_cell, "knock", vec![knock], &exec_fed);
        let mut call_forest = CallForest::new();
        call_forest.add_root(action);
        let mut turn = Turn {
            agent: player_cell,
            nonce,
            fee: 0,
            memo: Some("player_knock".to_string()),
            valid_until: Some(i64::MAX / 2),
            call_forest,
            depends_on: vec![],
            previous_receipt_hash: prev,
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        };
        let executor = crate::executor_setup::new_submit_executor(&s);
        turn.fee = executor.estimate_cost(&turn);
        let signed = player_cclerk.sign_turn(&turn);
        postcard::to_stdvec(&signed).expect("serialize SignedTurn")
    };

    // A loopback ConnectInfo so the rate limiter + the pre-passphrase loopback auth
    // gate admit the in-process request (the genuine handler extracts both).
    let loopback = std::net::SocketAddr::from(([127, 0, 0, 1], 54321));
    let mut fire_req = Request::builder()
        .method("POST")
        .uri("/turns/submit")
        .header("Content-Type", "application/octet-stream")
        .body(Body::from(signed_bytes))
        .unwrap();
    fire_req
        .extensions_mut()
        .insert(axum::extract::ConnectInfo(loopback));
    let fire_resp = make_router().oneshot(fire_req).await.expect("fire request");
    assert_eq!(
        fire_resp.status(),
        StatusCode::OK,
        "submit route returns 200"
    );
    let fire_body = fire_resp.into_body().collect().await.unwrap().to_bytes();
    let fire: serde_json::Value = serde_json::from_slice(&fire_body).unwrap();
    assert_eq!(
        fire["accepted"].as_bool(),
        Some(true),
        "the player's knock turn was ACCEPTED; body={fire}"
    );

    // ── (6) ASSERT: the door field changed on the real ledger; a receipt landed ───
    let (door_field_after, receipts_after, last_agent) = {
        let s = state.read().await;
        let field = s
            .ledger
            .get(&door_cell)
            .expect("door cell present")
            .state
            .get_field(0)
            .map(unpack_u64)
            .unwrap_or(0);
        let count = s.cclerk.receipt_chain_length();
        let agent = s.cclerk.receipt_chain().last().map(|r| r.agent);
        (field, count, agent)
    };

    assert_eq!(
        door_field_after, 1,
        "the CLIENT's fire flipped the door's field on the REAL node ledger (0 → 1)"
    );
    assert!(
        receipts_after > receipts_before,
        "a real TurnReceipt landed (chain {receipts_before} → {receipts_after})"
    );
    assert_eq!(
        last_agent,
        Some(player_cell),
        "the committed receipt's agent is the PLAYER's own cell (a client-signed turn)"
    );
}
