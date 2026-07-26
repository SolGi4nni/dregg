//! deos_host_fork_client_e2e.rs — THE FORK + CLIENT-HELPER KEYSTONE, PROVEN BY RUNNING.
//!
//! This proves the two halves the deos-host split needs:
//!
//!   * a hosted private-server program FORKS an INSTANCE (`deos.server.fork(seed)`) — a
//!     cap-bounded fork of its world for a party/session (a fresh OPEN cell minted on the
//!     node's live ledger), and registers a cap-gated affordance SCOPED to that instance;
//!   * a CLIENT (the gpui-free `dregg-sdk-net` helper) CONNECTS over real HTTP, DISCOVERS
//!     the instance's affordance surface, and FIRES the affordance — a real signed turn on
//!     the node's live ledger that flips the instance cell's field.
//!
//! Unlike `deos_host_e2e` (an in-process axum `oneshot`), this binds a REAL TCP listener
//! and drives `dregg_sdk_net::{discover_server_affordances, fire_affordance}` over the
//! wire — exercising the genuine client-over-HTTP path a cockpit or thin client uses.
#![cfg(all(test, feature = "deos-host"))]

use std::net::SocketAddr;

use dregg_cell::{AuthRequired, Cell, CellId, Permissions};
use dregg_sdk::AgentCipherclerk;
use dregg_turn::action::Effect;
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

fn hex_of(id: &CellId) -> String {
    dregg_types::hex_encode(id.as_bytes())
}

/// The cell `deos.server.fork(seed)` mints — `mint_open_cell` derives the pubkey as
/// `blake3(seed)` and the cell id as `derive_raw(pubkey, blake3("default"))`.
fn forked_cell_for(seed: &str) -> CellId {
    let public_key = *blake3::hash(seed.as_bytes()).as_bytes();
    CellId(dregg_cell::CellId::derive_raw(&public_key, &default_token_id()).0)
}

/// The agent cell id the node's signed-turn ingress derives from a pubkey.
fn agent_cell_for(pubkey: &[u8; 32]) -> CellId {
    CellId(dregg_cell::CellId::derive_raw(pubkey, &default_token_id()).0)
}

fn pack_u64(v: u64) -> dregg_cell::state::FieldElement {
    dregg_cell::field_from_u64(v)
}

fn unpack_u64(fe: &dregg_cell::state::FieldElement) -> u64 {
    dregg_cell::field_to_u64(fe)
}

async fn instance_field0(state: &NodeState, cell: &CellId) -> u64 {
    let s = state.read().await;
    s.ledger
        .get(cell)
        .expect("cell present")
        .state
        .get_field(0)
        .map(|fe| unpack_u64(&fe))
        .unwrap_or(0)
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn server_forks_instance_and_client_discovers_and_fires_over_http() {
    let _ = rustls::crypto::ring::default_provider().install_default();

    // ── (1) a headless NodeState (NO gpui — node + deos-js only) ────────────────────
    let tmp = tempfile::tempdir().expect("tempdir");
    let state = NodeState::new(tmp.path(), vec![]).expect("build NodeState");
    {
        let mut s = state.write().await;
        s.unlocked = true; // the signed-turn ingress requires an unlocked node
    }

    // THE PLAYER — its own cipherclerk + cell (the client identity that discovers + fires).
    let player_cclerk = AgentCipherclerk::from_key_bytes(Zeroizing::new(
        *blake3::hash(b"fork-client-player").as_bytes(),
    ));
    let player_pubkey = player_cclerk.public_key().0;
    let player_cell = agent_cell_for(&player_pubkey);

    // Mint an OPEN, funded player cell so its signed turn passes the nonce + budget gates.
    {
        let mut s = state.write().await;
        let mut player = Cell::with_balance(player_pubkey, default_token_id(), 1_000_000);
        player.permissions = open_permissions();
        assert_eq!(
            player.id(),
            player_cell,
            "player cell id must match derivation"
        );
        s.ledger.insert_cell(player).expect("insert player cell");
    }

    // ── (2) HOST fork_gm.js — its setup FORKS a party instance + registers a
    //        cap-gated affordance scoped to it ──────────────────────────────────────
    let program =
        include_str!("../tests/fixtures/fork_gm.js").replace("__PLAYER__", &hex_of(&player_cell));
    let server_cell = crate::deos_host::host_server_program(
        &state,
        "fork-gamemaster",
        AuthRequired::None,
        program,
    )
    .await
    .expect("host the fork_gm.js private server");

    // The instance the fork minted (deterministic from its seed).
    let instance_cell = forked_cell_for("party-session-1");
    let instance_hex = hex_of(&instance_cell);

    // The host published the INSTANCE as its own discoverable surface (keyed by the
    // instance cell, NOT the root server cell — the fork is a distinct surface).
    {
        let s = state.read().await;
        assert!(
            s.ledger.get(&instance_cell).is_some(),
            "the forked instance cell exists on the real ledger"
        );
        let inst_specs = s
            .deos_server_surfaces
            .get(&instance_cell)
            .expect("the forked instance's surface is published");
        assert!(
            inst_specs.iter().any(|(n, _)| n == "raise-flag"),
            "the instance surface carries the raise-flag affordance"
        );
        // The ROOT server surface has NO affordances (the only one was instance-scoped).
        let root_specs = s
            .deos_server_surfaces
            .get(&server_cell)
            .expect("the root server surface is published");
        assert!(
            root_specs.is_empty(),
            "the root surface is empty (the affordance was scoped to the fork); got {root_specs:?}"
        );
    }

    // ── (3) bind a REAL HTTP listener so the dregg-sdk-net client drives the wire ───
    let metrics_handle = crate::metrics::install_recorder();
    let router = crate::api::router_with_cors(
        state.clone(),
        false,
        metrics_handle,
        std::collections::HashSet::new(),
    );
    let listener = tokio::net::TcpListener::bind("127.0.0.1:0")
        .await
        .expect("bind ephemeral port");
    let addr = listener.local_addr().expect("local addr");
    let server = tokio::spawn(async move {
        axum::serve(
            listener,
            router.into_make_service_with_connect_info::<SocketAddr>(),
        )
        .await
        .expect("serve");
    });
    let node_url = format!("http://{addr}");

    // ── (4) the CLIENT DISCOVERS the forked instance's surface (gpui-free helper) ───
    let discovery =
        dregg_sdk_net::discover_server_affordances(&node_url, &instance_hex, "signature")
            .await
            .expect("client discovers the instance surface");
    assert!(
        discovery.has("raise-flag"),
        "a signature-holding client discovers raise-flag on the instance; got {:?}",
        discovery.affordances
    );
    assert_eq!(
        discovery.executor_federation_id.len(),
        64,
        "discovery hands back the executor federation id (the fire-signing binding)"
    );

    // ── (5) the CLIENT FIRES raise-flag into the instance (signed turn over HTTP) ───
    assert_eq!(
        instance_field0(&state, &instance_cell).await,
        0,
        "the instance flag starts down (field 0 == 0)"
    );

    // The client's intent: raise-flag = SetField(instance, slot 0 := 1). The published
    // surface advertises the message + the authority it needs; the client supplies the
    // concrete effect (re-checked by the node's authority gate — the open instance admits
    // the player's signed cross-cell write).
    let raise = Effect::SetField {
        cell: instance_cell,
        index: 0,
        value: pack_u64(1),
    };
    let outcome = dregg_sdk_net::fire_affordance(
        &node_url,
        &player_cclerk,
        player_cell,
        "raise-flag",
        vec![raise],
        &discovery.executor_federation_id,
    )
    .await
    .expect("client fires raise-flag over HTTP");
    assert!(
        outcome.accepted,
        "the client's raise-flag turn was ACCEPTED; error={:?}",
        outcome.error
    );

    // ── (6) ASSERT: the instance's field flipped on the real ledger ─────────────────
    assert_eq!(
        instance_field0(&state, &instance_cell).await,
        1,
        "the CLIENT's fire flipped the forked instance's field on the REAL ledger (0 -> 1)"
    );

    server.abort();
}
