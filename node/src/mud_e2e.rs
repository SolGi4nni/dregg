//! mud_e2e.rs — THE MUD AS A PURE DEOS-JS SERVER, PROVEN BY RUNNING.
//!
//! The architecture this proves: a MUD is a userspace deos-js program (`mud_gm.js`) the
//! headless dregg node HOSTS — the rich living world, NOT fog-of-war. The GAMEMASTER is a
//! PRIVILEGED server holding broad caps over its whole world; players are cap-constrained
//! and drive the world ONLY through signed turns over the affordances the GM offers. No
//! Rust gameplay logic, no gpui — the world is DATA + verified turns on the node's ledger.
//!
//! THE LIVING-WORLD ARC (each step a hard assertion; DONE = ran):
//!   1. boot a headless `NodeState` (NO gpui — node + deos-js only); fund the player cell;
//!   2. HOST `mud_gm.js`: the GM spawns ROOMS (entrance + hall), a CHARACTER (level 1, xp
//!      0, room = entrance — stamped via the setField superpower), an NPC (watchman,
//!      calm), GRANTS the player a cap over its character, and registers the cap-gated
//!      gameplay affordances MOVE + GAIN-XP — all REAL verified turns on the ledger;
//!   3. ASSERT the published surface carries `move` + `gain-xp` and the character was
//!      stamped (level 1, xp 0, room 1) on the real ledger;
//!   4. a CLIENT (the player) DISCOVERS the affordances via the node's HTTP route;
//!   5. the player FIRES `gain-xp` (signed turn → SetField xp := 120) → xp lands on ledger;
//!   6. the player FIRES `move` (signed turn → SetField room := 2 = the hall) → lands;
//!   7. HOST `mud_gm_tick.js`: the GM OBSERVES xp ≥ 100 and the player's arrival, then
//!      drives the world's response — a LEVEL-UP (level := 2, xp reset, a real turn), an
//!      NPC REACTION (the watchman goes alert), and opens a DUNGEON INSTANCE (a fresh
//!      private room-set spawned for the party). ASSERT all three landed;
//!   8. THE ASYMMETRY (receipted): a player attempting GM-only moves — a cross-cell write
//!      on the NPC it holds NO cap over, and a cross-cell write into a DUNGEON INSTANCE it
//!      holds no cap over (the membrane-fork isolation) — is REFUSED by the executor's
//!      authority gate, while the GM's own moves over the same cells committed.
#![cfg(all(test, feature = "deos-host"))]

use std::collections::HashSet;

use axum::body::Body;
use axum::http::{Request, StatusCode};
use dregg_cell::{AuthRequired, Cell, CellId, Permissions};
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

/// Pack a u64 into a `FieldElement` (LE low 8 bytes) — matches deos-js `pack_u64`.
fn pack_u64(v: u64) -> dregg_cell::state::FieldElement {
    let mut fe = [0u8; 32];
    fe[..8].copy_from_slice(&v.to_le_bytes());
    fe
}

/// Read a u64 back out of a `FieldElement` (LE low 8 bytes).
fn unpack_u64(fe: &dregg_cell::state::FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&fe[..8]);
    u64::from_le_bytes(b)
}

fn hex_of(id: &CellId) -> String {
    dregg_types::hex_encode(id.as_bytes())
}

/// Derive an agent cell id the way the node's signed-turn ingress does.
fn agent_cell_for(pubkey: &[u8; 32]) -> CellId {
    CellId(dregg_cell::CellId::derive_raw(pubkey, &default_token_id()).0)
}

/// Derive a cell id the way `deos.server.spawnCell(seed, ...)` does: the seed is hashed to
/// a pubkey (it is not a 64-char hex), then derived against the default token domain.
fn spawned_cell_for(seed: &str) -> CellId {
    let pubkey = *blake3::hash(seed.as_bytes()).as_bytes();
    CellId(dregg_cell::CellId::derive_raw(&pubkey, &default_token_id()).0)
}

/// Read field `index` (as u64) of `cell` off the live ledger; `None` if cell absent.
async fn field_of(state: &NodeState, cell: &CellId, index: usize) -> Option<u64> {
    let s = state.read().await;
    s.ledger
        .get(cell)
        .map(|c| c.state.get_field(index).map(unpack_u64).unwrap_or(0))
}

/// Build + sign + submit ONE single-effect turn AS `signer`'s own agent cell, returning
/// the parsed `/turns/submit` JSON response (the genuine remote client path).
async fn fire_signed(
    state: &NodeState,
    metrics_handle: &metrics_exporter_prometheus::PrometheusHandle,
    signer: &dregg_sdk::AgentCipherclerk,
    agent: CellId,
    method: &str,
    effect: Effect,
) -> serde_json::Value {
    let signed_bytes = {
        let s = state.read().await;
        let exec_fed = crate::executor_setup::federation_id_for_executor(&s);
        let nonce = s.ledger.get(&agent).map(|c| c.state.nonce()).unwrap_or(0);
        let prev = s.cclerk.receipt_chain().last().map(|r| r.receipt_hash());
        let action = signer.make_action(agent, method, vec![effect], &exec_fed);
        let mut call_forest = CallForest::new();
        call_forest.add_root(action);
        let mut turn = Turn {
            agent,
            nonce,
            fee: 0,
            memo: Some(format!("mud_{method}")),
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
        let signed = signer.sign_turn(&turn);
        postcard::to_stdvec(&signed).expect("serialize SignedTurn")
    };

    let loopback = std::net::SocketAddr::from(([127, 0, 0, 1], 54321));
    let mut req = Request::builder()
        .method("POST")
        .uri("/turns/submit")
        .header("Content-Type", "application/octet-stream")
        .body(Body::from(signed_bytes))
        .unwrap();
    req.extensions_mut()
        .insert(axum::extract::ConnectInfo(loopback));
    let resp =
        crate::api::router_with_cors(state.clone(), false, metrics_handle.clone(), HashSet::new())
            .oneshot(req)
            .await
            .expect("submit request");
    assert_eq!(resp.status(), StatusCode::OK, "submit route returns 200");
    let body = resp.into_body().collect().await.unwrap().to_bytes();
    serde_json::from_slice(&body).unwrap()
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn headless_node_hosts_mud_living_world() {
    let _ = rustls::crypto::ring::default_provider().install_default();

    // ── (1) a headless NodeState (NO gpui — node + deos-js only) ────────────────────
    let tmp = tempfile::tempdir().expect("tempdir");
    let state = NodeState::new(tmp.path(), vec![]).expect("build NodeState");
    {
        let mut s = state.write().await;
        s.unlocked = true; // the signed-turn ingress requires an unlocked node
    }

    // THE PLAYER — its own cipherclerk + funded, open cell (the client identity).
    let player_cclerk = dregg_sdk::AgentCipherclerk::from_key_bytes(Zeroizing::new(
        *blake3::hash(b"mud-player-aria").as_bytes(),
    ));
    let player_pubkey = player_cclerk.public_key().0;
    let player_cell = agent_cell_for(&player_pubkey);
    {
        let mut s = state.write().await;
        let token = default_token_id();
        let mut player = Cell::with_balance(player_pubkey, token, 1_000_000);
        player.permissions = open_permissions();
        assert_eq!(
            player.id(),
            player_cell,
            "player cell id must match derivation"
        );
        s.ledger.insert_cell(player).expect("insert player cell");
    }

    // The deterministic ids the GM program's spawns will derive (so we can assert on the
    // real ledger). They mirror `deos.server.spawnCell(seed, ...)`'s derivation.
    let character = spawned_cell_for("mud-char-aria");
    let watchman = spawned_cell_for("mud-npc-watchman");
    let entrance = spawned_cell_for("mud-room-entrance");
    let hall = spawned_cell_for("mud-room-hall");
    // The dungeon instances the GM FORKS (mint_open_cell derives id == blake3(seed)).
    let dungeon_party1 = spawned_cell_for("mud-dungeon-party1");
    let dungeon_party2 = spawned_cell_for("mud-dungeon-party2");
    let dungeon_crypt2 = spawned_cell_for("mud-dungeon-crypt-party2");

    let metrics_handle = crate::metrics::install_recorder();

    // ── (2) HOST mud_gm.js — the GM spawns the world + registers the affordances ────
    let gm_program =
        include_str!("../tests/fixtures/mud_gm.js").replace("__PLAYER__", &hex_of(&player_cell));
    let gm_cell = crate::deos_host::host_server_program(
        &state,
        "mud-gamemaster",
        AuthRequired::None,
        gm_program,
    )
    .await
    .expect("host the mud_gm.js gamemaster");
    let gm_hex = hex_of(&gm_cell);

    // ── (3) the world STOOD UP on the real ledger ───────────────────────────────────
    {
        let s = state.read().await;
        let specs = s
            .deos_server_surfaces
            .get(&gm_cell)
            .expect("the GM server's surface is published");
        let names: Vec<&str> = specs.iter().map(|(n, _)| n.as_str()).collect();
        assert!(
            names.contains(&"move"),
            "the surface carries MOVE; got {names:?}"
        );
        assert!(
            names.contains(&"gain-xp"),
            "the surface carries GAIN-XP; got {names:?}"
        );
        // The rooms + npc exist as real cells; the character was stamped.
        assert!(
            s.ledger.get(&entrance).is_some(),
            "the entrance room exists"
        );
        assert!(s.ledger.get(&hall).is_some(), "the hall room exists");
        assert!(s.ledger.get(&watchman).is_some(), "the watchman NPC exists");
        // The DUNGEON INSTANCE forked at setup is a real OPEN cell with its OWN published
        // surface (the membrane-fork): the `descend` affordance is scoped to it, NOT the
        // root server surface.
        assert!(
            s.ledger.get(&dungeon_party1).is_some(),
            "the dungeon instance (party1) was forked"
        );
        assert!(
            !names.contains(&"descend"),
            "descend is NOT on the root surface (it is fork-scoped)"
        );
        let fork_specs = s
            .deos_server_surfaces
            .get(&dungeon_party1)
            .expect("the dungeon fork's own surface is published");
        assert!(
            fork_specs.iter().any(|(n, _)| n == "descend"),
            "the dungeon instance's OWN surface carries `descend`; got {fork_specs:?}"
        );
    }
    assert_eq!(
        field_of(&state, &character, 0).await,
        Some(1),
        "character LEVEL stamped to 1"
    );
    assert_eq!(
        field_of(&state, &character, 1).await,
        Some(0),
        "character XP stamped to 0"
    );
    assert_eq!(
        field_of(&state, &character, 2).await,
        Some(1),
        "character ROOM stamped to entrance (1)"
    );
    assert_eq!(
        field_of(&state, &watchman, 0).await,
        Some(0),
        "watchman starts calm (mood 0)"
    );

    // ── (4) the CLIENT DISCOVERS the affordances via the node's HTTP route ──────────
    let disco_uri = format!("/api/server/{gm_hex}/affordances?viewer=signature");
    let disco_resp =
        crate::api::router_with_cors(state.clone(), false, metrics_handle.clone(), HashSet::new())
            .oneshot(
                Request::builder()
                    .uri(&disco_uri)
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .expect("discovery request");
    assert_eq!(disco_resp.status(), StatusCode::OK);
    let disco_body = disco_resp.into_body().collect().await.unwrap().to_bytes();
    let disco: serde_json::Value = serde_json::from_slice(&disco_body).unwrap();
    let names: Vec<String> = disco["affordances"]
        .as_array()
        .unwrap()
        .iter()
        .map(|a| a["name"].as_str().unwrap().to_string())
        .collect();
    assert!(
        names.contains(&"gain-xp".to_string()),
        "player discovers GAIN-XP; got {names:?}"
    );
    assert!(
        names.contains(&"move".to_string()),
        "player discovers MOVE; got {names:?}"
    );

    // ── (5) the player FIRES gain-xp (signed turn → SetField xp := 120) ─────────────
    let gain = fire_signed(
        &state,
        &metrics_handle,
        &player_cclerk,
        player_cell,
        "gain-xp",
        Effect::SetField {
            cell: character,
            index: 1,
            value: pack_u64(120),
        },
    )
    .await;
    assert_eq!(
        gain["accepted"].as_bool(),
        Some(true),
        "the player's GAIN-XP was accepted; body={gain}"
    );
    assert_eq!(
        field_of(&state, &character, 1).await,
        Some(120),
        "character XP rose to 120 on the real ledger"
    );

    // ── (6) the player FIRES move (signed turn → SetField room := 2 = the hall) ─────
    let mov = fire_signed(
        &state,
        &metrics_handle,
        &player_cclerk,
        player_cell,
        "move",
        Effect::SetField {
            cell: character,
            index: 2,
            value: pack_u64(2),
        },
    )
    .await;
    assert_eq!(
        mov["accepted"].as_bool(),
        Some(true),
        "the player's MOVE was accepted; body={mov}"
    );
    assert_eq!(
        field_of(&state, &character, 2).await,
        Some(2),
        "character moved to the hall (room 2)"
    );

    // ── (7) HOST mud_gm_tick.js — the GM OBSERVES + the world RESPONDS ──────────────
    let tick_program = include_str!("../tests/fixtures/mud_gm_tick.js")
        .replace("__CHAR__", &hex_of(&character))
        .replace("__NPC__", &hex_of(&watchman));
    crate::deos_host::host_server_program(
        &state,
        "mud-gamemaster-tick",
        AuthRequired::None,
        tick_program,
    )
    .await
    .expect("host the mud_gm_tick.js reactive tick");

    // LEVEL-UP: xp crossed 100 ⇒ the GM raised the level + reset xp (real turns).
    assert_eq!(
        field_of(&state, &character, 0).await,
        Some(2),
        "the character LEVELED UP to 2"
    );
    assert_eq!(
        field_of(&state, &character, 1).await,
        Some(0),
        "XP reset after the level-up"
    );
    // NPC REACTION: the watchman went alert on the player's arrival in the hall.
    assert_eq!(
        field_of(&state, &watchman, 0).await,
        Some(1),
        "the watchman NPC REACTED (mood 1 = alert)"
    );
    // DUNGEON INSTANCE: the GM opened a fresh private instance for a second party.
    {
        let s = state.read().await;
        assert!(
            s.ledger.get(&dungeon_party2).is_some(),
            "the dungeon instance (party2) opened"
        );
        assert!(
            s.ledger.get(&dungeon_crypt2).is_some(),
            "the party2 crypt room opened"
        );
    }

    // ── (8) THE ASYMMETRY — a player CANNOT do GM-only moves (receipted refusals) ────
    // (a) a player cross-cell write on the NPC it holds NO cap over → REFUSED.
    let forge_npc = fire_signed(
        &state,
        &metrics_handle,
        &player_cclerk,
        player_cell,
        "forge-npc",
        Effect::SetField {
            cell: watchman,
            index: 0,
            value: pack_u64(99),
        },
    )
    .await;
    assert_ne!(
        forge_npc["accepted"].as_bool(),
        Some(true),
        "a player canNOT write the NPC (no cap held) — GM-only; body={forge_npc}"
    );
    assert_eq!(
        field_of(&state, &watchman, 0).await,
        Some(1),
        "the NPC mood is unchanged by the refused forge"
    );

    // (b) a player attempting to reach into a DUNGEON INSTANCE it holds no cap over →
    //     REFUSED. The forked instance is isolated (the membrane-fork): only the GM (which
    //     stood it up) and a player explicitly granted into THAT instance can write it; a
    //     player from the root world cannot forge progress inside someone's party session.
    let forge_dungeon = fire_signed(
        &state,
        &metrics_handle,
        &player_cclerk,
        player_cell,
        "forge-dungeon",
        Effect::SetField {
            cell: dungeon_party1,
            index: 0,
            value: pack_u64(1),
        },
    )
    .await;
    assert_ne!(
        forge_dungeon["accepted"].as_bool(),
        Some(true),
        "a player canNOT write a dungeon instance it holds no cap over (fork isolation); body={forge_dungeon}"
    );
    assert_eq!(
        field_of(&state, &dungeon_party1, 0).await,
        Some(0),
        "the dungeon instance's state is unchanged by the refused forge"
    );
}
