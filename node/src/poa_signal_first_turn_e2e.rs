//! poa_signal_first_turn_e2e.rs — THE MILESTONE: `latest_height` 0 → 1 with a
//! real JUDGED Signal turn, end to end through a live solo `dregg-node`.
//!
//! Path of Angels has never settled a game turn in production: `latest_height`
//! is 0 on the live node, so every judged Signal game is practice-only. The
//! machinery to change that has existed for a while — the curator ceremony opens
//! a slot, the finalized-turn path invokes the native Lean judge, and the weld
//! advances the persisted authority — but nothing had ever driven the WHOLE
//! chain and read the one public number that says a turn settled:
//! `store.latest_attested_root().height`, surfaced as `latest_height` on
//! `GET /status`.
//!
//! This test IS that drive, against the real router and the real consensus loop:
//!
//!   1. a solo node (committee = itself), a PoA Signal genesis head, and a slot
//!      opened through the GENUINE ceremony — the curator pin, a real Ed25519
//!      signature over the canonical statement, and the Lean-derived commitment
//!      re-checked by `install_poa_signal_slot_v1` (no `_for_test` stub);
//!   2. a funded player submits its GENUINELY-SOLVED Signal claim to the public
//!      `POST /api/poa/signal/{authority}/claims` route;
//!   3. the solo consensus loop orders it, the finalized-turn path runs the
//!      NATIVE Lean judge, the judged verdict finalizes, and the attested root
//!      advances;
//!   4. `GET /status` reports `latest_height == 1`, and the persisted authority
//!      carries exactly one judged transition.
//!
//! The assertion that BITES is `latest_height` read off the real `/status` wire
//! AFTER finalization — never the `accepted:true` the submit returns, which is
//! true for a losing guess too (admission staging is rolled back in every mode).
//! A settle that returned a plausible receipt without the Lean judge finalizing
//! would leave `latest_height` at 0, and this test would hang to its timeout and
//! fail — which is the honest outcome, not a green.
//!
//! ⚠ Requires the linked Lean archive (the judge + the slot-derivation export).
//! It DEMANDS them rather than skipping: a milestone test that quietly stopped
//! exercising the judge would report the milestone reached while proving nothing.
//!
//! The solving code is derived here because this harness holds the slot secret —
//! it is the operator AND the curator. Holding the secret is what knowing the
//! instance MEANS. A real external player, with no secret, plays the deduction
//! game: for the very first turn with no feedback that is a blind guess out of
//! the 216-code space (`docs`: the info-floor is 3 feedback rounds), which is
//! why a ≤216 sweep is the honest first-turn strategy for a stranger. The judge
//! is identical on either path; only who-knows-the-answer differs.

#![cfg(test)]

use std::time::{Duration, Instant};

use axum::body::Body;
use axum::extract::ConnectInfo;
use axum::http::{Request, StatusCode};
use dregg_persist::{PoaSlotOpeningStatementV1, SignedPoaSlotOpeningEnvelopeV1};
use dregg_types::hex_encode;
use ed25519_dalek::{Signer as _, SigningKey};
use http_body_util::BodyExt as _;
use tower::ServiceExt as _;
use zeroize::Zeroizing;

use crate::blocklace_sync::run_blocklace_sync_with_policy;
use crate::state::NodeState;

/// The slot this milestone opens. Any slot works; this matches the frozen
/// finality fixture so the derived solving code lines up with the fixture head.
const SLOT: u64 = 9;
/// The one public mission id (`POA_SIGNAL_PUBLIC_MISSION_ID`).
const MISSION_ID: u64 = 1;
/// The curator's slot secret. This is the SAME 32 bytes the pinned derive-wire
/// fixture commits (`7777…`), so the genuine ceremony install below reproduces
/// exactly the slot state (secret, slot, commitment) the fixture head was built
/// against — but reaches it through the real signature + Lean-commitment gate,
/// not the `_for_test` stub. A real deployment draws this off-line and never
/// checks it in; here it is a committed test secret, whose answer is therefore
/// computable by anyone holding it, which is precisely the property the split
/// preserves.
const SECRET: [u8; 32] = [0x77; 32];

fn default_token() -> [u8; 32] {
    crate::executor_setup::default_token_id()
}

/// Stand up a solo node with the PoA Signal world genesised and a slot opened
/// through the genuine curator ceremony, then start the real consensus loop and
/// the real router. Returns the derived federation id and the funded player.
async fn signal_solo_node() -> (
    NodeState,
    axum::Router,
    [u8; 32],
    dregg_sdk::AgentCipherclerk,
    tempfile::TempDir,
) {
    let _ = rustls::crypto::ring::default_provider().install_default();
    // The deployed node installs the Lean-verified ML-DSA cores in `run()`; a lib
    // test never reaches that, so install them here — otherwise the hybrid
    // perimeter degrades to "no PQ half present" and the funded player's identity
    // commitment would not match the key its turn signs with.
    let _ = crate::install_mldsa_verified_keygen_core_real();
    let _ = crate::install_mldsa_verified_sign_core_real();
    let _ = crate::install_mldsa_verified_verify_core();
    // The judge and the slot-derivation export must be linked, or the milestone
    // would be an unchecked number. DEMAND them.
    assert!(
        dregg_lean_ffi::poa_ffi::poa_signal_judge_available(),
        "this milestone requires the linked native PoA Signal judge"
    );
    assert!(
        dregg_lean_ffi::poa_slot_derive_ffi::poa_slot_derive_available(),
        "this milestone requires the linked PoA slot-derivation export"
    );

    let tmp = tempfile::tempdir().expect("tempdir");
    let state = NodeState::new(tmp.path(), vec![]).expect("build NodeState");

    // A fresh player identity no node has seen. Its default cell IS the Signal
    // player cell (`signal_player_cell = derive_raw(pk, blake3("default"))`).
    let player = dregg_sdk::AgentCipherclerk::from_key_bytes(Zeroizing::new([0xC7; 32]));

    let federation_id;
    {
        let mut s = state.write().await;
        s.unlocked = true;

        // THE COMMITTEE IS THIS NODE, ALONE. `known_federation_keys` of length one
        // makes the consensus loop solo (participants = [self], quorum = 1); it
        // also exits discovery mode so the public Signal routes resolve their
        // authority. The player is a USER, never a validator.
        let node_pk = s.cclerk.public_key();
        let node_seed = s.cclerk.gossip_signing_key().to_bytes();
        let (node_ml_dsa, _) = dregg_federation::frost::MlDsaSigningKey::from_seed(&node_seed);
        s.set_federation_keys_hybrid(vec![node_pk], vec![node_ml_dsa]);
        // The real run path installs solo consensus state; mirror it so the
        // finalizer stages the solo receipt exactly as production does.
        s.solo_consensus = Some(dregg_federation::solo::SoloConsensusState::new(node_seed));
        federation_id = crate::executor_setup::federation_id_for_executor(&s);

        // Fund the player with a COMMITTED hybrid identity. With the committee the
        // node alone, the roster does not stand in for a spender's PQ half, so a
        // bare `with_balance` cell is refused "required post-quantum target-cell
        // identity is not committed". `with_hybrid_balance` commits it.
        s.ledger
            .insert_cell(
                dregg_cell::Cell::with_hybrid_balance(
                    player.public_key().0,
                    &player.ml_dsa_public_bytes(),
                    default_token(),
                    1_000_000,
                )
                .expect("canonical ML-DSA-65 player identity"),
            )
            .expect("fund the Signal player");

        // Genesis the PoA Signal authority head under THIS federation id.
        let head = crate::poa_signal_adapter::fixture_signal_head_for_finality_test(federation_id);
        s.store
            .initialize_poa_signal_head(&head)
            .expect("initialize the PoA Signal authority head");

        // ── THE GENUINE SLOT-OPENING CEREMONY (no `_for_test` stub) ──────────
        // 1. derive the commitment through Lean (a function of secret+slot alone);
        // 2. a curator signs the canonical statement with a real Ed25519 key;
        // 3. `install_poa_signal_slot_v1` re-verifies the signature against the
        //    pinned curator key AND re-derives the commitment through Lean.
        let commitment = crate::poa_signal_slot_ceremony::derive_commitment(SECRET, SLOT)
            .expect("Lean derives the slot commitment");
        let statement = PoaSlotOpeningStatementV1::new(federation_id, MISSION_ID, SLOT, commitment);
        let curator = SigningKey::from_bytes(&[0xC0; 32]);
        let signature = curator.sign(
            &statement
                .signing_message()
                .expect("canonical slot-opening signing message"),
        );
        let envelope = SignedPoaSlotOpeningEnvelopeV1::new(
            statement,
            curator.verifying_key().to_bytes(),
            signature.to_bytes(),
        );
        s.store
            .install_poa_world_curator_pin_v1(curator.verifying_key().to_bytes())
            .expect("pin the curator key");
        let status = s
            .store
            .install_poa_signal_slot_v1(&envelope, SECRET)
            .expect("a curator-signed opening whose secret opens it must install");
        assert_eq!(
            status,
            dregg_persist::PoaSlotInstallStatusV1::Installed,
            "the ceremony must install a fresh slot"
        );
    }

    let handle = run_blocklace_sync_with_policy(
        state.clone(),
        0,      // gossip_port 0 ⇒ OS-assigned ephemeral
        true,   // auto_approve_joins (irrelevant: the node is already the sole member)
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
    (state, app, federation_id, player, tmp)
}

/// The exact player-signed Signal carrier: build the one-action `poa-signal`
/// turn, attach the hybrid authorization, and sign the turn — byte-for-byte what
/// an SDK client emits.
fn solved_signal_turn(
    player: &dregg_sdk::AgentCipherclerk,
    federation_id: [u8; 32],
    claim: dregg_sdk::poa_signal::SignalClaimV1,
) -> dregg_sdk::SignedTurn {
    let mut turn = dregg_sdk::poa_signal::signal_claim_turn(&player.public_key().0, 0, None, claim);
    let unsigned = turn.call_forest.roots[0].action.clone();
    turn.call_forest.roots[0].action = player.sign_action(unsigned, &federation_id);
    turn.call_forest.roots[0].hash = [0; 32];
    turn.call_forest.forest_hash = [0; 32];
    player.sign_turn(&turn)
}

/// POST a postcard `SignedTurn` to the public Signal claims route.
async fn post_claim(
    app: &axum::Router,
    authority_hex: &str,
    signed: &dregg_sdk::SignedTurn,
) -> (StatusCode, serde_json::Value) {
    let addr: std::net::SocketAddr = "127.0.0.1:4466".parse().unwrap();
    let wire = postcard::to_stdvec(signed).expect("encode SignedTurn");
    let response = app
        .clone()
        .oneshot(
            Request::builder()
                .method("POST")
                .uri(format!("/api/poa/signal/{authority_hex}/claims"))
                .header("content-type", "application/octet-stream")
                .extension(ConnectInfo(addr))
                .body(Body::from(wire))
                .expect("claim request"),
        )
        .await
        .expect("claim response");
    let status = response.status();
    let bytes = response
        .into_body()
        .collect()
        .await
        .expect("body")
        .to_bytes();
    let json = if bytes.is_empty() {
        serde_json::Value::Null
    } else {
        serde_json::from_slice(&bytes).unwrap_or(serde_json::Value::Null)
    };
    (status, json)
}

/// GET a JSON route through the real router.
async fn get_json(app: &axum::Router, uri: &str) -> serde_json::Value {
    let response = app
        .clone()
        .oneshot(
            Request::builder()
                .uri(uri)
                .extension(ConnectInfo(
                    "127.0.0.1:4467".parse::<std::net::SocketAddr>().unwrap(),
                ))
                .body(Body::empty())
                .expect("get request"),
        )
        .await
        .expect("get response");
    let bytes = response
        .into_body()
        .collect()
        .await
        .expect("body")
        .to_bytes();
    serde_json::from_slice(&bytes).expect("json body")
}

/// Poll `GET /status` until `latest_height == want`, or time out. Returns the
/// last observed height.
async fn await_latest_height(app: &axum::Router, want: u64, within: Duration) -> u64 {
    let deadline = Instant::now() + within;
    let mut seen = 0;
    loop {
        let status = get_json(app, "/status").await;
        seen = status["latest_height"].as_u64().unwrap_or(seen);
        if seen == want || Instant::now() >= deadline {
            return seen;
        }
        tokio::time::sleep(Duration::from_millis(100)).await;
    }
}

/// THE MILESTONE, end to end: a genuinely-solved judged Signal turn moves the
/// public `latest_height` from 0 to 1 on a live solo node.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_judged_signal_turn_moves_latest_height_from_zero_to_one() {
    let (state, app, federation_id, player, _tmp) = signal_solo_node().await;
    let authority = hex_encode(&federation_id);

    // Before any turn settles, the public number is 0 — the exact live symptom
    // this milestone exists to move.
    let before = get_json(&app, "/status").await;
    assert_eq!(
        before["latest_height"].as_u64(),
        Some(0),
        "a fresh node has settled no turns: {before}"
    );

    // The genuinely-solving code for THIS instance (this slot, this player).
    // Derived because the harness holds the slot secret; a stranger sweeps ≤216.
    let claim = crate::poa_signal_adapter::solving_claim_for_finality_test(
        &crate::poa_signal_adapter::fixture_signal_head_for_finality_test(federation_id),
        &crate::poa_signal_adapter::fixture_signal_slot_for_finality_test(federation_id),
        federation_id,
        player.public_key().0,
        [0u8; 32],
    );
    assert_eq!(
        u64::from(claim.mission_id()),
        MISSION_ID,
        "the solving claim must name the public mission"
    );

    let signed = solved_signal_turn(&player, federation_id, claim);
    let (status, body) = post_claim(&app, &authority, &signed).await;
    assert_eq!(
        status,
        StatusCode::OK,
        "the public claims route must admit a well-formed solved claim: {body}"
    );
    assert_eq!(
        body["accepted"], true,
        "admission staging accepts the claim (this alone settles nothing): {body}"
    );

    // ── THE ASSERTION THAT BITES: the public height AFTER finalization. ──────
    let height = await_latest_height(&app, 1, Duration::from_secs(45)).await;
    assert_eq!(
        height, 1,
        "a genuinely-solved judged Signal turn MUST finalize and move latest_height 0 -> 1. \
         Still 0 means the Lean judge never finalized the settle — the exact non-event the live \
         PoA node has shown since genesis."
    );

    // The judged verdict genuinely ran: the persisted authority carries exactly
    // one transition, and the world/canon advanced.
    {
        let s = state.read().await;
        let head = s
            .store
            .load_poa_signal_head(federation_id)
            .expect("PoA head read")
            .expect("advanced PoA head");
        assert_eq!(
            head.transition_count(),
            1,
            "exactly one judged transition settled"
        );
        assert_eq!(head.world_sequence(), 1, "the judged world advanced");
        assert_eq!(head.canon_revision(), 1, "the judged Canon advanced");
        assert!(
            s.store
                .load_poa_signal_transition(federation_id, 1)
                .expect("transition read")
                .is_some(),
            "the durable transition for sequence 1 must exist"
        );
    }

    // And the public Signal status route reflects the settled turn.
    let signal_status = get_json(&app, &format!("/api/poa/signal/{authority}/status")).await;
    assert_eq!(
        signal_status["transition_count"].as_u64(),
        Some(1),
        "the public Signal status must show one settled transition: {signal_status}"
    );

    // The complete durable semantic replay accepts the settled history: every
    // finalized row re-judged by native Lean, byte-identical, from genesis.
    {
        let s = state.read().await;
        let report =
            crate::poa_signal_adapter::audit_persisted_signal_semantics(&s.store, federation_id)
                .expect("durable semantic replay must accept the settled history");
        assert_eq!(report.transition_count, 1);
        assert_eq!(report.authority_id, federation_id);
    }
}
