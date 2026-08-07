//! poa_signal_session_e2e.rs — a JUDGED SESSION played end to end through the real
//! router, to both poles: one solves and moves `latest_height` 0 → 1, the other burns
//! its budget and is refused by name without wedging anything.
//!
//! # What this exercises that `poa_signal_first_turn_e2e` does not
//!
//! That milestone proves a *solved claim* settles. It says so plainly about the player
//! it drives: the harness holds the slot secret, and "a real external player, with no
//! secret, plays the deduction game: for the very first turn with no feedback that is a
//! blind guess out of the 216-code space". That was the shape of judged play — a slot
//! machine — and the deduction game it names had **no node-side surface at all**.
//!
//! This test drives that surface. A player opens a judged session, spends bursts, is
//! told LOCKED/DRIFT by the Lean oracle against the instance the judge will score, and
//! settles with the code the session itself hands back.
//!
//! ⚠ **THE HARNESS STILL HOLDS THE SECRET, AND THAT IS SAID OUT LOUD.** It uses it to
//! pick guesses whose classification is a KNOWN CONSEQUENCE of the Lean rule — a
//! derangement of the target must score `exact + present == 3`, and a monochromatic
//! guess on a band the target does not use must score `(0, 0)`
//! (`SignalTriangulation.feedback_of_absent_mono`). Those are the rule's own theorems
//! checked against served bytes.
//!
//! What this file deliberately does NOT contain is a Rust solver. Filtering 216
//! candidates by feedback needs `SignalTriangulation.feedback`, and a second copy of
//! that function in Rust — even in a test, even as "the player" — is the twin this repo
//! spends its time deleting: a copy that disagreed by one on a duplicate band would
//! make the test's player and the node's oracle play different games, and the test
//! would then be measuring the copy. The claim that five rounds suffice is carried
//! where it belongs: `SignalTriangulation.one_round_never_determines_the_target` and
//! `SignalFeedbackRuntime.served_transcript_cannot_separate_feedback_equivalent_targets`.
//!
//! # ⚑ AND IT IS PLAYED ANONYMOUSLY, 2026-08-07
//!
//! Every session request in this file is now sent from [`REMOTE`] — a non-loopback
//! address carrying no bearer token — because `poa_signal_session::routes()` moved from
//! `protected_routes` into `public_routes` today. `require_auth` refuses exactly that
//! caller, so each 200 below is positive evidence the request never reached that layer
//! and the player signature carried the whole authorization.
//!
//! The assertion that used to live here — "the judged session routes must sit behind the
//! bearer gate" — was INVERTED rather than deleted, into the two poles the move has to
//! survive:
//!
//! * **served** — anonymous + a signature that verifies → `200`, and a full judged run
//!   plays through to a settlement,
//! * **refused BY NAME** — anonymous + a wrong, truncated or absent signature →
//!   `401 session-signature`, three ways, with the forgery exhibited to differ from the
//!   honest bytes before the verdict is read, and with the read-back afterwards showing
//!   nothing was opened, resumed or spent.
//!
//! ⚠ Requires the linked Lean archive (judge + derivation + feedback exports). It
//! DEMANDS them rather than skipping.

#![cfg(test)]

use std::net::SocketAddr;
use std::time::{Duration, Instant};

use axum::body::Body;
use axum::extract::ConnectInfo;
use axum::http::{Request, StatusCode};
use dregg_persist::{PoaSlotOpeningStatementV1, SignedPoaSlotOpeningEnvelopeV1};
use dregg_types::hex_encode;
use ed25519_dalek::{Signer as _, SigningKey};
use http_body_util::BodyExt as _;
use serde_json::Value;
use tower::ServiceExt as _;
use zeroize::Zeroizing;

use crate::blocklace_sync::run_blocklace_sync_with_policy;
use crate::poa_signal_session::{
    SignalCodeWireV1, guess_statement_message, open_statement_message,
};
use crate::state::NodeState;

const SLOT: u64 = 9;
const MISSION_ID: u64 = 1;
/// The same committed test secret the first-turn milestone opens its slot with.
const SECRET: [u8; 32] = [0x77; 32];

/// Loopback: `require_auth`'s no-bearer-seed branch admits a loopback caller, which is
/// how the still-authenticated routes in this file (the settling claim path, `/status`)
/// are reachable at all in a harness with no passphrase.
const LOOPBACK: &str = "127.0.0.1:4470";
/// ⚑ NOT LOOPBACK, and it is where every SESSION request in this file is now sent from.
///
/// Until 2026-08-07 this address appeared exactly once, to assert the session routes
/// were behind the bearer gate. They are not any more (`poa_signal_session::routes()`
/// moved into `public_routes`), and the inversion is not "delete that assertion": it is
/// to drive the WHOLE judged run from here. `require_auth` refuses a non-loopback caller
/// with no bearer seed, so every 200 below is proof the request never touched that layer
/// — the player signature is carrying the entire authorization, exactly as claimed.
const REMOTE: &str = "203.0.113.7:4471";
/// A second anonymous address, for the poles that must not share a per-IP window with
/// the run itself.
const REMOTE_TWO: &str = "198.51.100.9:4472";

fn default_token() -> [u8; 32] {
    crate::executor_setup::default_token_id()
}

/// Stand up a solo node with a genesised Signal head and a slot opened through the
/// GENUINE curator ceremony, then start the real consensus loop and the real router.
async fn signal_session_node() -> (
    NodeState,
    axum::Router,
    [u8; 32],
    dregg_sdk::AgentCipherclerk,
    dregg_sdk::AgentCipherclerk,
    dregg_sdk::AgentCipherclerk,
    tempfile::TempDir,
) {
    let _ = rustls::crypto::ring::default_provider().install_default();
    let _ = crate::install_mldsa_verified_keygen_core_real();
    let _ = crate::install_mldsa_verified_sign_core_real();
    let _ = crate::install_mldsa_verified_verify_core();
    assert!(
        dregg_lean_ffi::poa_ffi::poa_signal_judge_available(),
        "a judged session e2e requires the linked native PoA Signal judge"
    );
    assert!(
        dregg_lean_ffi::poa_slot_derive_ffi::poa_slot_derive_available(),
        "a judged session e2e requires the linked PoA slot-derivation export"
    );
    assert!(
        dregg_lean_ffi::poa_signal_feedback_ffi::poa_signal_feedback_available(),
        "a judged session e2e requires the linked PoA feedback oracle; without it every \
         session route refuses and judged play is back to a blind 1-in-216 claim"
    );

    let tmp = tempfile::tempdir().expect("tempdir");
    let state = NodeState::new(tmp.path(), vec![]).expect("build NodeState");

    let solver = dregg_sdk::AgentCipherclerk::from_key_bytes(Zeroizing::new([0xC8; 32]));
    let loser = dregg_sdk::AgentCipherclerk::from_key_bytes(Zeroizing::new([0xC9; 32]));
    // The blind claimant: funded, hybrid-enrolled, able to pay the fee — and it
    // never opens a session. Everything about it is right except that it did not
    // play, so a refusal can only be about that.
    let stranger = dregg_sdk::AgentCipherclerk::from_key_bytes(Zeroizing::new([0xCA; 32]));

    let federation_id;
    {
        let mut s = state.write().await;
        s.unlocked = true;
        let node_pk = s.cclerk.public_key();
        let node_seed = s.cclerk.gossip_signing_key().to_bytes();
        let (node_ml_dsa, _) = dregg_federation::frost::MlDsaSigningKey::from_seed(&node_seed);
        s.set_federation_keys_hybrid(vec![node_pk], vec![node_ml_dsa]);
        s.solo_consensus = Some(dregg_federation::solo::SoloConsensusState::new(node_seed));
        federation_id = crate::executor_setup::federation_id_for_executor(&s);

        for player in [&solver, &loser, &stranger] {
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
        }

        let head = crate::poa_signal_adapter::fixture_signal_head_for_finality_test(federation_id);
        s.store
            .initialize_poa_signal_head(&head)
            .expect("initialize the PoA Signal authority head");

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
        assert_eq!(
            s.store
                .install_poa_signal_slot_v1(&envelope, SECRET)
                .expect("a curator-signed opening whose secret opens it must install"),
            dregg_persist::PoaSlotInstallStatusV1::Installed
        );
    }

    let handle = run_blocklace_sync_with_policy(
        state.clone(),
        0,
        true,
        100,
        10_000,
        50,
        2_000,
        0,
        None,
        dregg_blocklace::finality::ConsensusTimePolicyV1::new(1_700_000_000),
    )
    .await
    .expect("run_blocklace_sync must return a handle in solo mode");
    state.set_blocklace(handle).await;

    let recorder = metrics_exporter_prometheus::PrometheusBuilder::new().build_recorder();
    let app = crate::api::router(state.clone(), true, recorder.handle());
    (state, app, federation_id, solver, loser, stranger, tmp)
}

/// The instance THIS slot draws for THIS player.
///
/// ⚠ Available here only because the harness holds the slot secret; that is what the
/// operator-only derivation means. It is used to CHOOSE guesses whose classification is
/// a known consequence of the rule, and to name a losing guess as losing — never to
/// short-circuit the session, whose answers all come off the wire.
fn harness_target(federation_id: [u8; 32], player_key: [u8; 32]) -> SignalCodeWireV1 {
    let claim = crate::poa_signal_adapter::solving_claim_for_finality_test(
        &crate::poa_signal_adapter::fixture_signal_head_for_finality_test(federation_id),
        &crate::poa_signal_adapter::fixture_signal_slot_for_finality_test(federation_id),
        federation_id,
        player_key,
        [0u8; 32],
    );
    let code = claim.final_code();
    SignalCodeWireV1 {
        low: code.low(),
        mid: code.mid(),
        high: code.high(),
    }
}

/// The one place a claim is built in this file: from a list of `SignalCodeWireV1`
/// rounds, in order.
fn claim_over(
    mission_id: u64,
    transcript: &[SignalCodeWireV1],
) -> dregg_sdk::poa_signal::SignalClaimV1 {
    let codes: Vec<dregg_sdk::poa_signal::SignalCode> = transcript
        .iter()
        .map(|wire| {
            dregg_sdk::poa_signal::SignalCode::new(
                u64::from(wire.low),
                u64::from(wire.mid),
                u64::from(wire.high),
            )
            .expect("a bounded code")
        })
        .collect();
    dregg_sdk::poa_signal::SignalClaimV1::new(mission_id, &codes).expect("a legal claim")
}

/// Read a `settlement.transcript` array back into wire codes.
fn settlement_transcript(settlement: &Value) -> Vec<SignalCodeWireV1> {
    settlement["transcript"]
        .as_array()
        .expect("a settlement names the transcript it settles")
        .iter()
        .map(|entry| SignalCodeWireV1 {
            low: entry["low"].as_u64().unwrap() as u8,
            mid: entry["mid"].as_u64().unwrap() as u8,
            high: entry["high"].as_u64().unwrap() as u8,
        })
        .collect()
}

/// POST a carrier to the GENERIC signed-turn ingress, bypassing the claims route
/// and its courtesy check entirely.
///
/// ⚠ This is how the blind pole reaches CONSENSUS. The claims route refuses an
/// unplayed transcript at the door, which is good for a player and useless as
/// evidence about the gate that actually binds: a carrier gossiped in from a peer
/// never touches that handler. `/turns/submit` does not know Signal exists, so a
/// claim posted here is admitted, ordered, finalized — and refused by the
/// finalization gate or not at all.
async fn post_generic_turn(
    app: &axum::Router,
    signed: &dregg_sdk::SignedTurn,
) -> (StatusCode, Value) {
    let addr: SocketAddr = LOOPBACK.parse().unwrap();
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
                .expect("generic submit request"),
        )
        .await
        .expect("generic submit response");
    let status = response.status();
    let bytes = response
        .into_body()
        .collect()
        .await
        .expect("body")
        .to_bytes();
    let json = if bytes.is_empty() {
        Value::Null
    } else {
        serde_json::from_slice(&bytes).unwrap_or(Value::Null)
    };
    (status, json)
}

async fn post_json(app: &axum::Router, from: &str, uri: &str, body: Value) -> (StatusCode, Value) {
    let addr: SocketAddr = from.parse().unwrap();
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
    let json = if bytes.is_empty() {
        Value::Null
    } else {
        serde_json::from_slice(&bytes).unwrap_or(Value::Null)
    };
    (status, json)
}

async fn get_json_from(app: &axum::Router, from: &str, uri: &str) -> (StatusCode, Value) {
    let addr: SocketAddr = from.parse().unwrap();
    let response = app
        .clone()
        .oneshot(
            Request::builder()
                .uri(uri)
                .extension(ConnectInfo(addr))
                .body(Body::empty())
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
    let json = if bytes.is_empty() {
        Value::Null
    } else {
        serde_json::from_slice(&bytes).unwrap_or(Value::Null)
    };
    (status, json)
}

async fn get_json(app: &axum::Router, uri: &str) -> Value {
    get_json_from(app, LOOPBACK, uri).await.1
}

fn player_ed25519(player: &dregg_sdk::AgentCipherclerk) -> SigningKey {
    SigningKey::from_bytes(&player.gossip_signing_key().to_bytes())
}

/// Open a session AS AN ANONYMOUS REMOTE CALLER. No bearer, no loopback — nothing but
/// the player's own signature over the re-derived statement.
async fn open_session(
    app: &axum::Router,
    authority: &str,
    authority_id: [u8; 32],
    player: &dregg_sdk::AgentCipherclerk,
) -> (StatusCode, Value) {
    open_session_from(app, REMOTE, authority, authority_id, player).await
}

async fn open_session_from(
    app: &axum::Router,
    from: &str,
    authority: &str,
    authority_id: [u8; 32],
    player: &dregg_sdk::AgentCipherclerk,
) -> (StatusCode, Value) {
    let key = player.public_key().0;
    let signature = player_ed25519(player).sign(&open_statement_message(authority_id, SLOT, key));
    post_json(
        app,
        from,
        &format!("/api/poa/signal/{authority}/session/open"),
        serde_json::json!({
            "player_key": hex_encode(&key),
            "signature": hex_encode(&signature.to_bytes()),
        }),
    )
    .await
}

async fn guess(
    app: &axum::Router,
    authority: &str,
    authority_id: [u8; 32],
    player: &dregg_sdk::AgentCipherclerk,
    round: u32,
    code: SignalCodeWireV1,
) -> (StatusCode, Value) {
    let key = player.public_key().0;
    let signature = player_ed25519(player).sign(&guess_statement_message(
        authority_id,
        SLOT,
        key,
        round,
        code,
    ));
    post_json(
        app,
        // Anonymous, remote, no bearer — see `REMOTE`.
        REMOTE,
        &format!("/api/poa/signal/{authority}/session/guess"),
        serde_json::json!({
            "player_key": hex_encode(&key),
            "round": round,
            "guess": { "low": code.low, "mid": code.mid, "high": code.high },
            "signature": hex_encode(&signature.to_bytes()),
        }),
    )
    .await
}

async fn post_claim(
    app: &axum::Router,
    authority: &str,
    signed: &dregg_sdk::SignedTurn,
) -> (StatusCode, Value) {
    let addr: SocketAddr = "127.0.0.1:4472".parse().unwrap();
    let wire = postcard::to_stdvec(signed).expect("encode SignedTurn");
    let response = app
        .clone()
        .oneshot(
            Request::builder()
                .method("POST")
                .uri(format!("/api/poa/signal/{authority}/claims"))
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
        Value::Null
    } else {
        serde_json::from_slice(&bytes).unwrap_or(Value::Null)
    };
    (status, json)
}

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

/// A code that uses the same three bands as `target` but never in `target`'s position
/// where it can be avoided — a rotation. Because it is a PERMUTATION of the target, the
/// band multiset is identical, so `totalMatches == 3` and therefore
/// `exact + present == 3` for every target, duplicates included. That is
/// `SignalTriangulation.totalMatches`, not a reimplementation of it.
fn rotation_of(target: SignalCodeWireV1) -> SignalCodeWireV1 {
    SignalCodeWireV1 {
        low: target.mid,
        mid: target.high,
        high: target.low,
    }
}

/// The monochromatic code on the lowest band value the target does not use.
/// `SignalTriangulation.feedback_of_absent_mono` says its classification is exactly
/// `(0, 0)`, and `two_band_values_are_always_absent` says such a value always exists.
fn absent_mono(target: SignalCodeWireV1) -> SignalCodeWireV1 {
    let band = (0u8..6)
        .find(|v| *v != target.low && *v != target.mid && *v != target.high)
        .expect("a three-band code cannot use all six values");
    SignalCodeWireV1 {
        low: band,
        mid: band,
        high: band,
    }
}

fn assert_no_leak(document: &Value) {
    let bytes = document.to_string();
    assert!(
        !bytes.contains(&hex_encode(&SECRET)),
        "a session document carried the slot secret: {bytes}"
    );
    // Two spellings of the same wound: the secret as the node stores it, and any
    // 64-hex digest that is not the published commitment. The commitment is the ONLY
    // digest a session document may carry besides the coordinates.
    for (key, value) in document.as_object().into_iter().flatten() {
        if let Some(text) = value.as_str() {
            if text.len() == 64 && text.chars().all(|c| c.is_ascii_hexdigit()) {
                assert!(
                    matches!(
                        key.as_str(),
                        "authority_id" | "slot_commitment" | "player_key"
                    ),
                    "a session document carries an unexplained 64-hex digest at `{key}`: {bytes}"
                );
            }
        }
    }
}

/// ⚑ POLE ONE: a judged SESSION is played to solved through the real router, and the
/// code the SESSION hands back settles — `latest_height` 0 → 1.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_judged_session_is_played_to_solved_and_its_code_settles() {
    let (state, app, federation_id, solver, _loser, _stranger, _tmp) = signal_session_node().await;
    let authority = hex_encode(&federation_id);

    assert_eq!(
        get_json(&app, "/status").await["latest_height"].as_u64(),
        Some(0),
        "a fresh node has settled no turns"
    );

    // ── ⚑ THE REFUSING POLE, taken FIRST so the serving pole below cannot be read as
    //    "the gate is simply gone". Anonymous, remote, no bearer — and a signature that
    //    is NOT the player's. The refusal must be BY NAME and must spend nothing.
    //
    //    Mutation asserted present before the verdict: the forged bytes are exhibited
    //    to differ from the honest ones. A refusal test whose "hostile" input stopped
    //    being hostile is a green light that checks nothing.
    let solver_key = solver.public_key().0;
    let honest_open = player_ed25519(&solver)
        .sign(&open_statement_message(federation_id, SLOT, solver_key))
        .to_bytes();
    let impostor_open = SigningKey::from_bytes(&[0xEE; 32])
        .sign(&open_statement_message(federation_id, SLOT, solver_key))
        .to_bytes();
    assert_ne!(
        honest_open, impostor_open,
        "the forged signature must actually differ from the honest one"
    );
    //
    //    ⚑ AND THE COUNT IS DELIBERATE. It is one MORE than
    //    `SESSION_WRITES_PER_PLAYER_PER_MINUTE`, which makes this the detector for the
    //    ordering inside `SessionAdmission`: if the per-player-key budget were charged
    //    BEFORE the signature check, the last of these would come back
    //    `session-player-rate-limit` and the honest open below would be refused too —
    //    i.e. a stranger would have locked this player out of their own run using
    //    nothing but a public key. Every one of them must say `session-signature`.
    let forgeries = crate::poa_signal_session::SESSION_WRITES_PER_PLAYER_PER_MINUTE + 1;
    for attempt in 0..forgeries {
        let (label, signature) = match attempt % 3 {
            0 => ("a signature by the wrong key", hex_encode(&impostor_open)),
            1 => ("a truncated signature", "00".to_owned()),
            _ => ("no signature at all", String::new()),
        };
        let (status, body) = post_json(
            &app,
            REMOTE_TWO,
            &format!("/api/poa/signal/{authority}/session/open"),
            serde_json::json!({ "player_key": hex_encode(&solver_key), "signature": signature }),
        )
        .await;
        assert_eq!(
            status,
            StatusCode::UNAUTHORIZED,
            "attempt {attempt} ({label}) must be refused as unauthorized, not admitted \
             and not 403'd by a bearer layer that no longer runs: {body}"
        );
        assert_eq!(
            body["reason"], "session-signature",
            "attempt {attempt} ({label}) must be refused BY NAME, and NEVER as a \
             per-player rate limit — an unverified request must not be able to spend a \
             victim's budget: {body}"
        );
    }
    // ⚑ AND NOTHING WAS SPENT. Three refused opens left no session behind at all — the
    //   read-back 404s exactly as it does for a player who never played.
    let (after_forgery, _) = get_json_from(
        &app,
        REMOTE_TWO,
        &format!(
            "/api/poa/signal/{authority}/session/{}",
            hex_encode(&solver_key)
        ),
    )
    .await;
    assert_eq!(
        after_forgery,
        StatusCode::NOT_FOUND,
        "a refused signature must not have opened, resumed or spent anything"
    );

    // ── ⚑ THE READ-BACK CANNOT BE WALKED. A key nobody played answers the SAME 404 as
    //    a key that has not played yet, so probing separates nothing. There is no
    //    listing route to enumerate from in the first place.
    let (stranger_read, stranger_body) = get_json_from(
        &app,
        REMOTE_TWO,
        &format!("/api/poa/signal/{authority}/session/{}", "ab".repeat(32)),
    )
    .await;
    assert_eq!(stranger_read, StatusCode::NOT_FOUND);
    assert_eq!(stranger_body["reason"], "session-not-open");

    // ── The sibling slot PUBLICATION was already public and stays public. ─────────
    let (public, opening) =
        get_json_from(&app, REMOTE, &format!("/api/poa/signal/{authority}/slot")).await;
    assert_eq!(
        public,
        StatusCode::OK,
        "the curator-signed slot publication stays PUBLIC: {opening}"
    );
    assert_eq!(opening["open"], true);

    // ── ⚑ THE SERVING POLE. The SAME anonymous, bearerless, non-loopback posture that
    //    was just refused three times — plus a signature that verifies — is SERVED.
    //    Everything after this point is a judged run played by a caller holding no
    //    credential of this node whatsoever.
    let (status, session) = open_session(&app, &authority, federation_id, &solver).await;
    assert_eq!(
        status,
        StatusCode::OK,
        "an anonymous caller with a valid player signature must be SERVED — no bearer, \
         no loopback: {session}"
    );
    assert_eq!(
        session["judged"], true,
        "a judged session says so: {session}"
    );
    assert_eq!(session["max_rounds"], 5);
    assert_eq!(session["rounds_used"], 0);
    assert_eq!(session["rounds_remaining"], 5);
    assert_eq!(session["solved"], false);
    assert_eq!(session["settlement"], Value::Null);
    assert_eq!(
        session["slot_commitment"], opening["opening"]["statement"]["commitment"],
        "a client must be able to tie the session to the curator-signed opening"
    );
    assert_no_leak(&session);

    // Re-opening RESUMES; it never resets. (Checked again after bursts are spent.)
    let (_, resumed) = open_session(&app, &authority, federation_id, &solver).await;
    assert_eq!(resumed["rounds_used"], 0);

    let target = harness_target(federation_id, solver.public_key().0);
    eprintln!("SESSION harness-derived target for this player: {target:?}");

    // ── Burst 1: a band the target does not use. `feedback_of_absent_mono` says the
    //    classification is exactly (0, 0), and the wire must say the same. ────────
    let blank = absent_mono(target);
    let (status, one) = guess(&app, &authority, federation_id, &solver, 0, blank).await;
    assert_eq!(status, StatusCode::OK, "burst 1 must be served: {one}");
    let round_one = &one["transcript"][0];
    assert_eq!(
        (round_one["exact"].as_u64(), round_one["present"].as_u64()),
        (Some(0), Some(0)),
        "a monochromatic guess on an absent band must score (0,0) — that is \
         SignalTriangulation.feedback_of_absent_mono, checked on the served bytes: {one}"
    );
    assert_eq!(one["rounds_used"], 1);
    assert_eq!(one["rounds_remaining"], 4);
    assert_eq!(one["solved"], false);
    assert_eq!(one["settlement"], Value::Null);
    assert_no_leak(&one);

    // ── Burst 2: a rotation of the target. Same band multiset ⇒ totalMatches is 3 ⇒
    //    `exact + present == 3`, and it does not solve unless the target is
    //    rotation-invariant (all three bands equal), which the assertion allows for. ─
    let rotated = rotation_of(target);
    let (status, two) = guess(&app, &authority, federation_id, &solver, 1, rotated).await;
    assert_eq!(status, StatusCode::OK, "burst 2 must be served: {two}");
    let round_two = &two["transcript"][1];
    let exact = round_two["exact"].as_u64().unwrap();
    let present = round_two["present"].as_u64().unwrap();
    assert_eq!(
        exact + present,
        3,
        "a permutation of the target shares its whole band multiset, so every band is \
         matched somewhere: {two}"
    );
    assert_eq!(two["rounds_used"], 2);
    assert_eq!(two["rounds_remaining"], 3);
    assert_no_leak(&two);

    // ── A replayed burst is REFUSED, not spent twice. The signature covers `round`. ─
    let (replay_status, replay) = guess(&app, &authority, federation_id, &solver, 1, rotated).await;
    assert_eq!(replay_status, StatusCode::CONFLICT);
    assert_eq!(
        replay["reason"], "session-round-mismatch",
        "a replayed guess must refuse by name: {replay}"
    );
    assert_eq!(
        get_json_from(
            &app,
            REMOTE,
            &format!(
                "/api/poa/signal/{authority}/session/{}",
                hex_encode(&solver.public_key().0)
            )
        )
        .await
        .1["rounds_used"],
        2,
        "the replay must not have spent a burst"
    );

    // ── An impostor cannot spend this player's budget — and now the impostor is
    //    ANONYMOUS, which is the whole point of the route move. It is refused by the
    //    signature check, the only check that ever mattered, and the burst survives.
    let impostor = SigningKey::from_bytes(&[0xEE; 32]);
    let key = solver.public_key().0;
    let forged = impostor.sign(&guess_statement_message(federation_id, SLOT, key, 2, blank));
    assert_ne!(
        forged.to_bytes(),
        player_ed25519(&solver)
            .sign(&guess_statement_message(federation_id, SLOT, key, 2, blank))
            .to_bytes(),
        "the forged guess signature must actually differ from the honest one"
    );
    let (forged_status, forged_body) = post_json(
        &app,
        REMOTE_TWO,
        &format!("/api/poa/signal/{authority}/session/guess"),
        serde_json::json!({
            "player_key": hex_encode(&key),
            "round": 2,
            "guess": { "low": blank.low, "mid": blank.mid, "high": blank.high },
            "signature": hex_encode(&forged.to_bytes()),
        }),
    )
    .await;
    assert_eq!(forged_status, StatusCode::UNAUTHORIZED);
    assert_eq!(forged_body["reason"], "session-signature");
    assert_eq!(
        get_json_from(
            &app,
            REMOTE,
            &format!(
                "/api/poa/signal/{authority}/session/{}",
                hex_encode(&solver.public_key().0)
            )
        )
        .await
        .1["rounds_used"],
        2,
        "an anonymous forgery must not have spent this player's burst"
    );

    // ── Burst 3: the answer. ────────────────────────────────────────────────────
    let (status, solved) = guess(&app, &authority, federation_id, &solver, 2, target).await;
    assert_eq!(status, StatusCode::OK, "burst 3 must be served: {solved}");
    assert_eq!(solved["transcript"][2]["exact"], 3);
    assert_eq!(solved["transcript"][2]["present"], 0);
    assert_eq!(solved["solved"], true);
    assert_eq!(solved["open"], false, "a solved run is over");
    assert_eq!(solved["rounds_remaining"], 0);
    assert_no_leak(&solved);

    // ⚑ ONLY A SOLVED TRANSCRIPT SETTLES. `settlement` exists now and not before, and
    // it names the guesses THIS PLAYER submitted, read back out of the transcript.
    let settlement = &solved["settlement"];
    assert_ne!(*settlement, Value::Null, "a solved session must settle");
    assert_eq!(settlement["mission_id"], MISSION_ID);
    assert_eq!(settlement["code"]["low"], target.low);
    assert_eq!(settlement["code"]["mid"], target.mid);
    assert_eq!(settlement["code"]["high"], target.high);
    assert_eq!(
        settlement["code"], solved["transcript"][2]["guess"],
        "the settling code IS the player's own solving guess"
    );
    let played = settlement_transcript(settlement);
    assert_eq!(
        played,
        vec![blank, rotated, target],
        "the settlement names EVERY burst that was spent, in order — that is what a \
         claim carries now, and it is what the node compares against"
    );

    // A further burst on a solved run refuses by name rather than wedging.
    let (over, over_body) = guess(&app, &authority, federation_id, &solver, 3, blank).await;
    assert_eq!(over, StatusCode::CONFLICT);
    assert_eq!(over_body["reason"], "session-already-solved");

    // ── A CLAIM NAMING ONLY THE SOLVING CODE IS REFUSED, even though the code is
    //    right and this player really did deduce it. The game the node served was
    //    three rounds long; a one-round claim is not that game. ─────────────────
    let truncated = crate::poa_signal_slot_claim::signed_signal_claim_turn(
        &solver,
        federation_id,
        0,
        None,
        claim_over(MISSION_ID, &[target]),
    );
    let (status, body) = post_claim(&app, &authority, &truncated).await;
    assert_eq!(status, StatusCode::OK, "the route answers: {body}");
    assert_eq!(
        body["accepted"], false,
        "a claim that drops the rounds it was deduced from must refuse: {body}"
    );
    assert!(
        body["error"]
            .as_str()
            .unwrap_or_default()
            .starts_with("poa-signal-transcript-length-mismatch"),
        "the refusal must name the real cause: {body}"
    );

    // ── SETTLE with the TRANSCRIPT the SESSION handed back — not a derivation. ───
    let claim = claim_over(settlement["mission_id"].as_u64().unwrap(), &played);
    let signed = crate::poa_signal_slot_claim::signed_signal_claim_turn(
        &solver,
        federation_id,
        0,
        None,
        claim,
    );
    let (status, body) = post_claim(&app, &authority, &signed).await;
    assert_eq!(
        status,
        StatusCode::OK,
        "the claims route must admit it: {body}"
    );
    assert_eq!(body["accepted"], true, "{body}");

    let height = await_latest_height(&app, 1, Duration::from_secs(45)).await;
    let after = get_json(&app, "/status").await;
    eprintln!("SESSION /status latest_height: {}", after["latest_height"]);
    assert_eq!(
        height, 1,
        "a code deduced through the judged SESSION must settle. Still 0 means the session \
         classified against a different instance than the judge scores, which would teach a \
         player the wrong answer and then refuse it."
    );

    {
        let s = state.read().await;
        let head = s
            .store
            .load_poa_signal_head(federation_id)
            .expect("PoA head read")
            .expect("advanced PoA head");
        assert_eq!(head.transition_count(), 1);
        s.store
            .audit_poa_signal_sessions_v1()
            .expect("the durable session store must audit clean after a settled run");
    }
}

/// ⚑ POLE TWO: a session that never solves burns its budget, is refused BY NAME, and
/// settles nothing — and the blind claim it falls back on is refused cleanly rather
/// than wedging the node.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_losing_session_exhausts_its_budget_and_settles_nothing() {
    let (state, app, federation_id, _solver, loser, _stranger, _tmp) = signal_session_node().await;
    let authority = hex_encode(&federation_id);
    let player_hex = hex_encode(&loser.public_key().0);

    let (status, session) = open_session(&app, &authority, federation_id, &loser).await;
    assert_eq!(status, StatusCode::OK, "open must succeed: {session}");

    let target = harness_target(federation_id, loser.public_key().0);
    // Five codes, none of them the target. Chosen by walking the low band and stepping
    // past the target's own value — no rule knowledge required, only inequality.
    let wrong: Vec<SignalCodeWireV1> = (0u8..6)
        .map(|low| SignalCodeWireV1 {
            low,
            mid: target.mid,
            high: target.high,
        })
        .filter(|code| *code != target)
        .take(5)
        .collect();
    assert_eq!(wrong.len(), 5);

    for (round, code) in wrong.iter().enumerate() {
        let (status, body) =
            guess(&app, &authority, federation_id, &loser, round as u32, *code).await;
        assert_eq!(
            status,
            StatusCode::OK,
            "burst {round} must be served: {body}"
        );
        assert_eq!(
            body["solved"], false,
            "a wrong guess must not solve: {body}"
        );
        assert_eq!(body["rounds_used"], round as u64 + 1);
        assert_eq!(body["rounds_remaining"], 4 - round as u64);
        assert_eq!(body["settlement"], Value::Null);
        assert_no_leak(&body);
    }

    // ── The budget is spent, and the sixth burst refuses BY NAME. ───────────────
    let (status, exhausted) = guess(&app, &authority, federation_id, &loser, 5, wrong[0]).await;
    assert_eq!(status, StatusCode::CONFLICT);
    assert_eq!(
        exhausted["reason"], "session-budget-exhausted",
        "an over-limit burst must name the real cause: {exhausted}"
    );
    assert!(
        exhausted["detail"].as_str().unwrap().contains("durable"),
        "the refusal must say the budget does not come back: {exhausted}"
    );

    // Re-opening does NOT refund. This is the restart-safety property over HTTP.
    let (_, reopened) = open_session(&app, &authority, federation_id, &loser).await;
    assert_eq!(reopened["rounds_used"], 5);
    assert_eq!(reopened["rounds_remaining"], 0);
    assert_eq!(reopened["open"], false);
    assert_eq!(reopened["settlement"], Value::Null);

    let (read_status, read_back) = get_json_from(
        &app,
        REMOTE,
        &format!("/api/poa/signal/{authority}/session/{player_hex}"),
    )
    .await;
    assert_eq!(
        read_status,
        StatusCode::OK,
        "the read-back is anonymous now — it is what makes a lost response recoverable \
         instead of a lost burst, and a browser holds no bearer: {read_back}"
    );
    assert_eq!(read_back["rounds_used"], 5);
    assert_eq!(read_back["settlement"], Value::Null);
    assert_no_leak(&read_back);

    // ── The losing run's own transcript, submitted anyway. It is REFUSED cleanly,
    //    and by the JUDGE rather than by the transcript gate: these five rounds ARE
    //    the ones the node served, in order. What they are not is solved. ────────
    let losing = crate::poa_signal_slot_claim::signed_signal_claim_turn(
        &loser,
        federation_id,
        0,
        None,
        claim_over(MISSION_ID, &wrong),
    );
    let (status, body) = post_claim(&app, &authority, &losing).await;
    assert_eq!(status, StatusCode::OK, "the route answers: {body}");
    assert_eq!(
        body["accepted"], false,
        "an unsolved run has nothing to settle: {body}"
    );
    assert!(
        body["error"]
            .as_str()
            .unwrap_or_default()
            .starts_with("poa-signal-transcript-not-solved"),
        "the refusal must name the real cause — the node never scored the last \
         round as locking: {body}"
    );

    // …and the blind fallback that used to exist: a single code, no matching
    // session shape. Also refused, also cleanly.
    let blind = crate::poa_signal_slot_claim::signed_signal_claim_turn(
        &loser,
        federation_id,
        0,
        None,
        claim_over(MISSION_ID, &wrong[..1]),
    );
    let (status, body) = post_claim(&app, &authority, &blind).await;
    assert_eq!(status, StatusCode::OK, "the route answers: {body}");
    assert_eq!(body["accepted"], false, "{body}");

    // `latest_height` must STAY 0. `await_latest_height` polls to its deadline and
    // returns what it saw, so a spurious settle would be caught rather than raced past.
    let height = await_latest_height(&app, 1, Duration::from_secs(12)).await;
    assert_eq!(
        height, 0,
        "a losing claim must not settle. It is routed to \
         `persist_finalized_payload_rejection` with no transition and no height — a clean \
         refusal, not a wedge."
    );

    {
        let s = state.read().await;
        let head = s
            .store
            .load_poa_signal_head(federation_id)
            .expect("PoA head read")
            .expect("PoA head");
        assert_eq!(
            head.transition_count(),
            0,
            "a losing run leaves the authority exactly where it was"
        );
        s.store
            .audit_poa_signal_sessions_v1()
            .expect("the durable session store must audit clean after a losing run");
    }
    // And the node is still serving: the loss did not wedge anything.
    let status = get_json(&app, "/status").await;
    assert!(
        status["latest_height"].is_number(),
        "the node still answers"
    );
}

/// ⚑ THE BLIND POLE. A GENUINELY SOLVING CODE, WITH NO SESSION, NEVER SETTLES.
///
/// # Why this test is the one that matters
///
/// The judged session landed and made deduction POSSIBLE. Nothing made it
/// NECESSARY: `POST …/claims` still admitted a bare code, so a stranger who guessed
/// right — 1 in 216 — settled a turn with no session, no feedback and no deduction
/// anywhere in the causal history of the block. A settled turn was evidence of a
/// lucky guess OR a played game, and the chain could not tell which.
///
/// # ⚠ THE MUTATION, AND WHY IT CANNOT SILENTLY DIE HERE
///
/// A "refused" that is really "the guess was wrong" would pass just as green
/// against a node with no gate at all, so the code submitted here has to be the
/// REAL answer and that has to be checked rather than believed.
///
/// It is checked twice, both times by the NODE:
///
/// * **§2** plays the very same code through the judged session and requires the
///   Lean oracle to answer `exact: 3` — which
///   `SignalTriangulation.accepted_solved_iff_target` proves is equivalent to the
///   guess BEING the target;
/// * **§3** resubmits the BYTE-IDENTICAL carrier and requires `latest_height` to
///   move.
///
/// Both run AFTER the refusal, and they have to: the thing being tested is the
/// absence of a session, so anything that creates one has to come later. That
/// ordering costs nothing, because if the code were not the solving one, §2 and §3
/// both go RED — the refusal in §1 can never be quietly vacuous while this test is
/// green. What §3 pins that nothing else can is that the refused bytes and the
/// settling bytes are the SAME BYTES: the only difference between them is whether
/// the game had been played.
///
/// # Both doors
///
/// * `POST …/claims` — the courtesy check, which tells the player by name.
/// * `POST /turns/submit` — the GENERIC ingress, which knows nothing about Signal.
///   A carrier posted there is admitted, ordered and finalized, so it reaches the
///   gate that actually binds. This is the door a gossiped claim comes through, and
///   a check that only lived in the claims handler would be decoration.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_solving_code_with_no_session_never_settles() {
    let (state, app, federation_id, _solver, _loser, stranger, _tmp) = signal_session_node().await;
    let authority = hex_encode(&federation_id);
    let stranger_key = stranger.public_key().0;
    let player_hex = hex_encode(&stranger_key);

    assert_eq!(
        get_json(&app, "/status").await["latest_height"].as_u64(),
        Some(0)
    );

    // The answer for THIS player, from the operator derivation — the same Lean
    // export the judge re-derives with. Available only because the harness holds
    // the slot secret, said out loud exactly as the sibling tests say it.
    let answer = harness_target(federation_id, stranger_key);
    eprintln!("BLIND harness-derived target for the stranger: {answer:?}");

    // The precondition, asserted rather than assumed: this player has no session.
    let (status, absent) = get_json_from(
        &app,
        LOOPBACK,
        &format!("/api/poa/signal/{authority}/session/{player_hex}"),
    )
    .await;
    assert_eq!(status, StatusCode::NOT_FOUND, "{absent}");
    assert_eq!(absent["reason"], "session-not-open", "{absent}");

    let signed = crate::poa_signal_slot_claim::signed_signal_claim_turn(
        &stranger,
        federation_id,
        0,
        None,
        claim_over(MISSION_ID, &[answer]),
    );

    // ── §1a. DOOR ONE: the public claims route refuses BY NAME. ─────────────────
    let (status, body) = post_claim(&app, &authority, &signed).await;
    assert_eq!(status, StatusCode::OK, "the route answers cleanly: {body}");
    assert_eq!(
        body["accepted"], false,
        "a correct code with no game behind it must not be admitted: {body}"
    );
    let named = body["error"].as_str().unwrap_or_default().to_owned();
    assert!(
        named.starts_with("poa-signal-transcript-no-session"),
        "the refusal must name the real cause: {body}"
    );
    // …and it must not leak the target, nor say anything about how close it was.
    assert!(
        !named.contains(&format!("{},{},{}", answer.low, answer.mid, answer.high))
            && !named.to_ascii_lowercase().contains("exact")
            && !named.to_ascii_lowercase().contains("target"),
        "a refusal may not leak the target or the distance to it: {named}"
    );

    // ── §1b. DOOR TWO: the GENERIC ingress, which knows nothing about Signal. This
    //    is the one that reaches consensus, and therefore the gate that binds. ───
    let (status, staged) = post_generic_turn(&app, &signed).await;
    assert_eq!(
        status,
        StatusCode::OK,
        "the generic ingress must answer: {staged}"
    );
    eprintln!("BLIND generic-ingress staging: {staged}");

    // `latest_height` must STAY 0. The poller runs to its deadline and returns what
    // it saw, so a spurious settle is caught rather than raced past.
    let height = await_latest_height(&app, 1, Duration::from_secs(20)).await;
    assert_eq!(
        height, 0,
        "A BLIND CLAIM SETTLED. The code was right and no game was played; if the \
         height moved, `latest_height` is still evidence of luck rather than of \
         deduction and the whole judged session is optional decoration."
    );

    {
        let s = state.read().await;
        let head = s
            .store
            .load_poa_signal_head(federation_id)
            .expect("PoA head read")
            .expect("PoA head");
        assert_eq!(
            head.transition_count(),
            0,
            "no transition may be recorded for a claim with no game behind it"
        );
        s.store
            .audit_poa_signal_sessions_v1()
            .expect("the durable session store must audit clean");
    }

    // ── AND THE NODE IS STILL ANSWERING. A refused claim must fail CLEANLY, not
    //    wedge: `blocklace_sync` routes it to `persist_finalized_payload_rejection`
    //    with no transition, and the consensus loop keeps running. ───────────────
    let after = get_json(&app, "/status").await;
    assert!(
        after["latest_height"].is_number(),
        "the node still answers after refusing a blind claim: {after}"
    );

    // ── §2. THE MUTATION, EXHIBITED BY THE NODE'S OWN ORACLE. ──────────────────
    let (status, session) = open_session(&app, &authority, federation_id, &stranger).await;
    assert_eq!(status, StatusCode::OK, "open must succeed: {session}");
    assert_eq!(
        session["rounds_used"], 0,
        "the refused claim spent no burst: {session}"
    );
    let (status, solved) = guess(&app, &authority, federation_id, &stranger, 0, answer).await;
    assert_eq!(status, StatusCode::OK, "the burst must be served: {solved}");
    assert_eq!(
        solved["transcript"][0]["exact"], 3,
        "THE MUTATION MUST BE PRESENT: the node's own Lean oracle has to call the \
         refused code the solving one, or §1 refused a wrong answer and proves \
         nothing about the gate: {solved}"
    );
    assert_eq!(solved["solved"], true, "{solved}");
    assert_eq!(
        settlement_transcript(&solved["settlement"]),
        vec![answer],
        "the session's settlement names exactly the round that was played"
    );
    assert_no_leak(&solved);

    // ── §3. THE CONVERSE: the BYTE-IDENTICAL carrier now settles. ──────────────
    let (status, body) = post_claim(&app, &authority, &signed).await;
    assert_eq!(status, StatusCode::OK, "{body}");
    assert_eq!(
        body["accepted"], true,
        "the very same carrier must be admitted once the game behind it exists: {body}"
    );
    let height = await_latest_height(&app, 1, Duration::from_secs(45)).await;
    assert_eq!(
        height, 1,
        "the played claim must settle. If it does not, the gate is refusing \
         everything and the blind pole above is measuring a node that cannot settle \
         at all rather than one that refuses unplayed claims."
    );
    {
        let s = state.read().await;
        assert_eq!(
            s.store
                .load_poa_signal_head(federation_id)
                .expect("PoA head read")
                .expect("PoA head")
                .transition_count(),
            1,
            "exactly one judged transition — the played one"
        );
    }
}
