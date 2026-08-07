//! ⚑ **THE EXHIBIT: a proof served under turn B, checked against turn A's anchor, is REFUSED.**
//!
//! End to end, through the REAL endpoint (`GET /api/turn/{hash}/anchor`, driven over the real
//! axum router) and the REAL verify entry (`dregg_sdk::verify_full_turn_bound`, the same call the
//! discord bot's `/proof turn` makes). No unit comparison stands in for either half:
//!
//! * the anchors come out of the router, postcard-decoded off `anchor_hex` exactly as
//!   `discord_bot::commands::proof_verify::verify_anchor_hex` decodes them;
//! * they are verified by `dregg_federation::TurnAnchorV1::verify` against a committee roster
//!   built here, not read out of the anchor;
//! * the proof is a real full-turn STARK from `turn_proving::prove_and_verify_finalized_turn`;
//! * the refusal is `verify_full_turn_bound`'s own, with the anchor's turn hash as the
//!   `expected_turn_hash` argument.
//!
//! The completeness control runs the same proof under its OWN anchor and requires acceptance —
//! without it the refusal could be a proof that never verified at all.
//!
//! ## Why the durable state is seeded rather than driven through consensus
//!
//! Reaching `execute_finalized_turn` needs a live blocklace quorum. What this exhibit is about is
//! the *custody chain* — receipt -> `receipt_stream_root` -> `AttestedRoot::signing_message()` ->
//! committee signature -> the endpoint -> the verifier — so the seed writes exactly the objects
//! the finalized path writes, with the SAME constructors and the SAME signing message
//! (`node/src/blocklace_sync.rs:9685-9762`): a `CommitRecord` through
//! `PersistentStore::commit_finalized_turn`, a receipt through `AgentCipherclerk::append_receipt`,
//! and an `AttestedRoot` whose `receipt_stream_root` is
//! `merkle_root_of_receipt_hashes(&[receipt.receipt_hash()])`, signed with the node's own key.
//! A drift between this seed and the production writer shows up as an anchor that does not
//! verify, which is the failure mode this file is shaped to catch.

use axum::body::Body;
use axum::http::{Request, StatusCode};
use dregg_cell::{Cell, CellId, Ledger};
use dregg_federation::turn_anchor::{AnchorCommittee, TurnAnchorV1};
use dregg_node::state::NodeState;
use dregg_turn::TurnReceipt;
use http_body_util::BodyExt;
use tower::ServiceExt;

/// A receipt for `turn_hash`, chained after `prev` for the same agent (the cipherclerk enforces
/// the agent-scoped predecessor, so this cannot be faked past it).
fn receipt(agent: CellId, turn_hash: [u8; 32], prev: Option<[u8; 32]>, marker: u8) -> TurnReceipt {
    TurnReceipt {
        turn_hash,
        forest_hash: [marker; 32],
        pre_state_hash: [marker.wrapping_add(1); 32],
        post_state_hash: [marker.wrapping_add(2); 32],
        timestamp: 1_800_000_000 + i64::from(marker),
        effects_hash: [marker.wrapping_add(3); 32],
        computrons_used: 10,
        action_count: 1,
        previous_receipt_hash: prev,
        agent,
        ..Default::default()
    }
}

/// Seed one finalized turn into the durable state exactly as the commit path does.
async fn seed_finalized_turn(
    state: &NodeState,
    receipt: TurnReceipt,
    height: u64,
    block_id: [u8; 32],
    ordinal: u64,
) {
    let mut s = state.write().await;
    let receipt_hash = receipt.receipt_hash();
    let turn_hash = receipt.turn_hash;
    let agent = receipt.agent;

    s.cclerk
        .append_receipt(receipt)
        .expect("the receipt chain must accept a correctly-chained receipt");

    let record = dregg_persist::commit_log::CommitRecord {
        ordinal,
        height,
        block_id,
        block_executed_up_to: height,
        turn_hash,
        creator: *agent.as_bytes(),
        receipt_hash,
        ledger_root: [0x33; 32],
        touched_cells: Vec::new(),
        removed: Vec::new(),
    };
    s.store
        .commit_finalized_turn(ordinal, &record)
        .expect("durable commit");

    // The attestation, built and signed the way `blocklace_sync` builds and signs it.
    let signing_key =
        dregg_types::SigningKey::from_bytes(&s.cclerk.gossip_signing_key().to_bytes());
    let local_pk = signing_key.public_key();
    let mut attested = dregg_types::AttestedRoot {
        merkle_root: [0x33; 32],
        note_tree_root: None,
        nullifier_set_root: None,
        height,
        timestamp: 1_800_000_000,
        blocklace_block_id: Some(block_id),
        finality_round: Some(height),
        quorum_signatures: Vec::new(),
        threshold_qc: None,
        threshold: 1,
        federation_id: dregg_types::FederationId(s.federation_id),
        receipt_stream_root: Some(dregg_types::merkle_root_of_receipt_hashes(&[receipt_hash])),
        hybrid_quorum: Vec::new(),
    };
    let sig = dregg_types::sign(&signing_key, &attested.signing_message());
    attested.quorum_signatures.push((local_pk, sig));

    s.known_federation_keys = vec![local_pk];
    s.store
        .store_attested_root(&dregg_persist::StoredAttestedRoot {
            merkle_root: attested.merkle_root,
            note_tree_root: attested.note_tree_root,
            nullifier_set_root: attested.nullifier_set_root,
            height: attested.height,
            timestamp: attested.timestamp,
            blocklace_block_id: attested.blocklace_block_id,
            finality_round: attested.finality_round,
            quorum_signatures: attested.quorum_signatures.clone(),
            threshold_qc: None,
            threshold: attested.threshold,
            federation_id: attested.federation_id,
            receipt_stream_root: attested.receipt_stream_root,
            finalization_quorum: Vec::new(),
        })
        .expect("store attested root");
}

/// Fetch an anchor off the REAL router and postcard-decode it, exactly as the bot does.
async fn fetch_anchor(app: &axum::Router, turn_hash: [u8; 32]) -> TurnAnchorV1 {
    let uri = format!("/api/turn/{}/anchor", hex::encode(turn_hash));
    let response = app
        .clone()
        .oneshot(
            Request::builder()
                .uri(&uri)
                .body(Body::empty())
                .expect("req"),
        )
        .await
        .expect("response");
    assert_eq!(
        response.status(),
        StatusCode::OK,
        "the anchor endpoint must serve a committed turn"
    );
    let body = response
        .into_body()
        .collect()
        .await
        .expect("body")
        .to_bytes();
    let json: serde_json::Value = serde_json::from_slice(&body).expect("json");
    assert_eq!(json["anchor_status"], "anchored");
    assert_eq!(json["artifact_format"], "DTA1");
    let hex_str = json["anchor_hex"].as_str().expect("anchor_hex");
    postcard::from_bytes(&hex::decode(hex_str).expect("hex")).expect("anchor decodes")
}

#[tokio::test]
async fn a_proof_of_one_turn_is_refused_against_another_turns_committee_anchor() {
    // ── A REAL FULL-TURN STARK, for a turn whose hash we choose. ───────────
    // `prove_and_verify_finalized_turn` is the production prover the commit path calls; its
    // internal verify→accept leg already ran before it returned.
    let before_cell = Cell::with_balance([0xA1; 32], [0u8; 32], 1_000);
    let agent = before_cell.id();
    let mut after_cell = before_cell.clone();
    assert!(after_cell.state.increment_nonce(), "nonce must advance");
    let effects = vec![dregg_turn::Effect::IncrementNonce { cell: agent }];
    let turn_hash_b: [u8; 32] = *blake3::hash(b"turn-anchor-exhibit:B").as_bytes();

    // The rotation witness the LIVE commit path threads (`blocklace_sync.rs:9317`): real
    // before/after cells, the turn's receipt hashes, and the executor's accumulator frontiers.
    let receipt_hashes_b = [*blake3::hash(b"turn-anchor-exhibit:B-receipt").as_bytes()];
    let rotation = dregg_node::turn_proving::rotation_witness_for_self_sovereign_with_root(
        1_000,
        0,
        &before_cell,
        &after_cell,
        &receipt_hashes_b,
        &effects,
        &dregg_turn::rotation_witness::empty_nullifier_root_8(),
        &dregg_turn::rotation_witness::empty_commitments_root_8(),
    )
    .expect("the actor cell must be representable by the rotated leg");

    let proven_b = dregg_node::turn_proving::prove_and_verify_finalized_turn(
        &agent,
        1_000,
        0,
        &effects,
        turn_hash_b,
        Some(rotation),
    )
    .expect("the production prover must produce a verified full-turn proof");

    // ── TWO COMMITTED TURNS IN THE NODE'S DURABLE STATE. ───────────────────
    let tmp = tempfile::tempdir().expect("tempdir");
    let state = NodeState::new(tmp.path(), vec![]).expect("node state");
    {
        let mut s = state.write().await;
        s.federation_id = [0x5F; 32];
        let mut ledger = Ledger::new();
        ledger.insert_cell(before_cell.clone()).expect("seed actor");
        s.ledger = ledger;
    }

    let turn_hash_a: [u8; 32] = *blake3::hash(b"turn-anchor-exhibit:A").as_bytes();
    let receipt_a = receipt(agent, turn_hash_a, None, 0x10);
    let receipt_a_hash = receipt_a.receipt_hash();
    seed_finalized_turn(&state, receipt_a, 1, [0x81; 32], 0).await;
    let receipt_b = receipt(agent, turn_hash_b, Some(receipt_a_hash), 0x20);
    seed_finalized_turn(&state, receipt_b, 2, [0x82; 32], 1).await;

    let recorder = metrics_exporter_prometheus::PrometheusBuilder::new().build_recorder();
    let app = dregg_node::api::router(state.clone(), false, recorder.handle());

    // The roster is built HERE, from the node's identity — a stand-in for the genesis roster an
    // operator configures. It is not read out of the anchors being judged.
    let committee = {
        let s = state.read().await;
        AnchorCommittee {
            ed25519: s.known_federation_keys.clone(),
            ml_dsa: Vec::new(),
            threshold: 1,
            federation_id: dregg_types::FederationId(s.federation_id),
        }
    };

    // ── THE REAL ENDPOINT, THEN THE REAL ANCHOR VERIFIER. ──────────────────
    let anchor_a = fetch_anchor(&app, turn_hash_a)
        .await
        .verify(&committee)
        .expect("turn A's served anchor must verify against the committee");
    let anchor_b = fetch_anchor(&app, turn_hash_b)
        .await
        .verify(&committee)
        .expect("turn B's served anchor must verify against the committee");

    assert_eq!(anchor_a.turn_hash, turn_hash_a);
    assert_eq!(anchor_b.turn_hash, turn_hash_b);
    assert_eq!(anchor_a.receipt_quorum_signers, 1);
    assert_ne!(
        anchor_a.turn_hash, anchor_b.turn_hash,
        "the exhibit needs two distinct anchored turns"
    );

    // ── COMPLETENESS: the honest pairing accepts. ──────────────────────────
    dregg_sdk::verify_full_turn_bound(
        &proven_b.proof,
        anchor_b.turn_hash,
        proven_b.old_commit,
        proven_b.new_commit,
        None,
    )
    .expect("an honest proof under ITS OWN committee-signed anchor must verify");

    // ── ⚑ THE REFUSAL: turn B's proof under turn A's anchor. ───────────────
    let refused = dregg_sdk::verify_full_turn_bound(
        &proven_b.proof,
        anchor_a.turn_hash,
        proven_b.old_commit,
        proven_b.new_commit,
        None,
    );
    let err = refused.expect_err(
        "⚑ a proof of turn B accepted under turn A's committee-signed anchor means the turn-hash \
         binding is not firing — the anchor would be decoration",
    );
    let named = format!("{err:?}");
    assert!(
        named.to_lowercase().contains("turn"),
        "the refusal must name the turn identity, not fail generically: {named}"
    );
}

/// An uncommitted turn has no anchor, and the endpoint says which of the two absences it is
/// rather than answering one 404 for both.
#[tokio::test]
async fn an_uncommitted_turn_has_no_anchor_and_the_endpoint_says_so() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let state = NodeState::new(tmp.path(), vec![]).expect("node state");
    let recorder = metrics_exporter_prometheus::PrometheusBuilder::new().build_recorder();
    let app = dregg_node::api::router(state, false, recorder.handle());

    let uri = format!("/api/turn/{}/anchor", "ab".repeat(32));
    let response = app
        .clone()
        .oneshot(
            Request::builder()
                .uri(&uri)
                .body(Body::empty())
                .expect("req"),
        )
        .await
        .expect("response");
    assert_eq!(response.status(), StatusCode::NOT_FOUND);
    let body = response
        .into_body()
        .collect()
        .await
        .expect("body")
        .to_bytes();
    let json: serde_json::Value = serde_json::from_slice(&body).expect("json");
    assert_eq!(json["anchor_status"], "not_committed");

    // A malformed hash is a 400, never a silent all-zero lookup.
    let response = app
        .oneshot(
            Request::builder()
                .uri("/api/turn/not-a-hash/anchor")
                .body(Body::empty())
                .expect("req"),
        )
        .await
        .expect("response");
    assert_eq!(response.status(), StatusCode::BAD_REQUEST);
}
