//! ⚑ **THE EXHIBIT: the reflexive endpoint tooth becoming real.**
//!
//! `dregg_sdk::verify_full_turn_bound` takes `expected_old_commit` / `expected_new_commit` from its
//! CALLER, and until 2026-08-07 no production surface had them. The one that re-verifies a served
//! artifact for a stranger — `discord-bot`'s `/proof turn` — read the pair **out of the artifact**
//! (`proof_verify::extract_commits`) and handed it straight back, so the verifier's two
//! `CommitmentMismatch` teeth compared `x != x` and **structurally could not fire**.
//!
//! This file drives the closure end to end, through the REAL router:
//!
//! * a REAL full-turn STARK from the production prover (`turn_proving::prove_and_verify_finalized_turn`);
//! * the pair the node's commit path DERIVED for it, persisted under the same key
//!   `blocklace_sync` writes (`turn_proving::turn_proof_anchors_config_key`);
//! * `GET /api/turn/{hash}/anchor` serving it as `proof_state_commits`, parsed with the SHARED
//!   codec the checker parses it with (`dregg_circuit::commit8_wire`) — no second convention;
//! * **COMPLETENESS**: the honest artifact verifies against the served pair;
//! * ⚑ **THE REFUSAL, EXHIBITED**: one lane of the served pair moved, and the same call is
//!   REFUSED. The mutation is built CONSTRUCTIVELY here and asserted to have changed the value
//!   before the verdict is read, so this cannot decay into a no-op falsifier;
//! * **THE `cipherclerk` BOUNDARY**: a committed turn whose artifact this node did not mint serves
//!   `proof_commit_status: "absent"` and a null pair, which is what makes the checker refuse
//!   rather than serve a wrong pair. A ledgerless producer cannot compute this chain's
//!   whole-ledger rotation context, so there is no honest pair for its artifacts and none is
//!   invented.
//!
//! ## What this exhibit does NOT establish, stated here so the file cannot be read as more
//!
//! The served pair is **node-derived, not committee-signed**. The committee signs
//! `TurnReceipt::{pre,post}_state_hash`, a DIFFERENT commitment of the same transition — see
//! `turn/tests/receipt_state_commit_is_not_the_proof_state_commit.rs`. So a hostile NODE can still
//! serve a forged artifact beside a matching forged pair; what it can no longer do is serve an
//! artifact whose own published commitments contradict what its commit path derived, and no
//! checker anywhere reads the expected pair out of the object it is judging.
//!
//! ## Why the durable state is seeded rather than driven through consensus
//!
//! Same reason as `turn_anchor_binds_a_proof_to_the_committee.rs`: reaching
//! `execute_finalized_turn` needs a live blocklace quorum, and what is under test is the CUSTODY
//! of the pair — derived at commit time, persisted, served, bound — not the consensus round. The
//! seed writes exactly the objects and keys the finalized path writes, so a drift between this
//! seed and the production writer shows up as an endpoint that serves no pair.

use axum::body::Body;
use axum::http::{Request, StatusCode};
use dregg_cell::{Cell, CellId, Ledger};
use dregg_circuit::commit8_wire::{commit8_from_hex, commit8_pair_to_bytes};
use dregg_circuit::field::BabyBear;
use dregg_federation::turn_anchor::{AnchorCommittee, TurnAnchorV1};
use dregg_node::state::NodeState;
use dregg_turn::TurnReceipt;
use http_body_util::BodyExt;
use tower::ServiceExt;

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

/// The `/anchor` response, whole — the JSON a checker reads.
async fn fetch_anchor_body(app: &axum::Router, turn_hash: [u8; 32]) -> serde_json::Value {
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
    serde_json::from_slice(&body).expect("json")
}

/// The served pair, read EXACTLY the way `discord_bot::commands::proof_verify` reads it: the two
/// JSON keys, through the shared `commit8_wire` codec. The bot lives in a separate cargo workspace
/// so it cannot be linked here; pinning the field names and the codec is what keeps the two ends
/// from drifting into two conventions.
fn served_pair(body: &serde_json::Value) -> Option<([BabyBear; 8], [BabyBear; 8])> {
    if body.get("proof_commit_status").and_then(|v| v.as_str()) != Some("derived") {
        return None;
    }
    let c = body.get("proof_state_commits")?;
    let old = commit8_from_hex(c.get("old_commit")?.as_str()?)?;
    let new = commit8_from_hex(c.get("new_commit")?.as_str()?)?;
    Some((old, new))
}

#[tokio::test]
async fn the_served_state_commit_pair_binds_the_artifact_and_a_mismatch_is_refused() {
    // ── A REAL FULL-TURN STARK from the production prover. ─────────────────
    let before_cell = Cell::with_balance([0xA1; 32], [0u8; 32], 1_000);
    let agent = before_cell.id();
    let mut after_cell = before_cell.clone();
    assert!(after_cell.state.increment_nonce(), "nonce must advance");
    let effects = vec![dregg_turn::Effect::IncrementNonce { cell: agent }];
    let turn_hash_b: [u8; 32] = *blake3::hash(b"served-pair-exhibit:B").as_bytes();

    let receipt_hashes_b = [*blake3::hash(b"served-pair-exhibit:B-receipt").as_bytes()];
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

    let proven = dregg_node::turn_proving::prove_and_verify_finalized_turn(
        &agent,
        1_000,
        0,
        &effects,
        turn_hash_b,
        Some(rotation),
    )
    .expect("the production prover must produce a verified full-turn proof");

    // ── TWO COMMITTED TURNS. Only B carries the derived pair the commit path writes. ──
    let tmp = tempfile::tempdir().expect("tempdir");
    let state = NodeState::new(tmp.path(), vec![]).expect("node state");
    {
        let mut s = state.write().await;
        s.federation_id = [0x5F; 32];
        let mut ledger = Ledger::new();
        ledger.insert_cell(before_cell.clone()).expect("seed actor");
        s.ledger = ledger;
    }

    let turn_hash_a: [u8; 32] = *blake3::hash(b"served-pair-exhibit:A").as_bytes();
    let receipt_a = receipt(agent, turn_hash_a, None, 0x10);
    let receipt_a_hash = receipt_a.receipt_hash();
    seed_finalized_turn(&state, receipt_a, 1, [0x81; 32], 0).await;
    let receipt_b = receipt(agent, turn_hash_b, Some(receipt_a_hash), 0x20);
    seed_finalized_turn(&state, receipt_b, 2, [0x82; 32], 1).await;

    // The SAME key and the SAME encoding `blocklace_sync` writes after a finalized commit.
    {
        let s = state.write().await;
        let key =
            dregg_node::turn_proving::turn_proof_anchors_config_key(&hex::encode(turn_hash_b));
        let bytes = commit8_pair_to_bytes(&proven.old_commit, &proven.new_commit);
        s.store.set_config(&key, &bytes).expect("persist anchors");
    }

    let recorder = metrics_exporter_prometheus::PrometheusBuilder::new().build_recorder();
    let app = dregg_node::api::router(state.clone(), false, recorder.handle());

    let committee = {
        let s = state.read().await;
        AnchorCommittee {
            ed25519: s.known_federation_keys.clone(),
            ml_dsa: Vec::new(),
            threshold: 1,
            federation_id: dregg_types::FederationId(s.federation_id),
        }
    };

    // ── THE ENDPOINT SERVES THE PAIR, AND IT IS THE ONE THE PROVER DERIVED. ──
    let body_b = fetch_anchor_body(&app, turn_hash_b).await;
    assert_eq!(body_b["proof_commit_status"], "derived");
    let (served_old, served_new) =
        served_pair(&body_b).expect("a minted turn must serve a bindable pair");
    assert_eq!(
        (served_old, served_new),
        (proven.old_commit, proven.new_commit),
        "the endpoint must serve the pair the commit path derived, not some other value"
    );

    // …and the anchor itself still verifies against a roster built here, so the turn identity the
    // pair is fetched under is the committee's.
    let anchor: TurnAnchorV1 = postcard::from_bytes(
        &hex::decode(body_b["anchor_hex"].as_str().expect("anchor_hex")).expect("hex"),
    )
    .expect("anchor decodes");
    let verified = anchor
        .verify(&committee)
        .expect("turn B's served anchor must verify against the committee");
    assert_eq!(verified.turn_hash, turn_hash_b);

    // ⚑ THE SERVED PAIR IS NOT THE ONE THE COMMITTEE SIGNED, and this exhibit must not be read as
    // if it were. The receipt's pair is a different commitment of the same transition; if these
    // ever coincide, the alignment in `docs/DESIGN-pi-authority.md` §4(a) has landed and this
    // assertion is the place that says so.
    assert_ne!(
        dregg_circuit::commit8_wire::commit8_to_bytes(&served_old),
        verified.receipt_pre_state_commit,
        "if the served pair HAS become the committee-signed one, the four-cause alignment landed \
         — go update this file, `federation/src/turn_anchor.rs` and the bot's `unbound_claims`, \
         because the reported provenance is now wrong (and better than documented)"
    );

    // ── COMPLETENESS: the honest artifact verifies against the SERVED pair. ──
    dregg_sdk::verify_full_turn_bound(
        &proven.proof,
        verified.turn_hash,
        served_old,
        served_new,
        None,
    )
    .expect("an honest proof must verify against the pair the endpoint serves");

    // ── ⚑ THE REFUSAL, BUILT CONSTRUCTIVELY. ──────────────────────────────
    // One lane of the BEFORE anchor moved. The mutation is asserted to have changed the value
    // before the verdict is read, so a future edit that makes it a no-op fails HERE rather than
    // leaving a green test that checks nothing.
    let mut forged_old = served_old;
    forged_old[0] = forged_old[0] + BabyBear::new(1);
    assert_ne!(
        forged_old, served_old,
        "the mutation must actually move the anchor, or the refusal below proves nothing"
    );
    let refused = dregg_sdk::verify_full_turn_bound(
        &proven.proof,
        verified.turn_hash,
        forged_old,
        served_new,
        None,
    );
    let err = refused.expect_err(
        "⚑ a proof accepted against a DIFFERENT before-state commit means the endpoint teeth are \
         still not firing — the served pair would be decoration",
    );
    let named = format!("{err:?}");
    assert!(
        named.contains("Commitment") || named.to_lowercase().contains("commit"),
        "the refusal must name the commitment, not fail generically: {named}"
    );

    // …and the same for the AFTER anchor, so neither tooth is carrying the other.
    let mut forged_new = served_new;
    forged_new[7] = forged_new[7] + BabyBear::new(1);
    assert_ne!(forged_new, served_new, "the AFTER mutation must move it");
    let err = dregg_sdk::verify_full_turn_bound(
        &proven.proof,
        verified.turn_hash,
        served_old,
        forged_new,
        None,
    )
    .expect_err(
        "a proof accepted against a DIFFERENT after-state commit means the AFTER tooth is dead",
    );
    let named = format!("{err:?}");
    assert!(
        named.contains("Commitment") || named.to_lowercase().contains("commit"),
        "the AFTER refusal must name the commitment: {named}"
    );

    // ── THE `cipherclerk` BOUNDARY: a turn this node did not mint serves NO pair. ──
    let body_a = fetch_anchor_body(&app, turn_hash_a).await;
    assert_eq!(
        body_a["proof_commit_status"], "absent",
        "a turn with no node-derived anchors must not serve a pair"
    );
    assert!(
        body_a["proof_state_commits"].is_null(),
        "an absent pair must be null, never a zero octet a checker could bind against: {}",
        body_a["proof_state_commits"]
    );
    assert!(
        served_pair(&body_a).is_none(),
        "a checker reading the response must get NO pair, hence no verdict"
    );
    // The provenance rides with every response, so a reader cannot mistake the node's claim for
    // the committee's.
    assert!(
        body_a["proof_commit_provenance"]
            .as_str()
            .expect("provenance is served")
            .contains("NOT committee-signed"),
        "the response must say whose claim the pair is"
    );
}
