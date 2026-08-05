//! Bearer-authenticated, bounded export of one rostered node's durable view of
//! a PoA Signal transition for offline curator review.
//!
//! The export does not contain a carrying-block quorum certificate and is not a
//! portable federation-finality proof.

use std::collections::BTreeMap;
use std::net::SocketAddr;
use std::sync::Arc;

use axum::extract::{ConnectInfo, Path, State};
use axum::http::{HeaderMap, StatusCode};
use axum::routing::get;
use axum::{Json, Router};
use base64::Engine as _;
use base64::engine::general_purpose::STANDARD as BASE64;
use dregg_blocklace::finality::Payload;
use poa_curator::authority_export::{
    POA_SIGNAL_AUTHORITY_EXPORT_FORMAT_V1, POA_SIGNAL_AUTHORITY_EXPORT_SCHEMA_VERSION_V1,
    PoaSignalAuthorityExportV1, PublicCommitProjectionV1,
};
use serde_json::Value;
use sha2::{Digest as _, Sha256};
use tokio::sync::Semaphore;

use crate::api::RateLimiter;
use crate::state::NodeState;

const EXPORTS_PER_MINUTE: u32 = 6;
const EXPORT_MAX_IN_FLIGHT: usize = 1;

pub(crate) fn routes() -> Router<NodeState> {
    let limiter = RateLimiter::new(EXPORTS_PER_MINUTE, 60);
    let in_flight = Arc::new(Semaphore::new(EXPORT_MAX_IN_FLIGHT));
    Router::new().route(
        "/api/poa/signal/{authority}/node-envelope/{sequence}",
        get(move |connect, headers, path, state| {
            get_authority_export(
                connect,
                headers,
                path,
                state,
                limiter.clone(),
                in_flight.clone(),
            )
        }),
    )
}

async fn get_authority_export(
    ConnectInfo(addr): ConnectInfo<SocketAddr>,
    headers: HeaderMap,
    Path((authority, sequence)): Path<(String, u64)>,
    State(state): State<NodeState>,
    limiter: RateLimiter,
    in_flight: Arc<Semaphore>,
) -> Result<Json<PoaSignalAuthorityExportV1>, (StatusCode, String)> {
    if !limiter.check_request(addr.ip(), &headers).await {
        return Err((StatusCode::TOO_MANY_REQUESTS, "rate limit exceeded".into()));
    }
    let permit = in_flight.try_acquire_owned().map_err(|_| {
        (
            StatusCode::SERVICE_UNAVAILABLE,
            "node envelope diagnostic busy".into(),
        )
    })?;
    let authority_id = dregg_types::parse_hex32(&authority).ok_or_else(|| {
        (
            StatusCode::BAD_REQUEST,
            "authority must be 32 lowercase hexadecimal bytes".into(),
        )
    })?;
    if authority != dregg_types::hex_encode(&authority_id) || sequence == 0 {
        return Err((
            StatusCode::BAD_REQUEST,
            "authority/sequence is not canonical".into(),
        ));
    }

    let (store, signing_key) = {
        let inner = state.read().await;
        if inner.federation_id != authority_id {
            return Err((
                StatusCode::NOT_FOUND,
                "authority is not hosted by this node".into(),
            ));
        }
        (inner.store.clone(), inner.cclerk.gossip_signing_key())
    };
    let export = tokio::task::spawn_blocking(move || {
        let _permit = permit;
        build_authority_export(&store, authority_id, sequence, &signing_key)
    })
    .await
    .map_err(|_| {
        (
            StatusCode::INTERNAL_SERVER_ERROR,
            "node envelope diagnostic worker failed".into(),
        )
    })?
    .map_err(|error| (StatusCode::CONFLICT, error))?;
    Ok(Json(export))
}

pub fn build_authority_export(
    store: &dregg_persist::PersistentStore,
    authority_id: [u8; 32],
    sequence: u64,
    signing_key: &dregg_types::SigningKey,
) -> Result<PoaSignalAuthorityExportV1, String> {
    crate::poa_signal_adapter::audit_persisted_signal_semantics(store, authority_id)
        .map_err(|error| format!("complete Signal semantic replay refused: {error}"))?;
    let transition = store
        .load_poa_signal_transition(authority_id, sequence)
        .map_err(|error| error.to_string())?
        .ok_or_else(|| format!("Signal sequence {sequence} is not durable"))?;
    let snapshot = store
        .poa_authority_commit_snapshot(transition.commit_ordinal())
        .map_err(|error| error.to_string())?
        .ok_or_else(|| "carrying durable commit is absent".to_owned())?;
    let commit = snapshot.record();

    let block = store
        .load_all_blocks()
        .map_err(|error| error.to_string())?
        .into_iter()
        .find(|block| block.id().0 == commit.block_id)
        .ok_or_else(|| "carrying persisted block is absent".to_owned())?;
    let signed_turn_bytes = signed_turn_bytes(&block.payload)
        .ok_or_else(|| "carrying block has no exact SignedTurn".to_owned())?
        .to_vec();
    let (signed, remainder): (dregg_sdk::SignedTurn, &[u8]) =
        postcard::take_from_bytes(&signed_turn_bytes)
            .map_err(|error| format!("carrying SignedTurn is malformed: {error}"))?;
    if !remainder.is_empty()
        || postcard::to_stdvec(&signed).ok().as_deref() != Some(signed_turn_bytes.as_slice())
    {
        return Err("carrying SignedTurn is not exact canonical postcard".into());
    }

    let mut receipts = BTreeMap::new();
    let mut receipt_bytes = BTreeMap::new();
    for bytes in store
        .load_receipt_chain()
        .map_err(|error| error.to_string())?
    {
        let (receipt, remainder): (dregg_turn::TurnReceipt, &[u8]) =
            postcard::take_from_bytes(&bytes)
                .map_err(|error| format!("durable receipt is malformed: {error}"))?;
        if !remainder.is_empty() {
            return Err("durable receipt contains trailing bytes".into());
        }
        let hash = receipt.receipt_hash();
        if receipts.insert(hash, receipt).is_some() || receipt_bytes.insert(hash, bytes).is_some() {
            return Err("durable receipt chain contains a duplicate hash".into());
        }
    }
    let receipt = receipts
        .get(&commit.receipt_hash)
        .ok_or_else(|| "carrying durable receipt is absent".to_owned())?;
    let exact_receipt_bytes = receipt_bytes
        .get(&commit.receipt_hash)
        .ok_or_else(|| "carrying exact receipt bytes are absent".to_owned())?;
    dregg_turn::verify_receipt_signature_with_keys(receipt, &[signing_key.public_key().0])
        .map_err(|error| format!("local node did not sign the carrying receipt: {error}"))?;
    if receipt.routing_directives.len() != 0
        || receipt.introduction_exports.len() != 0
        || receipt.derivation_records.len() != 0
        || receipt.consumed_capabilities.len() != 0
        || receipt.was_encrypted
        || receipt.was_burn
    {
        return Err("carrying receipt is not safe for the node-envelope diagnostic".into());
    }

    let predecessor = transition
        .predecessor_head()
        .map_err(|error| error.to_string())?;
    let successor = transition
        .successor_head()
        .map_err(|error| error.to_string())?;
    if predecessor.deployment_digest() != successor.deployment_digest() {
        return Err("Signal transition changes deployment identity".into());
    }
    let input: Value = serde_json::from_slice(transition.judge_input())
        .map_err(|error| format!("stored judge input is not JSON: {error}"))?;
    let mission_id = value_u64(&input, &["request", "mission_id"])?;
    let federation_id = value_string(&input, &["request", "federation_id"])?;
    let content_root = value_string(&input, &["request", "content_root"])?;
    let activation_digest = value_string(&input, &["request", "activation_digest"])?;
    let content_session = value_string(&input, &["request", "content_session"])?;
    let content_epoch = value_u64(&input, &["request", "content_epoch"])?;
    let player_key = value_string(&input, &["request", "player_key"])?;
    let actor_root = value_string(&input, &["request", "actor_root"])?;
    if federation_id != dregg_types::hex_encode(&authority_id)
        || player_key != signed.signer.hex()
        || actor_root != dregg_types::hex_encode(&receipt.pre_state_hash)
    {
        return Err("stored judge authority differs from exact turn/receipt".into());
    }

    let mut export = PoaSignalAuthorityExportV1 {
        format: POA_SIGNAL_AUTHORITY_EXPORT_FORMAT_V1.into(),
        schema_version: POA_SIGNAL_AUTHORITY_EXPORT_SCHEMA_VERSION_V1,
        authority_id: dregg_types::hex_encode(&authority_id),
        deployment_digest: dregg_types::hex_encode(&predecessor.deployment_digest()),
        federation_id,
        sequence,
        mission_id,
        content_root,
        activation_digest,
        content_session,
        content_epoch,
        player_key,
        actor_root,
        transition_digest: dregg_types::hex_encode(&transition.transition_digest()),
        predecessor_head_digest: dregg_types::hex_encode(&transition.predecessor_head_digest()),
        successor_head_digest: dregg_types::hex_encode(&transition.successor_head_digest()),
        judge_input_sha256: sha256_hex(transition.judge_input()),
        judge_output_sha256: sha256_hex(transition.judge_output()),
        judge_input_base64: BASE64.encode(transition.judge_input()),
        judge_output_base64: BASE64.encode(transition.judge_output()),
        commit: PublicCommitProjectionV1 {
            ordinal: commit.ordinal,
            height: commit.height,
            block_id: dregg_types::hex_encode(&commit.block_id),
            block_executed_up_to: commit.block_executed_up_to,
            turn_hash: dregg_types::hex_encode(&commit.turn_hash),
            creator: dregg_types::hex_encode(&commit.creator),
            receipt_hash: dregg_types::hex_encode(&commit.receipt_hash),
            ledger_root: dregg_types::hex_encode(&commit.ledger_root),
            exact_record_sha256: sha256_hex(snapshot.exact_bytes()),
        },
        signed_turn_sha256: sha256_hex(&signed_turn_bytes),
        signed_turn_postcard_base64: BASE64.encode(&signed_turn_bytes),
        signer: signed.signer.hex(),
        receipt_bytes_sha256: sha256_hex(exact_receipt_bytes),
        receipt_postcard_base64: BASE64.encode(exact_receipt_bytes),
        executor_public_key: signing_key.public_key().hex(),
        export_signature: String::new(),
    };
    export
        .seal(signing_key)
        .map_err(|error| error.to_string())?;
    Ok(export)
}

fn signed_turn_bytes(payload: &Payload) -> Option<&[u8]> {
    match payload {
        Payload::Turn(bytes) => Some(bytes),
        Payload::TurnBundle(bundle) => Some(&bundle.signed_turn),
        Payload::ConsensusTimedTurnV1(bundle) => Some(bundle.signed_turn()),
        Payload::Ack
        | Payload::Checkpoint { .. }
        | Payload::MembershipVote { .. }
        | Payload::Data(_) => None,
    }
}

fn value_at<'a>(value: &'a Value, path: &[&str]) -> Result<&'a Value, String> {
    path.iter().try_fold(value, |value, key| {
        value
            .get(*key)
            .ok_or_else(|| format!("judge input lacks {}", path.join(".")))
    })
}

fn value_string(value: &Value, path: &[&str]) -> Result<String, String> {
    value_at(value, path)?
        .as_str()
        .map(str::to_owned)
        .ok_or_else(|| format!("judge input {} is not a string", path.join(".")))
}

fn value_u64(value: &Value, path: &[&str]) -> Result<u64, String> {
    value_at(value, path)?
        .as_u64()
        .ok_or_else(|| format!("judge input {} is not a u64", path.join(".")))
}

fn sha256_hex(bytes: &[u8]) -> String {
    dregg_types::hex_encode(&Sha256::digest(bytes))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    use axum::body::Body;
    use axum::extract::ConnectInfo;
    use axum::http::Request;
    use dregg_blocklace::finality::{Block, Payload};
    use dregg_persist::{CommitRecord, PersistentStore, PoaSignalHeadV1};
    use dregg_sdk::poa_signal::{SignalClaimV1, SignalCode};
    use dregg_turn::{Finality, TurnReceipt};
    use poa_curator::PoaDeploymentScope;
    use poa_curator::authority_export::{PoaSignalAuthorityExportV1, verify_authority_export};
    use tower::ServiceExt as _;
    use zeroize::Zeroizing;

    fn deployment_scope(authority: [u8; 32], node_public_key: [u8; 32]) -> PoaDeploymentScope {
        let temp = tempfile::tempdir().unwrap();
        let path = temp.path().join("poa-devnet.json");
        fs::write(
            &path,
            serde_json::to_vec(&serde_json::json!({
                "schema": poa_curator::POA_DEPLOYMENT_MANIFEST_SCHEMA,
                "deployment_domain": poa_curator::POA_DEPLOYMENT_DOMAIN,
                "deployment_id": dregg_types::hex_encode(&[0x91; 32]),
                "federation_id": dregg_types::hex_encode(&authority),
                "committee_epoch": 0,
                "threshold": 1,
                "genesis_sha256": dregg_types::hex_encode(&[0x92; 32]),
                "descriptor": "bundle/genesis.json",
                "policy": {},
                "nodes": [{"public_key": dregg_types::hex_encode(&node_public_key)}]
            }))
            .unwrap(),
        )
        .unwrap();
        PoaDeploymentScope::load(path).unwrap()
    }

    fn diagnostic_fixture() -> (
        PoaSignalAuthorityExportV1,
        PoaDeploymentScope,
        dregg_types::SigningKey,
    ) {
        assert!(
            dregg_lean_ffi::poa_ffi::poa_signal_judge_available(),
            "diagnostic envelope tests require the native Lean Signal judge"
        );
        let authority = [0x73; 32];
        let node_seed = [0x74; 32];
        let node_key = dregg_types::SigningKey::from_bytes(&node_seed);
        let deployment = deployment_scope(authority, node_key.public_key().0);
        let base = crate::poa_signal_adapter::fixture_signal_head_for_finality_test(authority);
        let head = PoaSignalHeadV1::genesis(
            authority,
            dregg_types::parse_hex32(deployment.deployment_digest()).unwrap(),
            base.world_sequence(),
            base.canon_revision(),
            base.config().to_vec(),
            base.canon().to_vec(),
        )
        .unwrap();
        let store = PersistentStore::open_in_memory().unwrap();
        store.initialize_poa_signal_head(&head).unwrap();

        let player = dregg_sdk::AgentCipherclerk::from_key_bytes(Zeroizing::new([0x75; 32]));
        let claim = SignalClaimV1::new(1, SignalCode::new(2, 4, 1).unwrap()).unwrap();
        let turn = dregg_sdk::poa_signal::signal_claim_turn(&player.public_key().0, 0, None, claim);
        let signed = player.sign_turn(&turn);
        let actor_root = [0x76; 32];
        let candidate = crate::poa_signal_adapter::evaluate_persisted_signal_claim(
            &head,
            authority,
            player.public_key().0,
            actor_root,
            claim,
        )
        .unwrap();

        let mut receipt = TurnReceipt {
            turn_hash: signed.turn.hash(),
            forest_hash: signed.turn.call_forest.compute_hash(),
            pre_state_hash: actor_root,
            post_state_hash: [0x77; 32],
            effects_hash: [0x78; 32],
            action_count: signed.turn.call_forest.action_count(),
            agent: signed.turn.agent,
            federation_id: authority,
            finality: Finality::Final,
            ..Default::default()
        };
        receipt.executor_signature = Some(dregg_turn::sign_receipt(&receipt, &node_seed));
        let receipt_hash = receipt.receipt_hash();
        let block = Block {
            creator: [0x79; 32],
            ed25519: node_key.public_key().0,
            seq: 1,
            payload: Payload::Turn(postcard::to_stdvec(&signed).unwrap()),
            predecessors: Vec::new(),
            signature: [0; 64],
            pq_signature: Vec::new(),
        };
        let record = CommitRecord {
            ordinal: 0,
            height: 1,
            block_id: block.id().0,
            block_executed_up_to: 1,
            turn_hash: signed.turn.hash(),
            creator: *signed.turn.agent.as_bytes(),
            receipt_hash,
            ledger_root: [0x7a; 32],
            touched_cells: Vec::new(),
            removed: Vec::new(),
        };
        store.persist_block(&block).unwrap();
        store
            .append_receipt_chain_entry(0, &postcard::to_stdvec(&receipt).unwrap())
            .unwrap();
        store
            .commit_finalized_turn_with_poa_signal_for_test(0, &record, &candidate)
            .unwrap();

        let export = build_authority_export(&store, authority, 1, &node_key).unwrap();
        (export, deployment, node_key)
    }

    fn mutate_component(value: &str) -> String {
        let mut bytes = BASE64.decode(value).unwrap();
        bytes[0] ^= 0x80;
        BASE64.encode(bytes)
    }

    #[test]
    fn empty_store_cannot_export_caller_invented_authority() {
        let store = dregg_persist::PersistentStore::open_in_memory().unwrap();
        let key = dregg_types::SigningKey::from_bytes(&[0x71; 32]);
        let error = build_authority_export(&store, [0x22; 32], 1, &key).unwrap_err();
        assert!(error.contains("no persisted genesis"));
    }

    #[test]
    fn exact_node_envelope_roundtrips_as_diagnostic_with_all_authority_flags_false() {
        let (export, deployment, _) = diagnostic_fixture();
        let verified = verify_authority_export(&export, &deployment).unwrap();
        assert_eq!(export.format, "POA-SIGNAL-NODE-ENVELOPE-V1");
        assert!(!verified.deployment_manifest_externally_pinned());
        assert!(!verified.actor_pq_enrollment_verified());
        assert!(!verified.authenticated_mission_config_bound());
        assert!(!verified.federation_finality_verified());
    }

    #[test]
    fn node_envelope_refuses_signature_roster_and_exact_component_substitution() {
        let (export, deployment, node_key) = diagnostic_fixture();

        let mut bad_signature = export.clone();
        let replacement = if bad_signature.export_signature.starts_with('0') {
            "1"
        } else {
            "0"
        };
        bad_signature
            .export_signature
            .replace_range(..1, replacement);
        assert!(verify_authority_export(&bad_signature, &deployment).is_err());

        let outsider = dregg_types::SigningKey::from_bytes(&[0x7b; 32]);
        let mut wrong_roster = export.clone();
        wrong_roster.executor_public_key = outsider.public_key().hex();
        wrong_roster.seal(&outsider).unwrap();
        let roster_error = verify_authority_export(&wrong_roster, &deployment).unwrap_err();
        assert!(roster_error.to_string().contains("validator roster"));

        let mut bad_turn = export.clone();
        bad_turn.signed_turn_postcard_base64 =
            mutate_component(&bad_turn.signed_turn_postcard_base64);
        bad_turn.signed_turn_sha256 = sha256_hex(
            &BASE64
                .decode(&bad_turn.signed_turn_postcard_base64)
                .unwrap(),
        );
        bad_turn.seal(&node_key).unwrap();
        assert!(verify_authority_export(&bad_turn, &deployment).is_err());

        let mut bad_receipt = export.clone();
        bad_receipt.receipt_postcard_base64 =
            mutate_component(&bad_receipt.receipt_postcard_base64);
        bad_receipt.receipt_bytes_sha256 =
            sha256_hex(&BASE64.decode(&bad_receipt.receipt_postcard_base64).unwrap());
        bad_receipt.seal(&node_key).unwrap();
        assert!(verify_authority_export(&bad_receipt, &deployment).is_err());

        let mut bad_judge = export;
        bad_judge.judge_input_base64 = mutate_component(&bad_judge.judge_input_base64);
        bad_judge.judge_input_sha256 =
            sha256_hex(&BASE64.decode(&bad_judge.judge_input_base64).unwrap());
        bad_judge.seal(&node_key).unwrap();
        assert!(verify_authority_export(&bad_judge, &deployment).is_err());
    }

    #[tokio::test]
    async fn node_envelope_route_is_bearer_gated_and_rate_limited() {
        let temp = tempfile::tempdir().unwrap();
        let state = NodeState::new(temp.path(), vec![]).unwrap();
        let bearer_seed = [0x7c; 32];
        state.write().await.bearer_seed = Some(bearer_seed);
        let recorder = metrics_exporter_prometheus::PrometheusBuilder::new().build_recorder();
        let app = crate::api::router(state, false, recorder.handle());
        let uri = format!(
            "/api/poa/signal/{}/node-envelope/1",
            dregg_types::hex_encode(&[0; 32])
        );
        let request = |authorized: bool| {
            let mut builder = Request::builder()
                .uri(&uri)
                .extension(ConnectInfo("127.0.0.1:4555".parse::<SocketAddr>().unwrap()));
            if authorized {
                let token = dregg_types::hex_encode(&blake3::derive_key(
                    "dregg-api-bearer-v1",
                    &bearer_seed,
                ));
                builder = builder.header("authorization", format!("Bearer {token}"));
            }
            builder.body(Body::empty()).unwrap()
        };

        let unauthorized = app.clone().oneshot(request(false)).await.unwrap();
        assert_eq!(unauthorized.status(), StatusCode::UNAUTHORIZED);
        for index in 0..7 {
            let response = app.clone().oneshot(request(true)).await.unwrap();
            if index < 6 {
                assert_ne!(response.status(), StatusCode::TOO_MANY_REQUESTS);
            } else {
                assert_eq!(response.status(), StatusCode::TOO_MANY_REQUESTS);
            }
        }
    }
}
