//! Private, restart-durable dependent-turn scheduler.
//!
//! The public PromiseResolution API never carries a `Turn`.  Instead, a client
//! may pre-arm this node with one already-signed envelope.  It is strictly
//! decoded and admission-validated, AEAD-sealed under a node-local custody key,
//! and stored in the private redb table. A durable `ReadyToExecute` row performs
//! an atomic destructive claim; only then is the envelope decrypted and handed
//! to the ordinary blocklace SignedTurn ingress. Claim-before-submit gives
//! crash/restart at-most-once semantics: a crash may strand one claimed item,
//! but it can never submit the private turn twice.

use chacha20poly1305::aead::{Aead, AeadCore, KeyInit, OsRng, Payload};
use chacha20poly1305::{XChaCha20Poly1305, XNonce};
use dregg_persist::{
    ClaimedPrivateDependentTurnV1, PersistentStore, PrivateDependentTurnFinishV1,
    PrivateDependentTurnSnapshotV1, private_dependent_ingress_reservation_id_v1,
    private_dependent_ready_digest_v1,
};
use dregg_sdk::SignedTurn;
use serde::Deserialize;

use axum::{
    Json, Router,
    body::Bytes,
    extract::{DefaultBodyLimit, Path, Query, State},
    http::{HeaderMap, StatusCode},
    routing::{get, post},
};

use crate::state::NodeState;

const CUSTODY_KEY_DOMAIN_V1: &str = "dregg-private-dependent-custody-key-v1";
const CUSTODY_AAD_DOMAIN_V1: &[u8] = b"dregg-private-dependent-custody-aad-v1";
const DRAIN_PAGE: usize = 200;
pub const MAX_PRIVATE_DEPENDENT_SIGNED_TURN_BYTES: usize = 256 * 1024;

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct PrivateDependentTurnHandle {
    pub promise_id: String,
    pub expected_resolution_digest: String,
    pub expires_at_sequence_exclusive: u64,
}

#[derive(Clone, Debug, serde::Serialize)]
struct PrivateDependentTurnStatusResponse {
    promise_id: String,
    signed_turn_hash: String,
    expected_resolution_digest: String,
    expires_at_sequence_exclusive: u64,
    status: PrivateDependentTurnStatusWire,
}

#[derive(Clone, Debug, serde::Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
enum PrivateDependentTurnStatusWire {
    Armed,
    Claimed {
        ready_sequence: u64,
        event_id: String,
    },
    Submitted {
        ready_sequence: u64,
        event_id: String,
        ingress_id: String,
    },
    Refused {
        ready_sequence: u64,
        event_id: String,
        reason: String,
    },
    Cancelled,
    Expired {
        ready_sequence: u64,
    },
}

impl From<PrivateDependentTurnSnapshotV1> for PrivateDependentTurnStatusResponse {
    fn from(snapshot: PrivateDependentTurnSnapshotV1) -> Self {
        let status = match snapshot.status {
            dregg_persist::PrivateDependentTurnStatusV1::Armed => {
                PrivateDependentTurnStatusWire::Armed
            }
            dregg_persist::PrivateDependentTurnStatusV1::Claimed {
                ready_sequence,
                event_id,
            } => PrivateDependentTurnStatusWire::Claimed {
                ready_sequence,
                event_id: dregg_types::hex_encode(&event_id),
            },
            dregg_persist::PrivateDependentTurnStatusV1::Submitted {
                ready_sequence,
                event_id,
                ingress_id,
            } => PrivateDependentTurnStatusWire::Submitted {
                ready_sequence,
                event_id: dregg_types::hex_encode(&event_id),
                ingress_id: dregg_types::hex_encode(&ingress_id),
            },
            dregg_persist::PrivateDependentTurnStatusV1::Refused {
                ready_sequence,
                event_id,
                reason,
            } => PrivateDependentTurnStatusWire::Refused {
                ready_sequence,
                event_id: dregg_types::hex_encode(&event_id),
                reason,
            },
            dregg_persist::PrivateDependentTurnStatusV1::Cancelled => {
                PrivateDependentTurnStatusWire::Cancelled
            }
            dregg_persist::PrivateDependentTurnStatusV1::Expired { ready_sequence } => {
                PrivateDependentTurnStatusWire::Expired { ready_sequence }
            }
        };
        Self {
            promise_id: dregg_types::hex_encode(&snapshot.promise_id),
            signed_turn_hash: dregg_types::hex_encode(&snapshot.signed_turn_hash),
            expected_resolution_digest: dregg_types::hex_encode(
                &snapshot.expected_resolution_digest,
            ),
            expires_at_sequence_exclusive: snapshot.expires_at_sequence_exclusive,
            status,
        }
    }
}

#[derive(Debug, serde::Serialize)]
struct PrivateDependentErrorResponse {
    error: String,
}

type PrivateApiError = (StatusCode, Json<PrivateDependentErrorResponse>);

#[derive(Clone, Copy, Debug, Deserialize)]
struct ArmQuery {
    expires_at_sequence_exclusive: u64,
}

#[derive(Debug, serde::Serialize)]
struct CancelResponse {
    promise_id: String,
    cancelled: bool,
}

fn api_error(status: StatusCode, error: impl ToString) -> PrivateApiError {
    (
        status,
        Json(PrivateDependentErrorResponse {
            error: error.to_string(),
        }),
    )
}

fn parse_promise_id(encoded: &str) -> Result<[u8; 32], PrivateApiError> {
    crate::trustline_service::hex_decode_32(encoded)
        .ok_or_else(|| api_error(StatusCode::BAD_REQUEST, "promise id must be 32-byte hex"))
}

/// Bearer-gated, private API. The arm body is canonical postcard `SignedTurn`
/// bytes; no handler response contains plaintext or ciphertext.
pub fn routes() -> Router<NodeState> {
    Router::new()
        .route("/private-dependent-turns", post(post_arm))
        .route("/private-dependent-turns/{promise_id}", get(get_status))
        .route(
            "/private-dependent-turns/{promise_id}/cancel",
            post(post_cancel),
        )
        .route("/api/private-dependent-turns", post(post_arm))
        .route("/api/private-dependent-turns/{promise_id}", get(get_status))
        .route(
            "/api/private-dependent-turns/{promise_id}/cancel",
            post(post_cancel),
        )
        .layer(DefaultBodyLimit::max(
            MAX_PRIVATE_DEPENDENT_SIGNED_TURN_BYTES,
        ))
}

async fn post_arm(
    Query(query): Query<ArmQuery>,
    State(state): State<NodeState>,
    headers: HeaderMap,
    body: Bytes,
) -> Result<Json<PrivateDependentTurnHandle>, PrivateApiError> {
    if headers
        .get(axum::http::header::CONTENT_TYPE)
        .and_then(|value| value.to_str().ok())
        != Some("application/octet-stream")
    {
        return Err(api_error(
            StatusCode::UNSUPPORTED_MEDIA_TYPE,
            "private dependent-turn arm requires application/octet-stream",
        ));
    }
    if body.len() > MAX_PRIVATE_DEPENDENT_SIGNED_TURN_BYTES {
        return Err(api_error(
            StatusCode::PAYLOAD_TOO_LARGE,
            "signed dependent turn exceeds 262144-byte bound",
        ));
    }
    arm_private_dependent_turn(&state, &body, query.expires_at_sequence_exclusive)
        .await
        .map(Json)
        .map_err(|error| {
            let status = match error {
                PrivateDependentTurnError::NodeLocked => StatusCode::FORBIDDEN,
                PrivateDependentTurnError::AlreadyExpired => StatusCode::CONFLICT,
                PrivateDependentTurnError::Store(_) => StatusCode::INTERNAL_SERVER_ERROR,
                PrivateDependentTurnError::IngressUnavailable => StatusCode::SERVICE_UNAVAILABLE,
                _ => StatusCode::BAD_REQUEST,
            };
            api_error(status, error)
        })
}

async fn get_status(
    Path(promise_id): Path<String>,
    State(state): State<NodeState>,
) -> Result<Json<PrivateDependentTurnStatusResponse>, PrivateApiError> {
    let promise_id = parse_promise_id(&promise_id)?;
    private_dependent_turn_status(&state, promise_id)
        .await
        .map_err(|error| api_error(StatusCode::INTERNAL_SERVER_ERROR, error))?
        .map(PrivateDependentTurnStatusResponse::from)
        .map(Json)
        .ok_or_else(|| api_error(StatusCode::NOT_FOUND, "private dependent turn not found"))
}

async fn post_cancel(
    Path(promise_id): Path<String>,
    State(state): State<NodeState>,
) -> Result<Json<CancelResponse>, PrivateApiError> {
    let promise_id = parse_promise_id(&promise_id)?;
    let cancelled = cancel_private_dependent_turn(&state, promise_id)
        .await
        .map_err(|error| api_error(StatusCode::INTERNAL_SERVER_ERROR, error))?;
    Ok(Json(CancelResponse {
        promise_id: dregg_types::hex_encode(&promise_id),
        cancelled,
    }))
}

#[derive(Debug)]
pub enum PrivateDependentTurnError {
    NodeLocked,
    Decode(String),
    Validation(String),
    ReceiptChainMismatch,
    PromiseHashMismatch,
    AlreadyExpired,
    Seal(String),
    Store(String),
    IngressUnavailable,
}

impl core::fmt::Display for PrivateDependentTurnError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::NodeLocked => f.write_str("node cipherclerk is locked"),
            Self::Decode(error) => write!(f, "signed dependent turn decode failed: {error}"),
            Self::Validation(error) => {
                write!(f, "signed dependent turn admission refused: {error}")
            }
            Self::ReceiptChainMismatch => {
                f.write_str("signed dependent turn receipt chain does not match current agent head")
            }
            Self::PromiseHashMismatch => {
                f.write_str("signed dependent turn hash does not equal its promise id")
            }
            Self::AlreadyExpired => {
                f.write_str("private dependent-turn expiry is not ahead of the scheduler cursor")
            }
            Self::Seal(error) => write!(f, "private dependent-turn custody seal failed: {error}"),
            Self::Store(error) => write!(f, "private dependent-turn store refused: {error}"),
            Self::IngressUnavailable => f.write_str("validated blocklace ingress is unavailable"),
        }
    }
}

impl std::error::Error for PrivateDependentTurnError {}

fn custody_key(secret: [u8; 32]) -> [u8; 32] {
    *blake3::Hasher::new_derive_key(CUSTODY_KEY_DOMAIN_V1)
        .update(&secret)
        .finalize()
        .as_bytes()
}

fn custody_aad(
    promise_id: [u8; 32],
    expected_resolution_digest: [u8; 32],
    expires_at_sequence_exclusive: u64,
) -> Vec<u8> {
    let mut aad = Vec::with_capacity(CUSTODY_AAD_DOMAIN_V1.len() + 72);
    aad.extend_from_slice(CUSTODY_AAD_DOMAIN_V1);
    aad.extend_from_slice(&promise_id);
    aad.extend_from_slice(&expected_resolution_digest);
    aad.extend_from_slice(&expires_at_sequence_exclusive.to_le_bytes());
    aad
}

fn seal_signed_turn(
    secret: [u8; 32],
    promise_id: [u8; 32],
    expected_resolution_digest: [u8; 32],
    expires_at_sequence_exclusive: u64,
    plaintext: &[u8],
) -> Result<Vec<u8>, PrivateDependentTurnError> {
    let key = custody_key(secret);
    let cipher = XChaCha20Poly1305::new((&key).into());
    let nonce = XChaCha20Poly1305::generate_nonce(&mut OsRng);
    let aad = custody_aad(
        promise_id,
        expected_resolution_digest,
        expires_at_sequence_exclusive,
    );
    let ciphertext = cipher
        .encrypt(
            &nonce,
            Payload {
                msg: plaintext,
                aad: &aad,
            },
        )
        .map_err(|error| PrivateDependentTurnError::Seal(error.to_string()))?;
    let mut sealed = Vec::with_capacity(nonce.len() + ciphertext.len());
    sealed.extend_from_slice(&nonce);
    sealed.extend_from_slice(&ciphertext);
    Ok(sealed)
}

fn open_signed_turn(
    secret: [u8; 32],
    claim: &ClaimedPrivateDependentTurnV1,
    expires_at_sequence_exclusive: u64,
) -> Result<Vec<u8>, PrivateDependentTurnError> {
    if claim.sealed_signed_turn.len() < 24 + 16 {
        return Err(PrivateDependentTurnError::Seal(
            "sealed envelope is truncated".to_string(),
        ));
    }
    let (nonce, ciphertext) = claim.sealed_signed_turn.split_at(24);
    let key = custody_key(secret);
    let cipher = XChaCha20Poly1305::new((&key).into());
    let aad = custody_aad(
        claim.promise_id,
        claim.expected_resolution_digest,
        expires_at_sequence_exclusive,
    );
    cipher
        .decrypt(
            XNonce::from_slice(nonce),
            Payload {
                msg: ciphertext,
                aad: &aad,
            },
        )
        .map_err(|_| PrivateDependentTurnError::Seal("AEAD authentication failed".to_string()))
}

fn strict_signed_turn(bytes: &[u8]) -> Result<SignedTurn, PrivateDependentTurnError> {
    let signed = crate::signed_turn_validation::decode_signed_turn(bytes)
        .map_err(|error| PrivateDependentTurnError::Decode(error.to_string()))?;
    let canonical = postcard::to_stdvec(&signed)
        .map_err(|error| PrivateDependentTurnError::Decode(error.to_string()))?;
    if canonical != bytes {
        return Err(PrivateDependentTurnError::Decode(
            "signed dependent turn is not canonical".to_string(),
        ));
    }
    Ok(signed)
}

/// Privately arm one dependent turn before its promise becomes ready.
///
/// The envelope is already signed; this node never manufactures authority for
/// it. The shared outer SignedTurn predicate and current receipt-chain link are
/// checked before any private bytes reach durable custody.
pub async fn arm_private_dependent_turn(
    state: &NodeState,
    signed_turn_bytes: &[u8],
    expires_at_sequence_exclusive: u64,
) -> Result<PrivateDependentTurnHandle, PrivateDependentTurnError> {
    let signed = strict_signed_turn(signed_turn_bytes)?;
    let promise_id = signed.turn.hash();
    let (store, secret) = {
        let state = state.read().await;
        if !state.unlocked {
            return Err(PrivateDependentTurnError::NodeLocked);
        }
        let executor = crate::executor_setup::new_submit_executor(&state);
        crate::signed_turn_validation::validate_signed_turn(
            &signed,
            &executor,
            state.ledger.get(&signed.turn.agent),
        )
        .map_err(|error| PrivateDependentTurnError::Validation(error.to_string()))?;
        if signed.turn.previous_receipt_hash
            != state.cclerk.agent_receipt_head_hash(&signed.turn.agent)
        {
            return Err(PrivateDependentTurnError::ReceiptChainMismatch);
        }
        (
            state.store.clone(),
            state.cclerk.gossip_signing_key().to_bytes(),
        )
    };
    if store
        .private_dependent_scheduler_cursor_v1()
        .map_err(|error| PrivateDependentTurnError::Store(error.to_string()))?
        .is_some_and(|cursor| expires_at_sequence_exclusive <= cursor)
    {
        return Err(PrivateDependentTurnError::AlreadyExpired);
    }
    let expected_resolution_digest = private_dependent_ready_digest_v1(promise_id, promise_id);
    let sealed = seal_signed_turn(
        secret,
        promise_id,
        expected_resolution_digest,
        expires_at_sequence_exclusive,
        signed_turn_bytes,
    )?;
    store
        .arm_private_dependent_turn_v1(
            promise_id,
            promise_id,
            sealed,
            expires_at_sequence_exclusive,
        )
        .map_err(|error| PrivateDependentTurnError::Store(error.to_string()))?;
    Ok(PrivateDependentTurnHandle {
        promise_id: dregg_types::hex_encode(&promise_id),
        expected_resolution_digest: dregg_types::hex_encode(&expected_resolution_digest),
        expires_at_sequence_exclusive,
    })
}

pub async fn cancel_private_dependent_turn(
    state: &NodeState,
    promise_id: [u8; 32],
) -> Result<bool, PrivateDependentTurnError> {
    let store = { state.read().await.store.clone() };
    store
        .cancel_private_dependent_turn_v1(promise_id)
        .map_err(|error| PrivateDependentTurnError::Store(error.to_string()))
}

pub async fn private_dependent_turn_status(
    state: &NodeState,
    promise_id: [u8; 32],
) -> Result<Option<PrivateDependentTurnSnapshotV1>, PrivateDependentTurnError> {
    let store = { state.read().await.store.clone() };
    store
        .private_dependent_turn_status_v1(promise_id)
        .map_err(|error| PrivateDependentTurnError::Store(error.to_string()))
}

/// Nudge the scheduler after Fresh publication or after startup installs the
/// consensus handle. Concurrent nudges are safe: redb's destructive claim is
/// the unique release authority.
pub(crate) fn spawn_private_dependent_turn_drain(state: NodeState) {
    tokio::spawn(async move {
        if let Err(error) = drain_private_dependent_turns(&state).await {
            tracing::error!(error = %error, "private dependent-turn scheduler stopped");
        }
    });
}

async fn drain_private_dependent_turns(state: &NodeState) -> Result<(), PrivateDependentTurnError> {
    let blocklace = state
        .blocklace()
        .await
        .ok_or(PrivateDependentTurnError::IngressUnavailable)?;
    let store = { state.read().await.store.clone() };
    reconcile_claimed_turns(&store)?;
    let mut cursor = store
        .private_dependent_scheduler_cursor_v1()
        .map_err(|error| PrivateDependentTurnError::Store(error.to_string()))?;

    loop {
        let rows = store
            .promise_resolutions_after_v1(cursor, DRAIN_PAGE)
            .map_err(|error| PrivateDependentTurnError::Store(error.to_string()))?;
        if rows.is_empty() {
            return Ok(());
        }
        let page_len = rows.len();
        for row in rows {
            if row.outcome == dregg_persist::PromiseResolutionKindV1::ReadyToExecute {
                // Do not consume custody while the node cannot submit. Once the
                // destructive claim commits, at-most-once deliberately wins
                // over retry-on-crash liveness.
                if !state.read().await.unlocked {
                    return Err(PrivateDependentTurnError::NodeLocked);
                }
                if let Some(claim) = store
                    .claim_private_dependent_turn_v1(row.pending_id, row.sequence)
                    .map_err(|error| PrivateDependentTurnError::Store(error.to_string()))?
                {
                    let outcome = submit_claimed_turn(state, &blocklace, &store, &claim).await;
                    let finish = match outcome {
                        Ok(Some(ingress_id)) => {
                            Some(PrivateDependentTurnFinishV1::Submitted { ingress_id })
                        }
                        // Multi-party ingress is safely queued with the durable
                        // reservation still Reserved. The round cadence owns the
                        // atomic block+Submitted transition.
                        Ok(None) => None,
                        Err(error) => Some(PrivateDependentTurnFinishV1::Refused {
                            reason: error.to_string(),
                        }),
                    };
                    if let Some(finish) = finish {
                        store
                            .finish_private_dependent_turn_v1(
                                claim.promise_id,
                                claim.ready_sequence,
                                claim.event_id,
                                finish,
                            )
                            .map_err(|error| PrivateDependentTurnError::Store(error.to_string()))?;
                    }
                }
            }
            store
                .advance_private_dependent_scheduler_cursor_v1(row.sequence)
                .map_err(|error| PrivateDependentTurnError::Store(error.to_string()))?;
            cursor = Some(row.sequence);
        }
        if page_len < DRAIN_PAGE {
            return Ok(());
        }
    }
}

fn reconcile_claimed_turns(store: &PersistentStore) -> Result<(), PrivateDependentTurnError> {
    let claimed = store
        .claimed_private_dependent_turns_v1()
        .map_err(|error| PrivateDependentTurnError::Store(error.to_string()))?;
    for snapshot in claimed {
        let dregg_persist::PrivateDependentTurnStatusV1::Claimed {
            ready_sequence,
            event_id,
        } = snapshot.status
        else {
            continue;
        };
        let Some(finalized) = store
            .lookup_turn(&snapshot.signed_turn_hash)
            .map_err(|error| PrivateDependentTurnError::Store(error.to_string()))?
        else {
            // Crash uncertainty is intentionally not a retry authority. The
            // byte-identical payload may already be queued but not finalized;
            // remain Claimed until a later wake/restart can reconcile it.
            continue;
        };
        store
            .finish_private_dependent_turn_v1(
                snapshot.promise_id,
                ready_sequence,
                event_id,
                PrivateDependentTurnFinishV1::Submitted {
                    ingress_id: finalized.block_id,
                },
            )
            .map_err(|error| PrivateDependentTurnError::Store(error.to_string()))?;
        tracing::info!(
            promise_id = %dregg_types::hex_encode(&snapshot.promise_id),
            ready_sequence,
            "reconciled crash-uncertain private dependent turn from finalized turn index"
        );
    }
    Ok(())
}

async fn submit_claimed_turn(
    state: &NodeState,
    blocklace: &crate::blocklace_sync::BlocklaceHandle,
    store: &PersistentStore,
    claim: &ClaimedPrivateDependentTurnV1,
) -> Result<Option<[u8; 32]>, PrivateDependentTurnError> {
    let snapshot = store
        .private_dependent_turn_status_v1(claim.promise_id)
        .map_err(|error| PrivateDependentTurnError::Store(error.to_string()))?
        .ok_or_else(|| {
            PrivateDependentTurnError::Store("claimed custody row disappeared".to_string())
        })?;
    let (secret, plaintext) = {
        let state = state.read().await;
        if !state.unlocked {
            return Err(PrivateDependentTurnError::NodeLocked);
        }
        let secret = state.cclerk.gossip_signing_key().to_bytes();
        let plaintext = open_signed_turn(secret, claim, snapshot.expires_at_sequence_exclusive)?;
        (secret, plaintext)
    };
    // Drop the derived secret from the logical flow before admission. (The
    // stack copy is overwritten here; AEAD key material is never persisted.)
    let mut secret = secret;
    secret.fill(0);

    let signed = strict_signed_turn(&plaintext)?;
    if signed.turn.hash() != claim.promise_id
        || claim.signed_turn_hash != claim.promise_id
        || private_dependent_ready_digest_v1(claim.promise_id, signed.turn.hash())
            != claim.expected_resolution_digest
    {
        return Err(PrivateDependentTurnError::PromiseHashMismatch);
    }
    {
        let state = state.read().await;
        let executor = crate::executor_setup::new_submit_executor(&state);
        crate::signed_turn_validation::validate_signed_turn(
            &signed,
            &executor,
            state.ledger.get(&signed.turn.agent),
        )
        .map_err(|error| PrivateDependentTurnError::Validation(error.to_string()))?;
        if signed.turn.previous_receipt_hash
            != state.cclerk.agent_receipt_head_hash(&signed.turn.agent)
        {
            return Err(PrivateDependentTurnError::ReceiptChainMismatch);
        }
    }

    // This is the ordinary consensus ingress; finalization runs the same shared
    // SignedTurn predicate again under the authoritative state lock. No private
    // scheduler execution path or unsigned auto-submit exists.
    let reservation_id = private_dependent_ingress_reservation_id_v1(
        claim.promise_id,
        claim.signed_turn_hash,
        claim.ready_sequence,
        claim.event_id,
    );
    blocklace
        .submit_private_dependent_turn(state, reservation_id, plaintext)
        .await
        .map(|block_id| block_id.map(|id| id.0))
        .map_err(PrivateDependentTurnError::Store)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lifecycle_turn(marker: u8, actor: dregg_cell::CellId) -> dregg_turn::Turn {
        dregg_turn::Turn {
            agent: actor,
            nonce: u64::from(marker),
            fee: 0,
            memo: None,
            valid_until: None,
            call_forest: dregg_turn::CallForest::new(),
            depends_on: vec![],
            previous_receipt_hash: None,
            conservation_proof: None,
            sovereign_witnesses: Default::default(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        }
    }

    fn lifecycle_receipt(turn: &dregg_turn::Turn, marker: u8) -> dregg_turn::TurnReceipt {
        dregg_turn::TurnReceipt {
            turn_hash: turn.hash(),
            forest_hash: turn.call_forest.compute_hash(),
            pre_state_hash: [marker; 32],
            post_state_hash: [marker.wrapping_add(1); 32],
            timestamp: i64::from(marker),
            effects_hash: [marker.wrapping_add(2); 32],
            computrons_used: 0,
            action_count: 0,
            previous_receipt_hash: None,
            agent: turn.agent,
            federation_id: [marker.wrapping_add(3); 32],
            routing_directives: vec![],
            introduction_exports: vec![],
            derivation_records: vec![],
            emitted_events: vec![],
            executor_signature: None,
            finality: Default::default(),
            was_encrypted: false,
            was_burn: false,
            consumed_capabilities: vec![],
        }
    }

    fn lifecycle_commit_record(
        ordinal: u64,
        turn_hash: [u8; 32],
        receipt_hash: [u8; 32],
    ) -> dregg_persist::CommitRecord {
        dregg_persist::CommitRecord {
            ordinal,
            height: ordinal + 1,
            block_id: [0x80u8.wrapping_add(ordinal as u8); 32],
            block_executed_up_to: ordinal,
            turn_hash,
            creator: [0x90; 32],
            receipt_hash,
            ledger_root: [0xA0u8.wrapping_add(ordinal as u8); 32],
            touched_cells: Vec::new(),
            removed: Vec::new(),
        }
    }

    fn lifecycle_executor_state(
        predecessor: &[u8],
        successor: Vec<u8>,
        promise_resolutions: Vec<dregg_persist::PromiseResolutionCandidateV1>,
    ) -> dregg_persist::FinalizedExecutorConsensusState {
        dregg_persist::FinalizedExecutorConsensusState {
            reactive_registry: dregg_persist::ReactiveRegistryCasV1::new(
                dregg_persist::reactive_registry_commitment(predecessor),
                successor,
            ),
            promise_resolutions,
            ..Default::default()
        }
    }

    #[test]
    fn custody_aead_binds_promise_digest_and_expiry() {
        let secret = [7; 32];
        let promise = [3; 32];
        let digest = private_dependent_ready_digest_v1(promise, promise);
        let sealed = seal_signed_turn(secret, promise, digest, 99, b"signed-turn").unwrap();
        let claim = ClaimedPrivateDependentTurnV1 {
            promise_id: promise,
            signed_turn_hash: promise,
            expected_resolution_digest: digest,
            ready_sequence: 2,
            event_id: [4; 32],
            sealed_signed_turn: sealed,
        };
        assert_eq!(
            open_signed_turn(secret, &claim, 99).unwrap(),
            b"signed-turn"
        );
        assert!(open_signed_turn(secret, &claim, 100).is_err());
        let mut substituted = claim.clone();
        substituted.promise_id[0] ^= 1;
        assert!(open_signed_turn(secret, &substituted, 99).is_err());
        let mut corrupted = claim;
        corrupted.sealed_signed_turn[30] ^= 1;
        assert!(open_signed_turn(secret, &corrupted, 99).is_err());
    }

    #[test]
    fn promise_id_parser_rejects_malformed_and_overlong_hex() {
        assert_eq!(parse_promise_id(&"00".repeat(32)).unwrap(), [0; 32]);
        assert!(parse_promise_id(&"00".repeat(33)).is_err());
        assert!(parse_promise_id(&"0g".repeat(32)).is_err());
        assert!(parse_promise_id("é").is_err());
    }

    #[tokio::test]
    async fn arm_uses_shared_signed_ingress_and_public_handle_has_no_turn() {
        let dir = tempfile::tempdir().unwrap();
        let state = NodeState::new(dir.path(), vec![]).unwrap();
        let signed = {
            let mut inner = state.write().await;
            inner.unlocked = true;
            let operator = crate::executor_setup::local_agent_cell(&inner);
            if inner.ledger.get(&operator).is_none() {
                let token = *blake3::hash(b"default").as_bytes();
                let public_key = inner.cclerk.public_key().0;
                inner
                    .ledger
                    .insert_cell(dregg_cell::Cell::with_balance(public_key, token, 1_000_000))
                    .unwrap();
            }
            let turn = dregg_turn::Turn {
                agent: operator,
                nonce: inner.ledger.get(&operator).unwrap().state.nonce(),
                fee: 0,
                memo: None,
                valid_until: Some(i64::MAX / 2),
                call_forest: dregg_turn::CallForest::new(),
                depends_on: vec![],
                previous_receipt_hash: inner.cclerk.agent_receipt_head_hash(&operator),
                conservation_proof: None,
                sovereign_witnesses: Default::default(),
                execution_proof: None,
                execution_proof_cell: None,
                execution_proof_new_commitment: None,
                custom_program_proofs: None,
                effect_binding_proofs: Vec::new(),
                cross_effect_dependencies: Vec::new(),
                effect_witness_index_map: Vec::new(),
            };
            inner.cclerk.sign_turn(&turn)
        };
        let bytes = postcard::to_stdvec(&signed).unwrap();
        let handle = arm_private_dependent_turn(&state, &bytes, 100)
            .await
            .unwrap();
        let public = serde_json::to_value(&handle).unwrap();
        assert!(public.get("signed_turn").is_none());
        assert!(public.get("sealed_signed_turn").is_none());
        let promise_id = signed.turn.hash();
        assert_eq!(handle.promise_id, dregg_types::hex_encode(&promise_id));
        assert!(
            cancel_private_dependent_turn(&state, promise_id)
                .await
                .unwrap()
        );

        let mut trailing = bytes;
        trailing.push(0);
        assert!(matches!(
            arm_private_dependent_turn(&state, &trailing, 100).await,
            Err(PrivateDependentTurnError::Decode(_))
        ));
    }

    /// Composition canary for the complete durable lifecycle without entering
    /// blocklace internals: legacy waiting registry → finalized Ready outbox +
    /// DPRG2 successor in one commit → process restart → unique private claim →
    /// exact finalized wake receipt → durable Resolved row and removal.
    #[test]
    fn finalized_ready_survives_restart_and_only_exact_receipt_closes_wake() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("store.redb");
        let store = dregg_persist::PersistentStore::open(&path).unwrap();
        let actor = dregg_cell::CellId::from_bytes([0x31; 32]);
        let wake = lifecycle_turn(1, actor);
        let wake_hash = wake.hash();
        let condition = dregg_turn::ProofCondition::HashPreimage { hash: [0x41; 32] };

        // Commit the pre-armed Waiting image first. It is deliberately DPRG1:
        // restoring it must preserve the byte-exact CAS predecessor.
        let mut registry = dregg_turn::PendingTurnRegistry::new();
        let empty_v1 = registry.to_canonical_bytes().unwrap();
        assert!(empty_v1.starts_with(b"DPRG1"));
        registry
            .try_submit_pending_at(
                wake.clone(),
                dregg_turn::ResolutionCondition::AwaitCondition(condition.clone()),
                100,
                0,
            )
            .unwrap();
        let waiting_v1 = registry.to_canonical_bytes().unwrap();
        assert!(waiting_v1.starts_with(b"DPRG1"));
        store
            .commit_finalized_turn_with_executor_state(
                0,
                &lifecycle_commit_record(0, [0x50; 32], [0x51; 32]),
                &[],
                &lifecycle_executor_state(&empty_v1, waiting_v1.clone(), vec![]),
            )
            .unwrap();
        store
            .arm_private_dependent_turn_v1(wake_hash, wake_hash, vec![0xCC; 80], 100)
            .unwrap();

        // The carrier's finalized receipt publishes Ready and the promoted
        // registry as one executor-state transaction.
        registry
            .mark_react_ready(&wake_hash, &actor, &condition, &wake, 10)
            .unwrap();
        let carrier = lifecycle_turn(2, actor);
        let carrier_receipt = lifecycle_receipt(&carrier, 0x61);
        let ready = registry.resolve(
            carrier.hash(),
            dregg_turn::ResolutionOutcome::Resolved(carrier_receipt.clone()),
        );
        assert!(matches!(
            ready.as_slice(),
            [dregg_turn::ResolutionEvent::ReadyToExecute { turn_hash, turn }]
                if *turn_hash == wake_hash && turn.hash() == wake_hash
        ));
        let published_v2 = registry.to_canonical_bytes().unwrap();
        assert!(published_v2.starts_with(b"DPRG2"));
        let ready_candidates = crate::promise_resolutions::resolution_candidates(
            1,
            carrier_receipt.receipt_hash(),
            &ready,
        )
        .unwrap();
        store
            .commit_finalized_turn_with_executor_state(
                1,
                &lifecycle_commit_record(1, carrier.hash(), carrier_receipt.receipt_hash()),
                &[],
                &lifecycle_executor_state(&waiting_v1, published_v2.clone(), ready_candidates),
            )
            .unwrap();

        // Process death after the finalized commit cannot erase Ready or emit
        // it twice. The private scheduler consumes the durable row exactly once.
        drop(store);
        let store = dregg_persist::PersistentStore::open(&path).unwrap();
        let durable_ready = store
            .promise_resolution_batch_for_commit_v1(1)
            .unwrap()
            .unwrap();
        assert!(matches!(
            durable_ready.as_slice(),
            [row]
                if row.pending_id == wake_hash
                    && row.outcome == dregg_persist::PromiseResolutionKindV1::ReadyToExecute
        ));
        let claim = store
            .claim_private_dependent_turn_v1(wake_hash, durable_ready[0].sequence)
            .unwrap()
            .expect("restart scheduler claims durable Ready once");
        assert_eq!(claim.promise_id, wake_hash);
        assert!(
            store
                .claim_private_dependent_turn_v1(wake_hash, durable_ready[0].sequence)
                .unwrap()
                .is_none()
        );

        let restored_bytes = store
            .load_latest_reactive_registry_snapshot_bytes()
            .unwrap();
        assert_eq!(restored_bytes, published_v2);
        let mut restored =
            dregg_turn::PendingTurnRegistry::from_canonical_bytes(&restored_bytes).unwrap();
        assert_eq!(
            restored.authorize_react(&wake_hash, &actor, &condition, &wake, 11),
            Err(dregg_turn::PendingReactError::AlreadyReleased),
            "restart must retain Published and refuse a second release"
        );

        // A receipt for a different turn cannot consume the retained wake.
        let other = lifecycle_turn(3, actor);
        assert!(
            restored
                .resolve(
                    wake_hash,
                    dregg_turn::ResolutionOutcome::Resolved(lifecycle_receipt(&other, 0x71)),
                )
                .is_empty()
        );
        assert!(restored.get_pending(&wake_hash).is_some());

        // Only the exact wake receipt closes the registry and publishes the
        // terminal Resolved observer row in the next finalized transaction.
        let wake_receipt = lifecycle_receipt(&wake, 0x72);
        let resolved = restored.resolve(
            wake_hash,
            dregg_turn::ResolutionOutcome::Resolved(wake_receipt.clone()),
        );
        assert!(matches!(
            resolved.as_slice(),
            [dregg_turn::ResolutionEvent::Resolved { turn_hash, receipt }]
                if *turn_hash == wake_hash && receipt.turn_hash == wake_hash
        ));
        let resolved_candidates = crate::promise_resolutions::resolution_candidates(
            2,
            wake_receipt.receipt_hash(),
            &resolved,
        )
        .unwrap();
        store
            .commit_finalized_turn_with_executor_state(
                2,
                &lifecycle_commit_record(2, wake_hash, wake_receipt.receipt_hash()),
                &[],
                &lifecycle_executor_state(
                    &published_v2,
                    restored.to_canonical_bytes().unwrap(),
                    resolved_candidates,
                ),
            )
            .unwrap();
        drop(store);

        let reopened = dregg_persist::PersistentStore::open(&path).unwrap();
        let terminal = dregg_turn::PendingTurnRegistry::from_canonical_bytes(
            &reopened
                .load_latest_reactive_registry_snapshot_bytes()
                .unwrap(),
        )
        .unwrap();
        assert!(terminal.is_empty());
        let rows = reopened.promise_resolutions_after_v1(None, 10).unwrap();
        assert_eq!(rows.len(), 2);
        assert_eq!(
            rows[0].outcome,
            dregg_persist::PromiseResolutionKindV1::ReadyToExecute
        );
        assert!(matches!(
            rows[1].outcome,
            dregg_persist::PromiseResolutionKindV1::Resolved { receipt_hash }
                if receipt_hash == wake_receipt.receipt_hash()
        ));
    }
}
