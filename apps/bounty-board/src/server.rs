//! In-process bounty board server for embedding in examples and tests.
//!
//! This module provides a way to start the bounty board HTTP server within the
//! same process (as a background tokio task), avoiding the need for a separate
//! binary or a live devnet node.
//!
//! Uses the shared `AppServer` from `dregg-app-framework` for consistent
//! infrastructure (health endpoint, CORS) across all dregg apps.
//!
//! REVIEW[P2]: The blinded-queue and inbox upgrades live ONLY in this in-process
//! server. The production binary entrypoint `src/main.rs` does not call
//! `with_blinded_endpoint` / `with_inbox` and does not share a `CapInbox` with
//! its `submit_work` handler — so the upgrades are exercised only by lib tests
//! and `examples/`, not by the deployed binary. Either wire the same primitives
//! into `main.rs` or extract a shared builder.

use std::net::SocketAddr;
use std::sync::Arc;
use std::time::Instant;

use axum::{
    Json, Router,
    extract::{Path, Query, State},
    http::StatusCode,
    response::IntoResponse,
    routing::{get, post},
};
use serde_json::json;
use tokio::sync::{Mutex, RwLock};
use tracing::{info, warn};

use dregg_app_framework::auth::{AdminAuth, AdminToken, HasAdminToken};
use dregg_app_framework::blinded_endpoint::FairDistributionEndpoint;
use dregg_app_framework::hex::{bytes32_to_hex, hex_to_bytes32};
use dregg_app_framework::inbox_endpoint::InboxEndpoint;
use dregg_app_framework::server::{AppConfig, AppServer};
use dregg_app_framework::{CellId, EngineConfig, DreggEngine};
use dregg_storage::QuotaId;
use dregg_storage::blinded::BlindedQueue;
use dregg_storage::inbox::{CapInbox, InboxMessage};

use crate::qualification::{FederationRootHistory, verify_qualification};
use crate::state::BoardState;
use crate::{
    ApproveRequest, Bounty, BountyFilter, BountyStatus, BountyStatusResponse, ClaimRequest,
    CreateBountyRequest, SubmitRequest, bounty_id_from_hex, bounty_id_hex, compute_bounty_id,
};

// =============================================================================
// Configuration
// =============================================================================

/// Configuration for the in-process bounty board server.
pub struct ServerConfig {
    /// Initial federation root (can be updated via admin endpoint).
    pub federation_root: [u8; 32],
    /// Listen address.
    pub listen: SocketAddr,
}

impl Default for ServerConfig {
    fn default() -> Self {
        Self {
            federation_root: [0u8; 32],
            listen: "127.0.0.1:3030".parse().unwrap(),
        }
    }
}

// =============================================================================
// Application State
// =============================================================================

/// Shared application state passed to all handlers.
#[derive(Clone)]
struct AppState {
    board: BoardState,
    root_history: Arc<RwLock<FederationRootHistory>>,
    root_last_updated: Arc<RwLock<Option<Instant>>>,
    engine: Arc<Mutex<DreggEngine>>,
    node_url: Arc<String>,
    node_connected: Arc<RwLock<bool>>,
    admin_token: AdminToken,
    /// Blinded queue for fair bounty claiming (upgrade: blinded queue).
    claim_queue: Arc<Mutex<BlindedQueue>>,
    /// Inbox for issuer delivery notifications (upgrade: store-and-forward).
    issuer_inbox: Arc<Mutex<CapInbox>>,
}

impl HasAdminToken for AppState {
    fn admin_token(&self) -> &AdminToken {
        &self.admin_token
    }
}

// =============================================================================
// Public API
// =============================================================================

/// Start the bounty board server in the background as a tokio task.
///
/// Returns the actual `SocketAddr` the server is listening on (useful when
/// the port is 0 for random assignment).
///
/// Uses the framework's `AppServer` for consistent infrastructure. The server
/// runs until the tokio runtime is shut down.
pub async fn start_server(config: ServerConfig) -> SocketAddr {
    let now_ts = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0);

    // --- Upgrade 1: Blinded queue for fair bounty claiming ---
    // REVIEW[P1]: This is one shared queue across ALL bounties, not per-bounty.
    // The commitments and nullifiers do not bind a worker to a specific bounty:
    // `BlindedQueue::commit` stores any worker-supplied 32 bytes, and the
    // nullifier is `Hash(commitment, secret, position)` — no bounty_id is hashed
    // in. Consequence: a worker who consumes one slot has burned a nullifier
    // useful for any bounty, and there is no `claim_bounty` handler that actually
    // requires a queue token before claiming. The blinded queue is wired but
    // unused by the bounty lifecycle — it's plumbing, not enforcement.
    // Capacity 256: supports up to 256 concurrent claim commitments per bounty.
    let claims_endpoint = FairDistributionEndpoint::new(256);
    let claim_queue = claims_endpoint.queue_arc();

    // --- Upgrade 2: Store-and-forward inbox for issuer delivery notifications ---
    // REVIEW[P1]: One shared inbox for ALL issuers. Every issuer reads every
    // worker's notification, regardless of which bounty was submitted. There is
    // also no auth on `GET /inbox/issuers/next` — any HTTP client can drain the
    // queue. For a real deployment, scope inbox per-issuer (e.g. one CapInbox
    // keyed by issuer_cell) and gate `/next`/`/status` on issuer identity.
    // Capacity 128 messages, minimum deposit 0 (internal server-to-server delivery).
    let inbox = Arc::new(Mutex::new(CapInbox::new(QuotaId(0), 128, 0)));
    let issuers_endpoint = InboxEndpoint::from_inbox(Arc::clone(&inbox));
    let issuer_inbox = Arc::clone(&inbox);

    let state = AppState {
        board: BoardState::new(),
        root_history: Arc::new(RwLock::new(FederationRootHistory::with_initial_root(
            config.federation_root,
        ))),
        root_last_updated: Arc::new(RwLock::new(Some(Instant::now()))),
        engine: Arc::new(Mutex::new(DreggEngine::new(EngineConfig::new(now_ts)))),
        node_url: Arc::new("none".to_string()),
        node_connected: Arc::new(RwLock::new(false)),
        // In-process server uses open admin mode (no token needed for tests/examples).
        admin_token: AdminToken::open(),
        claim_queue,
        issuer_inbox,
    };

    let app_routes = app_router().with_state(state);

    let app_config = AppConfig::default().with_listen(config.listen.to_string());

    let addr = AppServer::new(app_config)
        .service_name("dregg-bounty-board")
        .with_health()
        .with_cors()
        // Upgrade 1: blinded queue for fair bounty claiming
        .with_blinded_endpoint("/queue/claims", claims_endpoint)
        // Upgrade 2: store-and-forward inbox for issuer delivery notifications
        .with_inbox("/inbox/issuers", issuers_endpoint)
        .routes(app_routes)
        .serve_background()
        .await
        .expect("failed to start bounty board server");

    addr
}

/// Build the application router for the in-process server.
fn app_router() -> Router<AppState> {
    Router::new()
        .route("/bounties", post(create_bounty))
        .route("/bounties", get(list_bounties))
        .route("/bounties/{id}/claim", post(claim_bounty))
        .route("/bounties/{id}/submit", post(submit_work))
        .route("/bounties/{id}/approve", post(approve_bounty))
        .route("/bounties/{id}/status", get(bounty_status))
        .route("/worker/bounties", get(worker_bounties))
        .route("/admin/height", post(advance_height))
        .route("/admin/expire", post(expire_bounties))
        .route("/admin/federation-root", post(set_federation_root))
}

// =============================================================================
// Handlers
// =============================================================================

async fn create_bounty(
    State(state): State<AppState>,
    Json(req): Json<CreateBountyRequest>,
) -> impl IntoResponse {
    let current_height = state.board.current_height().await;

    let issuer_cell = match bounty_id_from_hex(&req.issuer_cell) {
        Some(bytes) => CellId::from_bytes(bytes),
        None => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "invalid issuer_cell hex"})),
            );
        }
    };

    if req.deadline_height <= current_height {
        return (
            StatusCode::BAD_REQUEST,
            Json(json!({"error": "deadline must be in the future"})),
        );
    }

    let bounty_id = compute_bounty_id(&issuer_cell, &req.title, req.reward_amount, current_height);

    let bounty = Bounty {
        id: bounty_id,
        issuer_cell,
        title: req.title,
        description: req.description,
        reward_amount: req.reward_amount,
        reward_asset: req.reward_asset,
        deadline_height: req.deadline_height,
        qualification: req.qualification,
        status: BountyStatus::Open,
        reward_token: req.reward_token,
        created_at: current_height,
        tags: req.tags,
    };

    let id_hex = bounty_id_hex(&bounty_id);
    state.board.insert_bounty(bounty).await;

    (
        StatusCode::CREATED,
        Json(json!({
            "id": id_hex,
            "status": "open"
        })),
    )
}

async fn list_bounties(
    State(state): State<AppState>,
    Query(filter): Query<BountyFilter>,
) -> impl IntoResponse {
    let bounties = state.board.list_bounties(&filter).await;
    Json(json!({
        "bounties": bounties,
        "count": bounties.len()
    }))
}

async fn claim_bounty(
    State(state): State<AppState>,
    Path(id): Path<String>,
    Json(req): Json<ClaimRequest>,
) -> impl IntoResponse {
    let bounty_id = match bounty_id_from_hex(&id) {
        Some(bytes) => bytes,
        None => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "invalid bounty ID"})),
            );
        }
    };

    let bounty = match state.board.get_bounty(&bounty_id).await {
        Some(b) => b,
        None => {
            return (
                StatusCode::NOT_FOUND,
                Json(json!({"error": "bounty not found"})),
            );
        }
    };

    if !matches!(bounty.status, BountyStatus::Open) {
        return (
            StatusCode::CONFLICT,
            Json(json!({"error": "bounty is not open for claims"})),
        );
    }

    let current_height = state.board.current_height().await;
    if bounty.deadline_height <= current_height {
        return (
            StatusCode::GONE,
            Json(json!({"error": "bounty has expired"})),
        );
    }

    let proof_bytes = req.qualification_proof.as_deref().unwrap_or(&[]);
    let engine = state.engine.lock().await;
    let root_history = state.root_history.read().await;
    match verify_qualification(&engine, &bounty.qualification, proof_bytes, &*root_history) {
        Ok(true) => {}
        Ok(false) => {
            return (
                StatusCode::FORBIDDEN,
                Json(json!({"error": "qualification proof does not meet threshold"})),
            );
        }
        Err(e) => {
            warn!(bounty_id = %id, error = %e, "qualification verification failed");
            return (
                StatusCode::FORBIDDEN,
                Json(json!({"error": format!("qualification rejected: {e}")})),
            );
        }
    }

    let new_status = BountyStatus::Claimed {
        worker_commitment: req.worker_commitment,
        claimed_at: current_height,
    };
    state.board.update_status(&bounty_id, new_status).await;

    info!(bounty_id = %id, "bounty claimed");

    (
        StatusCode::OK,
        Json(json!({
            "status": "claimed",
            "bounty_id": id
        })),
    )
}

async fn submit_work(
    State(state): State<AppState>,
    Path(id): Path<String>,
    Json(req): Json<SubmitRequest>,
) -> impl IntoResponse {
    let bounty_id = match bounty_id_from_hex(&id) {
        Some(bytes) => bytes,
        None => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "invalid bounty ID"})),
            );
        }
    };

    let bounty = match state.board.get_bounty(&bounty_id).await {
        Some(b) => b,
        None => {
            return (
                StatusCode::NOT_FOUND,
                Json(json!({"error": "bounty not found"})),
            );
        }
    };

    match &bounty.status {
        BountyStatus::Claimed {
            worker_commitment, ..
        } => {
            if *worker_commitment != req.worker_commitment {
                return (
                    StatusCode::FORBIDDEN,
                    Json(json!({"error": "worker commitment does not match claim"})),
                );
            }
        }
        _ => {
            return (
                StatusCode::CONFLICT,
                Json(json!({"error": "bounty is not in claimed state"})),
            );
        }
    }

    if req.completion_proof.is_empty() {
        return (
            StatusCode::BAD_REQUEST,
            Json(json!({"error": "completion proof must not be empty"})),
        );
    }

    let completion_proof_hash = *blake3::hash(&req.completion_proof).as_bytes();

    let new_status = BountyStatus::Submitted {
        worker_commitment: req.worker_commitment,
        completion_proof_hash,
    };
    state.board.update_status(&bounty_id, new_status).await;

    // REVIEW[P2]: Inbox push fires on every successful submission, including
    // low-quality work that the issuer will reject in `approve_bounty`. For a
    // marketplace UX, defer the issuer notification to the approve/dispute step
    // (or push a typed "pending review" message with quality metadata so issuers
    // can filter). Currently every probe of `/bounties/{id}/submit` adds noise
    // to the inbox even before any work is reviewed.

    // --- Upgrade 2: notify issuer via store-and-forward inbox ---
    // REVIEW[P1]: This is NOT encrypted. `InboxMessage::Encrypted` is a variant tag,
    // not an enforcement primitive — the framework treats `ciphertext: Vec<u8>` as
    // opaque bytes and never encrypts them. Anyone with HTTP access to
    // `/inbox/issuers/next` (which has no auth, see below) can read the bounty_id
    // and completion_proof_hash in plaintext. To honor the "encrypted" claim, the
    // worker (not the server) must encrypt to the issuer's public key client-side,
    // and the server should only forward opaque ciphertext.
    let notification_payload = {
        let mut payload = Vec::with_capacity(64);
        payload.extend_from_slice(&bounty_id);
        payload.extend_from_slice(&completion_proof_hash);
        payload
    };
    let msg = InboxMessage::Encrypted {
        ciphertext: notification_payload,
        sender: req.worker_commitment,
    };
    let mut inbox = state.issuer_inbox.lock().await;
    // Deposit 0: internal server-generated message, no anti-spam deposit needed.
    if let Err(e) = inbox.receive(msg, 0) {
        warn!(bounty_id = %id, error = ?e, "failed to push delivery notification to issuer inbox");
    }
    drop(inbox);

    (
        StatusCode::OK,
        Json(json!({
            "status": "submitted",
            "bounty_id": id,
            "completion_proof_hash": bounty_id_hex(&completion_proof_hash)
        })),
    )
}

async fn approve_bounty(
    State(state): State<AppState>,
    Path(id): Path<String>,
    Json(req): Json<ApproveRequest>,
) -> impl IntoResponse {
    let bounty_id = match bounty_id_from_hex(&id) {
        Some(bytes) => bytes,
        None => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "invalid bounty ID"})),
            );
        }
    };

    let bounty = match state.board.get_bounty(&bounty_id).await {
        Some(b) => b,
        None => {
            return (
                StatusCode::NOT_FOUND,
                Json(json!({"error": "bounty not found"})),
            );
        }
    };

    let issuer_cell_hex = bounty_id_hex(bounty.issuer_cell.as_bytes());
    if req.issuer_cell != issuer_cell_hex {
        return (
            StatusCode::FORBIDDEN,
            Json(json!({"error": "only the issuer can approve"})),
        );
    }

    let worker_commitment = match &bounty.status {
        BountyStatus::Submitted {
            worker_commitment, ..
        } => *worker_commitment,
        _ => {
            return (
                StatusCode::CONFLICT,
                Json(json!({"error": "bounty is not in submitted state"})),
            );
        }
    };

    state
        .board
        .update_status(&bounty_id, BountyStatus::Approved)
        .await;

    state
        .board
        .record_completion(worker_commitment, bounty_id)
        .await;

    let receipt_hash = *blake3::hash(&bounty_id).as_bytes();
    state
        .board
        .update_status(&bounty_id, BountyStatus::Paid { receipt_hash })
        .await;

    (
        StatusCode::OK,
        Json(json!({
            "status": "paid",
            "bounty_id": id,
            "receipt_hash": bounty_id_hex(&receipt_hash)
        })),
    )
}

async fn bounty_status(State(state): State<AppState>, Path(id): Path<String>) -> impl IntoResponse {
    let bounty_id = match bounty_id_from_hex(&id) {
        Some(bytes) => bytes,
        None => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "invalid bounty ID"})),
            )
                .into_response();
        }
    };

    match state.board.get_bounty(&bounty_id).await {
        Some(bounty) => {
            let response = BountyStatusResponse {
                id: bounty_id_hex(&bounty.id),
                title: bounty.title,
                description: bounty.description,
                reward_amount: bounty.reward_amount,
                reward_asset: bounty.reward_asset,
                deadline_height: bounty.deadline_height,
                status: bounty.status,
                tags: bounty.tags,
                qualification: bounty.qualification,
                created_at: bounty.created_at,
            };
            (
                StatusCode::OK,
                Json(serde_json::to_value(&response).unwrap()),
            )
                .into_response()
        }
        None => (
            StatusCode::NOT_FOUND,
            Json(json!({"error": "bounty not found"})),
        )
            .into_response(),
    }
}

async fn worker_bounties(
    State(state): State<AppState>,
    Query(params): Query<WorkerQuery>,
) -> impl IntoResponse {
    let commitment = match bounty_id_from_hex(&params.commitment) {
        Some(bytes) => bytes,
        None => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "invalid worker commitment hex"})),
            )
                .into_response();
        }
    };

    let active = state.board.worker_active_bounties(&commitment).await;
    let completed_count = state.board.worker_completed_count(&commitment).await;
    let completed_ids: Vec<String> = state
        .board
        .worker_bounty_ids(&commitment)
        .await
        .iter()
        .map(bounty_id_hex)
        .collect();

    Json(json!({
        "active": active,
        "completed_count": completed_count,
        "completed_ids": completed_ids
    }))
    .into_response()
}

#[derive(serde::Deserialize)]
struct WorkerQuery {
    commitment: String,
}

// =============================================================================
// Admin Endpoints (protected by framework AdminAuth extractor)
// =============================================================================

async fn advance_height(
    _auth: AdminAuth,
    State(state): State<AppState>,
    Json(body): Json<serde_json::Value>,
) -> impl IntoResponse {
    let delta = body["delta"].as_u64().unwrap_or(1);
    state.board.advance_height(delta).await;
    let new_height = state.board.current_height().await;
    Json(json!({"height": new_height}))
}

async fn expire_bounties(_auth: AdminAuth, State(state): State<AppState>) -> impl IntoResponse {
    let count = state.board.expire_stale_bounties().await;
    Json(json!({"expired": count}))
}

async fn set_federation_root(
    _auth: AdminAuth,
    State(state): State<AppState>,
    Json(body): Json<serde_json::Value>,
) -> impl IntoResponse {
    let root_hex = match body["root"].as_str() {
        Some(s) => s,
        None => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": "missing 'root' field (64 hex chars)"})),
            );
        }
    };

    let root_hex = root_hex.strip_prefix("0x").unwrap_or(root_hex);
    match hex_to_bytes32(root_hex) {
        Ok(root) => {
            if root == [0u8; 32] {
                return (
                    StatusCode::BAD_REQUEST,
                    Json(json!({"error": "refusing to set all-zeroes federation root"})),
                );
            }
            let mut history = state.root_history.write().await;
            history.push(root);
            drop(history);
            *state.root_last_updated.write().await = Some(Instant::now());
            (StatusCode::OK, Json(json!({"root": bytes32_to_hex(&root)})))
        }
        Err(_) => (
            StatusCode::BAD_REQUEST,
            Json(json!({"error": "invalid root hex (expected 64 hex chars)"})),
        ),
    }
}
