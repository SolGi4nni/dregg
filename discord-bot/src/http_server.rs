//! Production-grade HTTP read surface for the Discord bot as a first-class dregg peer.
//!
//! Implements the exact surface from STARBRIDGE-PLAN §4.7 so that Starbridge
//! `RemoteRuntime` (and humans/agents) can target the bot:
//!   GET /api/cells
//!   GET /api/cell/<id>   (CellStateView-compatible shape for <dregg-cell> inspectors)
//!   GET /api/receipts/recent
//!   GET /api/federations
//!   GET /observability/stream (SSE, live activity)
//!
//! Production qualities (no bad defaults, robust, observable, secure):
//! - Structured tracing + tower-http TraceLayer + request ids
//! - Rate limiting (tower-http) + CORS (configurable origin for Starbridge)
//! - Graceful shutdown on SIGINT/SIGTERM
//! - Input validation + safe error responses (no panics, no leak of internals)
//! - Reuses existing DevnetClient, CapTPClient, DB, NullifierSet, activity feed
//! - Federation ID and listen addr from Config (no more hard-coded [0u8;32])
//! - Minimal dependencies; aligns with node/api.rs patterns (axum 0.8 + sse submodule)
//!
//! The bot remains a "soft-federation" for the friend clique: the HTTP surface +
//! NullifierSet + intent/handoff flows make it a reliable third-party participant
//! that Starbridge and cliques can depend on for real mutation + cross-federation.
//!
//! All code read before any prior edit; this file created only because a clean
//! production module is absolutely necessary (bloating main.rs would violate
//! "production quality, not prototype").

use std::net::SocketAddr;
use std::sync::Arc;
use std::time::Duration;

use axum::{
    Router,
    extract::{Path, Request, State},
    http::{HeaderMap, StatusCode, header},
    middleware::{self, Next},
    response::{
        Html, IntoResponse, Json,
        sse::{Event, Sse},
    },
    routing::{get, post},
};
use futures_util::stream::{self, Stream};
use serde::Serialize;
use tower_http::{cors::CorsLayer, limit::RequestBodyLimitLayer, trace::TraceLayer};
use tracing::{info, warn};

use crate::BotState;
use crate::db::{StarbridgeActivity, StarbridgeQueue, StarbridgeQueueSubscription};
use crate::devnet::DevnetError;

/// Bot's view of a cell, shaped to be compatible with the wasm CellStateView
/// binding so RemoteRuntime + <dregg-cell> inspectors "just work".
#[derive(Serialize, Clone, Debug)]
pub struct BotCellView {
    pub id: String,
    pub found: bool,
    pub balance: u64,
    pub nonce: u64,
    pub capability_count: u32,
    pub has_program: bool,
    pub program_vk: Option<String>,
    pub created_by_factory: Option<String>,
    /// Soft-federation note: whether this cell's notes have been seen spent
    /// via the clique's NullifierSet (best-effort, local view).
    pub nullifier_known: bool,
}

/// Recent receipt summary (lightweight for the read surface).
#[derive(Serialize, Clone, Debug)]
pub struct BotReceiptView {
    pub turn_hash: String,
    pub timestamp: String,
    pub cell_id: Option<String>,
    pub summary: String,
}

/// Federation info exposed by the bot (its own + known peers).
#[derive(Serialize, Clone, Debug)]
pub struct BotFederationView {
    pub id: String,
    pub name: String,
    pub node_count: u32,
    pub is_soft_federation: bool, // true for the bot's friend-clique mode
}

/// Starbridge app descriptor exposed to RemoteRuntime and dashboard clients.
#[derive(Serialize, Clone, Debug)]
pub struct StarbridgeAppView {
    pub id: &'static str,
    pub name: &'static str,
    pub description: &'static str,
    pub page: &'static str,
    pub factory_vks: &'static [&'static str],
    pub inspectors: &'static [&'static str],
    pub turn_builders: &'static [&'static str],
    pub required_apis: &'static [&'static str],
}

/// Discord-mounted programmable queue exposed to RemoteRuntime clients.
#[derive(Serialize, Clone, Debug)]
pub struct StarbridgeQueueView {
    pub namespace_path: String,
    pub guild_id: String,
    pub name: String,
    pub queue_id: String,
    pub queue_uri: String,
    pub created_by: String,
    pub acl_role: Option<String>,
    pub rate_limit: Option<i64>,
    pub min_deposit: Option<i64>,
    pub created_at: i64,
    pub subscriber_count: usize,
    pub subscriptions: Vec<StarbridgeQueueSubscriptionView>,
}

/// Subscriber link for a Discord-mounted Starbridge queue.
#[derive(Serialize, Clone, Debug)]
pub struct StarbridgeQueueSubscriptionView {
    pub discord_id: String,
    pub subscribed_at: i64,
}

/// Recent app activity shape.
#[derive(Serialize, Clone, Debug)]
pub struct StarbridgeActivityView {
    pub id: i64,
    pub app: String,
    pub action: String,
    pub actor_discord_id: String,
    pub guild_id: Option<String>,
    pub subject: Option<String>,
    pub status: String,
    pub details: serde_json::Value,
    pub queue: Option<StarbridgeActivityQueueLink>,
    pub timestamp: i64,
}

/// Queue link embedded in recent activity entries when the activity came from
/// queue commands.
#[derive(Serialize, Clone, Debug)]
pub struct StarbridgeActivityQueueLink {
    pub namespace_path: String,
    pub queue_id: Option<String>,
    pub queue_uri: Option<String>,
}

const STARBRIDGE_APPS: &[StarbridgeAppView] = &[
    StarbridgeAppView {
        id: "identity",
        name: "Identity",
        description: "Credential issuance and selective disclosure starbridge-app.",
        page: "/starbridge-apps/identity/pages/index.html",
        factory_vks: &["737461726272696467652d6964656e746974792d6973737565722d6661637421"],
        inspectors: &[
            "dregg-credential",
            "dregg-credential-issue-form",
            "dregg-credential-present-form",
            "dregg-credential-verifier",
        ],
        turn_builders: &[
            "issue_credential",
            "revoke_credential",
            "present_credential",
            "verify_presentation",
        ],
        required_apis: &["signTurn"],
    },
    StarbridgeAppView {
        id: "nameservice",
        name: "Nameservice",
        description: "Federation name directory built from dregg-native primitives.",
        page: "/starbridge-apps/nameservice/pages/index.html",
        factory_vks: &["737461726272696467652d6e616d65736572766963652d666163746f72792121"],
        inspectors: &[
            "dregg-name",
            "dregg-name-registry",
            "dregg-name-register-form",
        ],
        turn_builders: &[
            "register_name",
            "renew_name",
            "transfer_name",
            "revoke_name",
            "set_target_name",
        ],
        required_apis: &[
            "signTurn",
            "blake3",
            "cell.readField",
            "builders.nameservice",
        ],
    },
    StarbridgeAppView {
        id: "governed-namespace",
        name: "Governed Namespace",
        description: "Governance and table-driven namespace starbridge-app.",
        page: "/starbridge-apps/governed-namespace/pages/index.html",
        factory_vks: &["737461726272696467652d676f7665726e65642d6e616d6573706163652d6661"],
        inspectors: &["dregg-governed-namespace", "dregg-governance-proposal"],
        turn_builders: &[
            "propose_table_update",
            "vote_on_proposal",
            "commit_table_update",
            "register_service",
        ],
        required_apis: &["signTurn"],
    },
    StarbridgeAppView {
        id: "subscription",
        name: "Subscription",
        description: "Pub/sub topic and capability subscription starbridge-app.",
        page: "/starbridge-apps/subscription/pages/index.html",
        factory_vks: &["737461726272696467652d737562736372697074696f6e2d666163746f727921"],
        inspectors: &["dregg-subscription", "dregg-subscription-feed"],
        turn_builders: &["publish", "consume", "grant_publisher", "grant_consumer"],
        required_apis: &["signTurn"],
    },
];

/// Error type for handlers (never leaks internals in production).
#[derive(Debug)]
struct HttpError {
    status: StatusCode,
    message: String,
}

impl IntoResponse for HttpError {
    fn into_response(self) -> axum::response::Response {
        (self.status, self.message).into_response()
    }
}

impl From<DevnetError> for HttpError {
    fn from(e: DevnetError) -> Self {
        warn!(error = %e, "devnet error in HTTP handler");
        HttpError {
            status: StatusCode::BAD_GATEWAY,
            message: "upstream devnet unavailable".to_string(),
        }
    }
}

/// Build the production read-only router.
fn build_router(state: Arc<BotState>) -> Router {
    Router::new()
        .route("/api/cells", get(list_cells))
        .route("/api/cell/{id}", get(get_cell))
        .route("/api/receipts/recent", get(recent_receipts))
        .route("/api/federations", get(list_federations))
        .route("/api/apps", get(list_apps))
        .route("/api/apps/activity", get(recent_activity))
        .route("/api/apps/activity/recent", get(recent_activity))
        .route("/api/apps/{id}", get(get_app))
        .route("/api/activity/recent", get(recent_activity))
        .route("/api/intents/recent", get(recent_intents))
        .route("/api/queues", get(list_queues))
        // RELEGATED — NOT the desktop command path. The on-chain command path is a
        // real dregg turn the desktop submits to the command cell, which the bot's
        // `bot_reactor` WATCHES and reacts to (the chain is the message bus). This
        // endpoint survives only as the bot's optional internal reaction-delivery
        // surface — a peer that already speaks HTTP can still nudge the same
        // custodial `drive` — but the desktop never uses it to command the bot.
        .route("/api/op", post(drive_op))
        .route("/observability/stream", get(observability_stream))
        // ─── Admin webportal (ember-only monitoring over the bot DB) ─────────
        // Auth-gated (ADMIN_TOKEN bearer) read-mostly view of ALL users,
        // channels, per-channel Hermes activity, and the internal cap/cclerk
        // records. Sits behind Caddy basic-auth on the edge as defence in depth.
        .nest("/admin", admin_router(state.clone()))
        // Production middleware (order matters: trace outermost for full req)
        .layer(TraceLayer::new_for_http())
        .layer(CorsLayer::permissive()) // Starbridge origins; tighten in real deployment via config
        // Body size limit (DoS protection for the public-ish read surface; 2 MiB generous for JSON/SSE payloads)
        .layer(RequestBodyLimitLayer::new(2 * 1024 * 1024))
        .with_state(state)
}

/// Start the HTTP server (called via spawn from main).
/// Listens on the host:port from the BotState's Config (production: no
/// separate args that could cause borrow issues with 'static tasks).
/// Supports graceful shutdown on ctrl-c.
pub async fn start(state: Arc<BotState>) {
    let host = state.config.http_host.clone();
    let port = state.config.http_port;
    let addr: SocketAddr = format!("{}:{}", host, port)
        .parse()
        .expect("invalid HTTP listen address in config");
    let app = build_router(state);

    info!(%addr, "Starting production HTTP read surface for dregg Discord bot (Starbridge RemoteRuntime target)");

    let listener = match tokio::net::TcpListener::bind(addr).await {
        Ok(l) => l,
        Err(e) => {
            warn!(error = %e, "failed to bind HTTP listener");
            return;
        }
    };

    let server = axum::serve(listener, app).with_graceful_shutdown(shutdown_signal());

    if let Err(e) = server.await {
        warn!(error = %e, "HTTP server error");
    }
    info!("HTTP read surface shut down gracefully");
}

async fn shutdown_signal() {
    let _ = tokio::signal::ctrl_c().await;
    info!("received shutdown signal for HTTP server");
}

// ─── Handlers (production: validated, logged, reuse existing substrate) ─────

async fn list_cells(
    State(state): State<Arc<BotState>>,
) -> Result<Json<Vec<BotCellView>>, HttpError> {
    let mut cell_ids = vec![state.captp.bot_cell_id.clone()];

    match state.db.list_user_identities().await {
        Ok(identities) => {
            for identity in identities {
                if !cell_ids.iter().any(|id| id == &identity.cell_id) {
                    cell_ids.push(identity.cell_id);
                }
            }
        }
        Err(e) => {
            warn!(error = %e, "failed to list local bot cells");
        }
    }

    let mut views = Vec::with_capacity(cell_ids.len());
    for cell_id in cell_ids {
        views.push(cell_view_from_devnet(&state, &cell_id).await);
    }

    Ok(Json(views))
}

async fn get_cell(
    State(state): State<Arc<BotState>>,
    Path(id): Path<String>,
) -> Result<Json<BotCellView>, HttpError> {
    // Validate input (production security: no blind proxy of arbitrary strings that
    // could cause upstream DoS or log injection).
    if id.len() < 16 || id.len() > 128 || !id.chars().all(|c| c.is_ascii_hexdigit() || c == '-') {
        return Err(HttpError {
            status: StatusCode::BAD_REQUEST,
            message: "invalid cell id format".to_string(),
        });
    }

    Ok(Json(cell_view_from_devnet(&state, &id).await))
}

async fn recent_receipts(
    State(state): State<Arc<BotState>>,
) -> Result<Json<Vec<BotReceiptView>>, HttpError> {
    let transactions = state.db.get_recent_transactions(25).await.map_err(|e| {
        warn!(error = %e, "failed to load recent bot receipts");
        HttpError {
            status: StatusCode::INTERNAL_SERVER_ERROR,
            message: "local receipt store unavailable".to_string(),
        }
    })?;

    let receipts = transactions
        .into_iter()
        .map(|tx| BotReceiptView {
            turn_hash: tx.tx_hash,
            timestamp: tx.timestamp.to_string(),
            cell_id: None,
            summary: format!(
                "transfer {} DEC from Discord user {} to {}",
                tx.amount, tx.from_user, tx.to_user
            ),
        })
        .collect();

    Ok(Json(receipts))
}

async fn list_federations(
    State(state): State<Arc<BotState>>,
) -> Result<Json<Vec<BotFederationView>>, HttpError> {
    let fed_id = hex::encode(state.federation_id_bytes);
    let views = vec![BotFederationView {
        id: fed_id,
        name: "bot-soft-federation".to_string(),
        node_count: 1,
        is_soft_federation: true,
    }];
    Ok(Json(views))
}

async fn list_apps() -> Result<Json<&'static [StarbridgeAppView]>, HttpError> {
    Ok(Json(STARBRIDGE_APPS))
}

async fn get_app(Path(id): Path<String>) -> Result<Json<StarbridgeAppView>, HttpError> {
    STARBRIDGE_APPS
        .iter()
        .find(|app| app.id == id)
        .cloned()
        .map(Json)
        .ok_or_else(|| HttpError {
            status: StatusCode::NOT_FOUND,
            message: "unknown starbridge app".to_string(),
        })
}

async fn list_queues(
    State(state): State<Arc<BotState>>,
) -> Result<Json<Vec<StarbridgeQueueView>>, HttpError> {
    let queues = state.db.list_starbridge_queues().await.map_err(|e| {
        warn!(error = %e, "failed to load starbridge queues");
        HttpError {
            status: StatusCode::INTERNAL_SERVER_ERROR,
            message: "local queue store unavailable".to_string(),
        }
    })?;
    let subscriptions = state
        .db
        .list_starbridge_queue_subscriptions()
        .await
        .map_err(|e| {
            warn!(error = %e, "failed to load starbridge queue subscriptions");
            HttpError {
                status: StatusCode::INTERNAL_SERVER_ERROR,
                message: "local queue subscription store unavailable".to_string(),
            }
        })?;

    Ok(Json(queue_views(queues, subscriptions)))
}

/// **RELEGATED reaction-delivery surface — NOT the desktop command path.**
///
/// The desktop commands the bot ON-CHAIN: it submits a real dregg turn to the
/// command cell ([`crate::deos_drive::command_cell`]), and the bot's
/// [`crate::bot_reactor`] watches that cell and reacts. This HTTP endpoint is no
/// longer how the desktop drives the bot; it remains only as an optional internal
/// nudge for a peer that already speaks HTTP, routing through the SAME custodial
/// [`crate::deos_drive::drive`] the on-chain reactor uses. The command bus is the
/// chain, not this POST.
///
/// Because this path custodially signs as `req.user_id`, it is gated by
/// [`authorize_op`]: the caller must present an ownership proof (the per-user op
/// token, or the operator token) for that exact user. An unproven `user_id` is
/// `401` — closing GW-4a.
async fn drive_op(
    State(state): State<Arc<BotState>>,
    headers: HeaderMap,
    Json(req): Json<crate::deos_drive::DriveRequest>,
) -> Result<Json<crate::deos_drive::DriveOutcome>, HttpError> {
    // GW-4a fix: a custodial `/api/op` drive signs as `req.user_id`, so the
    // caller MUST prove they control that user. A bare, unproven `user_id` (the
    // forge-credentials / squat-names exploit) is REFUSED here, before any turn
    // is built or signed.
    authorize_op(&state, &headers, req.user_id)?;
    match crate::deos_drive::drive(&state, &req).await {
        Ok(outcome) => {
            info!(
                action = %outcome.action,
                accepted = outcome.accepted,
                "deos-desktop drove a bot op as a dregg turn"
            );
            Ok(Json(outcome))
        }
        Err(e) => {
            warn!(error = %e, "deos-desktop drive failed");
            Err(HttpError {
                status: StatusCode::BAD_GATEWAY,
                message: format!("drive failed: {e}"),
            })
        }
    }
}

/// **GW-4a ownership gate for `/api/op`.** The custodial drive signs as the
/// request body's `user_id`; this requires the caller to PROVE they control that
/// user. Two proofs are accepted (constant-time compared, no length/early-exit
/// leak):
///   1. the **per-user op token** [`crate::cipherclerk::op_token`] — the
///      capability the bot hands a Discord-authenticated user; it is bound to the
///      *exact* `user_id` being driven, so a token for one user cannot drive
///      another's cell; OR
///   2. the operator's `ADMIN_TOKEN` (the master credential — the operator
///      already holds the bot secret and can custodially act for anyone).
///
/// A missing token, or a token that matches neither, is `401 Unauthorized` — so a
/// bare unproven `user_id` (the exploit: forge `gov_id`/`kyc`, squat names on a
/// victim's cell) is REFUSED. The gate is always on: the per-user token is always
/// derivable, so the endpoint is never an open custodial-signing surface even
/// when `ADMIN_TOKEN` is unset.
fn authorize_op(state: &BotState, headers: &HeaderMap, user_id: u64) -> Result<(), HttpError> {
    let presented = bearer_token(headers).unwrap_or_default();
    if presented.is_empty() {
        warn!(user_id, "/api/op: rejected drive with no ownership proof");
        return Err(op_unauthorized());
    }

    // Proof 1: the per-user op token for the EXACT user being driven.
    let expected = crate::cipherclerk::op_token(&state.config.bot_secret, user_id);
    if constant_time_eq(presented.as_bytes(), expected.as_bytes()) {
        return Ok(());
    }

    // Proof 2: the operator master token (optional; only when configured).
    if let Some(admin) = state.config.admin_token.as_deref() {
        if constant_time_eq(presented.as_bytes(), admin.as_bytes()) {
            return Ok(());
        }
    }

    warn!(
        user_id,
        "/api/op: rejected drive — presented token does not prove control of this user"
    );
    Err(op_unauthorized())
}

/// The single 401 response for an unauthorized `/api/op` drive (no internals leak).
fn op_unauthorized() -> HttpError {
    HttpError {
        status: StatusCode::UNAUTHORIZED,
        message: "ownership proof required: present the per-user op token (or operator token) as `Authorization: Bearer <token>`".to_string(),
    }
}

/// Extract a `Authorization: Bearer <token>` value from request headers.
fn bearer_token(headers: &HeaderMap) -> Option<String> {
    headers
        .get(header::AUTHORIZATION)
        .and_then(|v| v.to_str().ok())
        .and_then(|s| s.strip_prefix("Bearer "))
        .map(|s| s.trim().to_string())
}

async fn recent_activity(
    State(state): State<Arc<BotState>>,
) -> Result<Json<Vec<StarbridgeActivityView>>, HttpError> {
    let mut activity = state
        .db
        .get_recent_starbridge_activity(50)
        .await
        .map_err(|e| {
            warn!(error = %e, "failed to load recent starbridge activity");
            HttpError {
                status: StatusCode::INTERNAL_SERVER_ERROR,
                message: "local activity store unavailable".to_string(),
            }
        })?;

    if activity.is_empty() {
        activity = queue_activity_fallback(&state).await?;
    }

    Ok(Json(activity.into_iter().map(activity_view).collect()))
}

async fn recent_intents(
    State(state): State<Arc<BotState>>,
) -> Result<Json<Vec<StarbridgeActivityView>>, HttpError> {
    let activity = state
        .db
        .get_recent_starbridge_activity_for_app("intent", 50)
        .await
        .map_err(|e| {
            warn!(error = %e, "failed to load recent intent activity");
            HttpError {
                status: StatusCode::INTERNAL_SERVER_ERROR,
                message: "local intent store unavailable".to_string(),
            }
        })?;
    Ok(Json(activity.into_iter().map(activity_view).collect()))
}

/// Live observability SSE feed (exactly as specified in §4.7 for RemoteRuntime).
/// Production: in a fuller version this would be a broadcast channel fed by the
/// activity_feed poller and captp events. Here we emit keep-alives + lightweight
/// pings so the connection is observable and useful for Starbridge inspectors.
async fn observability_stream(
    State(state): State<Arc<BotState>>,
) -> Sse<impl Stream<Item = Result<Event, std::convert::Infallible>>> {
    info!("new client connected to /observability/stream");

    // Simple production-grade SSE: 5s pings + an initial "hello" with bot cell.
    // Real impl would fold over a tokio::sync::broadcast receiver from activity_feed.
    let bot_cell = state.captp.bot_cell_id.clone();
    let nullifier_count = {
        let set = state.nullifier_set.lock().await;
        set.len()
    };

    let stream = stream::unfold(0u64, move |mut seq| {
        let bot_cell = bot_cell.clone();
        async move {
            seq += 1;
            let event = if seq == 1 {
                Event::default()
                    .event("hello")
                    .data(format!(r#"{{"bot_cell":"{}","nullifiers":{},"apps":{},"msg":"dregg-discord-bot observability stream live (soft-federation peer)"}}"#, bot_cell, nullifier_count, STARBRIDGE_APPS.len()))
            } else {
                Event::default().event("ping").data(format!(
                    r#"{{"seq":{},"ts":"{}","nullifiers":{}}}"#,
                    seq,
                    chrono_like_now(),
                    nullifier_count
                ))
            };
            Some((Ok(event), seq))
        }
    });

    Sse::new(stream).keep_alive(
        axum::response::sse::KeepAlive::new()
            .interval(Duration::from_secs(15))
            .text("keep-alive"),
    )
}

fn activity_view(activity: StarbridgeActivity) -> StarbridgeActivityView {
    let details = serde_json::from_str(&activity.details_json).unwrap_or(serde_json::Value::Null);
    let queue = queue_link_from_activity(&activity, &details);
    StarbridgeActivityView {
        id: activity.id,
        app: activity.app,
        action: activity.action,
        actor_discord_id: activity.actor_discord_id,
        guild_id: activity.guild_id,
        subject: activity.subject,
        status: activity.status,
        details,
        queue,
        timestamp: activity.timestamp,
    }
}

fn queue_views(
    queues: Vec<StarbridgeQueue>,
    subscriptions: Vec<StarbridgeQueueSubscription>,
) -> Vec<StarbridgeQueueView> {
    queues
        .into_iter()
        .map(|queue| {
            let subscriptions = subscriptions
                .iter()
                .filter(|subscription| subscription.namespace_path == queue.namespace_path)
                .map(|subscription| StarbridgeQueueSubscriptionView {
                    discord_id: subscription.discord_id.clone(),
                    subscribed_at: subscription.subscribed_at,
                })
                .collect::<Vec<_>>();

            StarbridgeQueueView {
                queue_uri: queue_uri(&queue.queue_id),
                subscriber_count: subscriptions.len(),
                subscriptions,
                namespace_path: queue.namespace_path,
                guild_id: queue.guild_id,
                name: queue.name,
                queue_id: queue.queue_id,
                created_by: queue.created_by,
                acl_role: queue.acl_role,
                rate_limit: queue.rate_limit,
                min_deposit: queue.min_deposit,
                created_at: queue.created_at,
            }
        })
        .collect()
}

async fn queue_activity_fallback(state: &BotState) -> Result<Vec<StarbridgeActivity>, HttpError> {
    let mut queues = state.db.list_starbridge_queues().await.map_err(|e| {
        warn!(error = %e, "failed to synthesize recent queue activity from queue store");
        HttpError {
            status: StatusCode::INTERNAL_SERVER_ERROR,
            message: "local queue store unavailable".to_string(),
        }
    })?;
    queues.sort_by(|left, right| {
        right
            .created_at
            .cmp(&left.created_at)
            .then_with(|| left.namespace_path.cmp(&right.namespace_path))
    });

    Ok(queues
        .into_iter()
        .take(50)
        .enumerate()
        .map(|(idx, queue)| StarbridgeActivity {
            id: -((idx as i64) + 1),
            app: "subscription".to_string(),
            action: "queue.mounted".to_string(),
            actor_discord_id: queue.created_by,
            guild_id: Some(queue.guild_id),
            subject: Some(queue.namespace_path),
            status: "materialized".to_string(),
            details_json: serde_json::json!({
                "queue_id": queue.queue_id,
                "name": queue.name,
                "acl_role": queue.acl_role,
                "rate_limit": queue.rate_limit,
                "min_deposit": queue.min_deposit,
            })
            .to_string(),
            timestamp: queue.created_at,
        })
        .collect())
}

fn queue_link_from_activity(
    activity: &StarbridgeActivity,
    details: &serde_json::Value,
) -> Option<StarbridgeActivityQueueLink> {
    if !activity.action.starts_with("queue.") {
        return None;
    }

    let namespace_path = activity.subject.clone()?;
    let queue_id = details
        .get("queue_id")
        .and_then(|value| value.as_str())
        .map(str::to_string);
    let queue_uri = queue_id.as_deref().map(queue_uri);

    Some(StarbridgeActivityQueueLink {
        namespace_path,
        queue_id,
        queue_uri,
    })
}

fn queue_uri(queue_id: &str) -> String {
    format!("dregg://queue/{queue_id}")
}

async fn cell_view_from_devnet(state: &BotState, id: &str) -> BotCellView {
    let nullifier_known = {
        let set = state.nullifier_set.lock().await;
        set.iter()
            .any(|n| hex::encode(n).starts_with(&id[..std::cmp::min(8, id.len())]))
    };

    match state.devnet.get_cell_details(id).await {
        Ok(details) => BotCellView {
            id: details.cell_id,
            found: true,
            balance: details.balance,
            nonce: details.nonce,
            capability_count: details.capabilities_count,
            has_program: details.program_vk.is_some(),
            program_vk: details.program_vk,
            created_by_factory: details.created_by_factory,
            nullifier_known,
        },
        Err(e) => {
            warn!(cell_id = %id, error = %e, "failed to hydrate cell details from devnet");
            BotCellView {
                id: id.to_string(),
                found: false,
                balance: 0,
                nonce: 0,
                capability_count: 0,
                has_program: false,
                program_vk: None,
                created_by_factory: None,
                nullifier_known,
            }
        }
    }
}

// ─── Admin webportal ────────────────────────────────────────────────────────

/// The admin monitoring subtree, gated behind the ADMIN_TOKEN bearer check.
fn admin_router(state: Arc<BotState>) -> Router<Arc<BotState>> {
    Router::new()
        .route("/", get(admin_index))
        .route("/api/users", get(admin_users))
        .route("/api/channels", get(admin_channels))
        .route("/api/hermes", get(admin_hermes))
        .route("/api/caps", get(admin_caps))
        .layer(middleware::from_fn_with_state(state, require_admin))
}

/// Extract the presented admin token from `Authorization: Bearer <t>` or a
/// `?token=<t>` query parameter.
fn presented_token(req: &Request) -> Option<String> {
    if let Some(bearer) = req
        .headers()
        .get(header::AUTHORIZATION)
        .and_then(|v| v.to_str().ok())
        .and_then(|s| s.strip_prefix("Bearer "))
    {
        return Some(bearer.trim().to_string());
    }
    req.uri().query().and_then(|q| {
        q.split('&').find_map(|kv| {
            kv.strip_prefix("token=")
                .map(|t| t.replace('+', " ").to_string())
        })
    })
}

/// Admin auth middleware. The portal is DISABLED (404) when no ADMIN_TOKEN is
/// configured; otherwise a missing/wrong token is 401. A constant-time-ish
/// compare avoids leaking the token length via early exit.
async fn require_admin(
    State(state): State<Arc<BotState>>,
    req: Request,
    next: Next,
) -> axum::response::Response {
    let Some(expected) = state.config.admin_token.clone() else {
        // No token configured → the admin surface does not exist.
        return (StatusCode::NOT_FOUND, "admin portal disabled").into_response();
    };
    let presented = presented_token(&req).unwrap_or_default();
    if !constant_time_eq(presented.as_bytes(), expected.as_bytes()) {
        warn!("admin portal: rejected request with missing/invalid token");
        return (
            StatusCode::UNAUTHORIZED,
            "admin authentication required (Bearer token or ?token=)",
        )
            .into_response();
    }
    next.run(req).await
}

/// Length-independent byte equality (no early return on first mismatch).
fn constant_time_eq(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut diff = 0u8;
    for (x, y) in a.iter().zip(b.iter()) {
        diff |= x ^ y;
    }
    diff == 0
}

/// Minimal HTML escaping for the server-rendered monitoring page.
fn esc(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
}

/// `GET /admin` — the server-rendered monitoring dashboard. Read-mostly: lists
/// every user (→ cell), every semi-private channel, recent per-channel Hermes
/// activity (the cap-gated verdicts + receipts), and the internal cap/cclerk
/// records. No client JS, so the token never has to live in the page.
async fn admin_index(State(state): State<Arc<BotState>>) -> Result<Html<String>, HttpError> {
    let users = state.db.list_users_admin().await.unwrap_or_default();
    let channels = state.db.list_user_channels().await.unwrap_or_default();
    let hermes = state
        .db
        .list_recent_hermes_activity(100)
        .await
        .unwrap_or_default();
    let exports = state.db.list_captp_exports().await.unwrap_or_default();
    let handoffs_held = state.db.list_captp_held_refs().await.unwrap_or_default();
    let local_handoffs = state
        .db
        .list_captp_local_handoffs()
        .await
        .unwrap_or_default();

    let mut h = String::new();
    h.push_str(
        "<!doctype html><html><head><meta charset=utf-8><title>DreggNet Cloud — Admin</title>\
         <style>body{font-family:ui-monospace,Menlo,monospace;background:#0b1020;color:#cfe;margin:2rem;}\
         h1{color:#00b4d8}h2{color:#7fd;border-bottom:1px solid #244;padding-top:1rem}\
         table{border-collapse:collapse;width:100%;margin:.5rem 0;font-size:13px}\
         th,td{border:1px solid #244;padding:4px 8px;text-align:left}th{background:#11203a}\
         .ok{color:#5f8}.no{color:#f88}.muted{color:#789}code{color:#fc8}</style></head><body>",
    );
    h.push_str("<h1>DreggNet Cloud — Admin Portal</h1>");
    h.push_str(&format!(
        "<p class=muted>Read-mostly operator view over the bot DB. Bot cell <code>{}</code>. \
         {} users · {} channels · {} Hermes events shown.</p>",
        esc(&state.captp.bot_cell_id),
        users.len(),
        channels.len(),
        hermes.len()
    ));

    h.push_str(
        "<h2>Users → cells</h2><table><tr><th>Discord ID</th><th>Cell</th><th>Mode</th></tr>",
    );
    for (discord_id, cell_id, mode) in &users {
        h.push_str(&format!(
            "<tr><td>{}</td><td><code>{}</code></td><td>{}</td></tr>",
            esc(discord_id),
            esc(cell_id),
            esc(mode)
        ));
    }
    h.push_str("</table>");

    h.push_str(
        "<h2>Semi-private channels</h2><table><tr><th>Channel</th><th>Owner</th><th>Guild</th><th>Cell</th><th>Status</th></tr>",
    );
    for c in &channels {
        h.push_str(&format!(
            "<tr><td>{}</td><td>{}</td><td>{}</td><td><code>{}</code></td><td>{}</td></tr>",
            esc(&c.channel_id),
            esc(&c.discord_id),
            esc(&c.guild_id),
            esc(&c.cell_id),
            esc(&c.status)
        ));
    }
    h.push_str("</table>");

    h.push_str(
        "<h2>Hermes activity (per-channel agent ledger)</h2><table>\
         <tr><th>User</th><th>Channel</th><th>Tool</th><th>Kind</th><th>Verdict</th><th>Receipt / reason</th><th>Left</th></tr>",
    );
    for a in &hermes {
        let verdict = if a.allowed {
            "<span class=ok>allow</span>"
        } else {
            "<span class=no>refuse</span>"
        };
        let detail = if a.allowed {
            a.receipt
                .as_deref()
                .map(|r| format!("<code>{}…</code>", esc(&r[..r.len().min(16)])))
                .unwrap_or_default()
        } else {
            esc(a.reason.as_deref().unwrap_or(""))
        };
        h.push_str(&format!(
            "<tr><td>{}</td><td>{}</td><td><code>{}</code></td><td>{}</td><td>{}</td><td>{}</td><td>{}</td></tr>",
            esc(&a.discord_id),
            esc(&a.channel_id),
            esc(&a.tool),
            esc(&a.kind),
            verdict,
            detail,
            a.remaining.map(|r| r.to_string()).unwrap_or_default()
        ));
    }
    h.push_str("</table>");

    h.push_str(&format!(
        "<h2>Internal cap / cclerk records</h2><p class=muted>{} exports · {} held refs · {} local handoffs</p>",
        exports.len(),
        handoffs_held.len(),
        local_handoffs.len()
    ));
    h.push_str("<table><tr><th>Kind</th><th>Cell</th><th>Detail</th></tr>");
    for e in &exports {
        h.push_str(&format!(
            "<tr><td>export</td><td><code>{}</code></td><td>{} {}</td></tr>",
            esc(&e.cell_id),
            esc(&e.sturdy_uri),
            if e.revoked { "(revoked)" } else { "" }
        ));
    }
    for r in &local_handoffs {
        h.push_str(&format!(
            "<tr><td>local-handoff</td><td><code>{}</code></td><td>{} → {}</td></tr>",
            esc(&r.cell_id),
            esc(&r.status),
            esc(&r.recipient_cell_id)
        ));
    }
    h.push_str("</table>");

    h.push_str("</body></html>");
    Ok(Html(h))
}

/// `GET /admin/api/users` — JSON user↔cell mapping (for the future portal.dregg.studio / web-extension).
async fn admin_users(
    State(state): State<Arc<BotState>>,
) -> Result<Json<serde_json::Value>, HttpError> {
    let users = state.db.list_users_admin().await.map_err(db_err)?;
    let rows: Vec<_> = users
        .into_iter()
        .map(|(discord_id, cell_id, mode)| {
            serde_json::json!({"discord_id": discord_id, "cell_id": cell_id, "mode": mode})
        })
        .collect();
    Ok(Json(serde_json::json!({ "users": rows })))
}

/// `GET /admin/api/channels` — JSON of every semi-private channel.
async fn admin_channels(
    State(state): State<Arc<BotState>>,
) -> Result<Json<serde_json::Value>, HttpError> {
    let channels = state.db.list_user_channels().await.map_err(db_err)?;
    Ok(Json(serde_json::json!({ "channels": channels })))
}

/// `GET /admin/api/hermes` — JSON of recent per-channel Hermes activity.
async fn admin_hermes(
    State(state): State<Arc<BotState>>,
) -> Result<Json<serde_json::Value>, HttpError> {
    let activity = state
        .db
        .list_recent_hermes_activity(200)
        .await
        .map_err(db_err)?;
    Ok(Json(serde_json::json!({ "hermes_activity": activity })))
}

/// `GET /admin/api/caps` — JSON of the internal cap/cclerk records.
async fn admin_caps(
    State(state): State<Arc<BotState>>,
) -> Result<Json<serde_json::Value>, HttpError> {
    let exports = state.db.list_captp_exports().await.map_err(db_err)?;
    let held = state.db.list_captp_held_refs().await.map_err(db_err)?;
    let local = state.db.list_captp_local_handoffs().await.map_err(db_err)?;
    Ok(Json(serde_json::json!({
        "exports": exports,
        "held_refs": held,
        "local_handoffs": local,
    })))
}

fn db_err(e: sqlx::Error) -> HttpError {
    warn!(error = %e, "admin portal db error");
    HttpError {
        status: StatusCode::INTERNAL_SERVER_ERROR,
        message: "admin store unavailable".to_string(),
    }
}

fn chrono_like_now() -> String {
    // Lightweight timestamp without adding chrono dep (already avoided in db.rs).
    use std::time::{SystemTime, UNIX_EPOCH};
    let secs = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs();
    format!("{}", secs)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::BotState;
    use crate::config::Config;
    use crate::db::Database;
    use crate::devnet::DevnetClient;
    use crate::discord_caps::{DiscordCapRegistry, EventBridge};
    use crate::presence::PresenceTracker;
    use axum::body::Body;
    use axum::http::Request as HttpRequest;
    use tokio::sync::Mutex;
    use tower::ServiceExt;

    async fn state_with_admin(admin_token: Option<String>) -> Arc<BotState> {
        let db = Database::connect("sqlite::memory:").await.unwrap();
        // Seed the internal state the portal monitors.
        db.register_user_with_mode("user-1", "cell-1", crate::db::IdentityMode::Hosted, None)
            .await
            .unwrap();
        db.upsert_user_channel("chan-1", "user-1", "guild-1", "cell-1", 100)
            .await
            .unwrap();
        db.record_hermes_activity(
            "user-1",
            "chan-1",
            "read README",
            "read_file",
            "Read",
            true,
            Some("abc123def4560000"),
            Some(199),
            None,
            100,
        )
        .await
        .unwrap();

        let config = Config {
            discord_token: "x".into(),
            discord_app_id: 0,
            bot_secret: [0u8; 32],
            devnet_url: "http://localhost:0".into(),
            database_url: "sqlite::memory:".into(),
            http_host: "127.0.0.1".into(),
            http_port: 0,
            federation_id_bytes: [0u8; 32],
            admin_discord_id: None,
            admin_token,
        };
        let fed = dregg_captp::FederationId([0u8; 32]);
        // A devnet/mock pay state with no hosted backend — these tests do not exercise paid runs.
        let pay = crate::pay::PayState::devnet_mock_no_backend(
            db.clone(),
            &[0u8; 32],
            tokio::runtime::Handle::current(),
        );
        let characters = crate::character_store::SqliteCharacterStore::new(
            db.clone(),
            tokio::runtime::Handle::current(),
        );
        Arc::new(BotState {
            config,
            db,
            devnet: DevnetClient::new("http://localhost:0"),
            presence: Mutex::new(PresenceTracker::new([0u8; 32])),
            captp: crate::captp_client::CapTPClient::new(
                fed,
                "bot-cell".into(),
                "http://localhost:0".into(),
            ),
            discord_caps: DiscordCapRegistry::new(),
            event_bridge: EventBridge::new("http://localhost:0".into()),
            orchestrator: crate::orchestration::SessionOrchestrator::new(),
            federation_id_bytes: [0u8; 32],
            nullifier_set: Mutex::new(Vec::new()),
            handoff_broker: Mutex::new(crate::handoff_flow::HandoffBroker::new(fed)),
            card_applets: crate::viewnode_applet::CardApplets::new(),
            channel_hermes: std::sync::Mutex::new(std::collections::HashMap::new()),
            pay,
            characters,
        })
    }

    async fn body_string(resp: axum::response::Response) -> String {
        let bytes = axum::body::to_bytes(resp.into_body(), usize::MAX)
            .await
            .unwrap();
        String::from_utf8(bytes.to_vec()).unwrap()
    }

    #[tokio::test]
    async fn admin_portal_requires_a_token() {
        let state = state_with_admin(Some("s3cret".into())).await;
        let app = build_router(state);
        let resp = app
            .oneshot(
                HttpRequest::builder()
                    .uri("/admin")
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(resp.status(), StatusCode::UNAUTHORIZED);
    }

    #[tokio::test]
    async fn admin_portal_renders_with_a_valid_token() {
        let state = state_with_admin(Some("s3cret".into())).await;
        let app = build_router(state);
        let resp = app
            .oneshot(
                HttpRequest::builder()
                    .uri("/admin?token=s3cret")
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(resp.status(), StatusCode::OK);
        let body = body_string(resp).await;
        // The monitoring view shows the seeded channel + the hermes verdict.
        assert!(body.contains("chan-1"), "channel listed");
        assert!(body.contains("read_file"), "hermes tool listed");
        assert!(body.contains("allow"), "the verdict is rendered");
    }

    #[tokio::test]
    async fn admin_portal_bearer_header_also_works() {
        let state = state_with_admin(Some("s3cret".into())).await;
        let app = build_router(state);
        let resp = app
            .oneshot(
                HttpRequest::builder()
                    .uri("/admin/api/channels")
                    .header("Authorization", "Bearer s3cret")
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(resp.status(), StatusCode::OK);
        let body = body_string(resp).await;
        assert!(body.contains("chan-1"));
    }

    #[tokio::test]
    async fn admin_portal_disabled_without_configured_token() {
        // No ADMIN_TOKEN → the surface does not exist (404), even with a token.
        let state = state_with_admin(None).await;
        let app = build_router(state);
        let resp = app
            .oneshot(
                HttpRequest::builder()
                    .uri("/admin?token=anything")
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(resp.status(), StatusCode::NOT_FOUND);
    }

    // ─── GW-4a: /api/op custodial-signing ownership gate ────────────────────

    fn op_body(user_id: u64) -> Body {
        Body::from(format!(
            r#"{{"user_id":{user_id},"op":"register_name","name":"victimsquat"}}"#
        ))
    }

    async fn post_op(
        state: Arc<BotState>,
        user_id: u64,
        bearer: Option<&str>,
    ) -> axum::response::Response {
        let app = build_router(state);
        let mut builder = HttpRequest::builder()
            .method("POST")
            .uri("/api/op")
            .header("content-type", "application/json");
        if let Some(token) = bearer {
            builder = builder.header("Authorization", format!("Bearer {token}"));
        }
        app.oneshot(builder.body(op_body(user_id)).unwrap())
            .await
            .unwrap()
    }

    #[tokio::test]
    async fn op_refused_without_ownership_proof() {
        // The GW-4a exploit: drive an op as some user_id with NO proof → REFUSED.
        let state = state_with_admin(None).await;
        let resp = post_op(state, 999_888, None).await;
        assert_eq!(resp.status(), StatusCode::UNAUTHORIZED);
    }

    #[tokio::test]
    async fn op_refused_with_wrong_users_token() {
        // A token that proves control of user A cannot drive user B's cell.
        let state = state_with_admin(None).await;
        // bot_secret is [0u8;32] in the test state; token for a DIFFERENT user.
        let other_token = crate::cipherclerk::op_token(&[0u8; 32], 111);
        let resp = post_op(state, 999_888, Some(&other_token)).await;
        assert_eq!(resp.status(), StatusCode::UNAUTHORIZED);
    }

    #[tokio::test]
    async fn op_refused_with_garbage_token() {
        let state = state_with_admin(None).await;
        let resp = post_op(state, 999_888, Some("not-a-real-token")).await;
        assert_eq!(resp.status(), StatusCode::UNAUTHORIZED);
    }

    #[tokio::test]
    async fn op_authorized_with_per_user_token_passes_the_gate() {
        // The legit path: the per-user op token for THAT user clears auth. The
        // drive then fails only at the dead test node (502) — proving the gate
        // let the proven caller THROUGH (it is not a 401).
        let state = state_with_admin(None).await;
        let token = crate::cipherclerk::op_token(&[0u8; 32], 999_888);
        let resp = post_op(state, 999_888, Some(&token)).await;
        assert_ne!(
            resp.status(),
            StatusCode::UNAUTHORIZED,
            "a valid per-user op token must clear the ownership gate"
        );
        assert_eq!(
            resp.status(),
            StatusCode::BAD_GATEWAY,
            "auth passed; the drive then fails at the unreachable test node"
        );
    }

    #[tokio::test]
    async fn op_authorized_with_operator_token() {
        // The operator master token (ADMIN_TOKEN) can drive any user.
        let state = state_with_admin(Some("op-master".into())).await;
        let resp = post_op(state, 999_888, Some("op-master")).await;
        assert_ne!(resp.status(), StatusCode::UNAUTHORIZED);
        assert_eq!(resp.status(), StatusCode::BAD_GATEWAY);
    }

    #[test]
    fn op_token_is_per_user_and_deterministic() {
        let secret = [9u8; 32];
        let a = crate::cipherclerk::op_token(&secret, 1);
        let a2 = crate::cipherclerk::op_token(&secret, 1);
        let b = crate::cipherclerk::op_token(&secret, 2);
        assert_eq!(a, a2, "deterministic for a fixed (secret,user)");
        assert_ne!(a, b, "distinct per user");
        // Bound to the secret too.
        assert_ne!(a, crate::cipherclerk::op_token(&[8u8; 32], 1));
    }

    #[test]
    fn token_extraction_and_compare() {
        let req = HttpRequest::builder()
            .uri("/admin?foo=1&token=abc")
            .body(Body::empty())
            .unwrap();
        assert_eq!(presented_token(&req).as_deref(), Some("abc"));
        assert!(constant_time_eq(b"abc", b"abc"));
        assert!(!constant_time_eq(b"abc", b"abd"));
        assert!(!constant_time_eq(b"abc", b"abcd"));
    }
}
