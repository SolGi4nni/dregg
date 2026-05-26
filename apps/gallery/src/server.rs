//! Axum API server with REST + WebSocket support.
//!
//! Serves the gallery backend API and the static frontend files.
//! WebSocket connections at `/ws` receive live updates for all gallery events.
//!
//! Uses `dregg-app-framework` for shared infrastructure: [`AppServer`] for
//! standard middleware (health, CORS), [`AdminAuth`] extractor for admin
//! endpoints, and [`JsonPersistence`] for atomic state snapshots.

use std::sync::Arc;

use axum::{
    Router,
    extract::{State, WebSocketUpgrade},
    response::IntoResponse,
    routing::{get, post},
};
use tokio::sync::Mutex;
use tower_http::services::ServeDir;
use tracing::info;

use dregg_app_framework::auth::{AdminMode, AdminToken, HasAdminToken};
use dregg_app_framework::persistence::JsonPersistence;
use dregg_app_framework::server::{AppConfig, AppServer};
use dregg_app_framework::{EngineConfig, DreggEngine};

use dregg_app_framework::blinded_endpoint::FairDistributionEndpoint;
use dregg_app_framework::inbox_endpoint::InboxEndpoint;

use crate::artwork::ArtworkRegistry;
use crate::auction::AuctionEngine;
use crate::blinded_bids::BLINDED_BID_QUEUE_CAPACITY;
use crate::handlers;
use crate::notification_inbox::{INBOX_CAPACITY, INBOX_MIN_DEPOSIT};
use crate::persistence::StateSnapshot;
use crate::provenance::ProvenanceRegistry;
use crate::ws::{WsBroadcaster, handle_ws_connection};

// =============================================================================
// Application State
// =============================================================================

/// Shared application state passed to all handlers.
#[derive(Clone)]
pub struct AppState {
    pub artwork_registry: ArtworkRegistry,
    pub auction_engine: AuctionEngine,
    pub provenance_registry: ProvenanceRegistry,
    pub engine: Arc<Mutex<DreggEngine>>,
    pub ws_broadcaster: WsBroadcaster,
    /// Admin token for protecting admin endpoints (from DREGG_ADMIN_TOKEN env var).
    pub admin_token: AdminToken,
    /// Persistence handle for atomic JSON snapshots (None = persistence disabled).
    pub persistence: Option<JsonPersistence>,
}

impl HasAdminToken for AppState {
    fn admin_token(&self) -> &AdminToken {
        &self.admin_token
    }
}

// =============================================================================
// Route Construction
// =============================================================================

/// Build the gallery application router (without framework middleware).
///
/// Callers can pass this to `AppServer::routes()` after calling `.with_state()`.
pub fn gallery_routes() -> Router<AppState> {
    Router::new()
        // Artwork endpoints.
        .route("/artworks", get(handlers::list_artworks))
        .route("/artworks", post(handlers::register_artwork))
        .route("/artworks/{id}", get(handlers::get_artwork))
        // Auction endpoints.
        .route("/auctions", get(handlers::list_auctions))
        .route("/auctions", post(handlers::create_auction))
        .route("/auctions/{id}", get(handlers::get_auction))
        .route("/auctions/{id}/bid", post(handlers::submit_bid))
        .route("/auctions/{id}/reveal", post(handlers::reveal_bid))
        .route("/auctions/{id}/result", get(handlers::get_auction_result))
        // WebSocket.
        .route("/ws", get(ws_upgrade))
        // Admin/devnet utilities (protected by AdminAuth extractor).
        .route("/admin/height", post(handlers::advance_height))
        .route("/admin/settle/{id}", post(handlers::trigger_settle))
        .route("/admin/persist", post(handlers::persist_state))
        // Health (gallery-specific: includes artwork/auction counts and block height).
        .route("/health", get(handlers::health_check))
}

// =============================================================================
// Public API
// =============================================================================

/// Start the gallery server using the shared `AppServer` framework.
///
/// Returns the actual `SocketAddr` the server is listening on (runs in background).
///
/// The gallery uses `AdminMode::Open` when no `DREGG_ADMIN_TOKEN` is configured,
/// matching devnet behavior (admin endpoints freely accessible without auth).
pub async fn start_server(
    config: AppConfig,
    frontend_path: Option<String>,
) -> std::net::SocketAddr {
    let now_ts = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0);

    let persistence = config.persistence();

    // Use Open mode for admin auth: if no token is configured, admin endpoints
    // are freely accessible (suitable for devnet). If DREGG_ADMIN_TOKEN is set,
    // it will be enforced.
    let admin_token = AdminToken::from_env_with_mode(AdminMode::Open);

    let artwork_registry = ArtworkRegistry::new();
    let auction_engine = AuctionEngine::new();
    let provenance_registry = ProvenanceRegistry::new();

    // Attempt to load persisted state via JsonPersistence.
    if let Some(ref persist) = persistence {
        match persist.load::<StateSnapshot>() {
            Ok(Some(snapshot)) => {
                snapshot
                    .restore(&artwork_registry, &auction_engine, &provenance_registry)
                    .await;
                info!(path = %persist.path().display(), "restored state from persistence file");
            }
            Ok(None) => {
                // No state file yet -- starting fresh.
            }
            Err(e) => {
                tracing::warn!(path = %persist.path().display(), error = %e, "failed to load state file, starting fresh");
            }
        }
    }

    let state = AppState {
        artwork_registry,
        auction_engine,
        provenance_registry,
        engine: Arc::new(Mutex::new(DreggEngine::new(EngineConfig::new(now_ts)))),
        ws_broadcaster: WsBroadcaster::new(),
        admin_token,
        persistence,
    };

    let mut app_routes: Router = gallery_routes().with_state(state);

    // Optionally serve frontend static files as a fallback.
    if let Some(ref fp) = frontend_path {
        app_routes = app_routes.fallback_service(ServeDir::new(fp));
    }

    // Upgrade 1: blinded bid commitment queue.
    // REVIEW[P2]: this is NOT a Vickrey implementation — `BlindedQueue` does not
    // rank bids. See `blinded_bids.rs` module docs. Bids here aren't linked to a
    // specific auction_id, and the legacy `/auctions/*` path still works in
    // parallel (no cross-path dedup).
    // REVIEW[P3]: this duplicates the constructor logic in
    // `blinded_bids::blinded_bid_endpoint()`. Either call the helper or remove it.
    let blinded_bids = FairDistributionEndpoint::new(BLINDED_BID_QUEUE_CAPACITY);

    // Upgrade 2: Store-and-forward inbox for offline bidder notifications.
    // REVIEW[P1]: no auction code calls `.receive(...)` on this inbox. Outbid /
    // win notifications are NEVER pushed by the gallery itself. See
    // `notification_inbox.rs` module docs.
    // REVIEW[P3]: duplicates `notification_inbox::bidder_inbox_endpoint()`.
    let bidder_inbox = InboxEndpoint::new(INBOX_CAPACITY, INBOX_MIN_DEPOSIT);

    AppServer::new(config)
        .service_name("dregg-gallery")
        .with_cors()
        .routes(app_routes)
        .with_blinded_endpoint("/queue/bids", blinded_bids)
        .with_inbox("/inbox/bidders", bidder_inbox)
        .serve_background()
        .await
        .expect("failed to start gallery server")
}

/// WebSocket upgrade handler.
async fn ws_upgrade(ws: WebSocketUpgrade, State(state): State<AppState>) -> impl IntoResponse {
    ws.on_upgrade(move |socket| handle_ws_connection(socket, state.ws_broadcaster))
}
