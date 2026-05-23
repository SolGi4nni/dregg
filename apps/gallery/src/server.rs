//! Axum API server with REST + WebSocket support.
//!
//! Serves the gallery backend API and the static frontend files.
//! WebSocket connections at `/ws` receive live updates for all gallery events.

use std::net::SocketAddr;
use std::sync::Arc;

use axum::{
    Router,
    extract::{State, WebSocketUpgrade},
    response::IntoResponse,
    routing::{get, post},
};
use tokio::sync::RwLock;
use tower_http::cors::CorsLayer;
use tower_http::services::ServeDir;
use tracing::info;

use pyana_app_framework::{EngineConfig, PyanaEngine};

use crate::artwork::ArtworkRegistry;
use crate::auction::AuctionEngine;
use crate::handlers;
use crate::provenance::ProvenanceRegistry;
use crate::ws::{WsBroadcaster, handle_ws_connection};

// =============================================================================
// Configuration
// =============================================================================

/// Configuration for the gallery server.
pub struct ServerConfig {
    /// Listen address.
    pub listen: SocketAddr,
    /// Path to frontend static files (for serving HTML/JS/CSS).
    pub frontend_path: Option<String>,
}

impl Default for ServerConfig {
    fn default() -> Self {
        Self {
            listen: "127.0.0.1:3040".parse().unwrap(),
            frontend_path: None,
        }
    }
}

// =============================================================================
// Application State
// =============================================================================

/// Shared application state passed to all handlers.
#[derive(Clone)]
pub struct AppState {
    pub artwork_registry: ArtworkRegistry,
    pub auction_engine: AuctionEngine,
    pub provenance_registry: ProvenanceRegistry,
    pub engine: Arc<RwLock<PyanaEngine>>,
    pub ws_broadcaster: WsBroadcaster,
}

// =============================================================================
// Public API
// =============================================================================

/// Start the gallery server in the background as a tokio task.
///
/// Returns the actual `SocketAddr` the server is listening on.
pub async fn start_server(config: ServerConfig) -> SocketAddr {
    let now_ts = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0);

    let state = AppState {
        artwork_registry: ArtworkRegistry::new(),
        auction_engine: AuctionEngine::new(),
        provenance_registry: ProvenanceRegistry::new(),
        engine: Arc::new(RwLock::new(PyanaEngine::new(EngineConfig::new(now_ts)))),
        ws_broadcaster: WsBroadcaster::new(),
    };

    let mut app = Router::new()
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
        // Admin/devnet utilities.
        .route("/admin/height", post(handlers::advance_height))
        .route("/admin/settle/{id}", post(handlers::trigger_settle))
        // Health.
        .route("/health", get(handlers::health_check))
        .layer(CorsLayer::permissive())
        .with_state(state);

    // Optionally serve frontend static files.
    if let Some(ref frontend_path) = config.frontend_path {
        app = app.fallback_service(ServeDir::new(frontend_path));
    }

    let listener = tokio::net::TcpListener::bind(config.listen)
        .await
        .expect("failed to bind gallery server");
    let addr = listener.local_addr().unwrap();

    info!("Gallery server listening on http://{addr}");

    tokio::spawn(async move {
        axum::serve(listener, app).await.expect("server error");
    });

    addr
}

/// WebSocket upgrade handler.
async fn ws_upgrade(ws: WebSocketUpgrade, State(state): State<AppState>) -> impl IntoResponse {
    ws.on_upgrade(move |socket| handle_ws_connection(socket, state.ws_broadcaster))
}
