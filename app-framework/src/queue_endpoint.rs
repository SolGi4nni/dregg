//! HTTP wrapper around [`ProgrammableQueue`].
// Storage types are deprecated pending cell-program migration (STORAGE-AS-CELL-PROGRAMS.md §3.2).
#![allow(deprecated)]
//!
//! `QueueEndpoint` exposes three routes:
//!
//! - `POST /enqueue` — enqueue a message; body: [`EnqueueRequest`].
//! - `POST /dequeue` — dequeue next entry (with optional preimage); body: [`DequeueRequest`].
//! - `GET /status` — queue status JSON.
//!
//! All heavy lifting (Merkle accounting, constraint validation) is performed by the
//! underlying `ProgrammableQueue` from `pyana-storage`. This module is a thin HTTP skin.
//!
//! # Usage
//!
//! ```ignore
//! use pyana_app_framework::queue_endpoint::QueueEndpoint;
//! use pyana_storage::programmable::{ProgrammableQueue, programs};
//!
//! let queue = ProgrammableQueue::new("orders".into(), owner, programs::open(0), None, 1024);
//! let endpoint = QueueEndpoint::new(queue)
//!     .with_height_provider(|| current_block_height());
//!
//! let app = AppServer::new(config)
//!     .with_queue_endpoint("/queue", endpoint)
//!     .serve();
//! ```

use std::sync::Arc;

use axum::{
    Json, Router,
    extract::State,
    http::StatusCode,
    routing::{get, post},
};
use serde::{Deserialize, Serialize};
use tokio::sync::Mutex;

use pyana_storage::{
    programmable::{ProgrammableQueue, ValidationContext},
    queue::QueueEntry,
};

use crate::server::api_error;

// =============================================================================
// Request / response types
// =============================================================================

/// Request body for `POST /enqueue`.
#[derive(Debug, Deserialize)]
pub struct EnqueueRequest {
    /// Content hash (hex-encoded 32 bytes). The caller is responsible for
    /// hashing the actual message body before sending.
    pub content_hash: String,
    /// Sender public key (hex-encoded 32 bytes).
    pub sender: String,
    /// Deposit amount in computrons.
    pub deposit: u64,
    /// Optional sequence number (for MonotonicSequence constraint).
    pub sequence: Option<u64>,
}

/// Request body for `POST /dequeue`.
#[derive(Debug, Deserialize)]
pub struct DequeueRequest {
    /// Optional preimage (hex-encoded 32 bytes) for secret-gated queues.
    pub preimage: Option<String>,
}

/// Response from `POST /enqueue`.
#[derive(Debug, Serialize)]
pub struct EnqueueResponse {
    /// New queue root hash (hex).
    pub root: String,
    /// Queue length after enqueue.
    pub len: usize,
}

/// Response from `POST /dequeue`.
#[derive(Debug, Serialize)]
pub struct DequeueResponse {
    /// The dequeued entry's content hash (hex).
    pub content_hash: String,
    /// Sender of the dequeued entry (hex).
    pub sender: String,
    /// Deposit paid by sender.
    pub deposit: u64,
    /// Old root (before dequeue).
    pub old_root: String,
    /// New root (after dequeue).
    pub new_root: String,
    /// Position in the queue.
    pub position: usize,
}

/// Response from `GET /status`.
#[derive(Debug, Serialize)]
pub struct StatusResponse {
    /// Current queue length.
    pub len: usize,
    /// Current Merkle root (hex).
    pub root: String,
    /// Program VK hash (hex) — content-addresses the queue's constraint rules.
    pub vk_hash: String,
    /// Queue name.
    pub name: String,
}

// =============================================================================
// QueueEndpoint
// =============================================================================

/// Shared state passed to all route handlers.
#[derive(Clone)]
struct EndpointState {
    inner: Arc<Mutex<ProgrammableQueue>>,
    height_provider: Arc<dyn Fn() -> u64 + Send + Sync>,
}

/// HTTP endpoint wrapping a [`ProgrammableQueue`].
///
/// Build with `QueueEndpoint::new(queue)`, optionally customize the height
/// provider, then call `.router()` to obtain an `axum::Router` that can be
/// nested into an `AppServer`.
#[derive(Clone)]
pub struct QueueEndpoint {
    inner: Arc<Mutex<ProgrammableQueue>>,
    height_provider: Arc<dyn Fn() -> u64 + Send + Sync>,
}

impl QueueEndpoint {
    /// Wrap a `ProgrammableQueue`. Height defaults to a provider that always
    /// returns `0` (suitable for tests or apps that don't use temporal gates).
    pub fn new(queue: ProgrammableQueue) -> Self {
        Self {
            inner: Arc::new(Mutex::new(queue)),
            height_provider: Arc::new(|| 0),
        }
    }

    /// Override the height provider used when building `ValidationContext`.
    pub fn with_height_provider(mut self, f: impl Fn() -> u64 + Send + Sync + 'static) -> Self {
        self.height_provider = Arc::new(f);
        self
    }

    /// Build the `axum::Router` with three mounted routes.
    pub fn router(self) -> Router {
        let state = EndpointState {
            inner: self.inner,
            height_provider: self.height_provider,
        };
        Router::new()
            .route("/enqueue", post(handle_enqueue))
            .route("/dequeue", post(handle_dequeue))
            .route("/status", get(handle_status))
            .with_state(state)
    }
}

// =============================================================================
// Helpers
// =============================================================================

fn parse_hex32(s: &str) -> Option<[u8; 32]> {
    if s.len() != 64 {
        return None;
    }
    let bytes = hex::decode(s).ok()?;
    bytes.try_into().ok()
}

fn hex_encode(b: &[u8; 32]) -> String {
    hex::encode(b)
}

// =============================================================================
// Route handlers
// =============================================================================

async fn handle_enqueue(
    State(state): State<EndpointState>,
    Json(req): Json<EnqueueRequest>,
) -> Result<Json<EnqueueResponse>, (StatusCode, Json<crate::server::ErrorResponse>)> {
    let content_hash = parse_hex32(&req.content_hash).ok_or_else(|| {
        api_error(
            StatusCode::BAD_REQUEST,
            "invalid content_hash hex (expected 64 hex chars)",
        )
    })?;
    let sender = parse_hex32(&req.sender).ok_or_else(|| {
        api_error(
            StatusCode::BAD_REQUEST,
            "invalid sender hex (expected 64 hex chars)",
        )
    })?;

    let height = (state.height_provider)();
    let ctx = ValidationContext {
        sender,
        current_height: height,
        current_epoch: height / 100, // simple epoch: 100 blocks
        sender_epoch_count: 0,       // stateless for now; apps can override via custom validation
        preimage: None,
        sequence: req.sequence,
    };

    let entry = QueueEntry {
        content_hash,
        sender,
        deposit: req.deposit,
        enqueued_at: height,
        size: 32, // content_hash is 32 bytes
    };

    let mut q = state.inner.lock().await;
    match q.enqueue_validated(entry, &ctx) {
        Ok(root) => Ok(Json(EnqueueResponse {
            root: hex_encode(&root),
            len: q.len(),
        })),
        Err(e) => Err(api_error(
            StatusCode::UNPROCESSABLE_ENTITY,
            format!("constraint violation: {e:?}"),
        )),
    }
}

async fn handle_dequeue(
    State(state): State<EndpointState>,
    Json(req): Json<DequeueRequest>,
) -> Result<Json<DequeueResponse>, (StatusCode, Json<crate::server::ErrorResponse>)> {
    // parse optional preimage: Option<String> → Option<[u8; 32]>
    let preimage = match req.preimage.as_deref() {
        None => None,
        Some(s) => {
            let bytes = parse_hex32(s)
                .ok_or_else(|| api_error(StatusCode::BAD_REQUEST, "invalid preimage hex"))?;
            Some(bytes)
        }
    };

    let height = (state.height_provider)();
    let ctx = ValidationContext {
        sender: [0u8; 32],
        current_height: height,
        current_epoch: height / 100,
        sender_epoch_count: 0,
        preimage,
        sequence: None,
    };

    let mut q = state.inner.lock().await;
    match q.dequeue_validated(&ctx) {
        Ok((entry, proof)) => Ok(Json(DequeueResponse {
            content_hash: hex_encode(&entry.content_hash),
            sender: hex_encode(&entry.sender),
            deposit: entry.deposit,
            old_root: hex_encode(&proof.old_root),
            new_root: hex_encode(&proof.new_root),
            position: proof.position,
        })),
        Err(e) => Err(api_error(
            StatusCode::UNPROCESSABLE_ENTITY,
            format!("dequeue rejected: {e:?}"),
        )),
    }
}

async fn handle_status(State(state): State<EndpointState>) -> Json<StatusResponse> {
    let q = state.inner.lock().await;
    Json(StatusResponse {
        len: q.len(),
        root: hex_encode(&q.root()),
        vk_hash: hex_encode(&q.vk_hash()),
        name: q.name().to_string(),
    })
}

// =============================================================================
// Hex helper (avoids a new dep — we already have blake3 etc.; use simple impl)
// =============================================================================

mod hex {
    pub fn decode(s: &str) -> Result<Vec<u8>, ()> {
        if s.len() % 2 != 0 {
            return Err(());
        }
        (0..s.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&s[i..i + 2], 16).map_err(|_| ()))
            .collect()
    }

    pub fn encode(b: &[u8]) -> String {
        b.iter().map(|byte| format!("{byte:02x}")).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use axum::body::Body;
    use axum::http::{Method, Request};
    use pyana_storage::programmable::programs;
    use tower::ServiceExt;

    fn make_queue() -> ProgrammableQueue {
        ProgrammableQueue::new(
            "test".into(),
            [0u8; 32],
            programs::open(0), // no minimum deposit for tests
            None,
            64,
        )
    }

    #[tokio::test]
    async fn enqueue_dequeue_via_router() {
        let endpoint = QueueEndpoint::new(make_queue());
        let app = endpoint.router();

        // Enqueue
        let content_hash = format!("{:064x}", 42u64);
        let sender = format!("{:064x}", 1u64);
        let body = serde_json::json!({
            "content_hash": content_hash,
            "sender": sender,
            "deposit": 0,
        });
        let req = Request::builder()
            .method(Method::POST)
            .uri("/enqueue")
            .header("content-type", "application/json")
            .body(Body::from(serde_json::to_vec(&body).unwrap()))
            .unwrap();
        let resp = app.clone().oneshot(req).await.unwrap();
        assert_eq!(resp.status(), StatusCode::OK);

        // Dequeue
        let body = serde_json::json!({ "preimage": null });
        let req = Request::builder()
            .method(Method::POST)
            .uri("/dequeue")
            .header("content-type", "application/json")
            .body(Body::from(serde_json::to_vec(&body).unwrap()))
            .unwrap();
        let resp = app.clone().oneshot(req).await.unwrap();
        assert_eq!(resp.status(), StatusCode::OK);
    }

    #[tokio::test]
    async fn status_endpoint_works() {
        let endpoint = QueueEndpoint::new(make_queue());
        let app = endpoint.router();

        let req = Request::builder()
            .method(Method::GET)
            .uri("/status")
            .body(Body::empty())
            .unwrap();
        let resp = app.oneshot(req).await.unwrap();
        assert_eq!(resp.status(), StatusCode::OK);
        let bytes = axum::body::to_bytes(resp.into_body(), usize::MAX)
            .await
            .unwrap();
        let status: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
        assert_eq!(status["len"], 0);
        assert_eq!(status["name"], "test");
    }
}
