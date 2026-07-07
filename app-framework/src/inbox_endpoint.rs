//! HTTP wrapper around [`CapInbox`].
// Storage types are deprecated pending cell-program migration (STORAGE-AS-CELL-PROGRAMS.md §3.1).
#![allow(deprecated)]
//!
//! `InboxEndpoint` exposes three routes:
//!
//! - `POST /send` — deliver a message to the inbox with a deposit.
//! - `GET /next` — owner reads the next queued entry.
//! - `GET /status` — inbox status JSON.
//!
//! All spam-prevention and Merkle accounting lives in `dregg_storage::inbox::CapInbox`.
//! This module is a thin HTTP skin.
//!
//! # Triage (storage→cell-program migration — 2026-05-24)
//!
//! `STORAGE-AS-CELL-PROGRAMS.md §3.1` lays out the migration plan for
//! `CapInbox`: it becomes a cell-program pattern with a sovereign
//! cell carrying `(queue_root, owner, min_deposit, capacity_per_user,
//! head, tail)` slots, governed by `StateConstraint`s
//! (`SenderAuthorized`, `MonotonicSequence(head)`,
//! `MonotonicSequence(tail)`, `WriteOnce(owner)`,
//! `FieldLte(deposit, balance)`). Vocabulary already exists; no new
//! `WitnessedPredicate` kind is needed (per `STORAGE-AS-CELL-PROGRAMS.md`
//! §1.2 table).
//!
//! Critically, the authorization-gap that subscription's CLAUDIT
//! flagged as P0-5 — "`POST /send` accepts client-asserted
//! `sender_hex`" — closes naturally in the migration: the executor
//! will only accept `Effect::QueueEnqueue` (or its `SetField`
//! equivalent) authorized by a real `Authorization::Signature` from
//! the sender's cipherclerk. The HTTP handler stops carrying a `sender_hex`
//! request field and instead extracts the signing cipherclerk from the
//! `AppCipherclerk` axum Extension.
//!
//! Verdict: **(c) needs updates post-migration**. Same shape as the
//! `blinded_endpoint.rs` post-migration sketch: the endpoint stays
//! as an HTTP-language entry point, but its implementation collapses
//! to "produce signed `Action` carrying queue-state effects, submit
//! through `StarbridgeAppContext::executor()`, surface the receipt as
//! JSON." Blocks on the cell-program migration; in the interim this
//! module continues to wrap `dregg_storage::inbox::CapInbox` directly.
//!
//! # Usage
//!
//! ```ignore
//! use dregg_app_framework::inbox_endpoint::InboxEndpoint;
//!
//! let endpoint = InboxEndpoint::new(256, 100).ttl_blocks(1000);
//! let app = AppServer::new(config)
//!     .with_inbox("/inbox", endpoint)
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

use dregg_storage::{
    QuotaId,
    inbox::{CapInbox, InboxMessage},
};

use crate::server::api_error;

// =============================================================================
// Request / response types
// =============================================================================

/// Request body for `POST /send` — delivers a message.
///
/// The message type is determined by which optional field is populated:
/// - `cert_bytes_hex` → `InboxMessage::Capability`
/// - `uri` → `InboxMessage::SturdyRef`
/// - `ciphertext_hex` → `InboxMessage::Encrypted`
#[derive(Debug, Deserialize)]
pub struct SendRequest {
    /// Sender identity (hex-encoded 32-byte ed25519 verifying key). The sender must PROVE it holds
    /// the matching key via `signature_hex` — the identity is no longer merely asserted.
    pub sender_hex: String,
    /// The sender's ed25519 signature (hex, 64 bytes) over the canonical send message
    /// (`"dregg-inbox-send-v1" || sender || deposit_le || type_tag || payload`). REQUIRED — a
    /// missing or invalid signature is refused (fail-closed). Closes the client-asserted-sender
    /// fail-open: an impostor cannot forge a signature for a `sender_hex` whose key it does not hold.
    #[serde(default)]
    pub signature_hex: Option<String>,
    /// Deposit paid by sender (must meet `min_deposit`).
    pub deposit: u64,
    /// Capability certificate bytes (hex-encoded). Mutually exclusive with the others.
    pub cert_bytes_hex: Option<String>,
    /// Sturdy-ref URI string. Mutually exclusive with the others.
    pub uri: Option<String>,
    /// Encrypted ciphertext (hex-encoded). Mutually exclusive with the others.
    pub ciphertext_hex: Option<String>,
}

/// Response from `POST /send`.
#[derive(Debug, Serialize)]
pub struct SendResponse {
    /// New inbox root hash (hex).
    pub root_hex: String,
}

/// Response from `GET /next`.
#[derive(Debug, Serialize)]
pub struct NextResponse {
    /// Content hash of the entry (hex).
    pub content_hash_hex: String,
    /// Sender of the entry (hex).
    pub sender_hex: String,
    /// Deposit paid.
    pub deposit: u64,
    /// Block height when enqueued.
    pub enqueued_at: u64,
    /// Dequeue proof: old root before this dequeue (hex).
    pub old_root_hex: String,
    /// Dequeue proof: new root after this dequeue (hex).
    pub new_root_hex: String,
    /// Position in the queue.
    pub position: usize,
}

/// Response from `GET /status`.
#[derive(Debug, Serialize)]
pub struct InboxStatusResponse {
    pub pending_messages: usize,
    pub is_full: bool,
    pub min_deposit: u64,
    pub max_message_size: usize,
    pub root_hex: String,
}

// =============================================================================
// Endpoint state
// =============================================================================

#[derive(Clone)]
struct EndpointState {
    inbox: Arc<Mutex<CapInbox>>,
    #[allow(dead_code)]
    ttl_blocks: Option<u64>,
}

/// HTTP endpoint wrapping a [`CapInbox`].
pub struct InboxEndpoint {
    inbox: Arc<Mutex<CapInbox>>,
    ttl_blocks: Option<u64>,
}

impl InboxEndpoint {
    /// Create a new inbox endpoint.
    ///
    /// * `capacity_per_user` — maximum number of messages that can be queued.
    /// * `min_deposit` — minimum deposit required from senders (anti-spam).
    ///
    /// Uses `QuotaId(0)` as the owner quota. Apps that need real quota accounting
    /// should construct `CapInbox` directly and use `InboxEndpoint::from_inbox`.
    pub fn new(capacity_per_user: usize, min_deposit: u64) -> Self {
        let inbox = CapInbox::new(QuotaId(0), capacity_per_user, min_deposit);
        Self {
            inbox: Arc::new(Mutex::new(inbox)),
            ttl_blocks: None,
        }
    }

    /// Create an endpoint from an existing `Arc<Mutex<CapInbox>>`.
    ///
    /// Use this when the app needs to share the inbox with other handlers
    /// (e.g., to push notifications from a submission handler).
    pub fn from_inbox(inbox: Arc<Mutex<CapInbox>>) -> Self {
        Self {
            inbox,
            ttl_blocks: None,
        }
    }

    /// Get a clone of the inner `Arc<Mutex<CapInbox>>` for sharing with handlers.
    pub fn inbox_arc(&self) -> Arc<Mutex<CapInbox>> {
        Arc::clone(&self.inbox)
    }

    /// Set a time-to-live (in blocks). Expired messages are evicted on GC.
    ///
    /// NOTE: Automatic GC is NOT called by the HTTP handlers — apps must call
    /// `gc_expired` on the inner `CapInbox` from their own background task.
    pub fn ttl_blocks(mut self, ttl: u64) -> Self {
        self.ttl_blocks = Some(ttl);
        self
    }

    /// Build the axum router.
    pub fn router(self) -> Router {
        let state = EndpointState {
            inbox: self.inbox,
            ttl_blocks: self.ttl_blocks,
        };
        Router::new()
            .route("/send", post(handle_send))
            .route("/next", get(handle_next))
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
    let bytes: Vec<u8> = (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16))
        .collect::<Result<_, _>>()
        .ok()?;
    bytes.try_into().ok()
}

fn hex_encode(b: &[u8; 32]) -> String {
    b.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn parse_hex_bytes(s: &str) -> Option<Vec<u8>> {
    if !s.len().is_multiple_of(2) {
        return None;
    }
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).ok())
        .collect()
}

/// The canonical bytes the sender signs for a `POST /send`: a domain tag, the sender key, the
/// deposit, a message-type tag, and the payload. Binding all of these makes a valid signature
/// unforgeable for a different sender, deposit, type, or content.
fn send_signing_message(sender: &[u8; 32], deposit: u64, type_tag: u8, payload: &[u8]) -> Vec<u8> {
    let mut m = Vec::with_capacity(19 + 32 + 8 + 1 + payload.len());
    m.extend_from_slice(b"dregg-inbox-send-v1");
    m.extend_from_slice(sender);
    m.extend_from_slice(&deposit.to_le_bytes());
    m.push(type_tag);
    m.extend_from_slice(payload);
    m
}

/// FAIL-CLOSED sender authentication — verify the ed25519 signature over the canonical send message
/// against `sender` (as a verifying key). Returns `false` on a missing/malformed/invalid signature
/// or a non-curve-point sender, so the send is refused: the sender identity is PROVEN, not asserted.
fn verify_send_auth(
    sender: &[u8; 32],
    deposit: u64,
    type_tag: u8,
    payload: &[u8],
    sig_hex: Option<&str>,
) -> bool {
    use ed25519_dalek::{Signature, Verifier, VerifyingKey};
    let Some(sig_hex) = sig_hex else {
        return false;
    };
    let Ok(vk) = VerifyingKey::from_bytes(sender) else {
        return false;
    };
    let Some(sig_bytes) = parse_hex_bytes(sig_hex) else {
        return false;
    };
    let Ok(sig_arr): Result<[u8; 64], _> = sig_bytes.try_into() else {
        return false;
    };
    let msg = send_signing_message(sender, deposit, type_tag, payload);
    vk.verify_strict(&msg, &Signature::from_bytes(&sig_arr))
        .is_ok()
}

// =============================================================================
// Handlers
// =============================================================================

async fn handle_send(
    State(state): State<EndpointState>,
    Json(req): Json<SendRequest>,
) -> Result<Json<SendResponse>, (StatusCode, Json<crate::server::ErrorResponse>)> {
    let sender = parse_hex32(&req.sender_hex)
        .ok_or_else(|| api_error(StatusCode::BAD_REQUEST, "invalid sender_hex"))?;

    // Determine message type + the signed payload/type-tag from the request.
    let (msg, type_tag, payload): (InboxMessage, u8, Vec<u8>) =
        if let Some(cert_hex) = &req.cert_bytes_hex {
            let cert_bytes = parse_hex_bytes(cert_hex)
                .ok_or_else(|| api_error(StatusCode::BAD_REQUEST, "invalid cert_bytes_hex"))?;
            (
                InboxMessage::Capability {
                    cert_bytes: cert_bytes.clone(),
                    sender,
                },
                0,
                cert_bytes,
            )
        } else if let Some(uri) = &req.uri {
            (
                InboxMessage::SturdyRef {
                    uri: uri.clone(),
                    sender,
                },
                1,
                uri.as_bytes().to_vec(),
            )
        } else if let Some(ct_hex) = &req.ciphertext_hex {
            let ciphertext = parse_hex_bytes(ct_hex)
                .ok_or_else(|| api_error(StatusCode::BAD_REQUEST, "invalid ciphertext_hex"))?;
            (
                InboxMessage::Encrypted {
                    ciphertext: ciphertext.clone(),
                    sender,
                },
                2,
                ciphertext,
            )
        } else {
            return Err(api_error(
                StatusCode::BAD_REQUEST,
                "one of cert_bytes_hex, uri, or ciphertext_hex must be provided",
            ));
        };

    // FAIL-CLOSED: the sender must PROVE it holds the key it claims — a missing or forged signature
    // is refused (was a client-asserted-sender fail-open: anyone could send as anyone).
    if !verify_send_auth(
        &sender,
        req.deposit,
        type_tag,
        &payload,
        req.signature_hex.as_deref(),
    ) {
        return Err(api_error(
            StatusCode::UNAUTHORIZED,
            "send not authenticated: missing or invalid signature for sender_hex",
        ));
    }

    let mut inbox = state.inbox.lock().await;
    match inbox.receive(msg, req.deposit) {
        Ok(root) => Ok(Json(SendResponse {
            root_hex: hex_encode(&root),
        })),
        Err(e) => Err(api_error(
            StatusCode::UNPROCESSABLE_ENTITY,
            format!("inbox rejected: {e:?}"),
        )),
    }
}

async fn handle_next(
    State(state): State<EndpointState>,
) -> Result<Json<NextResponse>, (StatusCode, Json<crate::server::ErrorResponse>)> {
    let mut inbox = state.inbox.lock().await;
    match inbox.read_next() {
        Ok((entry, proof)) => Ok(Json(NextResponse {
            content_hash_hex: hex_encode(&entry.content_hash),
            sender_hex: hex_encode(&entry.sender),
            deposit: entry.deposit,
            enqueued_at: entry.enqueued_at,
            old_root_hex: hex_encode(&proof.old_root),
            new_root_hex: hex_encode(&proof.new_root),
            position: proof.position,
        })),
        Err(e) => Err(api_error(
            StatusCode::NOT_FOUND,
            format!("inbox error: {e:?}"),
        )),
    }
}

async fn handle_status(State(state): State<EndpointState>) -> Json<InboxStatusResponse> {
    let inbox = state.inbox.lock().await;
    let status = inbox.status();
    Json(InboxStatusResponse {
        pending_messages: status.pending_messages,
        is_full: status.is_full,
        min_deposit: status.min_deposit,
        max_message_size: status.max_message_size,
        root_hex: hex_encode(&status.root),
    })
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use axum::body::Body;
    use axum::http::{Method, Request};
    use tower::ServiceExt;

    fn test_keypair() -> ed25519_dalek::SigningKey {
        ed25519_dalek::SigningKey::from_bytes(&[7u8; 32])
    }

    fn hex_all(b: &[u8]) -> String {
        b.iter().map(|x| format!("{x:02x}")).collect()
    }

    fn post_send(body: &serde_json::Value) -> Request<Body> {
        Request::builder()
            .method(Method::POST)
            .uri("/send")
            .header("content-type", "application/json")
            .body(Body::from(serde_json::to_vec(body).unwrap()))
            .unwrap()
    }

    /// A `/send` JSON body with a VALID ed25519 signature over the canonical send message.
    fn signed_sturdyref_body(
        sk: &ed25519_dalek::SigningKey,
        deposit: u64,
        uri: &str,
    ) -> serde_json::Value {
        use ed25519_dalek::Signer;
        let sender = sk.verifying_key().to_bytes();
        let sig = sk.sign(&send_signing_message(&sender, deposit, 1, uri.as_bytes()));
        serde_json::json!({
            "sender_hex": hex_encode(&sender),
            "signature_hex": hex_all(&sig.to_bytes()),
            "deposit": deposit,
            "uri": uri,
        })
    }

    #[tokio::test]
    async fn send_and_read_next_roundtrip() {
        let endpoint = InboxEndpoint::new(16, 0);
        let app = endpoint.router();

        // Send a SIGNED sturdy-ref message (the sender proves it holds the key).
        let resp = app
            .clone()
            .oneshot(post_send(&signed_sturdyref_body(
                &test_keypair(),
                0,
                "dregg://test/ref",
            )))
            .await
            .unwrap();
        assert_eq!(resp.status(), StatusCode::OK);

        // Read next.
        let req = Request::builder()
            .method(Method::GET)
            .uri("/next")
            .body(Body::empty())
            .unwrap();
        let resp = app.clone().oneshot(req).await.unwrap();
        assert_eq!(resp.status(), StatusCode::OK);
        let bytes = axum::body::to_bytes(resp.into_body(), usize::MAX)
            .await
            .unwrap();
        let entry: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
        assert_eq!(entry["deposit"], 0);
    }

    /// THE FAIL-OPEN IS CLOSED: an unsigned send AND an IMPOSTOR send (a valid signature by the
    /// WRONG key while claiming another `sender_hex`) are both REFUSED (401) — while the genuine
    /// signer is still admitted. Before the fix both attacks would have been accepted: anyone could
    /// send as anyone.
    #[tokio::test]
    async fn unsigned_or_impostor_send_is_refused() {
        use ed25519_dalek::Signer;
        let endpoint = InboxEndpoint::new(16, 0);
        let app = endpoint.router();
        let victim = test_keypair();
        let sender = victim.verifying_key().to_bytes();

        // (a) NO signature → 401.
        let unsigned = serde_json::json!({
            "sender_hex": hex_encode(&sender), "deposit": 0u64, "uri": "dregg://x"
        });
        assert_eq!(
            app.clone()
                .oneshot(post_send(&unsigned))
                .await
                .unwrap()
                .status(),
            StatusCode::UNAUTHORIZED
        );

        // (b) IMPOSTOR: a valid signature by a DIFFERENT key, claiming the victim's sender_hex → 401.
        let impostor = ed25519_dalek::SigningKey::from_bytes(&[9u8; 32]);
        let forged = impostor.sign(&send_signing_message(&sender, 0, 1, b"dregg://x"));
        let forged_body = serde_json::json!({
            "sender_hex": hex_encode(&sender),
            "signature_hex": hex_all(&forged.to_bytes()),
            "deposit": 0u64, "uri": "dregg://x"
        });
        assert_eq!(
            app.clone()
                .oneshot(post_send(&forged_body))
                .await
                .unwrap()
                .status(),
            StatusCode::UNAUTHORIZED
        );

        // (c) COMPLETENESS: the genuine signer IS admitted — we closed the hole, not the endpoint.
        assert_eq!(
            app.clone()
                .oneshot(post_send(&signed_sturdyref_body(&victim, 0, "dregg://x")))
                .await
                .unwrap()
                .status(),
            StatusCode::OK
        );
    }

    #[tokio::test]
    async fn status_initially_empty() {
        let endpoint = InboxEndpoint::new(8, 100);
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
        assert_eq!(status["pending_messages"], 0);
        assert_eq!(status["min_deposit"], 100);
    }
}
