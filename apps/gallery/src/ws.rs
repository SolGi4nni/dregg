//! WebSocket handler for live bid updates and auction state changes.
//!
//! Clients connect to `/ws` and receive JSON-encoded `WsEvent` messages
//! whenever bids are submitted, revealed, or auctions settle.

use axum::extract::ws::{Message, WebSocket};
use futures::SinkExt;
use futures::stream::StreamExt;
use tokio::sync::broadcast;
use tracing::{info, warn};

use crate::WsEvent;

/// Broadcast channel capacity for WebSocket events.
pub const WS_CHANNEL_CAPACITY: usize = 256;

/// The WebSocket broadcast hub.
///
/// All gallery events are sent through this hub and fanned out to all
/// connected WebSocket clients.
#[derive(Clone)]
pub struct WsBroadcaster {
    sender: broadcast::Sender<WsEvent>,
}

impl WsBroadcaster {
    /// Create a new broadcaster.
    pub fn new() -> Self {
        let (sender, _) = broadcast::channel(WS_CHANNEL_CAPACITY);
        Self { sender }
    }

    /// Broadcast an event to all connected clients.
    pub fn broadcast(&self, event: WsEvent) {
        // Ignore errors (no receivers connected).
        let _ = self.sender.send(event);
    }

    /// Subscribe to events (called per WebSocket connection).
    pub fn subscribe(&self) -> broadcast::Receiver<WsEvent> {
        self.sender.subscribe()
    }
}

/// Handle a single WebSocket connection.
///
/// Subscribes to the broadcast channel and forwards all events to the client.
/// Also listens for client messages (currently just ping/pong keepalive).
pub async fn handle_ws_connection(socket: WebSocket, broadcaster: WsBroadcaster) {
    let (mut ws_sender, mut ws_receiver) = socket.split();
    let mut rx = broadcaster.subscribe();

    info!("WebSocket client connected");

    // Spawn a task to forward broadcast events to this client.
    let send_task = tokio::spawn(async move {
        while let Ok(event) = rx.recv().await {
            let json = match serde_json::to_string(&event) {
                Ok(j) => j,
                Err(e) => {
                    warn!("failed to serialize WS event: {e}");
                    continue;
                }
            };

            if ws_sender.send(Message::Text(json.into())).await.is_err() {
                // Client disconnected.
                break;
            }
        }
    });

    // Listen for client messages (just drain them; we don't expect commands).
    while let Some(msg) = ws_receiver.next().await {
        match msg {
            Ok(Message::Close(_)) => break,
            Ok(Message::Ping(data)) => {
                // axum handles pong automatically, but log for debugging.
                let _ = data;
            }
            Ok(_) => {
                // Ignore text/binary messages from client.
            }
            Err(_) => break,
        }
    }

    // Clean up the send task.
    send_task.abort();
    info!("WebSocket client disconnected");
}
