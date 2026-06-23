//! The node connection — an HTTP+SSE client against a dregg node.
//!
//! The shell speaks the node's wire contract (`node/src/api.rs` routes,
//! `node/src/events.rs` SSE stream). In the scaffold this layer ships two
//! implementations behind one interface:
//!
//!   * [`NodeClient::mock`] — an in-process fixture so the gpui shell renders
//!     real components with real data shapes WITHOUT a running node. This is
//!     the default the scaffold boots into.
//!   * [`NodeClient::http`] — points at a real node base URL. The fetch
//!     methods are wired to the routes; the SSE receipt stream is a build-out
//!     lane (it needs to be driven on gpui's async executor — see
//!     docs/STARBRIDGE-V2.md §"Build-out lanes").
//!
//! Both return the same [`crate::model`] types, so the views never know which
//! backend they are bound to.

use crate::model::{
    BlockInfo, CellListEntry, FederationInfo, NodeStatus, ReceiptEvent, SubmitTurnRequest,
    TurnActionSpec, TurnEffectSpec,
};

/// Where the shell gets its data.
#[derive(Clone)]
pub enum NodeClient {
    /// In-process fixtures — the scaffold's default. No network.
    Mock,
    /// A real node at `base_url` (e.g. `http://127.0.0.1:8080`).
    Http { base_url: String },
}

impl NodeClient {
    pub fn mock() -> Self {
        NodeClient::Mock
    }

    pub fn http(base_url: impl Into<String>) -> Self {
        NodeClient::Http {
            base_url: base_url.into(),
        }
    }

    pub fn describe(&self) -> String {
        match self {
            NodeClient::Mock => "mock (no node)".to_string(),
            NodeClient::Http { base_url } => base_url.clone(),
        }
    }

    pub fn is_live(&self) -> bool {
        matches!(self, NodeClient::Http { .. })
    }

    // --- reads ------------------------------------------------------------

    pub fn status(&self) -> anyhow::Result<NodeStatus> {
        match self {
            NodeClient::Mock => Ok(mock::status()),
            NodeClient::Http { base_url } => http_get(base_url, "/status"),
        }
    }

    pub fn cells(&self) -> anyhow::Result<Vec<CellListEntry>> {
        match self {
            NodeClient::Mock => Ok(mock::cells()),
            NodeClient::Http { base_url } => http_get(base_url, "/api/cells"),
        }
    }

    pub fn receipts(&self) -> anyhow::Result<Vec<ReceiptEvent>> {
        match self {
            NodeClient::Mock => Ok(mock::receipts()),
            // The non-stream snapshot uses /api/starbridge/receipts; the
            // scaffold maps those summary fields onto ReceiptEvent.
            NodeClient::Http { base_url } => http_get(base_url, "/api/receipts"),
        }
    }

    /// A TOLERANT count of the node's committed receipts (`GET /api/receipts`,
    /// parsed as a raw JSON array — that endpoint returns the FULL receipt shape
    /// (`agent`/`pre_state`/`post_state`/`action_count`/…), a superset of the
    /// SSE-summary [`ReceiptEvent`] [`Self::receipts`] decodes, so a typed parse
    /// rejects it). This is the empirical write-back probe: re-read it after a
    /// turn and see whether the node's ledger grew, without coupling to the exact
    /// receipt schema.
    pub fn receipts_count(&self) -> anyhow::Result<usize> {
        match self {
            NodeClient::Mock => Ok(mock::receipts().len()),
            NodeClient::Http { base_url } => {
                let arr: Vec<serde_json::Value> = http_get(base_url, "/api/receipts")?;
                Ok(arr.len())
            }
        }
    }

    /// The RAW receipt array (`GET /api/receipts`) as untyped JSON values —
    /// newest first. Used to reflect the chain head without coupling to the exact
    /// receipt schema (the endpoint carries the full receipt shape, a superset of
    /// the SSE-summary [`ReceiptEvent`]).
    pub fn receipts_raw(&self) -> anyhow::Result<Vec<serde_json::Value>> {
        match self {
            NodeClient::Mock => Ok(Vec::new()),
            NodeClient::Http { base_url } => http_get(base_url, "/api/receipts"),
        }
    }

    pub fn federations(&self) -> anyhow::Result<Vec<FederationInfo>> {
        match self {
            NodeClient::Mock => Ok(mock::federations()),
            NodeClient::Http { base_url } => http_get(base_url, "/api/federations"),
        }
    }

    pub fn blocks(&self) -> anyhow::Result<Vec<BlockInfo>> {
        match self {
            NodeClient::Mock => Ok(mock::blocks()),
            NodeClient::Http { base_url } => http_get(base_url, "/api/blocklace/blocks"),
        }
    }

    /// The SSE receipt-stream URL for this node (`/api/events/stream`). Resume is
    /// NOT a query param — the node resumes from the `Last-Event-ID` HEADER (see
    /// `node/src/events.rs`), which the reader sets on a reconnect. The `_resume`
    /// argument is kept for call-site clarity (the reader passes its cursor) but is
    /// not folded into the URL. `None` for the mock backend (it has no stream).
    pub fn events_stream_url(&self, _resume: Option<u64>) -> Option<String> {
        match self {
            NodeClient::Mock => None,
            NodeClient::Http { base_url } => Some(format!("{base_url}/api/events/stream")),
        }
    }

    // --- writes -----------------------------------------------------------

    /// Drive a turn through the node. In the scaffold the mock backend echoes
    /// a synthetic receipt hash; the HTTP backend POSTs to `/turn/submit`
    /// (which signs with the node operator's cipherclerk — local-custody
    /// signing is a build-out lane).
    pub fn submit_turn(&self, req: &SubmitTurnRequest) -> anyhow::Result<String> {
        match self {
            NodeClient::Mock => Ok(format!(
                "mock-receipt:{}-actions",
                req.actions.len()
            )),
            NodeClient::Http { base_url } => http_post(base_url, "/turn/submit", req),
        }
    }
}

/// Blocking JSON GET. The live shell drives reads on a background thread (the
/// `LiveNode` reader) so the gpui side stays single-threaded; the bare call is
/// kept blocking for clarity. Gated on `live-node` (the reqwest byte-pull); the
/// `Mock` arm above needs none of this, so a no-`live-node` build still has a
/// working `NodeClient::Mock`.
#[cfg(feature = "live-node")]
fn http_get<T: serde::de::DeserializeOwned>(base: &str, path: &str) -> anyhow::Result<T> {
    let url = format!("{base}{path}");
    let body = reqwest::blocking::get(&url)?.error_for_status()?.text()?;
    Ok(serde_json::from_str(&body)?)
}

#[cfg(feature = "live-node")]
fn http_post<T: serde::Serialize>(base: &str, path: &str, req: &T) -> anyhow::Result<String> {
    let url = format!("{base}{path}");
    let resp = reqwest::blocking::Client::new()
        .post(&url)
        .json(req)
        .send()?
        .error_for_status()?
        .text()?;
    Ok(resp)
}

// Without `live-node` (no reqwest), an `Http` arm can't reach the network. These
// stubs keep `NodeClient` compiling (the `Mock` backend stays fully functional);
// an `Http` call returns an honest "feature off" error rather than failing to
// build. (In practice both `native-full` and `sel4-thin` enable `live-node`.)
#[cfg(not(feature = "live-node"))]
fn http_get<T: serde::de::DeserializeOwned>(_base: &str, _path: &str) -> anyhow::Result<T> {
    anyhow::bail!("live-node feature is off (no reqwest); only NodeClient::Mock is available")
}

#[cfg(not(feature = "live-node"))]
fn http_post<T: serde::Serialize>(_base: &str, _path: &str, _req: &T) -> anyhow::Result<String> {
    anyhow::bail!("live-node feature is off (no reqwest); only NodeClient::Mock is available")
}

/// In-process fixtures. These mirror the SHAPES a real node returns so the
/// views render against real data the moment a node is wired in.
pub mod mock {
    use super::*;

    pub fn status() -> NodeStatus {
        NodeStatus {
            healthy: true,
            peer_count: 3,
            latest_height: 142,
            dag_height: 1888,
            block_count: 1888,
            consensus_live: true,
            federation_mode: "sovereign".into(),
            public_key: "a1b2c3d4e5f60718293a4b5c6d7e8f90a1b2c3d4e5f60718293a4b5c6d7e8f90".into(),
            state_producer: "lean".into(),
            lean_producer: true,
            full_turn_proving: true,
            producer_covered_effects: 51,
        }
    }

    pub fn cells() -> Vec<CellListEntry> {
        vec![
            CellListEntry {
                id: "11".repeat(32),
                balance: 100_000,
                nonce: 12,
                capability_count: 3,
                has_delegate: true,
                has_program: false,
                found: true,
            },
            CellListEntry {
                id: "22".repeat(32),
                balance: -500_000, // an issuer well: −supply
                nonce: 4,
                capability_count: 1,
                has_delegate: false,
                has_program: true,
                found: true,
            },
            CellListEntry {
                id: "33".repeat(32),
                balance: 7_500,
                nonce: 88,
                capability_count: 9,
                has_delegate: true,
                has_program: true,
                found: true,
            },
        ]
    }

    pub fn receipts() -> Vec<ReceiptEvent> {
        vec![
            ReceiptEvent {
                chain_index: 141,
                receipt_hash: "ab".repeat(32),
                turn_hash: "cd".repeat(32),
                cells: vec!["11".repeat(32), "33".repeat(32)],
                kinds: vec!["transfer".into(), "emit_event".into()],
                height: 1887,
                has_proof: true,
                finality: "final".into(),
                timestamp: 1_718_000_000,
            },
            ReceiptEvent {
                chain_index: 142,
                receipt_hash: "ef".repeat(32),
                turn_hash: "01".repeat(32),
                cells: vec!["22".repeat(32)],
                kinds: vec!["set_field".into()],
                height: 1888,
                has_proof: false,
                finality: "committed".into(),
                timestamp: 1_718_000_042,
            },
        ]
    }

    pub fn federations() -> Vec<FederationInfo> {
        vec![FederationInfo {
            id: "local".into(),
            federation_id: "f0".repeat(32),
            committee_epoch: 7,
            threshold: 3,
            member_count: 5,
            members: (0..5).map(|i| format!("{:02x}", i).repeat(32)).collect(),
            is_local: true,
            latest_height: 142,
            latest_root: Some("9a".repeat(32)),
            num_finalized_roots: 142,
        }]
    }

    pub fn blocks() -> Vec<BlockInfo> {
        (1880..1888)
            .rev()
            .map(|h| BlockInfo {
                height: h,
                hash: format!("{h:04x}").repeat(16),
                creator: "11".repeat(32),
                seq: h,
            })
            .collect()
    }

    /// A demo turn the TurnComposer view starts from.
    pub fn sample_turn() -> SubmitTurnRequest {
        SubmitTurnRequest {
            agent: "11".repeat(32),
            nonce: 13,
            fee: 1,
            memo: Some("starbridge-v2 demo turn".into()),
            actions: vec![TurnActionSpec {
                target: Some("33".repeat(32)),
                method: Some("submit".into()),
                effects: vec![
                    TurnEffectSpec::Transfer {
                        from: Some("11".repeat(32)),
                        to: "33".repeat(32),
                        amount: 250,
                    },
                    TurnEffectSpec::EmitEvent {
                        cell: None,
                        topic: "greeting".into(),
                        data: vec!["0x01".into()],
                    },
                ],
            }],
        }
    }
}

// ===========================================================================
// THE LIVE NODE CONNECTION — snapshot sync + the background SSE reader.
//
// This is the I/O driver the embedded master interface's LIVE-NODE panel owns. It
// pairs a [`NodeClient`] with the live-reflection model (`crate::live_node`):
//   * `sync()` does the blocking snapshot reads (`/status`, `/api/cells`,
//     `/api/receipts`) and projects them into the uniform `Inspectable` model.
//   * `connect_stream()` spawns a BACKGROUND THREAD that pulls the
//     `/api/events/stream` SSE socket and feeds each chunk into the PURE
//     `SseParser`, pushing decoded receipts onto an mpsc channel. The cockpit owns
//     the receiver and drains it each frame under `cx.notify()` — so the gpui side
//     stays single-threaded and the ReceiptInspector advances LIVE (per receipt),
//     replacing the static snapshot. The reader auto-reconnects, resuming from the
//     `Last-Event-ID` cursor the channel's consumer reports back.
//
// The pure parse/reflect/feed live in `crate::live_node` (tested with byte
// fixtures, no socket); this is only the byte source + the thread plumbing.
// ===========================================================================

/// A live connection to a node: a [`NodeClient`] plus the reflection model. The
/// snapshot sync is always available (the byte-pull is `live-node`-gated inside
/// `http_get`); the SSE reader is `connect_stream`.
#[cfg(feature = "embedded-executor")]
pub struct LiveNode {
    client: NodeClient,
}

#[cfg(feature = "embedded-executor")]
impl LiveNode {
    /// Wrap a client (typically `NodeClient::http(base_url)`).
    pub fn new(client: NodeClient) -> Self {
        LiveNode { client }
    }

    /// The underlying client (for the writes surface / describe).
    pub fn client(&self) -> &NodeClient {
        &self.client
    }

    /// Blocking SNAPSHOT sync: fetch `/status` + `/api/cells` and project them
    /// into the uniform reflective model. Returns the node's status reflection +
    /// one cell reflection per live cell (the inspector renders these identically
    /// to embedded-world cells — no parallel view path). Errors propagate (an
    /// unreachable node surfaces honestly).
    ///
    /// The cockpit calls this off the gpui thread (or on a one-shot button) and
    /// re-renders from the result; the per-receipt LIVE updates come from
    /// [`LiveNode::connect_stream`], not this.
    pub fn sync(&self) -> anyhow::Result<LiveSnapshot> {
        let status = self.client.status()?;
        let cells = self.client.cells()?;
        let status_view = crate::live_node::LiveReflection::reflect_status(
            &self.client.describe(),
            &status,
        );
        let cell_views = cells
            .iter()
            .map(crate::live_node::LiveReflection::reflect_cell_entry)
            .collect();
        Ok(LiveSnapshot {
            status,
            status_view,
            cell_views,
        })
    }

    /// Spawn the BACKGROUND SSE READER (the live receipt nervous-system tap).
    ///
    /// Returns a [`ReceiptStreamHandle`]: the cockpit holds the `rx` and drains it
    /// each frame (each drained [`ReceiptEvent`] is a `cx.notify()`). The reader
    /// thread pulls `/api/events/stream`, feeds chunks into the pure
    /// [`crate::live_node::SseParser`], and auto-reconnects (resuming from the last
    /// delivered chain index) until the receiver is dropped. `None` for a mock
    /// backend (no stream) or when `live-node` is off.
    #[cfg(feature = "live-node")]
    pub fn connect_stream(&self) -> Option<ReceiptStreamHandle> {
        // Only an Http backend has a stream; the reader rebuilds the URL itself
        // (and sets the Last-Event-ID resume header) per connect attempt.
        let base = match &self.client {
            NodeClient::Http { base_url } => base_url.clone(),
            NodeClient::Mock => return None,
        };
        let (tx, rx) = std::sync::mpsc::channel::<crate::live_node::SseRecord>();
        let stop = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
        let stop_reader = stop.clone();
        let handle = std::thread::Builder::new()
            .name("starbridge-sse".into())
            .spawn(move || sse_reader_loop(base, tx, stop_reader))
            .ok()?;
        Some(ReceiptStreamHandle {
            rx,
            stop,
            _join: Some(handle),
        })
    }

    /// On a non-`live-node` build there is no reader; the panel falls back to the
    /// snapshot (`sync`) or the mock.
    #[cfg(not(feature = "live-node"))]
    pub fn connect_stream(&self) -> Option<ReceiptStreamHandle> {
        None
    }
}

/// A blocking snapshot of a live node, projected into the uniform reflective
/// model (the inspector renders these the same as embedded-world objects).
#[cfg(feature = "embedded-executor")]
pub struct LiveSnapshot {
    /// The raw status (for the header / producer badge).
    pub status: NodeStatus,
    /// The status reflection (the distribution-axis object).
    pub status_view: crate::reflect::Inspectable,
    /// One reflection per live cell.
    pub cell_views: Vec<crate::reflect::Inspectable>,
}

/// The handle the cockpit holds onto a running SSE reader. Dropping it signals the
/// reader thread to stop (the next read/reconnect observes the flag and exits).
#[cfg(feature = "embedded-executor")]
pub struct ReceiptStreamHandle {
    /// Decoded receipts as they stream in — the cockpit drains this each frame and
    /// fires a `cx.notify()` per record. Empty (would-block) between commits.
    pub rx: std::sync::mpsc::Receiver<crate::live_node::SseRecord>,
    stop: std::sync::Arc<std::sync::atomic::AtomicBool>,
    /// The reader thread join handle (joined on drop, best-effort).
    _join: Option<std::thread::JoinHandle<()>>,
}

#[cfg(feature = "embedded-executor")]
impl ReceiptStreamHandle {
    /// Non-blocking drain of every record that arrived since the last call. The
    /// cockpit calls this each frame; each returned record is one `cx.notify()`.
    pub fn drain(&self) -> Vec<crate::live_node::SseRecord> {
        self.rx.try_iter().collect()
    }
}

#[cfg(feature = "embedded-executor")]
impl Drop for ReceiptStreamHandle {
    fn drop(&mut self) {
        self.stop.store(true, std::sync::atomic::Ordering::Relaxed);
        if let Some(h) = self._join.take() {
            // Best-effort: the reader observes `stop` on its next read boundary.
            // We don't block shutdown on a slow socket — detach if it lingers.
            let _ = h;
        }
    }
}

/// The background SSE reader loop: pull `/api/events/stream`, feed the pure
/// parser, push decoded receipts onto `tx`, and reconnect (resuming from the last
/// delivered chain index) until `stop` is set or the receiver is gone.
#[cfg(all(feature = "embedded-executor", feature = "live-node"))]
fn sse_reader_loop(
    base_url: String,
    tx: std::sync::mpsc::Sender<crate::live_node::SseRecord>,
    stop: std::sync::Arc<std::sync::atomic::AtomicBool>,
) {
    use std::io::Read;
    use std::sync::atomic::Ordering;

    let client = NodeClient::http(&base_url);
    let mut resume: Option<u64> = None;
    while !stop.load(Ordering::Relaxed) {
        // The stream URL (no resume in the query — the node resumes from the
        // `Last-Event-ID` HEADER, which is the protocol's mechanism per
        // `node/src/events.rs`; we set that header below from `resume`).
        let Some(url) = client.events_stream_url(None) else {
            return;
        };
        // A long-lived streaming GET. reqwest blocking returns a `Response` whose
        // body we read in chunks (the stream stays open; reads block until the
        // node sends the next receipt or a heartbeat). On a RECONNECT we send
        // `Last-Event-ID: <resume>` so the node tails AFTER the last delivered
        // chain index (at-least-once across reconnects; the feed dedups).
        let mut req = match reqwest::blocking::Client::builder()
            .timeout(None) // no overall timeout — it's a long-lived stream
            .build()
        {
            Ok(c) => c.get(&url),
            Err(_) => {
                if backoff_or_stop(&stop) {
                    return;
                }
                continue;
            }
        };
        if let Some(id) = resume {
            req = req.header("Last-Event-ID", id.to_string());
        }
        let resp = match req.send() {
            Ok(r) => r,
            Err(_) => {
                // Connection failed — back off and retry (resuming from `resume`).
                if backoff_or_stop(&stop) {
                    return;
                }
                continue;
            }
        };
        let mut resp = resp;
        let mut parser = crate::live_node::SseParser::new();
        let mut chunk = [0u8; 4096];
        loop {
            if stop.load(Ordering::Relaxed) {
                return;
            }
            match resp.read(&mut chunk) {
                Ok(0) => break, // server closed — reconnect (resume cursor held)
                Ok(n) => {
                    for rec in parser.push(&chunk[..n]) {
                        if let Some(id) = rec.id {
                            resume = Some(id);
                        }
                        // The receiver was dropped (cockpit closed the panel) —
                        // stop the reader.
                        if tx.send(rec).is_err() {
                            return;
                        }
                    }
                }
                Err(_) => break, // read error — reconnect
            }
        }
        if backoff_or_stop(&stop) {
            return;
        }
    }
}

/// Sleep a short reconnect backoff in small steps, checking `stop` so a dropped
/// handle shuts the reader down promptly. Returns `true` if `stop` was observed
/// (the caller should return).
#[cfg(all(feature = "embedded-executor", feature = "live-node"))]
fn backoff_or_stop(stop: &std::sync::atomic::AtomicBool) -> bool {
    use std::sync::atomic::Ordering;
    for _ in 0..10 {
        if stop.load(Ordering::Relaxed) {
            return true;
        }
        std::thread::sleep(std::time::Duration::from_millis(100));
    }
    false
}
