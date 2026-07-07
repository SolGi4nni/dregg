//! # The CLIENT-SIDE `NodeWorldSink` — inhabit a remote box's node over HTTP.
//!
//! Pillar 0 of the distributed-deos goal: a [`deos_js::WorldSink`] a remote
//! inhabitation process uses to drive a node running on ANOTHER box. It is the
//! HTTP-CLIENT half of [`node`'s in-process `NodeWorldSink`](../../node/src/deos_host.rs):
//! same trait, same semantics (which cell a turn binds, the real receipt hash a
//! commit returns), reached over the wire instead of a shared `NodeState`.
//!
//!   * **the crawl** ([`NodeHttpClient::fetch_ledger_snapshot`]) rebuilds a
//!     SNAPSHOT [`Ledger`] from `GET /api/cells` (the id list) + `GET
//!     /api/cell/{id}` (per-cell detail). This is the SAME fidelity bar the
//!     world-bridge's `WithLedger` set: it snapshots cells (public_key, token,
//!     fields, balance, nonce, delegate) — enough for the reflective crawl
//!     (`CellModel`/`reflect`) — NOT a byte-perfect `Ledger` (no sovereign
//!     commitments, no reconstructed programs; the crawl does not read them).
//!   * **the commit** ([`NodeHttpClient::submit_turn`]) builds a signed
//!     [`Turn`] the EXACT way [`crate::deos_server::fire_affordance`] does (the
//!     agent's fresh nonce off the node, the receipt-chain head threaded, the
//!     computron fee estimated, the action signed over the executor's federation
//!     id) and POSTs the postcard `SignedTurn` to `/turns/submit`. Fail-CLOSED:
//!     an HTTP error or a node refusal is `Err`, never a silent success.
//!
//! The node re-checks every effect against its verified executor's authority
//! gate, so an over-reaching effect is refused BY THE NODE (an `Err` out of
//! `fire_effects`), not by this sink — the sink carries no cap tooth (that lives
//! above it, in `deos_js::AttachedApplet`).
//!
//! The [`WorldSink`](deos_js::WorldSink) impl over this client lives behind the
//! `world-sink` feature so the base net layer stays free of the `deos-js`
//! (SpiderMonkey) dependency; the light HTTP client here carries no such dep.

use dregg_cell::state::FieldElement;
use dregg_cell::{Cell, Ledger};
use dregg_sdk::AgentCipherclerk;
use dregg_sdk::error::SdkError;
use dregg_turn::action::Effect;
use dregg_turn::{ComputronCosts, Turn, TurnExecutor};
use dregg_types::CellId;

/// The light HTTP client half — ALWAYS compiled, no `deos-js` dependency.
///
/// It speaks the node's public REST surface: the explorer reads (`/api/cells`,
/// `/api/cell/{id}`, `/api/receipts`) and the signed-turn ingress
/// (`/turns/submit`). Every method is fail-closed.
#[derive(Clone, Debug)]
pub struct NodeHttpClient {
    base_url: String,
    http: reqwest::Client,
}

impl NodeHttpClient {
    /// A client for the node reachable at `base_url` (e.g. `http://box-2.local:8080`).
    pub fn new(base_url: impl Into<String>) -> Self {
        let base_url = base_url.into().trim_end_matches('/').to_string();
        NodeHttpClient {
            base_url,
            http: reqwest::Client::new(),
        }
    }

    /// The node base URL (already trimmed of a trailing slash).
    pub fn base_url(&self) -> &str {
        &self.base_url
    }

    // ─────────────────────────── the crawl (read) ───────────────────────────

    /// Rebuild a SNAPSHOT [`Ledger`] from the node's explorer surface: `GET
    /// /api/cells` for the id list, then `GET /api/cell/{id}` per cell for the
    /// detail. Snapshots cells only (the crawl surface `CellModel`/`reflect`
    /// walks); it does NOT reconstruct sovereign commitments or programs.
    ///
    /// Fail-closed: any HTTP/JSON error is an `Err`, so a caller never mistakes a
    /// degraded read for an empty world.
    pub async fn fetch_ledger_snapshot(&self) -> Result<Ledger, SdkError> {
        let list_url = format!("{}/api/cells", self.base_url);
        let list: serde_json::Value = self.get_json(&list_url).await?;
        let ids: Vec<String> = list
            .as_array()
            .ok_or_else(|| SdkError::Wire("/api/cells did not return an array".into()))?
            .iter()
            .filter_map(|e| e.get("id").and_then(|i| i.as_str()).map(String::from))
            .collect();

        let mut ledger = Ledger::new();
        for id in ids {
            let detail_url = format!("{}/api/cell/{}", self.base_url, id);
            let detail: serde_json::Value = self.get_json(&detail_url).await?;
            if let Some(cell) = cell_from_detail(&detail) {
                // insert_cell only re-checks id uniqueness; a detail whose fields
                // fail to rebuild a content-addressed cell is skipped (never a
                // substitute cell, never a hard fail of the whole crawl).
                let _ = ledger.insert_cell(cell);
            }
        }
        Ok(ledger)
    }

    // ────────────────────────── the commit (write) ──────────────────────────

    /// Build a signed [`Turn`] under `signer` (acting AS its own cell `agent`)
    /// carrying `effects`, named `method`, and POST it to `/turns/submit`.
    /// Returns the REAL receipt hash the node recorded for the committed turn.
    ///
    /// The flow mirrors [`crate::deos_server::fire_affordance`] exactly:
    ///   1. read `agent`'s current nonce (`GET /api/cell/{agent}`) + the node's
    ///      receipt-chain head (`GET /api/receipts`);
    ///   2. build a single-action turn (`signer.make_action` over `effects`,
    ///      signed against `federation_id`), thread the chain head as
    ///      `previous_receipt_hash`, and stamp `fee` = the estimated computron
    ///      cost (a pure function of the effects);
    ///   3. POST the postcard `SignedTurn` and read the verdict. On accept,
    ///      resolve the committed turn's `receipt_hash` off `/api/receipts`.
    ///
    /// Fail-closed: a transport error, a node rejection (`accepted != true`), or
    /// a committed turn not yet visible on `/api/receipts` all return `Err`.
    pub async fn submit_turn(
        &self,
        signer: &AgentCipherclerk,
        agent: CellId,
        method: &str,
        effects: Vec<Effect>,
        federation_id: &[u8; 32],
    ) -> Result<[u8; 32], SdkError> {
        // (1) the agent's fresh nonce + the node's chain head.
        let nonce = self.fetch_cell_nonce(&agent).await?;
        let chain_head = self.fetch_chain_head().await?;

        // (2) build + sign the single-action fire turn (the deos_server shape).
        let action = signer.make_action(agent, method, effects, federation_id);
        let mut turn: Turn = signer.make_turn_with_actions(vec![action]);
        turn.agent = agent;
        turn.nonce = nonce;
        turn.memo = Some(format!("node_world_sink_{method}"));
        turn.valid_until = Some(i64::MAX / 2);
        turn.previous_receipt_hash = chain_head;
        turn.fee = TurnExecutor::new(ComputronCosts::default()).estimate_cost(&turn);

        let signed = signer.sign_turn(&turn);
        let signed_bytes = postcard::to_stdvec(&signed)
            .map_err(|e| SdkError::Wire(format!("serialize SignedTurn: {e}")))?;

        // (3) POST the postcard SignedTurn to the signed-turn ingress.
        let url = format!("{}/turns/submit", self.base_url);
        let resp = self
            .http
            .post(&url)
            .header("Content-Type", "application/octet-stream")
            .body(signed_bytes)
            .send()
            .await
            .map_err(|e| SdkError::Wire(format!("turns/submit request failed: {e}")))?;
        if !resp.status().is_success() {
            return Err(SdkError::Wire(format!(
                "turns/submit returned status {}",
                resp.status()
            )));
        }
        let body: serde_json::Value = resp
            .json()
            .await
            .map_err(|e| SdkError::Wire(format!("parse submit response: {e}")))?;

        let accepted = body
            .get("accepted")
            .and_then(|a| a.as_bool())
            .unwrap_or(false);
        if !accepted {
            let reason = body
                .get("error")
                .and_then(|e| e.as_str())
                .unwrap_or("node refused the turn (no reason given)");
            return Err(SdkError::Wire(format!("turn refused by node: {reason}")));
        }
        let turn_hash = body
            .get("turn_hash")
            .and_then(|h| h.as_str())
            .ok_or_else(|| SdkError::Wire("accepted submit response missing turn_hash".into()))?
            .to_string();

        // Resolve the REAL receipt hash for the committed turn off /api/receipts.
        // (The submit response attests the turn hash; the sink's contract is the
        // receipt hash, the same value the in-process NodeWorldSink returns.)
        self.resolve_receipt_hash(&turn_hash).await
    }

    /// The executor's federation id — the binding a fire action is signed over.
    /// A remote client cannot derive it: an unconfigured/solo node uses
    /// `blake3(node_public_key)` (from `GET /status`), a configured federation
    /// uses its raw `federation_id` (from `GET /api/federation`). For a
    /// federation whose configured/solo state is ambiguous, obtain the id from
    /// [`crate::deos_server::discover_server_affordances`] (the proven source
    /// that hands back `executor_federation_id`) and pass it explicitly.
    pub async fn fetch_executor_federation_id(&self) -> Result<[u8; 32], SdkError> {
        let status: serde_json::Value = self.get_json(&format!("{}/status", self.base_url)).await?;
        let mode = status
            .get("federation_mode")
            .and_then(|m| m.as_str())
            .unwrap_or("solo");
        if mode == "solo" {
            let pk_hex = status
                .get("public_key")
                .and_then(|p| p.as_str())
                .ok_or_else(|| SdkError::Wire("/status missing public_key".into()))?;
            let pk = decode_32(pk_hex).ok_or_else(|| {
                SdkError::Wire("/status public_key is not 32 bytes of hex".into())
            })?;
            Ok(*blake3::hash(&pk).as_bytes())
        } else {
            let fed: serde_json::Value = self
                .get_json(&format!("{}/api/federation", self.base_url))
                .await?;
            let fid_hex = fed
                .get("federation_id")
                .and_then(|f| f.as_str())
                .ok_or_else(|| SdkError::Wire("/api/federation missing federation_id".into()))?;
            decode_32(fid_hex)
                .ok_or_else(|| SdkError::Wire("federation_id is not 32 bytes of hex".into()))
        }
    }

    /// `GET /api/cell/{id}` → the cell's current nonce (the executor rejects a
    /// stale nonce, so a fire must use this fresh value).
    pub async fn fetch_cell_nonce(&self, cell: &CellId) -> Result<u64, SdkError> {
        let url = format!(
            "{}/api/cell/{}",
            self.base_url,
            dregg_types::hex_encode(cell.as_bytes())
        );
        let body: serde_json::Value = self.get_json(&url).await?;
        if body.get("found").and_then(|f| f.as_bool()) != Some(true) {
            return Err(SdkError::Wire(format!(
                "agent cell {} not found on the node",
                dregg_types::hex_encode(cell.as_bytes())
            )));
        }
        Ok(body.get("nonce").and_then(|n| n.as_u64()).unwrap_or(0))
    }

    /// `GET /api/receipts` → the `receipt_hash` of the entry flagged
    /// `chain_head` (`None` when the chain is empty). The executor requires a
    /// turn to thread this head.
    pub async fn fetch_chain_head(&self) -> Result<Option<[u8; 32]>, SdkError> {
        let url = format!("{}/api/receipts", self.base_url);
        let body: serde_json::Value = self.get_json(&url).await?;
        let head_hex = body.as_array().and_then(|arr| {
            arr.iter()
                .find(|r| r.get("chain_head").and_then(|h| h.as_bool()) == Some(true))
                .and_then(|r| r.get("receipt_hash"))
                .and_then(|h| h.as_str())
        });
        match head_hex {
            Some(hex) => decode_32(hex).map(Some).ok_or_else(|| {
                SdkError::Wire("chain-head receipt_hash is not 32 hex bytes".into())
            }),
            None => Ok(None),
        }
    }

    /// Find the committed turn `turn_hash` on `/api/receipts` and return its
    /// `receipt_hash`. Fail-closed: a committed turn not yet visible (finality /
    /// gossip lag — the Pillar-2 handoff) is an `Err`, never a fabricated hash.
    async fn resolve_receipt_hash(&self, turn_hash: &str) -> Result<[u8; 32], SdkError> {
        let url = format!("{}/api/receipts", self.base_url);
        let body: serde_json::Value = self.get_json(&url).await?;
        let receipt_hex = body
            .as_array()
            .and_then(|arr| {
                arr.iter()
                    .find(|r| r.get("turn_hash").and_then(|t| t.as_str()) == Some(turn_hash))
                    .and_then(|r| r.get("receipt_hash"))
                    .and_then(|h| h.as_str())
            })
            .ok_or_else(|| {
                SdkError::Wire(format!(
                    "committed turn {turn_hash} not yet visible on /api/receipts \
                     (finality/gossip lag)"
                ))
            })?;
        decode_32(receipt_hex)
            .ok_or_else(|| SdkError::Wire("receipt_hash is not 32 bytes of hex".into()))
    }

    /// GET a URL and parse its JSON body, mapping every failure to `SdkError`.
    async fn get_json(&self, url: &str) -> Result<serde_json::Value, SdkError> {
        let resp = self
            .http
            .get(url)
            .send()
            .await
            .map_err(|e| SdkError::Wire(format!("GET {url} failed: {e}")))?;
        if !resp.status().is_success() {
            return Err(SdkError::Wire(format!(
                "GET {url} returned {}",
                resp.status()
            )));
        }
        resp.json()
            .await
            .map_err(|e| SdkError::Wire(format!("parse {url}: {e}")))
    }
}

/// Rebuild a [`Cell`] from a `GET /api/cell/{id}` detail JSON — the crawl-fidelity
/// snapshot (public_key, token, fields, balance, nonce, delegate). Returns `None`
/// if the detail is not a found cell or its key/token are malformed.
fn cell_from_detail(v: &serde_json::Value) -> Option<Cell> {
    if v.get("found").and_then(|f| f.as_bool()) != Some(true) {
        return None;
    }
    let public_key = decode_32(v.get("public_key")?.as_str()?)?;
    let token_id = decode_32(v.get("token_id")?.as_str()?)?;
    let balance = v.get("balance").and_then(|b| b.as_i64()).unwrap_or(0);

    let mut cell = Cell::with_balance(public_key, token_id, balance);
    if let Some(nonce) = v.get("nonce").and_then(|n| n.as_u64()) {
        cell.state.set_nonce(nonce);
    }
    if let Some(fields) = v.get("fields").and_then(|f| f.as_array()) {
        for (i, f) in fields.iter().enumerate() {
            if let Some(felt) = f.as_str().and_then(decode_32) {
                let felt: FieldElement = felt;
                cell.state.set_field(i, felt);
            }
        }
    }
    if let Some(del) = v.get("delegate").and_then(|d| d.as_str()) {
        if let Some(bytes) = decode_32(del) {
            cell.delegate = Some(CellId(bytes));
        }
    }
    Some(cell)
}

/// Decode a 64-char hex string into a 32-byte array. `None` on malformed input.
fn decode_32(s: &str) -> Option<[u8; 32]> {
    let s = s.trim();
    if s.len() != 64 {
        return None;
    }
    let mut out = [0u8; 32];
    for (i, byte) in out.iter_mut().enumerate() {
        *byte = u8::from_str_radix(s.get(i * 2..i * 2 + 2)?, 16).ok()?;
    }
    Some(out)
}

// ───────────────────────── the WorldSink impl (feature-gated) ────────────────

#[cfg(feature = "world-sink")]
pub use sink::NodeWorldSink;

#[cfg(feature = "world-sink")]
mod sink {
    use super::*;
    use deos_js::WorldSink;

    /// A [`deos_js::WorldSink`] over a REMOTE node's HTTP API — the client half of
    /// the in-process `node::deos_host::NodeWorldSink`. `with_ledger` runs the
    /// crawl closure over a freshly-fetched snapshot ledger; `fire_effects`
    /// submits a signed turn and returns the real receipt hash.
    ///
    /// The [`WorldSink`] trait methods are synchronous, so the sink owns a
    /// current-thread tokio [`Runtime`](tokio::runtime::Runtime) it blocks the
    /// async HTTP calls on. Like the in-process sink (which requires a non-worker
    /// thread), it must be driven OFF a tokio worker thread — the remote
    /// inhabitation process is a plain program, not an async task.
    pub struct NodeWorldSink {
        client: NodeHttpClient,
        cipherclerk: AgentCipherclerk,
        agent: CellId,
        federation_id: [u8; 32],
        rt: tokio::runtime::Runtime,
    }

    impl NodeWorldSink {
        /// Attach to the node at `base_url`, committing turns AS `cipherclerk`'s
        /// default cell, signed over `federation_id` (the node's executor
        /// federation id — see [`NodeHttpClient::fetch_executor_federation_id`]).
        pub fn new(
            base_url: impl Into<String>,
            cipherclerk: AgentCipherclerk,
            federation_id: [u8; 32],
        ) -> Result<Self, SdkError> {
            let default_token_id = *blake3::hash(b"default").as_bytes();
            let agent = CellId::derive_raw(&cipherclerk.public_key().0, &default_token_id);
            let rt = tokio::runtime::Builder::new_current_thread()
                .enable_all()
                .build()
                .map_err(|e| SdkError::Wire(format!("build sink runtime: {e}")))?;
            Ok(NodeWorldSink {
                client: NodeHttpClient::new(base_url),
                cipherclerk,
                agent,
                federation_id,
                rt,
            })
        }

        /// The agent cell every turn from this sink binds (the cipherclerk's
        /// default cell).
        pub fn agent(&self) -> CellId {
            self.agent
        }

        /// The light HTTP client underneath (for direct reads).
        pub fn client(&self) -> &NodeHttpClient {
            &self.client
        }
    }

    impl WorldSink for NodeWorldSink {
        fn with_ledger(&self, f: &mut dyn FnMut(&Ledger)) {
            // Fail-soft on the read, exactly like the world-bridge crawl: a fetch
            // fault means `f` is NOT run (a degraded read of nothing — never a
            // substitute world).
            if let Ok(ledger) = self.rt.block_on(self.client.fetch_ledger_snapshot()) {
                f(&ledger);
            }
        }

        fn fire_effects(
            &mut self,
            agent: CellId,
            method: &str,
            effects: Vec<Effect>,
        ) -> Result<[u8; 32], String> {
            self.rt
                .block_on(self.client.submit_turn(
                    &self.cipherclerk,
                    agent,
                    method,
                    effects,
                    &self.federation_id,
                ))
                .map_err(|e| e.to_string())
        }

        // `mint_open_cell` keeps the trait default (an `Err`): minting an open
        // cell is a privileged host-ledger op, not reachable over the signed-turn
        // ingress — a remote client cannot mint. (The in-process host sink is the
        // one that implements it.)
    }
}

#[cfg(all(test, feature = "world-sink"))]
mod tests {
    use super::*;
    use std::sync::Arc;

    use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
    use dregg_turn::{TurnReceipt, TurnResult};
    use tokio::io::{AsyncReadExt, AsyncWriteExt};
    use tokio::net::TcpListener;
    use tokio::sync::Mutex;

    // A fully-open permission set (every action AuthRequired::None) so a SetField
    // on the agent's own cell authorizes without a grant.
    fn open_permissions() -> Permissions {
        Permissions {
            send: AuthRequired::None,
            receive: AuthRequired::None,
            set_state: AuthRequired::None,
            set_permissions: AuthRequired::None,
            set_verification_key: AuthRequired::None,
            increment_nonce: AuthRequired::None,
            delegate: AuthRequired::None,
            access: AuthRequired::None,
        }
    }

    fn default_token_id() -> [u8; 32] {
        *blake3::hash(b"default").as_bytes()
    }

    /// The minimal in-process test NODE: a real `dregg_cell::Ledger` driven by the
    /// REAL `dregg_turn::TurnExecutor` (so the authority gate — the refusal pole —
    /// is genuine), plus the receipt chain the client threads. It cannot depend on
    /// the `node` crate (that crate depends on `dregg-sdk-net`, a cycle), so it
    /// serves just the four routes the client speaks over hand-rolled HTTP/1.1.
    struct TestNode {
        ledger: Ledger,
        receipts: Vec<TurnReceipt>,
        fed_id: [u8; 32],
        node_public_key: [u8; 32],
    }

    impl TestNode {
        fn chain_head(&self) -> Option<[u8; 32]> {
            self.receipts.last().map(|r| r.receipt_hash())
        }
    }

    /// Execute a submitted postcard `SignedTurn` through the REAL executor,
    /// mirroring `node::api::post_submit_signed_turn`'s checks. Returns the JSON
    /// body the client parses.
    fn handle_submit(node: &mut TestNode, body: &[u8]) -> serde_json::Value {
        let signed: dregg_sdk::SignedTurn = match postcard::from_bytes(body) {
            Ok(s) => s,
            Err(_) => {
                return serde_json::json!({"accepted": false, "error": "malformed SignedTurn"});
            }
        };
        let turn_hash = signed.turn.hash();
        if !signed.signer.verify(&turn_hash, &signed.signature) {
            return serde_json::json!({
                "accepted": false,
                "turn_hash": dregg_types::hex_encode(&turn_hash),
                "error": "invalid turn signature",
            });
        }
        let expected_agent = CellId::derive_raw(&signed.signer.0, &default_token_id());
        if signed.turn.agent != expected_agent {
            return serde_json::json!({
                "accepted": false,
                "turn_hash": dregg_types::hex_encode(&turn_hash),
                "error": "turn agent does not match signer default cell",
            });
        }
        if signed.turn.previous_receipt_hash != node.chain_head() {
            return serde_json::json!({
                "accepted": false,
                "turn_hash": dregg_types::hex_encode(&turn_hash),
                "error": "receipt chain mismatch",
            });
        }

        let mut executor = TurnExecutor::new(ComputronCosts::default());
        executor.set_local_federation_id(node.fed_id);
        executor.set_timestamp(0);
        match executor.execute(&signed.turn, &mut node.ledger) {
            TurnResult::Committed { receipt, .. } => {
                node.receipts.push(receipt);
                serde_json::json!({
                    "accepted": true,
                    "turn_hash": dregg_types::hex_encode(&turn_hash),
                })
            }
            TurnResult::Rejected { reason, .. } => serde_json::json!({
                "accepted": false,
                "turn_hash": dregg_types::hex_encode(&turn_hash),
                "error": format!("{reason}"),
            }),
            other => serde_json::json!({
                "accepted": false,
                "turn_hash": dregg_types::hex_encode(&turn_hash),
                "error": format!("unexpected result: {other:?}"),
            }),
        }
    }

    fn cell_detail_json(id_hex: &str, node: &TestNode) -> serde_json::Value {
        let bytes = match decode_32(id_hex) {
            Some(b) => b,
            None => return serde_json::json!({"id": id_hex, "found": false}),
        };
        match node.ledger.get(&CellId(bytes)) {
            Some(cell) => serde_json::json!({
                "id": id_hex,
                "found": true,
                "balance": cell.state.balance(),
                "nonce": cell.state.nonce(),
                "public_key": dregg_types::hex_encode(cell.public_key()),
                "token_id": dregg_types::hex_encode(cell.token_id()),
                "delegate": cell.delegate.as_ref().map(|d| dregg_types::hex_encode(&d.0)),
                "fields": cell.state.fields.iter()
                    .map(|f| dregg_types::hex_encode(f)).collect::<Vec<_>>(),
            }),
            None => serde_json::json!({"id": id_hex, "found": false}),
        }
    }

    fn receipts_json(node: &TestNode) -> serde_json::Value {
        let last = node.receipts.len().saturating_sub(1);
        let arr: Vec<serde_json::Value> = node
            .receipts
            .iter()
            .enumerate()
            .map(|(i, r)| {
                serde_json::json!({
                    "chain_index": i as u64,
                    "chain_head": i == last,
                    "receipt_hash": dregg_types::hex_encode(&r.receipt_hash()),
                    "turn_hash": dregg_types::hex_encode(&r.turn_hash),
                })
            })
            .collect();
        serde_json::Value::Array(arr)
    }

    /// Serve one HTTP/1.1 request on `sock` against the shared node.
    async fn handle_conn(mut sock: tokio::net::TcpStream, node: Arc<Mutex<TestNode>>) {
        // Read headers (until CRLFCRLF), then Content-Length body.
        let mut buf = Vec::new();
        let mut tmp = [0u8; 4096];
        let header_end = loop {
            match sock.read(&mut tmp).await {
                Ok(0) => return,
                Ok(n) => {
                    buf.extend_from_slice(&tmp[..n]);
                    if let Some(pos) = find_subslice(&buf, b"\r\n\r\n") {
                        break pos;
                    }
                }
                Err(_) => return,
            }
        };
        let header_str = String::from_utf8_lossy(&buf[..header_end]).to_string();
        let mut lines = header_str.split("\r\n");
        let request_line = lines.next().unwrap_or("");
        let mut parts = request_line.split_whitespace();
        let method = parts.next().unwrap_or("").to_string();
        let path = parts.next().unwrap_or("").to_string();
        let content_length = lines
            .find_map(|l| {
                let l = l.to_ascii_lowercase();
                l.strip_prefix("content-length:")
                    .map(|v| v.trim().parse::<usize>().unwrap_or(0))
            })
            .unwrap_or(0);

        let mut body = buf[header_end + 4..].to_vec();
        while body.len() < content_length {
            match sock.read(&mut tmp).await {
                Ok(0) => break,
                Ok(n) => body.extend_from_slice(&tmp[..n]),
                Err(_) => break,
            }
        }

        let json = {
            let mut guard = node.lock().await;
            route(&method, &path, &body, &mut guard)
        };
        let payload = serde_json::to_vec(&json).unwrap();
        let head = format!(
            "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
            payload.len()
        );
        let _ = sock.write_all(head.as_bytes()).await;
        let _ = sock.write_all(&payload).await;
        let _ = sock.flush().await;
    }

    fn route(method: &str, path: &str, body: &[u8], node: &mut TestNode) -> serde_json::Value {
        match (method, path) {
            ("GET", "/api/cells") => {
                let arr: Vec<serde_json::Value> = node
                    .ledger
                    .iter()
                    .map(|(id, cell)| {
                        serde_json::json!({
                            "id": dregg_types::hex_encode(&id.0),
                            "balance": cell.state.balance(),
                            "nonce": cell.state.nonce(),
                        })
                    })
                    .collect();
                serde_json::Value::Array(arr)
            }
            ("GET", "/api/receipts") => receipts_json(node),
            ("GET", "/status") => serde_json::json!({
                "federation_mode": "solo",
                "public_key": dregg_types::hex_encode(&node.node_public_key),
            }),
            ("POST", "/turns/submit") => handle_submit(node, body),
            ("GET", p) if p.starts_with("/api/cell/") => {
                let id_hex = p.trim_start_matches("/api/cell/");
                cell_detail_json(id_hex, node)
            }
            _ => serde_json::json!({"error": "not found"}),
        }
    }

    fn find_subslice(haystack: &[u8], needle: &[u8]) -> Option<usize> {
        haystack.windows(needle.len()).position(|w| w == needle)
    }

    /// Seed a funded open-perms cell for `public_key` and insert it.
    fn seed_open_cell(ledger: &mut Ledger, public_key: [u8; 32], balance: i64) -> CellId {
        let mut cell = Cell::with_balance(public_key, default_token_id(), balance);
        cell.permissions = open_permissions();
        let id = cell.id();
        ledger.insert_cell(cell).expect("seed cell");
        id
    }

    /// BOTH poles on ONE node:
    ///   * `fire_effects` commits a SetField on the agent cell and `with_ledger`
    ///     reads the new value back (the round-trip); and
    ///   * an over-reaching effect (a SetField on a foreign signature-gated cell)
    ///     is REFUSED by the node executor — an `Err` out of `fire_effects`, not a
    ///     sink-side rejection.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn fire_and_crawl_round_trip_then_executor_refuses_overreach() {
        // The agent (the client's identity) and a FOREIGN owner whose cell the
        // agent cannot write.
        let clerk = AgentCipherclerk::new();
        let foreign = AgentCipherclerk::new();
        let agent_pk = clerk.public_key().0;
        let foreign_pk = foreign.public_key().0;

        let fed_id = *blake3::hash(&agent_pk).as_bytes(); // arbitrary but shared
        let node_public_key = agent_pk; // so /status → blake3(pk) == fed_id

        let mut ledger = Ledger::new();
        let agent = seed_open_cell(&mut ledger, agent_pk, 1_000_000);

        // A foreign cell whose set_state REQUIRES the foreign owner's signature —
        // the agent holds neither the key nor a capability, so a SetField on it is
        // an over-reach the executor refuses.
        let mut foreign_cell = Cell::with_balance(foreign_pk, default_token_id(), 1_000_000);
        let mut perms = open_permissions();
        perms.set_state = AuthRequired::Signature;
        foreign_cell.permissions = perms;
        let foreign_id = foreign_cell.id();
        ledger.insert_cell(foreign_cell).expect("seed foreign cell");

        let node = Arc::new(Mutex::new(TestNode {
            ledger,
            receipts: Vec::new(),
            fed_id,
            node_public_key,
        }));

        let listener = TcpListener::bind("127.0.0.1:0").await.expect("bind");
        let addr = listener.local_addr().expect("addr");
        {
            let node = node.clone();
            tokio::spawn(async move {
                loop {
                    match listener.accept().await {
                        Ok((sock, _)) => {
                            let node = node.clone();
                            tokio::spawn(handle_conn(sock, node));
                        }
                        Err(_) => break,
                    }
                }
            });
        }

        let base_url = format!("http://{addr}");

        // Drive the SINK off the tokio runtime (a plain OS thread): the sink owns
        // its own current-thread runtime and blocks on it, exactly as the real
        // (non-async) inhabitation process would.
        let handle = std::thread::spawn(move || {
            let mut sink = NodeWorldSink::new(base_url, clerk, fed_id).expect("build sink");
            use deos_js::WorldSink;

            // ── POLE A: commit + read-back round-trip. ──
            let slot = 3usize;
            let new_value: FieldElement = {
                let mut v = [0u8; 32];
                v[0] = 42;
                v
            };
            // Just the SetField: the executor bumps the agent nonce once per turn
            // (execute.rs:574), so no explicit IncrementNonce is needed (that would
            // double-bump).
            let rh = sink
                .fire_effects(
                    agent,
                    "set_slot",
                    vec![Effect::SetField {
                        cell: agent,
                        index: slot,
                        value: new_value,
                    }],
                )
                .expect("honest SetField must commit");
            assert_ne!(
                rh, [0u8; 32],
                "committed turn must carry a real receipt hash"
            );

            // with_ledger reads the SNAPSHOT back: the new field value landed.
            let mut read_value: Option<FieldElement> = None;
            let mut read_nonce = 0u64;
            sink.with_ledger(&mut |l| {
                if let Some(cell) = l.get(&agent) {
                    read_value = Some(cell.state.fields[slot]);
                    read_nonce = cell.state.nonce();
                }
            });
            assert_eq!(
                read_value,
                Some(new_value),
                "with_ledger must read back the committed field value"
            );
            assert_eq!(
                read_nonce, 1,
                "the nonce bump must be visible in the snapshot"
            );

            // ── POLE B: the node EXECUTOR refuses an over-reach (not the sink). ──
            let refused = sink.fire_effects(
                agent,
                "steal",
                vec![Effect::SetField {
                    cell: foreign_id,
                    index: 0,
                    value: new_value,
                }],
            );
            let err = refused.expect_err("over-reaching SetField must be refused");
            assert!(
                err.contains("refused by node"),
                "refusal must come from the node executor, got: {err}"
            );

            // The refused turn left NO trace: the foreign cell is unchanged.
            let mut foreign_slot0: Option<FieldElement> = None;
            sink.with_ledger(&mut |l| {
                if let Some(c) = l.get(&foreign_id) {
                    foreign_slot0 = Some(c.state.fields[0]);
                }
            });
            assert_eq!(
                foreign_slot0,
                Some([0u8; 32]),
                "a refused over-reach must not mutate the foreign cell"
            );
        });
        handle.join().expect("sink thread");
    }

    /// The federation-id fetch helper resolves a solo node's executor id
    /// (`blake3(node_public_key)`) off `/status`.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn fetch_executor_federation_id_resolves_solo_node() {
        let node_public_key = *blake3::hash(b"some-node-key").as_bytes();
        let fed_id = *blake3::hash(&node_public_key).as_bytes();
        let node = Arc::new(Mutex::new(TestNode {
            ledger: Ledger::new(),
            receipts: Vec::new(),
            fed_id,
            node_public_key,
        }));
        let listener = TcpListener::bind("127.0.0.1:0").await.expect("bind");
        let addr = listener.local_addr().expect("addr");
        {
            let node = node.clone();
            tokio::spawn(async move {
                while let Ok((sock, _)) = listener.accept().await {
                    let node = node.clone();
                    tokio::spawn(handle_conn(sock, node));
                }
            });
        }
        let client = NodeHttpClient::new(format!("http://{addr}"));
        let got = client
            .fetch_executor_federation_id()
            .await
            .expect("fetch fed id");
        assert_eq!(
            got, fed_id,
            "solo executor fed id = blake3(node public key)"
        );
    }
}
