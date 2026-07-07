//! # `dregg-node-target` — the shared federation-routing seam for the flagship fleet
//!
//! Every flagship (`spween-dregg`, `mud-dregg`, `attested-dm`, `commons-arbiter`,
//! `auditable-fund`, `confined-swarm`) mints its turns onto an **in-process** ledger:
//! its own [`dregg_app_framework::EmbeddedExecutor`], `agent_platform::LocalNode`, or
//! commitment-chain. That is real and verifiable, but it is *this process's* ledger —
//! nobody else sees it.
//!
//! [`NodeTarget`] is the one small config that makes the fleet **federation-capable**.
//! A crate holds a `NodeTarget` and, each time it lands a turn, offers that turn's
//! commitment to it:
//!
//! * [`NodeTarget::Local`] — the default. [`route`](NodeTarget::route) is a no-op; the
//!   crate keeps its own in-process ledger. Every existing test stays green + fast, no
//!   network.
//! * [`NodeTarget::Federation`] — the turn's commitment is **submitted to a real node**
//!   (`POST /turn/submit`) and then **confirmed landed** on that node's finalized log
//!   (`GET /api/receipts`). A node that rejects the submit, is unreachable, or does not
//!   show the turn as landed makes [`route`](NodeTarget::route) return [`Err`] — a
//!   forged / failed / non-landing submit is refused, fail-closed.
//!
//! This generalizes the `DREGG_NODE_URL` + Local-default pattern `agent-platform`
//! established (commit `b655a9357`) into a seam the whole fleet shares.
//!
//! ## Honest scope
//!
//! The federation path is **fully wired and testable against a stub node**
//! ([`StubNode`], an in-memory federation node) with NO live server: submit → landed →
//! verified, and a rejecting / broken-link node is refused. The **real cross-node run**
//! — pointing `DREGG_NODE_URL` at ember's live hbox-persvati-nextop federation — is the
//! deploy step (the parallel lane standing that federation up), not the build. The real
//! HTTP transport ([`HttpNode`]) lives behind the `http` feature so the default build +
//! the green wiring tests never touch the network.

use std::sync::{Arc, Mutex};

/// The environment variable a crate reads to pick its [`NodeTarget`]: set it to a node's
/// base URL (e.g. `https://hbox.local:8443`) to route turns through that federation node;
/// leave it unset for the in-process [`NodeTarget::Local`] default.
pub const NODE_URL_ENV: &str = "DREGG_NODE_URL";

/// Why a federation submit did not land.
#[derive(Debug, Clone)]
pub enum NodeError {
    /// The node refused the submitted turn — a forged / non-extending / invalid turn,
    /// or the node's fail-closed finalization gate rejected it. Fail-closed.
    Rejected(String),
    /// The submit could not reach the node (network / HTTP transport failure). Treated
    /// as fail-closed: a turn we cannot confirm landed is not accepted.
    Transport(String),
    /// The submit was accepted by the node's ingress but the turn is NOT present on the
    /// node's finalized read log afterward — it did not actually land.
    NotLanded([u8; 32]),
    /// The [`NodeTarget`] could not be built from its configuration (e.g.
    /// `DREGG_NODE_URL` is set but the `http` feature is not compiled in).
    Config(String),
}

impl std::fmt::Display for NodeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            NodeError::Rejected(m) => write!(f, "federation node rejected turn: {m}"),
            NodeError::Transport(m) => write!(f, "federation transport failure: {m}"),
            NodeError::NotLanded(h) => {
                write!(f, "submitted turn {h:?} is not on the node's finalized log")
            }
            NodeError::Config(m) => write!(f, "node target misconfigured: {m}"),
        }
    }
}

impl std::error::Error for NodeError {}

/// A federation node's identity for a landed turn — the `turn_hash` the node committed
/// it under (which a light client checks against the node's read log).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Landed {
    /// The node's own `turn_hash` for the submitted turn (hex-decoded), the id under
    /// which it appears on `GET /api/receipts`.
    pub node_turn_hash: [u8; 32],
}

/// One minted turn a crate lands in-process and offers to a federation node.
///
/// `commitment` is the crate's own 32-byte per-turn fingerprint: the `TurnReceipt`'s
/// `turn_hash` for an executor-backed crate (`spween-dregg`, `mud-dregg`,
/// `auditable-fund`), or the receipt-id commitment for a commitment-chain crate
/// (`attested-dm`, `commons-arbiter`, `confined-swarm`).
#[derive(Clone, Debug)]
pub struct SubmittedTurn {
    /// The crate's world/domain label (becomes the node event topic).
    pub domain: String,
    /// The crate's own 32-byte per-turn commitment.
    pub commitment: [u8; 32],
    /// The previous submitted turn's commitment, linking the chain — `None` for the
    /// first turn a crate submits. A [`StubNode::linked`] node enforces this link; the
    /// permissive [`StubNode::new`] and the HTTP node do not require it.
    pub prev: Option<[u8; 32]>,
}

impl SubmittedTurn {
    /// A turn submission for `domain` carrying `commitment`, unlinked (`prev = None`).
    pub fn new(domain: impl Into<String>, commitment: [u8; 32]) -> SubmittedTurn {
        SubmittedTurn {
            domain: domain.into(),
            commitment,
            prev: None,
        }
    }

    /// Link this submission to the previous turn's commitment.
    pub fn linked(mut self, prev: [u8; 32]) -> SubmittedTurn {
        self.prev = Some(prev);
        self
    }
}

/// The transport a [`NodeTarget::Federation`] submits through — a real HTTP node
/// ([`HttpNode`]) in production, an in-memory [`StubNode`] in tests. Implementors submit
/// a turn, report whether a turn hash is on the node's finalized log, and structurally
/// verify the log.
pub trait FederationSink: Send + Sync {
    /// Submit a minted turn's commitment to the node. `Ok(Landed)` iff the node accepted
    /// and finalized it; `Err` (fail-closed) if it was rejected or unreachable.
    fn submit(&self, turn: &SubmittedTurn) -> Result<Landed, NodeError>;

    /// Whether `node_turn_hash` (as returned by [`submit`](Self::submit)) is present on
    /// the node's finalized read log — the light-client membership check.
    fn landed(&self, node_turn_hash: &[u8; 32]) -> Result<bool, NodeError>;

    /// Structurally verify the node's finalized log (best-effort; an empty log verifies
    /// vacuously).
    fn verify(&self) -> Result<(), NodeError>;
}

/// **Where a crate routes its minted turns** — the fleet's federation seam.
///
/// [`Local`](Self::Local) is the default: turns stay on the crate's in-process ledger,
/// [`route`](Self::route) is a no-op, no network. [`Federation`](Self::Federation) routes
/// every minted turn to a real node and confirms it landed.
#[derive(Clone)]
pub enum NodeTarget {
    /// In-process only (default). No federation routing.
    Local,
    /// Route every minted turn through this federation node.
    Federation(Arc<dyn FederationSink>),
}

impl Default for NodeTarget {
    fn default() -> Self {
        NodeTarget::Local
    }
}

impl NodeTarget {
    /// The in-process default.
    pub fn local() -> NodeTarget {
        NodeTarget::Local
    }

    /// Route through `sink` (a real [`HttpNode`] or a test [`StubNode`]).
    pub fn federation(sink: Arc<dyn FederationSink>) -> NodeTarget {
        NodeTarget::Federation(sink)
    }

    /// Whether this target is the in-process [`Local`](Self::Local) default.
    pub fn is_local(&self) -> bool {
        matches!(self, NodeTarget::Local)
    }

    /// Whether this target routes to a real federation node.
    pub fn is_federation(&self) -> bool {
        !self.is_local()
    }

    /// **Read [`NODE_URL_ENV`] (`DREGG_NODE_URL`) to pick the target.** Set → a
    /// [`Federation`](Self::Federation) over an [`HttpNode`] at that URL (the fleet is
    /// one env var from a real federation); unset → the [`Local`](Self::Local) default.
    ///
    /// Without the `http` feature a set `DREGG_NODE_URL` is a [`NodeError::Config`] (the
    /// transport is not compiled in) rather than a silent fallback to Local — so a
    /// misconfigured deploy fails loudly.
    pub fn from_env() -> Result<NodeTarget, NodeError> {
        match std::env::var(NODE_URL_ENV) {
            Ok(url) if !url.trim().is_empty() => Self::from_url(url.trim()),
            _ => Ok(NodeTarget::Local),
        }
    }

    /// A [`Federation`](Self::Federation) target over an [`HttpNode`] at `url` (requires
    /// the `http` feature).
    #[cfg(feature = "http")]
    pub fn from_url(url: impl Into<String>) -> Result<NodeTarget, NodeError> {
        Ok(NodeTarget::federation(Arc::new(HttpNode::new(url)?)))
    }

    /// Without the `http` feature, a node URL cannot be honored — fail loudly.
    #[cfg(not(feature = "http"))]
    pub fn from_url(_url: impl Into<String>) -> Result<NodeTarget, NodeError> {
        Err(NodeError::Config(
            "DREGG_NODE_URL is set but dregg-node-target was built without the `http` \
             feature — enable it to route turns to a real federation node"
                .into(),
        ))
    }

    /// **Route one minted turn.** [`Local`](Self::Local): no-op, `Ok(None)`.
    /// [`Federation`](Self::Federation): submit the turn to the node AND confirm it
    /// landed on the node's finalized log — `Ok(Some(Landed))` iff both succeed;
    /// otherwise `Err` (the caller refuses the operation, fail-closed).
    pub fn route(&self, turn: &SubmittedTurn) -> Result<Option<Landed>, NodeError> {
        match self {
            NodeTarget::Local => Ok(None),
            NodeTarget::Federation(sink) => {
                let landed = sink.submit(turn)?;
                if !sink.landed(&landed.node_turn_hash)? {
                    return Err(NodeError::NotLanded(landed.node_turn_hash));
                }
                Ok(Some(landed))
            }
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The in-memory stub — the green wiring test double (always available).
// ─────────────────────────────────────────────────────────────────────────────

/// An **in-memory federation node** for testing the seam with no live server: it records
/// each submitted turn's commitment as its finalized log, so a crate's federation wiring
/// (submit → landed → verified) is exercised end-to-end in a unit test.
///
/// The stub uses each turn's `commitment` verbatim as the node's `turn_hash` (a modeled
/// node whose commitment IS its turn id), so [`FederationSink::landed`] is exact.
///
/// Three modes cover the seam's obligations:
/// * [`new`](Self::new) — permissive: records every submit (ignores the `prev` link).
/// * [`linked`](Self::linked) — enforces the `prev` chain link: a submit whose `prev`
///   does not extend the current head is [`NodeError::Rejected`] (a forged / broken-link
///   turn is refused).
/// * [`rejecting`](Self::rejecting) — refuses every submit (models an unreachable /
///   hostile node), so a crate's fail-closed refusal path is testable.
pub struct StubNode {
    inner: Mutex<Vec<[u8; 32]>>,
    enforce_link: bool,
    reject_all: bool,
}

impl StubNode {
    /// A permissive stub: records every submitted turn, ignores the `prev` link.
    pub fn new() -> Arc<StubNode> {
        Arc::new(StubNode {
            inner: Mutex::new(Vec::new()),
            enforce_link: false,
            reject_all: false,
        })
    }

    /// A stub that enforces the `prev` chain link — a submit whose `prev` does not extend
    /// the current head is refused ([`NodeError::Rejected`]).
    pub fn linked() -> Arc<StubNode> {
        Arc::new(StubNode {
            inner: Mutex::new(Vec::new()),
            enforce_link: true,
            reject_all: false,
        })
    }

    /// A stub that refuses every submit — models an unreachable / hostile node.
    pub fn rejecting() -> Arc<StubNode> {
        Arc::new(StubNode {
            inner: Mutex::new(Vec::new()),
            enforce_link: false,
            reject_all: true,
        })
    }

    /// The number of turns the stub has finalized.
    pub fn len(&self) -> usize {
        self.inner.lock().expect("stub node poisoned").len()
    }

    /// Whether the stub has finalized no turns.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// A snapshot of the finalized commitment chain.
    pub fn chain(&self) -> Vec<[u8; 32]> {
        self.inner.lock().expect("stub node poisoned").clone()
    }

    /// Whether `commitment` is on the finalized log.
    pub fn contains(&self, commitment: &[u8; 32]) -> bool {
        self.inner
            .lock()
            .expect("stub node poisoned")
            .contains(commitment)
    }
}

impl FederationSink for StubNode {
    fn submit(&self, turn: &SubmittedTurn) -> Result<Landed, NodeError> {
        if self.reject_all {
            return Err(NodeError::Rejected(
                "stub node is configured to refuse every submit".into(),
            ));
        }
        let mut chain = self.inner.lock().expect("stub node poisoned");
        if self.enforce_link {
            let head = chain.last().copied();
            if turn.prev != head {
                return Err(NodeError::Rejected(format!(
                    "prev-link {:?} does not extend the finalized head {:?}",
                    turn.prev, head
                )));
            }
        }
        chain.push(turn.commitment);
        Ok(Landed {
            node_turn_hash: turn.commitment,
        })
    }

    fn landed(&self, node_turn_hash: &[u8; 32]) -> Result<bool, NodeError> {
        Ok(self
            .inner
            .lock()
            .expect("stub node poisoned")
            .contains(node_turn_hash))
    }

    fn verify(&self) -> Result<(), NodeError> {
        let chain = self.inner.lock().expect("stub node poisoned");
        // A finalized log must have no duplicate turn ids (a replayed / spliced entry).
        for (i, a) in chain.iter().enumerate() {
            if chain[i + 1..].contains(a) {
                return Err(NodeError::Rejected(format!(
                    "duplicate finalized turn {a:?}"
                )));
            }
        }
        Ok(())
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The real HTTP transport (feature = "http").
// ─────────────────────────────────────────────────────────────────────────────

/// **The real federation transport** — a blocking HTTP client that submits a minted turn
/// to a node's `POST /turn/submit` (as an `EmitEvent` action carrying the commitment) and
/// confirms landing via `GET /api/receipts`. This is the leg that runs when
/// `DREGG_NODE_URL` points at ember's live federation.
///
/// The submit encodes the turn's commitment as a single event data word under the
/// domain topic; the node commits it as a genuine operator turn and returns its own
/// `turn_hash`, which [`landed`](FederationSink::landed) then checks against the node's
/// finalized receipt log.
#[cfg(feature = "http")]
pub struct HttpNode {
    base_url: String,
    agent: String,
    client: reqwest::blocking::Client,
}

#[cfg(feature = "http")]
impl HttpNode {
    /// A client for the node at `url` (its base URL, e.g. `https://hbox.local:8443`).
    /// The `agent` cell defaults to all-zero (the node derives + signs as its own
    /// operator cell — the body value is advisory, per `SubmitTurnRequest`).
    pub fn new(url: impl Into<String>) -> Result<HttpNode, NodeError> {
        let client = reqwest::blocking::Client::builder()
            .build()
            .map_err(|e| NodeError::Config(e.to_string()))?;
        Ok(HttpNode {
            base_url: url.into().trim_end_matches('/').to_string(),
            agent: "0".repeat(64),
            client,
        })
    }

    /// Override the advisory `agent` cell id (hex) the submit reports.
    pub fn with_agent(mut self, agent_hex: impl Into<String>) -> HttpNode {
        self.agent = agent_hex.into();
        self
    }
}

#[cfg(feature = "http")]
impl FederationSink for HttpNode {
    fn submit(&self, turn: &SubmittedTurn) -> Result<Landed, NodeError> {
        let body = serde_json::json!({
            "agent": self.agent,
            "nonce": 0,
            "fee": 0,
            "actions": [{
                "method": "federation.land",
                "effects": [{
                    "kind": "emit_event",
                    "topic": turn.domain,
                    "data": [hex::encode(turn.commitment)],
                }],
            }],
        });
        let resp = self
            .client
            .post(format!("{}/turn/submit", self.base_url))
            .json(&body)
            .send()
            .map_err(|e| NodeError::Transport(e.to_string()))?;
        if !resp.status().is_success() {
            return Err(NodeError::Rejected(format!("HTTP {}", resp.status())));
        }
        let json: serde_json::Value = resp
            .json()
            .map_err(|e| NodeError::Transport(e.to_string()))?;
        if !json
            .get("accepted")
            .and_then(|a| a.as_bool())
            .unwrap_or(false)
        {
            let err = json
                .get("error")
                .and_then(|e| e.as_str())
                .unwrap_or("node did not accept the turn");
            return Err(NodeError::Rejected(err.to_string()));
        }
        let hash_hex = json
            .get("turn_hash")
            .and_then(|h| h.as_str())
            .ok_or_else(|| NodeError::Rejected("node accepted but returned no turn_hash".into()))?;
        Ok(Landed {
            node_turn_hash: decode_hash(hash_hex)?,
        })
    }

    fn landed(&self, node_turn_hash: &[u8; 32]) -> Result<bool, NodeError> {
        let want = hex::encode(node_turn_hash);
        let resp = self
            .client
            .get(format!("{}/api/receipts", self.base_url))
            .send()
            .map_err(|e| NodeError::Transport(e.to_string()))?;
        if !resp.status().is_success() {
            return Err(NodeError::Transport(format!("HTTP {}", resp.status())));
        }
        let receipts: serde_json::Value = resp
            .json()
            .map_err(|e| NodeError::Transport(e.to_string()))?;
        let found = receipts
            .as_array()
            .map(|rs| {
                rs.iter().any(|r| {
                    r.get("turn_hash")
                        .and_then(|h| h.as_str())
                        .map(|h| h.eq_ignore_ascii_case(&want))
                        .unwrap_or(false)
                })
            })
            .unwrap_or(false);
        Ok(found)
    }

    fn verify(&self) -> Result<(), NodeError> {
        // The node's read API IS the light-client surface; a dedicated chain re-verify
        // rides `GET /api/receipts/index/*`. The landed-membership check in
        // `NodeTarget::route` is the load-bearing confirmation here.
        Ok(())
    }
}

#[cfg(feature = "http")]
fn decode_hash(hex_str: &str) -> Result<[u8; 32], NodeError> {
    let bytes =
        hex::decode(hex_str).map_err(|e| NodeError::Rejected(format!("bad turn_hash hex: {e}")))?;
    let arr: [u8; 32] = bytes
        .try_into()
        .map_err(|_| NodeError::Rejected("turn_hash is not 32 bytes".into()))?;
    Ok(arr)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn c(n: u8) -> [u8; 32] {
        [n; 32]
    }

    #[test]
    fn local_is_the_default_and_routes_nowhere() {
        let t = NodeTarget::default();
        assert!(t.is_local());
        assert!(!t.is_federation());
        // Local routing is a no-op: Ok(None), no ledger, no network.
        let out = t.route(&SubmittedTurn::new("spween", c(1))).unwrap();
        assert!(out.is_none());
    }

    #[test]
    fn federation_submit_lands_and_verifies() {
        let node = StubNode::new();
        let target = NodeTarget::federation(node.clone());
        assert!(target.is_federation());

        // Submit → landed → verified, end to end.
        let landed = target
            .route(&SubmittedTurn::new("spween", c(7)))
            .expect("federation route")
            .expect("federation returns a landed receipt");
        assert_eq!(landed.node_turn_hash, c(7));
        assert!(node.contains(&c(7)));
        assert_eq!(node.len(), 1);
        node.verify().unwrap();
    }

    #[test]
    fn a_rejecting_node_refuses_the_turn() {
        let node = StubNode::rejecting();
        let target = NodeTarget::federation(node.clone());
        let err = target.route(&SubmittedTurn::new("spween", c(9)));
        assert!(matches!(err, Err(NodeError::Rejected(_))));
        // Nothing landed — fail-closed.
        assert_eq!(node.len(), 0);
    }

    #[test]
    fn a_broken_prev_link_is_refused() {
        let node = StubNode::linked();
        let target = NodeTarget::federation(node.clone());
        // Genesis (prev = None) lands.
        target
            .route(&SubmittedTurn::new("arbiter", c(1)))
            .unwrap()
            .unwrap();
        // A turn linking to the true head lands.
        target
            .route(&SubmittedTurn::new("arbiter", c(2)).linked(c(1)))
            .unwrap()
            .unwrap();
        // A forged turn linking to a NON-head commitment is refused.
        let forged = target.route(&SubmittedTurn::new("arbiter", c(3)).linked(c(99)));
        assert!(matches!(forged, Err(NodeError::Rejected(_))));
        assert_eq!(node.len(), 2);
    }

    #[test]
    fn from_env_defaults_to_local_when_unset() {
        // Not asserting on a set var (env is process-global + racy under parallel tests);
        // the unset default is the load-bearing invariant for the fleet's default build.
        if std::env::var(NODE_URL_ENV).is_err() {
            assert!(NodeTarget::from_env().unwrap().is_local());
        }
    }

    #[cfg(not(feature = "http"))]
    #[test]
    fn a_url_without_http_feature_fails_loudly() {
        assert!(matches!(
            NodeTarget::from_url("https://hbox.local:8443"),
            Err(NodeError::Config(_))
        ));
    }
}
