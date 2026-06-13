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

/// Blocking JSON GET. The live shell will move reads onto gpui's async
/// executor; the scaffold keeps them blocking for clarity.
fn http_get<T: serde::de::DeserializeOwned>(base: &str, path: &str) -> anyhow::Result<T> {
    let url = format!("{base}{path}");
    let body = reqwest::blocking::get(&url)?.error_for_status()?.text()?;
    Ok(serde_json::from_str(&body)?)
}

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
