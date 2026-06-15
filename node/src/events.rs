//! `GET /api/events/stream` — the receipt nervous system (SSE).
//!
//! REFINEMENT-DESIGN.md Decision 3: cells are law, agents are will, receipts
//! are the nervous system. This is the nervous system's node edge: a
//! Server-Sent-Events broadcast of every receipt the node commits, taken
//! from the one tap that already exists — the [`NodeEvent`] broadcast that
//! every commit path (HTTP submit, signed-envelope ingress, MCP, blocklace
//! finalization) fires after appending to the cipherclerk receipt chain.
//!
//! Delivery model: the broadcast is only a WAKE-UP; the receipt chain itself
//! is the cursor's source of truth, so a lagged broadcast subscriber loses
//! nothing — the cursor re-reads the chain and catches up. Each event carries
//! `id: <chain_index>`; a reconnecting client sends `Last-Event-ID` and the
//! stream resumes from the next chain entry (exactly-once per connection,
//! at-least-once across reconnects). `has_proof` is the value at send time;
//! proofs attach asynchronously (re-check `/api/receipts/{hash}/witnesses`).
//!
//! Filtering: `?cell=<hex id>` (agent cell or any cell named by the
//! receipt's emitted events / commit record) and `?kind=<effect kind>`
//! (matched against the commit record's effect summaries).

use std::convert::Infallible;
use std::time::Duration;

use axum::extract::{Query, State};
use axum::http::HeaderMap;
use axum::response::sse::{Event, KeepAlive, Sse};
use dregg_types::hex_encode;
use futures_util::stream::Stream;
use serde::{Deserialize, Serialize};
use tokio::sync::broadcast;

use crate::state::{NodeEvent, NodeState, NodeStateInner};

/// Optional stream filter: `?cell=<hex-cell-id>&kind=<effect-kind>`.
#[derive(Clone, Debug, Default, Deserialize)]
pub struct StreamFilter {
    pub cell: Option<String>,
    pub kind: Option<String>,
}

/// One committed receipt on the wire. The summary fields are for curl /
/// dashboards; `receipt` is the full canonical [`dregg_turn::TurnReceipt`]
/// so the SDK can yield the public `Receipt` noun without a second fetch.
#[derive(Debug, Serialize)]
pub struct ReceiptEvent {
    /// Position in the node's receipt chain — the SSE `id` / resume cursor.
    pub chain_index: u64,
    pub receipt_hash: String,
    pub turn_hash: String,
    /// Cells this commit touched (agent cell, event-emitting cells, and the
    /// commit record's cell), hex-encoded, deduplicated.
    pub cells: Vec<String>,
    /// Effect-kind summaries from the commit record (empty when the commit
    /// path recorded none — e.g. blocklace-finalized turns).
    pub kinds: Vec<String>,
    /// Block height at commit when recorded; 0 when unknown.
    pub height: u64,
    /// Whether a STARK attestation is attached *right now* (witnessed
    /// receipt or persisted full-turn proof). Proofs land asynchronously.
    pub has_proof: bool,
    pub finality: String,
    pub timestamp: i64,
    /// The full canonical receipt.
    pub receipt: dregg_turn::TurnReceipt,
}

fn receipt_event_at(s: &NodeStateInner, idx: usize) -> Option<ReceiptEvent> {
    let r = s.cclerk.receipt_chain().get(idx)?;
    let receipt_hash = r.receipt_hash();
    let turn_hash = hex_encode(&r.turn_hash);

    let mut cells = vec![hex_encode(&r.agent.0)];
    for ev in &r.emitted_events {
        let cell = hex_encode(&ev.cell.0);
        if !cells.contains(&cell) {
            cells.push(cell);
        }
    }
    let mut kinds = Vec::new();
    let mut height = 0;
    if let Some(committed) = s.event_log.iter().rev().find(|e| e.turn_hash == turn_hash) {
        height = committed.height;
        if !cells.contains(&committed.cell_id) {
            cells.push(committed.cell_id.clone());
        }
        kinds = committed.effects.clone();
    }

    let stored_proof = s
        .store
        .get_config(&crate::turn_proving::turn_proof_config_key(&turn_hash))
        .ok()
        .flatten()
        .is_some();
    let has_proof = s.witnessed_receipt_count(&receipt_hash) > 0 || stored_proof;

    Some(ReceiptEvent {
        chain_index: idx as u64,
        receipt_hash: hex_encode(&receipt_hash),
        turn_hash,
        cells,
        kinds,
        height,
        has_proof,
        finality: format!("{:?}", r.finality).to_lowercase(),
        timestamp: r.timestamp,
        receipt: r.clone(),
    })
}

fn matches(filter: &StreamFilter, ev: &ReceiptEvent) -> bool {
    if let Some(cell) = &filter.cell {
        if !ev.cells.iter().any(|c| c.eq_ignore_ascii_case(cell)) {
            return false;
        }
    }
    if let Some(kind) = &filter.kind {
        let hit = ev.kinds.iter().any(|k| {
            k.eq_ignore_ascii_case(kind)
                || k.split(':')
                    .next()
                    .is_some_and(|p| p.eq_ignore_ascii_case(kind))
        });
        if !hit {
            return false;
        }
    }
    true
}

struct Cursor {
    state: NodeState,
    rx: broadcast::Receiver<NodeEvent>,
    filter: StreamFilter,
    /// Next chain index to send.
    next: u64,
}

/// `GET /api/events/stream` — SSE of committed receipts.
pub async fn events_stream(
    Query(filter): Query<StreamFilter>,
    headers: HeaderMap,
    State(state): State<NodeState>,
) -> Sse<impl Stream<Item = Result<Event, Infallible>>> {
    // Subscribe BEFORE reading the chain head: anything committed between
    // the snapshot and the first recv() still wakes the cursor.
    let rx = state.subscribe_events();

    // `Last-Event-ID: <chain_index>` resumes after the last delivered
    // receipt; a fresh connection tails from the current head.
    let resume = headers
        .get("last-event-id")
        .and_then(|v| v.to_str().ok())
        .and_then(|v| v.trim().parse::<u64>().ok());
    let next = match resume {
        Some(id) => id.saturating_add(1),
        None => state.read().await.cclerk.receipt_chain_length() as u64,
    };

    let cursor = Cursor {
        state,
        rx,
        filter,
        next,
    };
    let stream = futures_util::stream::unfold(cursor, |mut c| async move {
        loop {
            // Drain the chain from the cursor before waiting again.
            let pending = {
                let s = c.state.read().await;
                let len = s.cclerk.receipt_chain_length() as u64;
                if c.next < len {
                    let ev = receipt_event_at(&s, c.next as usize);
                    c.next += 1;
                    Some(ev)
                } else {
                    None
                }
            };
            match pending {
                Some(Some(ev)) => {
                    if !matches(&c.filter, &ev) {
                        continue;
                    }
                    let sse = Event::default()
                        .event("receipt")
                        .id(ev.chain_index.to_string())
                        .data(
                            serde_json::to_string(&ev)
                                .unwrap_or_else(|e| format!("{{\"error\":\"serialize: {e}\"}}")),
                        );
                    return Some((Ok::<_, Infallible>(sse), c));
                }
                Some(None) => continue,
                None => {}
            }
            // Chain drained — sleep on the broadcast until the next commit.
            match c.rx.recv().await {
                Ok(NodeEvent::Receipt { .. }) => continue,
                Ok(_) => continue,
                // Lag is harmless: the chain cursor catches up above.
                Err(broadcast::error::RecvError::Lagged(_)) => continue,
                Err(broadcast::error::RecvError::Closed) => return None,
            }
        }
    });

    // Heartbeat comment every 30s so proxies keep the stream open.
    Sse::new(stream).keep_alive(
        KeepAlive::new()
            .interval(Duration::from_secs(30))
            .text("hb"),
    )
}
