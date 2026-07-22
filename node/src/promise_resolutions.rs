//! Typed, restart-durable promise-resolution notifications.
//!
//! A finalized executor may resolve one promise and wake/break dependents. The
//! authoritative transition is the finalized commit plus its executor-state
//! CAS; this module is its post-commit observer surface. The source-bound
//! durable journal batch is committed atomically with that CAS; this module
//! prepares the batch and, after a fresh commit, reads it back before emitting
//! typed [`NodeEvent`] messages. An exact replay emits nothing.

use axum::{
    Json,
    extract::{Query, State},
    http::StatusCode,
};
use dregg_persist::{
    DurablePromiseResolutionV1, PersistentStore, PromiseBrokenReasonV1,
    PromiseResolutionCandidateV1, PromiseResolutionKindV1,
};
use serde::{Deserialize, Serialize};

use crate::state::{NodeEvent, NodeState};

/// Public wire form: fixed-size identities are hex, and readiness never carries
/// the unsigned dependent turn body.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct PromiseResolutionRecord {
    pub sequence: u64,
    pub event_id: String,
    pub source_commit_ordinal: u64,
    pub source_receipt_hash: String,
    pub event_index: u32,
    pub pending_id: String,
    pub outcome: PromiseResolutionOutcome,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum PromiseResolutionOutcome {
    Resolved { receipt_hash: String },
    ReadyToExecute,
    Broken { reason: PromiseBrokenReason },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum PromiseBrokenReason {
    TurnRejected { reason: String },
    Timeout,
    FederationUnreachable,
    DependencyBroken { cause: Box<PromiseBrokenReason> },
}

impl From<PromiseBrokenReasonV1> for PromiseBrokenReason {
    fn from(reason: PromiseBrokenReasonV1) -> Self {
        match reason {
            PromiseBrokenReasonV1::TurnRejected { reason } => Self::TurnRejected { reason },
            PromiseBrokenReasonV1::Timeout => Self::Timeout,
            PromiseBrokenReasonV1::FederationUnreachable => Self::FederationUnreachable,
            PromiseBrokenReasonV1::DependencyBroken { cause } => Self::DependencyBroken {
                cause: Box::new((*cause).into()),
            },
        }
    }
}

impl From<DurablePromiseResolutionV1> for PromiseResolutionRecord {
    fn from(record: DurablePromiseResolutionV1) -> Self {
        let outcome = match record.outcome {
            PromiseResolutionKindV1::Resolved { receipt_hash } => {
                PromiseResolutionOutcome::Resolved {
                    receipt_hash: dregg_types::hex_encode(&receipt_hash),
                }
            }
            PromiseResolutionKindV1::ReadyToExecute => PromiseResolutionOutcome::ReadyToExecute,
            PromiseResolutionKindV1::Broken { reason } => PromiseResolutionOutcome::Broken {
                reason: reason.into(),
            },
        };
        Self {
            sequence: record.sequence,
            event_id: dregg_types::hex_encode(&record.event_id),
            source_commit_ordinal: record.source_commit_ordinal,
            source_receipt_hash: dregg_types::hex_encode(&record.source_receipt_hash),
            event_index: record.event_index,
            pending_id: dregg_types::hex_encode(&record.pending_id),
            outcome,
        }
    }
}

fn broken_reason(reason: &dregg_turn::BrokenReason) -> PromiseBrokenReasonV1 {
    match reason {
        dregg_turn::BrokenReason::TurnRejected(error) => PromiseBrokenReasonV1::TurnRejected {
            reason: error.to_string(),
        },
        dregg_turn::BrokenReason::Timeout => PromiseBrokenReasonV1::Timeout,
        dregg_turn::BrokenReason::FederationUnreachable => {
            PromiseBrokenReasonV1::FederationUnreachable
        }
        dregg_turn::BrokenReason::DependencyBroken(cause) => {
            PromiseBrokenReasonV1::DependencyBroken {
                cause: Box::new(broken_reason(cause)),
            }
        }
    }
}

pub(crate) fn resolution_candidates(
    source_commit_ordinal: u64,
    source_receipt_hash: [u8; 32],
    events: &[dregg_turn::ResolutionEvent],
) -> Result<Vec<PromiseResolutionCandidateV1>, String> {
    events
        .iter()
        .enumerate()
        .map(|(index, event)| {
            let event_index = u32::try_from(index)
                .map_err(|_| "promise-resolution event count exceeds u32".to_string())?;
            let (pending_id, outcome) = match event {
                dregg_turn::ResolutionEvent::Resolved { turn_hash, receipt } => (
                    *turn_hash,
                    PromiseResolutionKindV1::Resolved {
                        receipt_hash: receipt.receipt_hash(),
                    },
                ),
                dregg_turn::ResolutionEvent::ReadyToExecute { turn_hash, .. } => {
                    (*turn_hash, PromiseResolutionKindV1::ReadyToExecute)
                }
                dregg_turn::ResolutionEvent::Broken { turn_hash, reason } => (
                    *turn_hash,
                    PromiseResolutionKindV1::Broken {
                        reason: broken_reason(reason),
                    },
                ),
            };
            Ok(PromiseResolutionCandidateV1 {
                source_commit_ordinal,
                source_receipt_hash,
                event_index,
                pending_id,
                outcome,
            })
        })
        .collect()
}

/// Publish one fresh finalized commit's already-durable typed observer events.
///
/// Call this only after `trace_durable_resolution_events` and only on the
/// `freshly_committed` branch. The immutable batch already shares the source
/// commit's redb transaction; this function only reads it and emits. A missing
/// or different batch fails closed. `ReadyToExecute` is notification-only; no
/// unsigned turn is submitted here.
pub(crate) fn publish_durable_resolution_events(
    state: &NodeState,
    store: &PersistentStore,
    source_commit_ordinal: u64,
    source_receipt_hash: [u8; 32],
    events: &[dregg_turn::ResolutionEvent],
) -> Result<Vec<DurablePromiseResolutionV1>, String> {
    let expected = resolution_candidates(source_commit_ordinal, source_receipt_hash, events)?;
    let durable = store
        .promise_resolution_batch_for_commit_v1(source_commit_ordinal)
        .map_err(|error| error.to_string())?
        .ok_or_else(|| {
            format!("durable source commit {source_commit_ordinal} has no promise-resolution batch")
        })?;
    if durable.len() != expected.len()
        || !durable
            .iter()
            .zip(&expected)
            .all(|(record, candidate)| record.matches_candidate(candidate))
    {
        return Err(format!(
            "durable promise-resolution batch disagrees with source commit {source_commit_ordinal}"
        ));
    }
    for record in durable.iter().cloned() {
        state.emit(NodeEvent::PromiseResolution {
            resolution: record.into(),
        });
    }
    if durable
        .iter()
        .any(|record| record.outcome == PromiseResolutionKindV1::ReadyToExecute)
    {
        crate::private_dependent_turns::spawn_private_dependent_turn_drain(state.clone());
    }
    Ok(durable)
}

#[derive(Clone, Debug, Default, Deserialize)]
pub struct PromiseResolutionQuery {
    /// Exclusive durable sequence cursor. Omit to read from the retained start.
    pub after: Option<u64>,
    /// Page size (default 50, hard maximum 200 at this public endpoint).
    pub limit: Option<usize>,
}

/// `GET /api/promise-resolutions` — restart-durable typed notification history.
pub async fn get_promise_resolutions(
    Query(query): Query<PromiseResolutionQuery>,
    State(state): State<NodeState>,
) -> Result<Json<Vec<PromiseResolutionRecord>>, StatusCode> {
    let limit = query.limit.unwrap_or(50).min(200);
    let store = { state.read().await.store.clone() };
    let rows = store
        .promise_resolutions_after_v1(query.after, limit)
        .map_err(|error| {
            tracing::error!(error = %error, "durable promise-resolution query failed closed");
            StatusCode::INTERNAL_SERVER_ERROR
        })?;
    Ok(Json(rows.into_iter().map(Into::into).collect()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ready_wire_contains_no_unsigned_turn() {
        let record: PromiseResolutionRecord = DurablePromiseResolutionV1 {
            sequence: 4,
            event_id: [1; 32],
            source_commit_ordinal: 3,
            source_receipt_hash: [2; 32],
            event_index: 0,
            pending_id: [3; 32],
            outcome: PromiseResolutionKindV1::ReadyToExecute,
        }
        .into();
        let json = serde_json::to_value(record).unwrap();
        assert_eq!(json["outcome"]["kind"], "ready_to_execute");
        assert!(json["outcome"].get("turn").is_none());
    }
}
