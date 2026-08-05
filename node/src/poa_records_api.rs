//! Path of Angels Records: the public read where a finished run lands.
//!
//! There is no Rust projection here and there must never be one. The record
//! shape — what a landed run is, which artifact it discovered, whose locker and
//! inbox it reaches, what Canon status that artifact now carries — is decided by
//! `Dregg2.Games.PathOfAngels.RecordsRuntime`, and this module only:
//!
//! 1. runs the durable semantic replay
//!    ([`crate::poa_signal_adapter::replay_persisted_signal_history`]), which is
//!    the same function the boot audit uses with its rows discarded, so a served
//!    Records view has passed every check the audit performs;
//! 2. hands Lean the retained genesis config/Canon blobs and one row per
//!    replayed transition, with `signer` from the finalized `SignedTurn` and
//!    `actor_root` from the durable receipt — never re-derived from the judge
//!    input's own carrier, which is what they exist to bind; and
//! 3. serves Lean's emitted document verbatim.
//!
//! The read is honest before any turn settles. With zero transitions the
//! response is not an empty list dressed as a feature: it carries the exact
//! world identity, world meters, Canon revision and playable mission the genesis
//! ceremony installed, plus a replay verdict that has actually run. A node whose
//! `latest_height` is 0 has something true to show, and the same page will hold
//! the first real run without changing shape.
//!
//! Every failure is a refusal. A missing Lean export, a corrupt history, a
//! disagreeing world, or a history longer than Lean's read fuse returns an error
//! with a reason and no records — there is no partial or cached view.

use std::net::SocketAddr;
use std::sync::Arc;

use axum::extract::{ConnectInfo, Path as AxumPath, State};
use axum::http::{HeaderMap, StatusCode};
use axum::routing::get;
use axum::{Json, Router};
use serde::Serialize;
use serde_json::value::RawValue;
use tokio::sync::Semaphore;

use crate::api::RateLimiter;
use crate::poa_signal_adapter::{FinalizedSignalRow, replay_persisted_signal_history};
use crate::state::NodeState;
use dregg_types::hex_encode;

pub const RECORDS_PATH: &str = "/api/poa/records/{authority}";
pub const RECORDS_VIEW_FORMAT_V1: &str = "POA-RECORDS-VIEW-1";
pub const RECORDS_REQUEST_FORMAT_V1: &str = "POA-RECORDS-IN-1";

/// This read re-judges every finalized row through native Lean on every
/// request, so it is budgeted like an expensive full-scan read (the
/// `/api/cells` precedent) and additionally capped in flight across the process.
const RECORDS_READS_PER_MINUTE: u32 = 30;
const RECORDS_MAX_IN_FLIGHT: usize = 2;

/// Lean's own `MAX_ROWS` fuse. Refusing here first turns a certain Lean refusal
/// into a legible one, and keeps a long history from being hex-encoded twice
/// before being rejected.
const RECORDS_MAX_ROWS: usize = 256;

#[derive(Clone)]
struct RecordsReadLimits {
    per_ip: RateLimiter,
    in_flight: Arc<Semaphore>,
}

impl RecordsReadLimits {
    fn new() -> Self {
        Self {
            per_ip: RateLimiter::new(RECORDS_READS_PER_MINUTE, 60),
            in_flight: Arc::new(Semaphore::new(RECORDS_MAX_IN_FLIGHT)),
        }
    }
}

/// The replay verdict. It is meaningful at zero transitions: it says the
/// retained genesis reopened, decoded, and is the head this node publishes.
#[derive(Debug, Clone, Serialize)]
pub struct PoaRecordsReplayViewV1 {
    /// Finalized transitions re-judged through native Lean for this response.
    pub transitions_replayed: u64,
    /// The zero-transition image the ceremony installed, and the head this
    /// replay derived from it. Replay refuses unless the derived head is the
    /// one the node publishes, so these two digests are a checkable claim
    /// rather than a restatement: a reader can compare `rebuilt_head_digest`
    /// with `/api/poa/signal/{authority}/status`.
    pub retained_genesis_digest: String,
    pub rebuilt_head_digest: String,
}

#[derive(Debug, Serialize)]
pub struct PoaRecordsResponseV1 {
    pub format: &'static str,
    pub authority_id: String,
    pub federation_id: String,
    /// Whether the PoA genesis ceremony has run on this node.
    pub installed: bool,
    pub replay: Option<PoaRecordsReplayViewV1>,
    /// The exact `POA-RECORDS-OUT-2` document native Lean emitted. Not
    /// re-serialized: these are its bytes.
    pub records: Option<Box<RawValue>>,
    pub consensus_finality: &'static str,
}

#[derive(Debug, Serialize)]
pub struct PoaRecordsRefusalV1 {
    pub format: &'static str,
    pub authority_id: String,
    pub refused: &'static str,
    pub detail: String,
}

/// Every view served by this node carries the same finality caveat the other
/// PoA reads carry: one validator's finalized commits, not a quorum claim.
const RECORDS_FINALITY_CLAIM: &str =
    "records reflect this node's finalized commit history; no quorum-finality claim is made";

type RecordsResult = Result<Json<PoaRecordsResponseV1>, (StatusCode, Json<PoaRecordsRefusalV1>)>;

fn refuse(
    status: StatusCode,
    authority: &str,
    refused: &'static str,
    detail: impl Into<String>,
) -> (StatusCode, Json<PoaRecordsRefusalV1>) {
    (
        status,
        Json(PoaRecordsRefusalV1 {
            format: RECORDS_VIEW_FORMAT_V1,
            authority_id: authority.to_owned(),
            refused,
            detail: detail.into(),
        }),
    )
}

/// Exactly `RecordsRuntime.RowWire`, in its exact field order. Serde emits
/// struct fields in declaration order and compact JSON, so this is the byte
/// image Lean's canonical decoder re-encodes and compares against.
#[derive(Debug, Serialize)]
struct RecordsRowRequest {
    commit_ordinal: u64,
    turn_hash: String,
    receipt_hash: String,
    actor_root: String,
    signer: String,
    judge_input: String,
    judge_output: String,
}

/// Exactly `RecordsRuntime.RequestWire`, in its exact field order.
#[derive(Debug, Serialize)]
struct RecordsRequest {
    format: &'static str,
    federation_id: String,
    genesis_canon: String,
    config: String,
    rows: Vec<RecordsRowRequest>,
}

impl RecordsRowRequest {
    fn from_replayed(row: &FinalizedSignalRow) -> Self {
        Self {
            commit_ordinal: row.commit_ordinal,
            turn_hash: hex_encode(&row.turn_hash),
            receipt_hash: hex_encode(&row.receipt_hash),
            actor_root: hex_encode(&row.actor_root),
            signer: hex_encode(&row.signer),
            judge_input: hex_encode(row.judge_input.as_bytes()),
            judge_output: hex_encode(row.judge_output.as_bytes()),
        }
    }
}

/// `GET /api/poa/records/{authority}` — public, read-only.
///
/// The authority path component must name this node's exact configured
/// federation; this route never enumerates authorities. It returns Canon and
/// judge material only in the reduced form Lean chose to publish.
///
/// ⚑ What is absent from `POA-RECORDS-OUT-2`, and why each absence is needed —
/// this list used to be one item and one item was not enough:
///
/// * `target` — the Signal answer itself.
/// * `run_seed` — `SignalTriangulation.targetFromSeed` is public and total, so a
///   published live seed IS the answer. The mission is published as
///   `PublicMissionWire`, which has no such field, and Lean additionally refuses
///   any config whose seed is not the all-zero template sentinel.
/// * `transcript_digest` — never a digest.
///   `SignalTriangulation.transcriptDigest` is fixed-width plaintext whose tail
///   is the submitted code. Hashing it would not help: an accepted transcript is
///   at most five guesses from 216, about `2^39`, which brute-force inverts.
///
/// Everything this route does publish is chain-public or content-public already:
/// commit coordinates, signer and actor root, the receipt key, the discovered
/// artifact and its Canon status, the reward contribution, and world meters.
async fn get_poa_records(
    ConnectInfo(peer): ConnectInfo<SocketAddr>,
    headers: HeaderMap,
    AxumPath(authority): AxumPath<String>,
    State(state): State<NodeState>,
    limits: RecordsReadLimits,
) -> RecordsResult {
    // The selector is never echoed back before it parses: a refusal body is not
    // a mirror for arbitrary path bytes.
    let requested = parse_records_authority(&authority).ok_or_else(|| {
        refuse(
            StatusCode::BAD_REQUEST,
            "",
            "malformed-authority",
            "the authority selector must be exactly 64 lowercase hexadecimal digits",
        )
    })?;
    let normalized_request = hex_encode(&requested);
    if !limits.per_ip.check_request(peer.ip(), &headers).await {
        return Err(refuse(
            StatusCode::TOO_MANY_REQUESTS,
            &normalized_request,
            "rate-limited",
            format!("this read is budgeted at {RECORDS_READS_PER_MINUTE} per minute per client"),
        ));
    }
    let Ok(_permit) = limits.in_flight.clone().try_acquire_owned() else {
        return Err(refuse(
            StatusCode::SERVICE_UNAVAILABLE,
            &normalized_request,
            "read-saturated",
            format!("at most {RECORDS_MAX_IN_FLIGHT} Records replays run at once"),
        ));
    };

    let (store, federation_configured, federation_id) = {
        let s = state.read().await;
        (s.store.clone(), s.federation_configured, s.federation_id)
    };
    if !federation_configured {
        return Err(refuse(
            StatusCode::SERVICE_UNAVAILABLE,
            &normalized_request,
            "no-local-authority",
            "this node is in discovery mode and serves no PoA authority",
        ));
    }
    if requested != federation_id {
        return Err(refuse(
            StatusCode::BAD_REQUEST,
            &normalized_request,
            "foreign-authority",
            "this node serves only its own configured federation",
        ));
    }
    let normalized = hex_encode(&federation_id);

    // A node that has not run the genesis ceremony has no world to show, and
    // says so rather than serving an empty projection as if it were one.
    let installed = store
        .load_poa_signal_head(federation_id)
        .map_err(|error| {
            refuse(
                StatusCode::INTERNAL_SERVER_ERROR,
                &normalized,
                "head-unreadable",
                error.to_string(),
            )
        })?
        .is_some();
    if !installed {
        return Ok(Json(PoaRecordsResponseV1 {
            format: RECORDS_VIEW_FORMAT_V1,
            authority_id: normalized.clone(),
            federation_id: normalized,
            installed: false,
            replay: None,
            records: None,
            consensus_finality: RECORDS_FINALITY_CLAIM,
        }));
    }

    if !dregg_lean_ffi::poa_records_ffi::poa_records_project_available() {
        return Err(refuse(
            StatusCode::SERVICE_UNAVAILABLE,
            &normalized,
            "lean-records-absent",
            "the Lean Records read model is not in the linked archive; there is no host projection",
        ));
    }

    // Replay and projection are CPU-bound native Lean work: keep them off the
    // async runtime's threads entirely.
    let projected = tokio::task::spawn_blocking(move || project_records(&store, federation_id))
        .await
        .map_err(|error| {
            refuse(
                StatusCode::INTERNAL_SERVER_ERROR,
                &normalized,
                "read-task-failed",
                error.to_string(),
            )
        })?;

    match projected {
        Ok((replay, records)) => Ok(Json(PoaRecordsResponseV1 {
            format: RECORDS_VIEW_FORMAT_V1,
            authority_id: normalized.clone(),
            federation_id: normalized,
            installed: true,
            replay: Some(replay),
            records: Some(records),
            consensus_finality: RECORDS_FINALITY_CLAIM,
        })),
        Err(RecordsReadError { refused, detail }) => Err(refuse(
            StatusCode::INTERNAL_SERVER_ERROR,
            &normalized,
            refused,
            detail,
        )),
    }
}

struct RecordsReadError {
    refused: &'static str,
    detail: String,
}

/// The blocking half: durable replay, then the Lean projection over its rows.
fn project_records(
    store: &dregg_persist::PersistentStore,
    federation_id: [u8; 32],
) -> Result<(PoaRecordsReplayViewV1, Box<RawValue>), RecordsReadError> {
    let replay = replay_persisted_signal_history(store, federation_id, None).map_err(|error| {
        RecordsReadError {
            refused: "replay-refused",
            detail: error.to_string(),
        }
    })?;
    if replay.rows.len() > RECORDS_MAX_ROWS {
        return Err(RecordsReadError {
            refused: "history-exceeds-read-fuse",
            detail: format!(
                "{} finalized runs exceed the {RECORDS_MAX_ROWS}-row Lean read fuse; this read \
                 needs a windowed request before it can serve again",
                replay.rows.len()
            ),
        });
    }

    let genesis_canon =
        String::from_utf8(replay.genesis_canon.clone()).map_err(|error| RecordsReadError {
            refused: "genesis-canon-not-utf8",
            detail: error.to_string(),
        })?;
    let genesis_config =
        String::from_utf8(replay.genesis_config.clone()).map_err(|error| RecordsReadError {
            refused: "genesis-config-not-utf8",
            detail: error.to_string(),
        })?;
    let request = RecordsRequest {
        format: RECORDS_REQUEST_FORMAT_V1,
        federation_id: hex_encode(&federation_id),
        genesis_canon: hex_encode(genesis_canon.as_bytes()),
        config: hex_encode(genesis_config.as_bytes()),
        rows: replay
            .rows
            .iter()
            .map(RecordsRowRequest::from_replayed)
            .collect(),
    };
    let wire = serde_json::to_string(&request).map_err(|error| RecordsReadError {
        refused: "records-request-unserializable",
        detail: error.to_string(),
    })?;

    let verdict = dregg_lean_ffi::poa_records_ffi::project_poa_records(&wire).map_err(|error| {
        RecordsReadError {
            refused: "lean-transport-failed",
            detail: error,
        }
    })?;
    let projected = match verdict {
        dregg_lean_ffi::poa_records_ffi::PoaRecordsVerdict::Projected(projected) => projected,
        dregg_lean_ffi::poa_records_ffi::PoaRecordsVerdict::Rejected => {
            return Err(RecordsReadError {
                refused: "lean-refused",
                detail: "native Lean refused this world's records: the genesis blobs, the \
                         mission binding, a row's re-judgement, or the Canon refold did not hold"
                    .to_owned(),
            });
        }
    };
    // Belt: the carrier must be the reply to the request we just built.
    if !projected.was_projected_for(wire.as_bytes()) {
        return Err(RecordsReadError {
            refused: "lean-reply-unbound",
            detail: "the Lean reply is not bound to this request".to_owned(),
        });
    }
    let records =
        RawValue::from_string(projected.into_string()).map_err(|error| RecordsReadError {
            refused: "lean-view-not-json",
            detail: error.to_string(),
        })?;

    Ok((
        PoaRecordsReplayViewV1 {
            transitions_replayed: replay.report.transition_count,
            retained_genesis_digest: hex_encode(&replay.report.retained_genesis_digest),
            rebuilt_head_digest: hex_encode(&replay.report.rebuilt_head_digest),
        },
        records,
    ))
}

/// One canonical URL per authority: exactly 64 lowercase hex digits.
fn parse_records_authority(authority: &str) -> Option<[u8; 32]> {
    if authority.len() != 64
        || !authority
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return None;
    }
    dregg_types::parse_hex32(authority)
}

pub(crate) fn routes() -> Router<NodeState> {
    let limits = RecordsReadLimits::new();
    Router::new().route(
        RECORDS_PATH,
        get({
            let limits = limits.clone();
            move |connect_info, headers, path, state| {
                get_poa_records(connect_info, headers, path, state, limits.clone())
            }
        }),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn authority_selector_has_one_lowercase_canonical_url() {
        let canonical = hex_encode(&[0x2b; 32]);
        assert_eq!(parse_records_authority(&canonical), Some([0x2b; 32]));
        assert_eq!(parse_records_authority(&canonical.to_uppercase()), None);
        assert_eq!(parse_records_authority(&canonical[..63]), None);
        assert_eq!(parse_records_authority("not-hex"), None);
    }

    /// The request must be the byte image `RecordsRuntime.RequestWire.toJson`
    /// emits, or Lean's canonical seal refuses it — silently, from the caller's
    /// point of view. This pins the field order and the compact spelling.
    #[test]
    fn request_is_the_exact_lean_field_order_and_spelling() {
        let request = RecordsRequest {
            format: RECORDS_REQUEST_FORMAT_V1,
            federation_id: hex_encode(&[0x01; 32]),
            genesis_canon: hex_encode(b"{}"),
            config: hex_encode(b"[]"),
            rows: vec![RecordsRowRequest {
                commit_ordinal: 7,
                turn_hash: hex_encode(&[0x02; 32]),
                receipt_hash: hex_encode(&[0x03; 32]),
                actor_root: hex_encode(&[0x04; 32]),
                signer: hex_encode(&[0x05; 32]),
                judge_input: hex_encode(b"in"),
                judge_output: hex_encode(b"out"),
            }],
        };
        let wire = serde_json::to_string(&request).unwrap();
        assert!(
            wire.starts_with("{\"format\":\"POA-RECORDS-IN-1\",\"federation_id\":\"0101"),
            "{wire}"
        );
        assert!(
            wire.contains("\"rows\":[{\"commit_ordinal\":7,\"turn_hash\":\"0202"),
            "{wire}"
        );
        assert!(
            wire.ends_with("\"judge_input\":\"696e\",\"judge_output\":\"6f7574\"}]}"),
            "{wire}"
        );
        // No whitespace anywhere: Lean's encoder emits none.
        assert!(!wire.contains(' '), "{wire}");
    }

    /// The hex spelling must be the one Lean's `OpaqueUtf8.toHex` produces:
    /// lowercase, two digits per byte, no prefix. `catalog.json` stores digests
    /// with a `sha256:` prefix and that spelling would fail closed here.
    #[test]
    fn blob_hex_is_bare_lowercase() {
        let spelling = hex_encode("{\"a\":1}".as_bytes());
        assert_eq!(spelling, "7b2261223a317d");
        assert!(!spelling.contains(':'));
        assert!(
            spelling
                .bytes()
                .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
        );
    }
}
