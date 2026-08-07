//! Path of Angels station: OPENING the daily salvage crate.
//!
//! There is no Rust ceremony here and there must never be one. Which day the crate is at, which
//! ticket a crew key draws, what that draw contributes, and whether the communal gauges move at all
//! are decided by `Dregg2.Games.PathOfAngels.StationCrateOpenRuntime`. This module carries an
//! identity to Lean, carries Lean's document back verbatim, and — only when Lean says the crate
//! ACCEPTED — appends one row to the node's durable open log.
//!
//! # Why a Rust twin would be worse here than anywhere
//!
//! `SalvageCrate.OpenResult`, `SalvageCrate.OpenReceipt`, `ShipInstrumentPanel.Receipt` and
//! `SalvageCrate.CurrentStateCapability` all have PRIVATE constructors. Possession of a receipt is
//! exactly possession of an accepted opening; possession of a capability is exactly a
//! genesis-rooted chain of accepted transitions. A Rust re-typing of any of them would be a public
//! mint for a sealed authority — a caller could post a contribution the crate never authorized and
//! move the communal gauges. Absent the Lean export this route refuses, and the daily ritual is
//! simply unavailable. That is the correct failure.
//!
//! # AUTHENTICATED, and why the panel it returns is still unattributed
//!
//! This route is mounted in the node's `protected_routes` block, behind the bearer layer. The
//! opener is identified because opening is an authorized act against a curator-authored roster —
//! `SalvageCrate` refuses a crew key that is not enrolled, and the append-only `consumed` set keys
//! on `(period, player)`.
//!
//! The document it returns is still **communal**. `ShipInstrumentPanel.State` has no per-player
//! field, so `panel` is one supplies number, a recovered-kind count and two arrival counts, exactly
//! as the unauthenticated `/panel` read serves them. The one attributable value here is the
//! opener's OWN drawn row, returned to the opener.
//!
//! ⚠ Because it is authenticated it is deliberately NOT in `public_routes`, and
//! `api::tests::the_unauthenticated_route_surface_is_exactly_this` is untouched by it.
//!
//! # ⚑ THE NODE'S LOG IS THE REPLAY AUTHORITY
//!
//! Lean rebuilds `SalvageCrate`'s append-only `consumed` set by replaying the log this route sends
//! it. That means the replay guard is exactly as strong as the log: a node that loses, truncates or
//! fails to append re-opens the crate for everyone. Lean states both halves as
//! `the_replay_guard_is_exactly_as_strong_as_the_node_log`. Here that obligation is discharged by
//! three things and no more, and they are worth naming plainly:
//!
//! * the log is a durable `PersistentStore` blob under a federation-scoped key;
//! * the append happens ONLY on an accepted open, and a failed append fails the REQUEST (the
//!   caller is told the open did not stick) rather than being logged and swallowed;
//! * the read-open-append critical section is serialized by a process-wide mutex, because
//!   `get_config`/`set_config` are not a compare-and-set. One node owns one store, so the process
//!   is the serialization point; this would NOT be sufficient if two processes shared a store, and
//!   redb's single-writer file lock is what makes that not a configuration anyone can reach.
//!
//! # ⚠ The crate is at the INSTALLED period and stays there
//!
//! `SalvageCrate.advancePeriod` is capability-gated and NOTHING CALLS IT, so replaying from
//! `genesis` leaves `currentPeriod` at the first authored beacon forever. One crew key can
//! therefore open the crate exactly once, ever. [`CRATE_FINALITY_GAP_CLAIM`] says that in the
//! response instead of leaving a caller to infer it from a second request being refused. The
//! finality adapter is named work, not a caveat.
//!
//! # Content provenance, stated rather than implied
//!
//! ⚠ The station is Lean-authored content, not content installed by a genesis ceremony. The
//! `federation_id` inside the Lean document is the AUTHORED one and need not be this node's; the
//! response carries the node's own `authority_id` beside it so the two can be compared instead of
//! assumed equal.

use std::net::SocketAddr;
use std::sync::OnceLock;

use axum::extract::{ConnectInfo, DefaultBodyLimit, Path as AxumPath, State};
use axum::http::{HeaderMap, StatusCode};
use axum::routing::post;
use axum::{Json, Router};
use serde::{Deserialize, Serialize};
use serde_json::value::RawValue;
use tokio::sync::Mutex;

use crate::api::RateLimiter;
use crate::state::NodeState;
use dregg_lean_ffi::poa_crate_open_ffi::{
    CrateOpenLogRow, MAX_POA_CRATE_OPEN_HISTORY_ROWS, PoaCrateOpenVerdict, crate_open_request,
    open_poa_crate, poa_crate_open_available,
};
use dregg_types::hex_encode;

pub const CRATE_OPEN_PATH: &str = "/api/poa/station/{authority}/crate/open";
pub const CRATE_OPEN_VIEW_FORMAT_V1: &str = "POA-CRATE-OPEN-VIEW-1";

/// Opening is a durable write behind one small Lean replay; it is budgeted well below the cheap
/// public reads and per client.
const CRATE_OPENS_PER_MINUTE: u32 = 12;

/// The request body is one crew key. Anything larger is a malformed caller.
const MAX_CRATE_OPEN_BODY_BYTES: usize = 4 * 1024;

/// Says what a refusal MEANS and what an acceptance costs, so a caller does not have to guess.
const CRATE_WRITE_PATH_CLAIM: &str = "write: `crate_open` is the exact POA-CRATE-OPEN-OUT-1 document native Lean emitted. \
     `opened:true` means SalvageCrate.openCrate accepted under a genesis-rooted capability chain \
     and ShipInstrumentPanel.observe folded the crate's own sealed receipt, so `panel` is the \
     MOVED communal ship; the node appended one row to its durable open log before replying. \
     `opened:false` is a refusal carrying a tag and NO panel and NO entry — Lean's \
     a_refused_open_publishes_no_gauge_and_no_entry — and nothing was appended";

/// The finality gap, in the response rather than only in a docblock.
const CRATE_FINALITY_GAP_CLAIM: &str = "the crate is at the INSTALLED period (the first authored beacon) and stays there: \
     SalvageCrate.advancePeriod is capability-gated and no finality adapter calls it, so a \
     genesis-rooted replay never advances currentPeriod. One crew key therefore opens the crate \
     exactly ONCE. The period is never taken from the request — the wire has no field for it";

/// The station content is authored in Lean rather than installed by a ceremony.
const CRATE_CONTENT_PROVENANCE: &str = "lean-authored station content (SalvageCrateExamples.config + StationCrateOpen.panel, the SAME \
     panel object the station read serves); no station genesis ceremony exists, so the \
     federation_id inside the document is the AUTHORED one and need not equal authority_id";

const CRATE_CONSENSUS_CLAIM: &str = "the open is recorded in this node's durable open log; it is not a consensus turn and no \
     quorum-finality claim is made. The log is the replay authority — see the module docblock";

/// The durable open-log key, scoped by federation and VERSIONED. A shape change bumps `v1` and the
/// old blob then refuses to load rather than being reinterpreted.
fn log_key(federation_id: &[u8; 32]) -> String {
    format!("poa_crate_open_log:v1:{}", hex_encode(federation_id))
}

/// Canonical durable encoding: an 8-byte magic then 40 bytes per row (32-byte player, 8-byte
/// big-endian period). Fixed width, so there is no length prefix to disagree with the content.
const LOG_MAGIC: &[u8; 8] = b"POACLOG1";
const LOG_ROW_BYTES: usize = 40;

fn encode_log(rows: &[CrateOpenLogRow]) -> Vec<u8> {
    let mut out = Vec::with_capacity(LOG_MAGIC.len() + rows.len() * LOG_ROW_BYTES);
    out.extend_from_slice(LOG_MAGIC);
    for row in rows {
        out.extend_from_slice(&row.player);
        out.extend_from_slice(&row.period.to_be_bytes());
    }
    out
}

/// Refuses rather than truncating: a blob with the wrong magic, a ragged tail, or more rows than
/// Lean's parser accepts is not a log this node wrote, and reinterpreting it would silently rewind
/// the replay guard.
fn decode_log(blob: &[u8]) -> Result<Vec<CrateOpenLogRow>, String> {
    if blob.len() < LOG_MAGIC.len() || &blob[..LOG_MAGIC.len()] != LOG_MAGIC {
        return Err("the stored crate-open log does not carry the POACLOG1 magic".to_owned());
    }
    let body = &blob[LOG_MAGIC.len()..];
    if body.len() % LOG_ROW_BYTES != 0 {
        return Err(format!(
            "the stored crate-open log is ragged: {} trailing bytes",
            body.len() % LOG_ROW_BYTES
        ));
    }
    let count = body.len() / LOG_ROW_BYTES;
    if count > MAX_POA_CRATE_OPEN_HISTORY_ROWS {
        return Err(format!(
            "the stored crate-open log holds {count} rows, above the {MAX_POA_CRATE_OPEN_HISTORY_ROWS}-row bound Lean's parser accepts"
        ));
    }
    let mut rows = Vec::with_capacity(count);
    for chunk in body.chunks_exact(LOG_ROW_BYTES) {
        let mut player = [0u8; 32];
        player.copy_from_slice(&chunk[..32]);
        let mut period = [0u8; 8];
        period.copy_from_slice(&chunk[32..]);
        rows.push(CrateOpenLogRow {
            player,
            period: u64::from_be_bytes(period),
        });
    }
    Ok(rows)
}

/// Serializes read-open-append. `PersistentStore::get_config`/`set_config` are not a
/// compare-and-set, so without this two concurrent opens could both read the same log and both
/// append — and the second would have been refused had it seen the first.
fn append_gate() -> &'static Mutex<()> {
    static GATE: OnceLock<Mutex<()>> = OnceLock::new();
    GATE.get_or_init(|| Mutex::new(()))
}

/// The whole request: an identity. No seed, beacon, date, ticket, entry, contribution, counter,
/// sequence, period or state — Lean derives every one of those.
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PoaCrateOpenRequestV1 {
    /// The opening crew key: exactly 64 lowercase hexadecimal digits.
    pub opener: String,
}

#[derive(Debug, Serialize)]
pub struct PoaCrateOpenResponseV1 {
    pub format: &'static str,
    /// This node's configured federation, which the path component must name.
    pub authority_id: String,
    pub content_provenance: &'static str,
    pub write_path: &'static str,
    pub finality_gap: &'static str,
    /// The exact `POA-CRATE-OPEN-OUT-1` document native Lean emitted. Not re-serialized: these are
    /// its bytes.
    pub crate_open: Box<RawValue>,
    /// How many rows the node's durable open log held when this open was replayed, and whether the
    /// accepted open was appended. A reader can tell a move from a refusal without parsing the
    /// nested document.
    pub log_rows_replayed: usize,
    pub log_appended: bool,
    pub consensus_finality: &'static str,
}

#[derive(Debug, Serialize)]
pub struct PoaCrateOpenRefusalV1 {
    pub format: &'static str,
    pub authority_id: String,
    pub refused: &'static str,
    pub detail: String,
}

type CrateOpenResult =
    Result<Json<PoaCrateOpenResponseV1>, (StatusCode, Json<PoaCrateOpenRefusalV1>)>;

fn refuse(
    status: StatusCode,
    authority: &str,
    refused: &'static str,
    detail: impl Into<String>,
) -> (StatusCode, Json<PoaCrateOpenRefusalV1>) {
    (
        status,
        Json(PoaCrateOpenRefusalV1 {
            format: CRATE_OPEN_VIEW_FORMAT_V1,
            authority_id: authority.to_owned(),
            refused,
            detail: detail.into(),
        }),
    )
}

/// One canonical spelling per key: exactly 64 lowercase hex digits. Uppercase is refused rather
/// than normalized, because Lean's canonical seal refuses it too and a silently normalized key
/// would make the two disagree about which crew member opened.
fn parse_hex32_lowercase(spelling: &str) -> Option<[u8; 32]> {
    if spelling.len() != 64
        || !spelling
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return None;
    }
    dregg_types::parse_hex32(spelling)
}

/// `POST /api/poa/station/{authority}/crate/open` — authenticated, durable, communal.
async fn post_poa_crate_open(
    ConnectInfo(peer): ConnectInfo<SocketAddr>,
    headers: HeaderMap,
    AxumPath(authority): AxumPath<String>,
    State(state): State<NodeState>,
    limiter: RateLimiter,
    body: Json<PoaCrateOpenRequestV1>,
) -> CrateOpenResult {
    // The selectors are never echoed back before they parse: a refusal body is not a mirror for
    // arbitrary path bytes.
    let requested = parse_hex32_lowercase(&authority).ok_or_else(|| {
        refuse(
            StatusCode::BAD_REQUEST,
            "",
            "malformed-authority",
            "the authority selector must be exactly 64 lowercase hexadecimal digits",
        )
    })?;
    let normalized_request = hex_encode(&requested);

    let opener = parse_hex32_lowercase(&body.opener).ok_or_else(|| {
        refuse(
            StatusCode::BAD_REQUEST,
            &normalized_request,
            "malformed-opener",
            "the opener crew key must be exactly 64 lowercase hexadecimal digits",
        )
    })?;

    if !limiter.check_request(peer.ip(), &headers).await {
        return Err(refuse(
            StatusCode::TOO_MANY_REQUESTS,
            &normalized_request,
            "rate-limited",
            format!("this write is budgeted at {CRATE_OPENS_PER_MINUTE} per minute per client"),
        ));
    }

    let (federation_configured, federation_id, store) = {
        let s = state.read().await;
        (s.federation_configured, s.federation_id, s.store.clone())
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

    if !poa_crate_open_available() {
        return Err(refuse(
            StatusCode::SERVICE_UNAVAILABLE,
            &normalized,
            "lean-crate-open-absent",
            "the Lean crate open is not in the linked archive; there is no host ceremony and there \
             must never be one",
        ));
    }

    // ⚑ The whole read-open-append is one critical section. Releasing between the replay and the
    // append would let two concurrent opens both replay against the same log.
    let _appending = append_gate().lock().await;

    let key = log_key(&federation_id);
    let stored = store.get_config(&key).map_err(|error| {
        refuse(
            StatusCode::INTERNAL_SERVER_ERROR,
            &normalized,
            "log-read-failed",
            error.to_string(),
        )
    })?;
    let history = match stored {
        None => Vec::new(),
        Some(blob) => decode_log(&blob).map_err(|detail| {
            refuse(
                StatusCode::INTERNAL_SERVER_ERROR,
                &normalized,
                "log-unreadable",
                detail,
            )
        })?,
    };
    if history.len() >= MAX_POA_CRATE_OPEN_HISTORY_ROWS {
        return Err(refuse(
            StatusCode::SERVICE_UNAVAILABLE,
            &normalized,
            "log-full",
            format!(
                "the durable open log holds {} rows, the bound Lean's parser accepts; the crate \
                 cannot admit another open until the log is rotated",
                history.len()
            ),
        ));
    }
    let log_rows_replayed = history.len();

    // Native Lean work belongs off the async runtime's threads: the replay is a fold over the whole
    // log, so it is the one PoA call here that is not O(1).
    let wire = crate_open_request(&opener, &history);
    let opened = {
        let wire = wire.clone();
        tokio::task::spawn_blocking(move || open_crate(&wire))
            .await
            .map_err(|error| {
                refuse(
                    StatusCode::INTERNAL_SERVER_ERROR,
                    &normalized,
                    "open-task-failed",
                    error.to_string(),
                )
            })?
    };

    let CrateOpenOutcome { document, accepted } =
        opened.map_err(|CrateOpenError { refused, detail }| {
            refuse(
                StatusCode::INTERNAL_SERVER_ERROR,
                &normalized,
                refused,
                detail,
            )
        })?;

    // Append ONLY on an accepted open, and only after Lean said so. A failed append fails the
    // REQUEST: telling a caller their gauges moved while the row that defends the next replay was
    // not written would make the node's own log a lie.
    let mut log_appended = false;
    if accepted.is_some() {
        let period = accepted.expect("accepted open carries its period");
        let mut rows = history;
        rows.push(CrateOpenLogRow {
            player: opener,
            period,
        });
        store
            .set_config(&key, &encode_log(&rows))
            .map_err(|error| {
                refuse(
                    StatusCode::INTERNAL_SERVER_ERROR,
                    &normalized,
                    "log-append-failed",
                    format!(
                        "the crate accepted this open and the durable log could not record it, so \
                         the open is NOT in effect: {error}"
                    ),
                )
            })?;
        log_appended = true;
    }

    Ok(Json(PoaCrateOpenResponseV1 {
        format: CRATE_OPEN_VIEW_FORMAT_V1,
        authority_id: normalized,
        content_provenance: CRATE_CONTENT_PROVENANCE,
        write_path: CRATE_WRITE_PATH_CLAIM,
        finality_gap: CRATE_FINALITY_GAP_CLAIM,
        crate_open: document,
        log_rows_replayed,
        log_appended,
        consensus_finality: CRATE_CONSENSUS_CLAIM,
    }))
}

#[derive(Debug)]
struct CrateOpenError {
    refused: &'static str,
    detail: String,
}

/// Lean's document plus, when the crate ACCEPTED, the period it reported. `accepted` is read off
/// Lean's own `opened` field — the node never decides acceptance.
struct CrateOpenOutcome {
    document: Box<RawValue>,
    accepted: Option<u64>,
}

fn open_crate(wire: &str) -> Result<CrateOpenOutcome, CrateOpenError> {
    let verdict = open_poa_crate(wire).map_err(|error| CrateOpenError {
        refused: "lean-transport-failed",
        detail: error,
    })?;
    let view = match verdict {
        PoaCrateOpenVerdict::Read(view) => view,
        PoaCrateOpenVerdict::Rejected => {
            return Err(CrateOpenError {
                refused: "lean-refused",
                detail: "native Lean refused this request: it is not the canonical byte image \
                         StationCrateOpenRuntime.Request.toJson emits"
                    .to_owned(),
            });
        }
    };
    // Belt: the carrier must be the reply to the request we just built.
    if !view.was_opened_for(wire.as_bytes()) {
        return Err(CrateOpenError {
            refused: "lean-reply-unbound",
            detail: "the Lean reply is not bound to this request".to_owned(),
        });
    }
    let bytes = view.into_string();
    let accepted = read_acceptance(&bytes)?;
    let document = RawValue::from_string(bytes).map_err(|error| CrateOpenError {
        refused: "lean-view-not-json",
        detail: error.to_string(),
    })?;
    Ok(CrateOpenOutcome { document, accepted })
}

/// Read Lean's verdict out of Lean's document. This does not RE-DECIDE anything: `opened` and
/// `period` are values Lean computed, and the node only needs them to know whether — and with what
/// period — to append a row.
fn read_acceptance(document: &str) -> Result<Option<u64>, CrateOpenError> {
    let parsed: serde_json::Value =
        serde_json::from_str(document).map_err(|error| CrateOpenError {
            refused: "lean-view-not-json",
            detail: error.to_string(),
        })?;
    let opened = parsed
        .get("opened")
        .and_then(serde_json::Value::as_bool)
        .ok_or_else(|| CrateOpenError {
            refused: "lean-view-shape",
            detail: "the Lean document has no boolean `opened` field".to_owned(),
        })?;
    if !opened {
        return Ok(None);
    }
    let period = parsed
        .get("period")
        .and_then(serde_json::Value::as_u64)
        .ok_or_else(|| CrateOpenError {
            refused: "lean-view-shape",
            detail: "the Lean document reports an accepted open with no numeric `period`"
                .to_owned(),
        })?;
    Ok(Some(period))
}

pub(crate) fn routes() -> Router<NodeState> {
    let limiter = RateLimiter::new(CRATE_OPENS_PER_MINUTE, 60);
    Router::new()
        .route(
            CRATE_OPEN_PATH,
            post({
                let limiter = limiter.clone();
                move |connect_info, headers, path, state, body| {
                    post_poa_crate_open(connect_info, headers, path, state, limiter.clone(), body)
                }
            }),
        )
        .layer(DefaultBodyLimit::max(MAX_CRATE_OPEN_BODY_BYTES))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn selectors_have_one_lowercase_canonical_spelling() {
        let canonical = hex_encode(&[0x2b; 32]);
        assert_eq!(parse_hex32_lowercase(&canonical), Some([0x2b; 32]));
        assert_eq!(parse_hex32_lowercase(&canonical.to_uppercase()), None);
        assert_eq!(parse_hex32_lowercase(&canonical[..63]), None);
        assert_eq!(parse_hex32_lowercase("not-hex"), None);
    }

    #[test]
    fn the_durable_log_round_trips_and_refuses_every_other_shape() {
        let rows = vec![
            CrateOpenLogRow {
                player: [0x29; 32],
                period: 31,
            },
            CrateOpenLogRow {
                player: [0x28; 32],
                period: 31,
            },
        ];
        let blob = encode_log(&rows);
        assert_eq!(decode_log(&blob).expect("round trip"), rows);

        // Wrong magic: a blob this node did not write must not be reinterpreted as an empty or
        // partial log, because either reading REWINDS the replay guard.
        let mut wrong_magic = blob.clone();
        wrong_magic[0] = b'X';
        assert!(decode_log(&wrong_magic).is_err());

        // A ragged tail is a truncated write, not "the rows we can see".
        let mut ragged = blob.clone();
        ragged.pop();
        assert!(decode_log(&ragged).is_err());

        assert!(decode_log(&[]).is_err());
        assert_eq!(decode_log(LOG_MAGIC).expect("empty log"), Vec::new());
    }

    #[test]
    fn the_log_refuses_more_rows_than_lean_will_parse() {
        let mut blob = LOG_MAGIC.to_vec();
        blob.extend(std::iter::repeat_n(
            0u8,
            (MAX_POA_CRATE_OPEN_HISTORY_ROWS + 1) * LOG_ROW_BYTES,
        ));
        assert!(decode_log(&blob).is_err());
    }

    /// The node reads Lean's verdict; it never forms one. A document with `opened:false` yields no
    /// period and therefore no appended row, whatever else it carries.
    #[test]
    fn acceptance_is_read_from_leans_own_fields() {
        assert_eq!(
            read_acceptance(r#"{"opened":true,"period":31}"#)
                .expect("well-formed")
                .expect("accepted"),
            31
        );
        assert!(
            read_acceptance(
                r#"{"opened":false,"period":31,"refusal":"already-opened-this-period"}"#
            )
            .expect("well-formed")
            .is_none()
        );
        // An accepted open with no period is a document shape this node refuses rather than
        // guessing a period for — guessing one would write a row that defends the wrong day.
        assert!(read_acceptance(r#"{"opened":true,"period":null}"#).is_err());
        assert!(read_acceptance(r#"{"period":31}"#).is_err());
        assert!(read_acceptance("not json").is_err());
    }
}
