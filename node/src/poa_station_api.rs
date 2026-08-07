//! Path of Angels station: the communal ship instrument panel, and the crate's
//! visible daily rotation.
//!
//! There is no Rust projection here and there must never be one. What a gauge
//! reads, what a crate ticket contains, and which day a crew member draws it are
//! decided by `Dregg2.Games.PathOfAngels.StationDailyRuntime`, and this module
//! only carries a request to Lean and serves Lean's emitted document verbatim.
//!
//! # Why a Rust twin would be worse here than usual
//!
//! `ShipInstrumentPanel.Receipt` and `SalvageCrate.OpenResult` have PRIVATE
//! constructors: possession of a receipt is exactly possession of an accepted
//! opening, and that is the entire authority story of the ritual. A Rust
//! re-typing of either would be a public mint for a sealed authority — any
//! caller could then post a contribution the crate never authorized and move the
//! communal gauges.
//!
//! # ⚑ THIS READ FOLDS THE NODE'S DURABLE OPEN LOG
//!
//! ⚠ CORRECTED 2026-08-07. This section used to say the write path was
//! unreachable — that `SalvageCrate.openCrate` demanded a
//! `CurrentStateCapability` "declared `opaque` with no producer anywhere in the
//! tree" — and that the ship served was therefore `ShipInstrumentPanel.initial`,
//! asserted by `the_served_ship_has_not_been_moved`, "the assertion that goes
//! RED the day a judged opening can be folded in".
//!
//! Every clause of that is now false. The capability is a sealed structure
//! rooted in `genesis`, the crate-open route accepts openings, and the old
//! assertion did **not** go red when they landed — it was a claim about the
//! request type (which had no `history` field), not about reachability. Measured
//! over HTTP the same day: the write path served `exact_total: 1, observed: 2`
//! while this route served `exact_total: 0, observed: 0`.
//!
//! So this route now reads the node's durable open log — the SAME blob
//! `poa_crate_api` appends to, under the same key and through the same decoder,
//! imported rather than re-derived — and hands it to Lean, which replays it
//! through `SalvageCrate.openCrate` and serves the ship it folds to. The fold
//! lives in `StationDailyRuntime` and the write path abbreviates it, so there is
//! exactly one.
//!
//! What replaces the retired assertion:
//! `StationDailyRuntime.the_served_ship_moves_when_the_log_records_an_opening`
//! (two logs one row apart, two different ships) and
//! `StationCrateOpenRuntime.the_station_read_serves_the_ship_this_write_published`
//! (this document's communal fields ARE the panel the write published).
//!
//! # ⚠ An unreadable or unreplayable log REFUSES; it never renders as zeros
//!
//! A blob without the `POACLOG1` magic, a ragged one, or one Lean cannot replay
//! is a 500 with a named refusal. Serving the installed ship there would tell a
//! player "nobody has opened the crate yet" when the truth is "this node's log
//! is broken", and those are indistinguishable on a page of zeros.
//!
//! # It is still READ-ONLY, for a narrower and sufficient reason
//!
//! Lean reaches `openCrate` here, once per log row. Nothing is written, because
//! the export returns a projection and drops every `OpenResult` the replay
//! produces, and because **only `poa_crate_api` appends** — this module holds no
//! write handle to the log at all. `SalvageCrate.openCore` is `private` and
//! `ShipInstrumentPanel.Receipt` has a private `mk`, so no wire decodes a
//! receipt into existence.
//!
//! [`STATION_WRITE_PATH_CLAIM`] says all of this in the response rather than
//! leaving a reader to infer it.
//!
//! # Content provenance, stated rather than implied
//!
//! ⚠ The station is **Lean-authored content**, not content installed by a
//! genesis ceremony: there is no station genesis and no activated-content
//! component for it. The served `federation_id` inside the Lean document is the
//! *authored* one and need not be this node's. The response carries the node's
//! own `authority_id` beside it and states the provenance, so the two can be
//! compared instead of assumed equal.
//!
//! # What is safe to publish here
//!
//! The panel half is communal by construction — `ShipInstrumentPanel.State` has
//! no per-player field at all, and
//! `StationDailyRuntime.the_served_panel_does_not_depend_on_the_crew` proves
//! substituting any request leaves every communal field of the document
//! bit-identical. The crate half is a **visible rotation**: `SalvageCrate` is
//! explicit that its mixer is not an unpredictability source and its beacon
//! schedule is curator-authored and visible, and `generatedRotation` hands a
//! player their rotation deliberately. Neither `HiddenInstance` nor
//! `SlotDeriveRuntime` is in this read's import cone, so no run seed, slot
//! secret, commitment or target can appear on this wire.
//!
//! ⚠ The standing condition, carried forward from `ShipInstrumentPanel`'s own
//! docblock: the visible rotation is fine **only because the panel is communal
//! and unattributed**. If anything attributable is ever hung off the panel, the
//! rotation must leave this route.

use std::net::SocketAddr;

use axum::extract::{ConnectInfo, Path as AxumPath, State};
use axum::http::{HeaderMap, StatusCode};
use axum::routing::get;
use axum::{Json, Router};
use serde::Serialize;
use serde_json::value::RawValue;

use crate::api::RateLimiter;
// ⚑ The log key and its decoder come from the module that WRITES the log. A second spelling of
// either here would fold an empty log and serve zeros forever while the write path moved the ship.
use crate::poa_crate_api::{decode_log, log_key};
use crate::state::NodeState;
use dregg_lean_ffi::poa_crate_open_ffi::{CrateOpenLogRow, MAX_POA_CRATE_OPEN_HISTORY_ROWS};
use dregg_types::hex_encode;

pub const STATION_PANEL_PATH: &str = "/api/poa/station/{authority}/panel";
pub const STATION_CREW_PATH: &str = "/api/poa/station/{authority}/crew/{crew}";
pub const STATION_VIEW_FORMAT_V1: &str = "POA-STATION-VIEW-1";

/// ⚠ LOWERED from 120. This read was "a pure Lean function over authored constants — no replay,
/// no store access, no sponge" and is not any more: it opens the store and Lean replays the whole
/// durable log, one `openCrate` and one `observe` per row plus a prefix count, so the request is
/// QUADRATIC in the log length exactly as the crate-open write is. It is still a cheap public read
/// on an empty or short log and it is budgeted for the case where it is not.
const STATION_READS_PER_MINUTE: u32 = 60;

/// Says what the gauges MEAN, so a reader does not have to guess between "nobody has opened the
/// crate", "the organ is broken", and "the ship really has moved".
const STATION_WRITE_PATH_CLAIM: &str = "read-only projection of the node's DURABLE OPEN LOG: every gauge is the fold of that log \
     through SalvageCrate.openCrate itself, replayed from genesis, and is the same fold the \
     crate-open write path uses (StationDailyRuntime owns it; StationCrateOpenRuntime \
     abbreviates it). Zeros therefore mean the log is EMPTY — nobody has opened the crate on \
     this node — and not that openings are impossible; a crew member can open the crate at \
     POST /api/poa/station/{authority}/crate/open. A log that does not replay is a REFUSAL, \
     never a page of zeros. There is still NO CURRENT-PERIOD POINTER on this document: \
     `rotation` is the whole authored schedule rather than one day of it";

/// The station content is authored in Lean rather than installed by a ceremony.
const STATION_CONTENT_PROVENANCE: &str = "lean-authored station content (SalvageCrateExamples.config + StationCrateOpen.panel, the SAME \
     panel object the crate-open write folds receipts into); no station genesis ceremony exists, \
     so the federation_id inside the document is the AUTHORED one and need not equal authority_id";

const STATION_FINALITY_CLAIM: &str = "the station panel is a projection of installed content on this node; no quorum-finality \
     claim is made";

#[derive(Debug, Serialize)]
pub struct PoaStationResponseV1 {
    pub format: &'static str,
    /// This node's configured federation, which the path component must name.
    pub authority_id: String,
    pub content_provenance: &'static str,
    pub write_path: &'static str,
    /// The exact `POA-STATION-DAILY-OUT-1` document native Lean emitted. Not
    /// re-serialized: these are its bytes.
    pub station: Box<RawValue>,
    /// How many rows of the node's durable open log were folded to produce that
    /// document. A reader can tell "the ship has not moved because nobody has
    /// opened the crate" from "…because this read is not folding the log" —
    /// which is exactly the pair that was indistinguishable before this field
    /// existed, and stayed that way for as long as it did partly because
    /// nothing on the wire could have shown it.
    pub log_rows_folded: usize,
    pub consensus_finality: &'static str,
}

#[derive(Debug, Serialize)]
pub struct PoaStationRefusalV1 {
    pub format: &'static str,
    pub authority_id: String,
    pub refused: &'static str,
    pub detail: String,
}

type StationResult = Result<Json<PoaStationResponseV1>, (StatusCode, Json<PoaStationRefusalV1>)>;

fn refuse(
    status: StatusCode,
    authority: &str,
    refused: &'static str,
    detail: impl Into<String>,
) -> (StatusCode, Json<PoaStationRefusalV1>) {
    (
        status,
        Json(PoaStationRefusalV1 {
            format: STATION_VIEW_FORMAT_V1,
            authority_id: authority.to_owned(),
            refused,
            detail: detail.into(),
        }),
    )
}

/// One canonical URL per authority and per crew key: exactly 64 lowercase hex
/// digits. Uppercase is refused rather than normalized, so one key has one URL.
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

/// `GET /api/poa/station/{authority}/panel` — public, read-only, communal.
///
/// Serves the ship instrument panel with no crew member named at all. Lean's
/// `the_served_panel_does_not_depend_on_the_crew` proves this document's
/// communal fields are the same ones the crew route returns, so the two views
/// cannot drift.
async fn get_poa_station_panel(
    ConnectInfo(peer): ConnectInfo<SocketAddr>,
    headers: HeaderMap,
    AxumPath(authority): AxumPath<String>,
    State(state): State<NodeState>,
    limiter: RateLimiter,
) -> StationResult {
    serve_station(peer, headers, authority, None, state, limiter).await
}

/// `GET /api/poa/station/{authority}/crew/{crew}` — public, read-only.
///
/// Adds the named crew member's VISIBLE rotation to the same communal document:
/// which authored period carries which beacon, and which loot row that crew key
/// draws on each. This is publishable because the crate's own docblock makes it
/// so — the mixer is not an unpredictability source and the schedule is
/// curator-authored — and because the panel it hangs off records nobody.
async fn get_poa_station_crew(
    ConnectInfo(peer): ConnectInfo<SocketAddr>,
    headers: HeaderMap,
    AxumPath((authority, crew)): AxumPath<(String, String)>,
    State(state): State<NodeState>,
    limiter: RateLimiter,
) -> StationResult {
    serve_station(peer, headers, authority, Some(crew), state, limiter).await
}

async fn serve_station(
    peer: SocketAddr,
    headers: HeaderMap,
    authority: String,
    crew: Option<String>,
    state: NodeState,
    limiter: RateLimiter,
) -> StationResult {
    // The selectors are never echoed back before they parse: a refusal body is
    // not a mirror for arbitrary path bytes.
    let requested = parse_hex32_lowercase(&authority).ok_or_else(|| {
        refuse(
            StatusCode::BAD_REQUEST,
            "",
            "malformed-authority",
            "the authority selector must be exactly 64 lowercase hexadecimal digits",
        )
    })?;
    let normalized_request = hex_encode(&requested);

    let crew_key = match crew {
        None => None,
        Some(spelling) => Some(parse_hex32_lowercase(&spelling).ok_or_else(|| {
            refuse(
                StatusCode::BAD_REQUEST,
                &normalized_request,
                "malformed-crew",
                "the crew selector must be exactly 64 lowercase hexadecimal digits",
            )
        })?),
    };

    if !limiter.check_request(peer.ip(), &headers).await {
        return Err(refuse(
            StatusCode::TOO_MANY_REQUESTS,
            &normalized_request,
            "rate-limited",
            format!("this read is budgeted at {STATION_READS_PER_MINUTE} per minute per client"),
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

    if !dregg_lean_ffi::poa_station_daily_ffi::poa_station_daily_read_available() {
        return Err(refuse(
            StatusCode::SERVICE_UNAVAILABLE,
            &normalized,
            "lean-station-absent",
            "the Lean station read is not in the linked archive; there is no host projection",
        ));
    }

    // ⚑ THE SHIP THIS ROUTE SERVES IS THIS LOG. No lock is taken: reading a torn-free durable
    // blob needs none, and this route never appends. A concurrent open that lands between this
    // read and the reply is simply not in this reply — the next read has it.
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
        // ⚠ A blob this node did not write is a REFUSAL, not an empty log. Reading it as empty
        // would serve the installed ship and tell a player nobody has ever opened the crate.
        Some(blob) => decode_log(&blob).map_err(|detail| {
            refuse(
                StatusCode::INTERNAL_SERVER_ERROR,
                &normalized,
                "log-unreadable",
                detail,
            )
        })?,
    };
    if history.len() > MAX_POA_CRATE_OPEN_HISTORY_ROWS {
        return Err(refuse(
            StatusCode::SERVICE_UNAVAILABLE,
            &normalized,
            "log-too-long",
            format!(
                "the durable open log holds {} rows, above the {MAX_POA_CRATE_OPEN_HISTORY_ROWS}-row bound Lean's parser accepts; the ship cannot be folded until the log is rotated",
                history.len()
            ),
        ));
    }
    let log_rows_folded = history.len();

    // Native Lean work belongs off the async runtime's threads, and this one is no longer cheap:
    // the replay is a fold over the whole log.
    let wire = station_wire(crew_key.as_ref(), &history);
    let read = tokio::task::spawn_blocking(move || read_station(&wire))
        .await
        .map_err(|error| {
            refuse(
                StatusCode::INTERNAL_SERVER_ERROR,
                &normalized,
                "read-task-failed",
                error.to_string(),
            )
        })?;

    match read {
        Ok(station) => Ok(Json(PoaStationResponseV1 {
            format: STATION_VIEW_FORMAT_V1,
            authority_id: normalized,
            content_provenance: STATION_CONTENT_PROVENANCE,
            write_path: STATION_WRITE_PATH_CLAIM,
            station,
            log_rows_folded,
            consensus_finality: STATION_FINALITY_CLAIM,
        })),
        Err(StationReadError { refused, detail }) => Err(refuse(
            StatusCode::INTERNAL_SERVER_ERROR,
            &normalized,
            refused,
            detail,
        )),
    }
}

struct StationReadError {
    refused: &'static str,
    detail: String,
}

/// The exact canonical request bytes. Spelled by the FFI crate's single
/// constructor rather than by a serializer here, because Lean re-encodes what it
/// parsed and compares BYTES: a second spelling of this request is refused with
/// an empty sentinel that reads to a caller like an ordinary rejection.
fn station_wire(crew: Option<&[u8; 32]>, history: &[CrateOpenLogRow]) -> String {
    let spelling = crew.map(|key| hex_encode(key));
    dregg_lean_ffi::poa_station_daily_ffi::station_daily_request(spelling.as_deref(), history)
}

fn read_station(wire: &str) -> Result<Box<RawValue>, StationReadError> {
    let verdict =
        dregg_lean_ffi::poa_station_daily_ffi::read_poa_station_daily(wire).map_err(|error| {
            StationReadError {
                refused: "lean-transport-failed",
                detail: error,
            }
        })?;
    let view = match verdict {
        dregg_lean_ffi::poa_station_daily_ffi::PoaStationDailyVerdict::Read(view) => view,
        dregg_lean_ffi::poa_station_daily_ffi::PoaStationDailyVerdict::Rejected => {
            // ⚠ Since `station_wire` builds the canonical byte image itself — pinned by
            // `request_is_the_exact_lean_field_order_and_spelling` — the reachable cause of this
            // refusal is the LOG: a row this crate could not have accepted in that position makes
            // the whole replay `none`. That is deliberately NOT served as a ship at zero.
            return Err(StationReadError {
                refused: "lean-refused",
                detail: "native Lean refused this station read. The request is built from Lean's \
                         own canonical spelling and pinned by a test, so this is the node's \
                         durable open log failing to replay from genesis: some row is not one \
                         this crate could have accepted in that position. The ship is NOT served \
                         as zeros, because a broken log and an unopened crate must not read the \
                         same"
                    .to_owned(),
            });
        }
    };
    // Belt: the carrier must be the reply to the request we just built.
    if !view.was_read_for(wire.as_bytes()) {
        return Err(StationReadError {
            refused: "lean-reply-unbound",
            detail: "the Lean reply is not bound to this request".to_owned(),
        });
    }
    RawValue::from_string(view.into_string()).map_err(|error| StationReadError {
        refused: "lean-view-not-json",
        detail: error.to_string(),
    })
}

pub(crate) fn routes() -> Router<NodeState> {
    let limiter = RateLimiter::new(STATION_READS_PER_MINUTE, 60);
    Router::new()
        .route(
            STATION_PANEL_PATH,
            get({
                let limiter = limiter.clone();
                move |connect_info, headers, path, state| {
                    get_poa_station_panel(connect_info, headers, path, state, limiter.clone())
                }
            }),
        )
        .route(
            STATION_CREW_PATH,
            get({
                let limiter = limiter.clone();
                move |connect_info, headers, path, state| {
                    get_poa_station_crew(connect_info, headers, path, state, limiter.clone())
                }
            }),
        )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn selectors_have_one_lowercase_canonical_url() {
        let canonical = hex_encode(&[0x2b; 32]);
        assert_eq!(parse_hex32_lowercase(&canonical), Some([0x2b; 32]));
        assert_eq!(parse_hex32_lowercase(&canonical.to_uppercase()), None);
        assert_eq!(parse_hex32_lowercase(&canonical[..63]), None);
        assert_eq!(parse_hex32_lowercase("not-hex"), None);
    }

    /// The request must be the byte image `StationDailyRuntime.Request.toJson`
    /// emits, or Lean's canonical seal refuses it — silently, from the caller's
    /// point of view. This pins both spellings.
    #[test]
    fn request_is_the_exact_lean_field_order_and_spelling() {
        assert_eq!(
            station_wire(None, &[]),
            r#"{"format":"POA-STATION-DAILY-1","crew":null,"history":[]}"#
        );
        let crew = [0x28; 32];
        assert_eq!(
            station_wire(Some(&crew), &[]),
            format!(
                r#"{{"format":"POA-STATION-DAILY-1","crew":"{}","history":[]}}"#,
                "28".repeat(32)
            )
        );
        // No whitespace anywhere: Lean's encoder emits none.
        assert!(!station_wire(None, &[]).contains(' '));
        assert!(!station_wire(Some(&crew), &[]).contains(' '));
    }

    /// ⭐ THE LOG REACHES THE WIRE. This is the field whose absence made the read serve zeros
    /// while the write moved the ship, so it is asserted to be PRESENT and to carry the row —
    /// a wire that dropped it would still be canonical-looking and would still parse.
    #[test]
    fn the_durable_log_is_on_the_request_and_is_not_empty_when_the_node_holds_rows() {
        let empty = station_wire(None, &[]);
        assert!(empty.ends_with(r#""history":[]}"#), "{empty}");

        let rows = [CrateOpenLogRow {
            player: [0x29; 32],
            period: 31,
        }];
        let folded = station_wire(None, &rows);
        assert_eq!(
            folded,
            format!(
                r#"{{"format":"POA-STATION-DAILY-1","crew":null,"history":[{{"player":"{}","period":31}}]}}"#,
                "29".repeat(32)
            )
        );
        assert_ne!(folded, empty, "the log made no difference to the request");
    }

    /// The two routes differ only in whether a crew key is named — the panel
    /// route must not quietly become a per-player read.
    #[test]
    fn the_panel_route_names_no_crew_member() {
        assert!(!station_wire(None, &[]).contains("crew\":\""));
        assert!(station_wire(None, &[]).contains("\"crew\":null"));
    }

    /// ⚑ ONE LOG, ONE KEY, ONE DECODER. The station read must fold the very blob the crate-open
    /// write appends to. This asserts the key is the imported one rather than a lookalike spelled
    /// here — a divergence would make every station read fold an EMPTY log and serve zeros
    /// forever while the write path moved the ship, which is the exact defect this lane closed.
    #[test]
    fn the_station_read_folds_the_same_durable_log_the_write_appends_to() {
        let federation = [0x41; 32];
        assert_eq!(
            log_key(&federation),
            format!("poa_crate_open_log:v1:{}", hex_encode(&federation))
        );
        // And the decoder is the write path's: an empty log is the magic alone, and a blob
        // without it refuses rather than reading as zero rows.
        assert_eq!(decode_log(b"POACLOG1").expect("empty log"), Vec::new());
        assert!(decode_log(b"NOTALOG1").is_err());
        assert!(decode_log(&[]).is_err());
    }
}
