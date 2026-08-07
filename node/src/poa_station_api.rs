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
//! # READ ONLY, and by TYPE rather than by policy
//!
//! Nothing in this module needs to *decline* to write:
//!
//! * `SalvageCrate.openCore` is `private`;
//! * `SalvageCrate.openCrate` demands a `CurrentStateCapability`, declared
//!   `opaque` with **no producer anywhere in the tree** — no Lean term builds
//!   one, so no `@[export]` can hand one to Rust;
//! * `SalvageCrate.State` has a private `mk` and deliberately no public
//!   empty-state producer ("genesis/restore belongs to the global state
//!   adapter", and no such adapter exists).
//!
//! So the ship this route serves is `ShipInstrumentPanel.initial`: the station
//! exactly as installed. That is not a placeholder dressed as content — Lean's
//! `the_served_ship_has_not_been_moved` asserts it (every gauge zero, nothing
//! observed, nothing admitted), and it is the assertion that goes RED the day a
//! judged opening can be folded in.
//!
//! [`STATION_WRITE_PATH_CLAIM`] says that in the response rather than leaving a
//! reader to infer "nothing has happened yet" from a page of zeros.
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
use crate::state::NodeState;
use dregg_types::hex_encode;

pub const STATION_PANEL_PATH: &str = "/api/poa/station/{authority}/panel";
pub const STATION_CREW_PATH: &str = "/api/poa/station/{authority}/crew/{crew}";
pub const STATION_VIEW_FORMAT_V1: &str = "POA-STATION-VIEW-1";

/// This read is a pure Lean function over authored constants — no replay, no
/// store access, no sponge. It is budgeted like the other cheap public reads.
const STATION_READS_PER_MINUTE: u32 = 120;

/// Says what a page of zeros MEANS, so a reader does not have to guess between
/// "nobody has opened the crate" and "the organ is broken".
const STATION_WRITE_PATH_CLAIM: &str = "read-only: no judged opening exists, so every gauge reads its installed value. \
     SalvageCrate.openCrate requires a CurrentStateCapability, declared opaque with no producer \
     anywhere, so this is a type-level absence and not an unwired route. For the same reason \
     there is no SalvageCrate.State and therefore NO CURRENT-PERIOD POINTER: 'what does the \
     crate hold today' is not answerable here, and `rotation` is the whole authored schedule \
     rather than one day of it";

/// The station content is authored in Lean rather than installed by a ceremony.
const STATION_CONTENT_PROVENANCE: &str = "lean-authored station content (SalvageCrateExamples.config + StationDailyRuntime.\
     stationPanel); no station genesis ceremony exists, so the federation_id inside the \
     document is the AUTHORED one and need not equal authority_id";

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

    let (federation_configured, federation_id) = {
        let s = state.read().await;
        (s.federation_configured, s.federation_id)
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

    // Native Lean work belongs off the async runtime's threads even when it is
    // cheap: the same discipline as every other Lean call site here.
    let wire = station_wire(crew_key.as_ref());
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
fn station_wire(crew: Option<&[u8; 32]>) -> String {
    let spelling = crew.map(|key| hex_encode(key));
    dregg_lean_ffi::poa_station_daily_ffi::station_daily_request(spelling.as_deref())
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
            return Err(StationReadError {
                refused: "lean-refused",
                detail: "native Lean refused this request: it is not the canonical byte image \
                         StationDailyRuntime.Request.toJson emits"
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
            station_wire(None),
            r#"{"format":"POA-STATION-DAILY-1","crew":null}"#
        );
        let crew = [0x28; 32];
        assert_eq!(
            station_wire(Some(&crew)),
            format!(
                r#"{{"format":"POA-STATION-DAILY-1","crew":"{}"}}"#,
                "28".repeat(32)
            )
        );
        // No whitespace anywhere: Lean's encoder emits none.
        assert!(!station_wire(None).contains(' '));
        assert!(!station_wire(Some(&crew)).contains(' '));
    }

    /// The two routes differ only in whether a crew key is named — the panel
    /// route must not quietly become a per-player read.
    #[test]
    fn the_panel_route_names_no_crew_member() {
        assert!(!station_wire(None).contains("crew\":\""));
        assert!(station_wire(None).contains("\"crew\":null"));
    }
}
