//! Path of Angels station daily READ boundary.
//!
//! The only implementation is
//! `Dregg2.Games.PathOfAngels.StationDailyRuntime.stationDailyReadFFI`. This module supplies
//! bounded UTF-8 transport and preserves its two outcomes: a nonempty canonical
//! `POA-STATION-DAILY-OUT-1` document is [`StationDailyView`], and Lean's empty refusal sentinel
//! is [`PoaStationDailyVerdict::Rejected`]. Archive absence, initialization failure, an interior
//! NUL, or a transport-limit fault is an `Err`.
//!
//! # There is no Rust fallback and there must never be one
//!
//! `SalvageCrate` (the daily ritual) and `ShipInstrumentPanel` (the communal ship it moves) both
//! seal their authority in the type system: `ShipInstrumentPanel.Receipt` and
//! `SalvageCrate.OpenResult` have PRIVATE constructors, so possession of a receipt is exactly
//! possession of an accepted opening. A Rust re-typing of either would be a public mint for a
//! sealed authority — a caller could post a contribution the crate never authorized and move the
//! communal gauges.
//!
//! # This seam is READ-ONLY because it RETURNS A DOCUMENT, not because it cannot reach the write
//!
//! ⚠ CORRECTED. The three bullets here used to say `SalvageCrate.openCrate` demanded a
//! `CurrentStateCapability` "declared `opaque` with no producer anywhere in the tree". That is
//! false at HEAD: the capability is a sealed structure rooted in `genesis`, `openCrate` is
//! reachable, and this read reaches it once per log row while replaying. What keeps the seam
//! read-only is narrower and still sufficient:
//!
//! * every `OpenResult` the replay produces is consumed by the fold and dropped — the export
//!   returns a projection and nothing else;
//! * NO ROW IS APPENDED HERE. Only `node/src/poa_crate_api.rs` appends, and only after Lean
//!   reports an accepted open;
//! * `SalvageCrate.openCore` is `private`, so no module outside the crate can call it;
//! * `ShipInstrumentPanel.Receipt` has a private `mk` whose only producer consumes an accepted
//!   `OpenReceipt`, so no wire can decode a receipt into existence.
//!
//! A log a caller did not earn buys nothing: a row the crate would not have accepted in that
//! position makes the whole replay `none` and the reply the `""` refusal.
//!
//! # ⚑ THIS SEAM CARRIES THE NODE'S DURABLE OPEN LOG
//!
//! ⚠ CORRECTED. This docblock used to say the panel served was `ShipInstrumentPanel.initial` —
//! "the ship exactly as installed" — and cited `the_served_ship_has_not_been_moved` as "the
//! assertion that goes RED the day a judged opening can be folded in, which is when this seam must
//! grow a second input". That day came, the assertion did NOT go red (it was about the request
//! type, not about reachability), and **this is that second input**.
//!
//! `station_daily_request` now takes the node's durable open log. Lean replays it through
//! `SalvageCrate.openCrate` — the same fold the crate-open write path uses, which lives in
//! `StationDailyRuntime` precisely so there is only one — and serves the ship it folds to. The
//! retired assertion is replaced by `the_served_ship_moves_when_the_log_records_an_opening`, a pair
//! whose halves differ by one log row, and by
//! `StationCrateOpenRuntime.the_station_read_serves_the_ship_this_write_published`, which equates
//! this read's communal fields with the panel the write published.
//!
//! ⚠ A log that does not replay is Lean's `""` refusal, NOT a ship at zero. The caller must
//! surface that as a refusal — rendering it as an unmoved ship is indistinguishable, to a player,
//! from "nobody has opened the crate yet".
//!
//! ⚠ `StationDailyRuntime.decodeRequest` is `canonicalDecode parseRequestJson Request.toJson` —
//! Lean re-encodes what it parsed and compares BYTES. The request key order at
//! [`STATION_DAILY_INPUT_FORMAT`] is therefore load-bearing, not cosmetic: any other order is
//! refused with the `""` sentinel. Callers must build this wire from a type whose field order is
//! fixed, never from a map whose order depends on a cargo feature.

use crate::poa_crate_open_ffi::{crate_open_log_rows_json, CrateOpenLogRow};
use crate::{ensure_lean_init, lean_init_once};

/// Host-transport ceiling for the request and the emitted document. Lean independently refuses a
/// request above its own 16 KiB pre-parser fuse; this only prevents unbounded host allocation.
pub const MAX_POA_STATION_DAILY_WIRE_BYTES: usize = 1024 * 1024;

/// The canonical request format this seam sends to Lean.
///
/// ```text
/// {"format":"POA-STATION-DAILY-1","crew":null,"history":[]}
/// {"format":"POA-STATION-DAILY-1","crew":"<64 lowercase hex>",
///  "history":[{"player":"<64 lowercase hex>","period":n},…]}
/// ```
///
/// `null` and a 64-digit lowercase hex string are the only accepted spellings of the `crew`
/// field, and each has exactly one, so "absent" has no second encoding.
///
/// ⚠ THE PRE-`history` SHAPE NO LONGER LOADS. `{"format":…,"crew":null}` is a MISSING FIELD to
/// Lean's exact-key parser, not a request with an implicitly empty log — deliberately, because a
/// defaulted history would serve the installed ship to every caller of the old shape, which is the
/// silent zero this input exists to remove. Lean pins it:
/// `StationDailyRuntime.the_pre_history_request_shape_refuses`.
pub const STATION_DAILY_INPUT_FORMAT: &str = "POA-STATION-DAILY-1";

/// The canonical document format Lean emits.
pub const STATION_DAILY_OUTPUT_FORMAT: &str = "POA-STATION-DAILY-OUT-1";

/// A nonempty canonical station document produced by native Lean for one exact request.
///
/// The field is private so a caller cannot substitute its own document for Lean's; the exact
/// bytes are readable through [`Self::as_str`] and are what the public route serves verbatim.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StationDailyView {
    view: String,
    read_request_digest: [u8; 32],
}

impl StationDailyView {
    /// Exact canonical bytes returned by native Lean.
    pub fn as_str(&self) -> &str {
        &self.view
    }

    /// Whether these bytes were produced by reading this exact request.
    pub fn was_read_for(&self, request: &[u8]) -> bool {
        self.read_request_digest == *blake3::hash(request).as_bytes()
    }

    /// Consume the carrier and retain the exact Lean bytes.
    pub fn into_string(self) -> String {
        self.view
    }
}

/// The only two semantic outcomes exposed by the read.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PoaStationDailyVerdict {
    /// Lean emitted these canonical `POA-STATION-DAILY-OUT-1` bytes.
    Read(StationDailyView),
    /// Lean refused strict canonical decoding of the request.
    Rejected,
}

/// Build the exact canonical request wire. The key order here is the one Lean re-encodes and
/// compares against, so this function — not a serializer whose order is incidental — is the only
/// place the request is spelled.
///
/// `history` is the node's durable open log. The rows are spelled by
/// [`crate::poa_crate_open_ffi::crate_open_log_rows_json`], the same function the crate-open write
/// wire uses, because the node must not spell its own log two ways on two wires.
pub fn station_daily_request(crew_hex: Option<&str>, history: &[CrateOpenLogRow]) -> String {
    let rows = crate_open_log_rows_json(history);
    match crew_hex {
        None => {
            format!("{{\"format\":\"{STATION_DAILY_INPUT_FORMAT}\",\"crew\":null,\"history\":[{rows}]}}")
        }
        Some(hex) => {
            format!(
                "{{\"format\":\"{STATION_DAILY_INPUT_FORMAT}\",\"crew\":\"{hex}\",\"history\":[{rows}]}}"
            )
        }
    }
}

/// Whether the linked archive exports the station daily read and the Lean runtime initialized.
pub fn poa_station_daily_read_available() -> bool {
    ffi_poa_station_daily::poa_station_daily_read_present() && lean_init_once().is_ok()
}

/// Run the Lean export and return its raw canonical output or empty refusal sentinel.
pub fn shadow_poa_station_daily_read(wire: &str) -> Result<String, String> {
    validate_transport_input(wire.len(), wire.as_bytes().contains(&0))?;
    ensure_lean_init()?;
    ffi_poa_station_daily::lean_poa_station_daily_read(wire)
}

fn validate_transport_input(len: usize, has_interior_nul: bool) -> Result<(), String> {
    if has_interior_nul {
        return Err("PoA station daily wire has interior NUL".into());
    }
    if len > MAX_POA_STATION_DAILY_WIRE_BYTES {
        return Err(format!(
            "dregg_poa_station_daily_read input exceeds {MAX_POA_STATION_DAILY_WIRE_BYTES}-byte transport ceiling"
        ));
    }
    Ok(())
}

/// Run the Lean read, preserving refusal separately from transport unavailability.
pub fn read_poa_station_daily(wire: &str) -> Result<PoaStationDailyVerdict, String> {
    let view = shadow_poa_station_daily_read(wire)?;
    Ok(decode_reply(wire, view))
}

fn decode_reply(request: &str, view: String) -> PoaStationDailyVerdict {
    if view.is_empty() {
        PoaStationDailyVerdict::Rejected
    } else {
        PoaStationDailyVerdict::Read(StationDailyView {
            view,
            read_request_digest: *blake3::hash(request.as_bytes()).as_bytes(),
        })
    }
}

#[cfg(all(lean_lib_present, dregg_poa_station_daily_read_present))]
mod ffi_poa_station_daily {
    use std::ffi::CString;
    use std::os::raw::c_char;

    use super::MAX_POA_STATION_DAILY_WIRE_BYTES;

    const MAX_BUFFER_CAP: usize = MAX_POA_STATION_DAILY_WIRE_BYTES + 1;

    extern "C" {
        fn dregg_poa_station_daily_read_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
    }

    pub fn poa_station_daily_read_present() -> bool {
        true
    }

    pub fn lean_poa_station_daily_read(wire: &str) -> Result<String, String> {
        let c_in = CString::new(wire)
            .map_err(|e| format!("PoA station daily wire has interior NUL: {e}"))?;
        let requested = wire
            .len()
            .checked_mul(2)
            .and_then(|n| n.checked_add(4096))
            .unwrap_or(MAX_BUFFER_CAP);
        let mut cap = requested.clamp(4096, MAX_BUFFER_CAP);

        loop {
            let mut buf = vec![0u8; cap];
            let full = unsafe {
                dregg_poa_station_daily_read_str(
                    c_in.as_ptr(),
                    buf.as_mut_ptr().cast::<c_char>(),
                    cap,
                )
            };
            if full == usize::MAX {
                return Err(
                    "dregg_poa_station_daily_read_str refused an unusable or over-limit transport"
                        .into(),
                );
            }
            if full > MAX_POA_STATION_DAILY_WIRE_BYTES {
                return Err(format!(
                    "dregg_poa_station_daily_read output exceeds {MAX_POA_STATION_DAILY_WIRE_BYTES}-byte transport ceiling"
                ));
            }
            if full < cap {
                return String::from_utf8(buf[..full].to_vec())
                    .map_err(|e| format!("PoA station daily result is not UTF-8: {e}"));
            }
            cap = full
                .checked_add(1)
                .filter(|next| *next <= MAX_BUFFER_CAP)
                .ok_or_else(|| "dregg_poa_station_daily_read output length overflow".to_owned())?;
        }
    }
}

#[cfg(not(all(lean_lib_present, dregg_poa_station_daily_read_present)))]
mod ffi_poa_station_daily {
    pub fn poa_station_daily_read_present() -> bool {
        false
    }

    pub fn lean_poa_station_daily_read(_wire: &str) -> Result<String, String> {
        Err(
            "dregg_poa_station_daily_read not exported by the linked archive; the PoA station read refuses"
                .into(),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_lean_reply_is_rejected_not_read() {
        assert_eq!(
            decode_reply("request", String::new()),
            PoaStationDailyVerdict::Rejected
        );
    }

    #[test]
    fn nonempty_lean_reply_is_preserved_opaquely_and_bound_to_its_request() {
        let view = r#"{"format":"POA-STATION-DAILY-OUT-1"}"#.to_owned();
        let PoaStationDailyVerdict::Read(read) = decode_reply("exact request", view.clone()) else {
            panic!("a nonempty native reply must be read");
        };
        assert_eq!(read.as_str(), view);
        assert!(read.was_read_for(b"exact request"));
        assert!(!read.was_read_for(b"another request"));
    }

    #[test]
    fn interior_nul_and_oversize_are_transport_faults() {
        assert!(validate_transport_input(4, true).is_err());
        assert!(validate_transport_input(MAX_POA_STATION_DAILY_WIRE_BYTES + 1, false).is_err());
        assert!(validate_transport_input(MAX_POA_STATION_DAILY_WIRE_BYTES, false).is_ok());
    }

    /// The request spelling is the one Lean re-encodes and compares BYTES against, so it is pinned
    /// here rather than left to a serializer whose key order is incidental.
    #[test]
    fn the_request_wire_is_spelled_exactly_once() {
        assert_eq!(
            station_daily_request(None, &[]),
            r#"{"format":"POA-STATION-DAILY-1","crew":null,"history":[]}"#
        );
        assert_eq!(
            station_daily_request(Some(&"aa".repeat(32)), &[]),
            format!(
                r#"{{"format":"POA-STATION-DAILY-1","crew":"{}","history":[]}}"#,
                "aa".repeat(32)
            )
        );
    }

    /// ⚑ THE LOG IS SPELLED BY ONE FUNCTION, ON BOTH WIRES. The `history` array this read sends
    /// must be byte-identical to the one the crate-open write sends for the same log, because Lean
    /// parses both with the same exact-key row parser and folds both with the same replay. A
    /// second spelling here is how the read and the write come to report different ships.
    #[test]
    fn the_read_and_the_write_spell_the_node_log_identically() {
        let rows = [
            CrateOpenLogRow {
                player: [0x29; 32],
                period: 31,
            },
            CrateOpenLogRow {
                player: [0x28; 32],
                period: 31,
            },
        ];
        let read = station_daily_request(None, &rows);
        let write = crate::poa_crate_open_ffi::crate_open_request(&[0x2a; 32], &rows);

        let body = crate_open_log_rows_json(&rows);
        assert_eq!(
            body,
            format!(
                r#"{{"player":"{}","period":31}},{{"player":"{}","period":31}}"#,
                "29".repeat(32),
                "28".repeat(32)
            )
        );
        // The identical substring is the point: neither wire re-spells the log.
        assert!(read.contains(&format!("\"history\":[{body}]")));
        assert!(write.contains(&format!("\"history\":[{body}]")));
        assert!(!read.contains(' '));
    }
}
