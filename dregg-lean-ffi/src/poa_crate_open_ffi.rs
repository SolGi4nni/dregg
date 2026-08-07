//! Path of Angels station crate-open WRITE boundary.
//!
//! The only implementation is
//! `Dregg2.Games.PathOfAngels.StationCrateOpenRuntime.crateOpenFFI`. This module supplies bounded
//! UTF-8 transport and preserves its two outcomes: a nonempty canonical `POA-CRATE-OPEN-OUT-1`
//! document is [`CrateOpenView`], and Lean's empty refusal sentinel is
//! [`PoaCrateOpenVerdict::Rejected`]. Archive absence, initialization failure, an interior NUL, or
//! a transport-limit fault is an `Err`.
//!
//! # Two refusals, and they are NOT the same refusal
//!
//! * [`PoaCrateOpenVerdict::Rejected`] — Lean's canonical seal declined the REQUEST BYTES. Nothing
//!   was replayed and nothing was decided.
//! * A `Read` document with `"opened":false` — Lean replayed the log and the CRATE declined the
//!   open (already opened this period, ineligible crew, a log that is not one this crate could have
//!   produced). That document carries a `refusal` tag and, by Lean's
//!   `a_refused_open_publishes_no_gauge_and_no_entry`, **no gauge and no entry**.
//!
//! Collapsing those two would make "your log is corrupt" indistinguishable from "you already opened
//! today", so the transport keeps them apart and so does the route.
//!
//! # There is no Rust fallback and there must never be one
//!
//! `SalvageCrate.OpenResult`, `SalvageCrate.OpenReceipt`, `ShipInstrumentPanel.Receipt` and
//! `SalvageCrate.CurrentStateCapability` all have PRIVATE constructors: possession of a receipt is
//! exactly possession of an accepted opening, and possession of a capability is exactly a
//! genesis-rooted chain of accepted transitions. A Rust re-typing of any of them would be a public
//! mint for a sealed authority — a caller could then post a contribution the crate never authorized
//! and move the communal gauges. Absent the export, this seam refuses and the daily ritual is
//! unavailable, which is the correct failure.
//!
//! # What the caller may author
//!
//! Identity and intent. The wire carries the authenticated opener's crew key and the node's durable
//! open log, and nothing else. There is no field for a seed, a beacon, a date, a ticket index, an
//! entry, a contribution, a counter, a sequence number, a period or a panel state — Lean derives
//! every one of those from the authored deployment and from positions in the log.
//!
//! ⚠ `StationCrateOpenRuntime.decodeRequest` is `canonicalDecode parseRequestJson Request.toJson` —
//! Lean re-encodes what it parsed and compares BYTES. The request key order at
//! [`CRATE_OPEN_INPUT_FORMAT`] is therefore load-bearing, not cosmetic: any other order is refused
//! with the `""` sentinel. Callers must build this wire from [`crate_open_request`], never from a
//! map whose order depends on a cargo feature.
//!
//! ⚑ THE NODE'S LOG IS THE REPLAY AUTHORITY. `SalvageCrate`'s append-only `consumed` set is what
//! refuses a second open of one period, and Lean rebuilds that set by replaying the log this wire
//! carries. A node that loses, truncates or fails to append to its log re-opens the crate. Lean's
//! `the_replay_guard_is_exactly_as_strong_as_the_node_log` states both halves; the storage side has
//! to carry the rest.

use crate::{ensure_lean_init, lean_init_once};

/// Host-transport ceiling for the request and the emitted document. Lean independently refuses a
/// request above its own 1 MiB pre-parser fuse and a log above 4096 rows; this only prevents
/// unbounded host allocation.
pub const MAX_POA_CRATE_OPEN_WIRE_BYTES: usize = 1024 * 1024;

/// The log bound Lean's parser enforces. Mirrors `StationCrateOpenRuntime.MAX_HISTORY_ROWS`, which
/// is `ShipInstrumentPanel.MAX_OBSERVED` — beyond it the panel refuses the fold anyway.
pub const MAX_POA_CRATE_OPEN_HISTORY_ROWS: usize = 4096;

/// The canonical request format this seam sends to Lean.
///
/// ```text
/// {"format":"POA-CRATE-OPEN-1","opener":"<64 lowercase hex>",
///  "history":[{"player":"<64 lowercase hex>","period":n},…]}
/// ```
pub const CRATE_OPEN_INPUT_FORMAT: &str = "POA-CRATE-OPEN-1";

/// The canonical document format Lean emits.
pub const CRATE_OPEN_OUTPUT_FORMAT: &str = "POA-CRATE-OPEN-OUT-1";

/// One durable open-log row: who opened, and which authored period they consumed.
///
/// There is deliberately no counter or sequence field. Lean derives both from the row's POSITION,
/// so a caller cannot advance a counter without moving a row, and moving a row breaks the replay.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CrateOpenLogRow {
    pub player: [u8; 32],
    pub period: u64,
}

/// A nonempty canonical crate-open document produced by native Lean for one exact request.
///
/// The field is private so a caller cannot substitute its own document for Lean's; the exact bytes
/// are readable through [`Self::as_str`] and are what the route serves verbatim.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CrateOpenView {
    view: String,
    opened_request_digest: [u8; 32],
}

impl CrateOpenView {
    /// Exact canonical bytes returned by native Lean.
    pub fn as_str(&self) -> &str {
        &self.view
    }

    /// Whether these bytes were produced by opening against this exact request.
    pub fn was_opened_for(&self, request: &[u8]) -> bool {
        self.opened_request_digest == *blake3::hash(request).as_bytes()
    }

    /// Consume the carrier and retain the exact Lean bytes.
    pub fn into_string(self) -> String {
        self.view
    }
}

/// The only two TRANSPORT outcomes. A crate refusal is a `Read` document whose `opened` field is
/// `false` — see the module docblock on why the two are not collapsed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PoaCrateOpenVerdict {
    /// Lean emitted these canonical `POA-CRATE-OPEN-OUT-1` bytes.
    Read(CrateOpenView),
    /// Lean refused strict canonical decoding of the request bytes.
    Rejected,
}

fn hex32(bytes: &[u8; 32]) -> String {
    let mut out = String::with_capacity(64);
    for byte in bytes {
        out.push_str(&format!("{byte:02x}"));
    }
    out
}

/// Build the exact canonical request wire. The key order here is the one Lean re-encodes and
/// compares against, so this function — not a serializer whose order is incidental — is the only
/// place the request is spelled.
pub fn crate_open_request(opener: &[u8; 32], history: &[CrateOpenLogRow]) -> String {
    let rows: Vec<String> = history
        .iter()
        .map(|row| {
            format!(
                "{{\"player\":\"{}\",\"period\":{}}}",
                hex32(&row.player),
                row.period
            )
        })
        .collect();
    format!(
        "{{\"format\":\"{CRATE_OPEN_INPUT_FORMAT}\",\"opener\":\"{}\",\"history\":[{}]}}",
        hex32(opener),
        rows.join(",")
    )
}

/// Whether the linked archive exports the crate open and the Lean runtime initialized.
pub fn poa_crate_open_available() -> bool {
    ffi_poa_crate_open::poa_crate_open_present() && lean_init_once().is_ok()
}

/// Run the Lean export and return its raw canonical output or empty refusal sentinel.
pub fn shadow_poa_crate_open(wire: &str) -> Result<String, String> {
    validate_transport_input(wire.len(), wire.as_bytes().contains(&0))?;
    ensure_lean_init()?;
    ffi_poa_crate_open::lean_poa_crate_open(wire)
}

fn validate_transport_input(len: usize, has_interior_nul: bool) -> Result<(), String> {
    if has_interior_nul {
        return Err("PoA crate-open wire has interior NUL".into());
    }
    if len > MAX_POA_CRATE_OPEN_WIRE_BYTES {
        return Err(format!(
            "dregg_poa_crate_open input exceeds {MAX_POA_CRATE_OPEN_WIRE_BYTES}-byte transport ceiling"
        ));
    }
    Ok(())
}

/// Run the Lean open, preserving seal refusal separately from transport unavailability.
pub fn open_poa_crate(wire: &str) -> Result<PoaCrateOpenVerdict, String> {
    let view = shadow_poa_crate_open(wire)?;
    Ok(decode_reply(wire, view))
}

fn decode_reply(request: &str, view: String) -> PoaCrateOpenVerdict {
    if view.is_empty() {
        PoaCrateOpenVerdict::Rejected
    } else {
        PoaCrateOpenVerdict::Read(CrateOpenView {
            view,
            opened_request_digest: *blake3::hash(request.as_bytes()).as_bytes(),
        })
    }
}

#[cfg(all(lean_lib_present, dregg_poa_crate_open_present))]
mod ffi_poa_crate_open {
    use std::ffi::CString;
    use std::os::raw::c_char;

    use super::MAX_POA_CRATE_OPEN_WIRE_BYTES;

    const MAX_BUFFER_CAP: usize = MAX_POA_CRATE_OPEN_WIRE_BYTES + 1;

    extern "C" {
        fn dregg_poa_crate_open_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
    }

    pub fn poa_crate_open_present() -> bool {
        true
    }

    pub fn lean_poa_crate_open(wire: &str) -> Result<String, String> {
        let c_in =
            CString::new(wire).map_err(|e| format!("PoA crate-open wire has interior NUL: {e}"))?;
        let requested = wire
            .len()
            .checked_mul(2)
            .and_then(|n| n.checked_add(4096))
            .unwrap_or(MAX_BUFFER_CAP);
        let mut cap = requested.clamp(4096, MAX_BUFFER_CAP);

        loop {
            let mut buf = vec![0u8; cap];
            let full = unsafe {
                dregg_poa_crate_open_str(c_in.as_ptr(), buf.as_mut_ptr().cast::<c_char>(), cap)
            };
            if full == usize::MAX {
                return Err(
                    "dregg_poa_crate_open_str refused an unusable or over-limit transport".into(),
                );
            }
            if full > MAX_POA_CRATE_OPEN_WIRE_BYTES {
                return Err(format!(
                    "dregg_poa_crate_open output exceeds {MAX_POA_CRATE_OPEN_WIRE_BYTES}-byte transport ceiling"
                ));
            }
            if full < cap {
                return String::from_utf8(buf[..full].to_vec())
                    .map_err(|e| format!("PoA crate-open result is not UTF-8: {e}"));
            }
            cap = full
                .checked_add(1)
                .filter(|next| *next <= MAX_BUFFER_CAP)
                .ok_or_else(|| "dregg_poa_crate_open output length overflow".to_owned())?;
        }
    }
}

#[cfg(not(all(lean_lib_present, dregg_poa_crate_open_present)))]
mod ffi_poa_crate_open {
    pub fn poa_crate_open_present() -> bool {
        false
    }

    pub fn lean_poa_crate_open(_wire: &str) -> Result<String, String> {
        Err(
            "dregg_poa_crate_open not exported by the linked archive; the PoA crate open refuses"
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
            PoaCrateOpenVerdict::Rejected
        );
    }

    #[test]
    fn nonempty_lean_reply_is_preserved_opaquely_and_bound_to_its_request() {
        let view = r#"{"format":"POA-CRATE-OPEN-OUT-1"}"#.to_owned();
        let PoaCrateOpenVerdict::Read(read) = decode_reply("exact request", view.clone()) else {
            panic!("a nonempty native reply must be read");
        };
        assert_eq!(read.as_str(), view);
        assert!(read.was_opened_for(b"exact request"));
        assert!(!read.was_opened_for(b"another request"));
    }

    #[test]
    fn interior_nul_and_oversize_are_transport_faults() {
        assert!(validate_transport_input(4, true).is_err());
        assert!(validate_transport_input(MAX_POA_CRATE_OPEN_WIRE_BYTES + 1, false).is_err());
        assert!(validate_transport_input(MAX_POA_CRATE_OPEN_WIRE_BYTES, false).is_ok());
    }

    /// The request spelling is the one Lean re-encodes and compares BYTES against, so it is pinned
    /// here rather than left to a serializer whose key order is incidental.
    #[test]
    fn the_request_wire_is_spelled_exactly_once() {
        let opener = [0x29; 32];
        assert_eq!(
            crate_open_request(&opener, &[]),
            format!(
                r#"{{"format":"POA-CRATE-OPEN-1","opener":"{}","history":[]}}"#,
                "29".repeat(32)
            )
        );
        let player = [0x28; 32];
        assert_eq!(
            crate_open_request(&opener, &[CrateOpenLogRow { player, period: 31 }]),
            format!(
                r#"{{"format":"POA-CRATE-OPEN-1","opener":"{}","history":[{{"player":"{}","period":31}}]}}"#,
                "29".repeat(32),
                "28".repeat(32)
            )
        );
    }

    /// No whitespace anywhere: Lean's encoder emits none, and its seal compares bytes.
    #[test]
    fn the_request_wire_carries_no_whitespace() {
        let wire = crate_open_request(
            &[0x01; 32],
            &[
                CrateOpenLogRow {
                    player: [0x02; 32],
                    period: 31,
                },
                CrateOpenLogRow {
                    player: [0x03; 32],
                    period: 31,
                },
            ],
        );
        assert!(!wire.contains(' '));
        assert!(!wire.contains('\n'));
    }
}
