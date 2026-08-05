//! Path of Angels Records read boundary.
//!
//! The only implementation is `Dregg2.Games.PathOfAngels.RecordsRuntime.recordsProjectFFI`. This
//! module supplies bounded UTF-8 transport and preserves its two outcomes: a nonempty canonical
//! `POA-RECORDS-OUT-1` document is [`ProjectedRecords`], and Lean's empty refusal sentinel is
//! [`PoaRecordsVerdict::Rejected`]. Archive absence, initialization failure, an interior NUL, or a
//! transport-limit fault is an `Err`; none has a Rust fallback, and in particular there is no
//! host-side projection of a finalized run — the record shape is Lean's alone.
//!
//! Availability is not authority in either direction. This export re-judges exactly the bytes it
//! is handed; that those bytes came from finality is the caller's separate obligation, discharged
//! by the durable replay driver, not by calling this function.

use crate::{ensure_lean_init, lean_init_once};

/// Host-transport ceiling for both the request and the emitted view. Lean independently refuses
/// above its own 64 MiB pre-parser fuse and enforces its row/component bounds; this only prevents
/// unbounded host allocation before and after the call.
pub const MAX_POA_RECORDS_WIRE_BYTES: usize = 64 * 1024 * 1024;

/// A nonempty canonical Records view produced by native Lean for one exact request.
///
/// The fields are private so a caller cannot substitute its own document for Lean's; the exact
/// bytes are readable through [`Self::as_str`] and are what the public route serves verbatim.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProjectedRecords {
    view: String,
    projected_request_digest: [u8; 32],
}

impl ProjectedRecords {
    /// Exact canonical bytes returned by native Lean.
    pub fn as_str(&self) -> &str {
        &self.view
    }

    /// Whether these bytes were produced by projecting this exact request.
    pub fn was_projected_for(&self, request: &[u8]) -> bool {
        self.projected_request_digest == *blake3::hash(request).as_bytes()
    }

    /// Consume the carrier and retain the exact Lean bytes.
    pub fn into_string(self) -> String {
        self.view
    }
}

/// The only two semantic outcomes exposed by the read model.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PoaRecordsVerdict {
    /// Lean rebuilt the projection and emitted these canonical `POA-RECORDS-OUT-1` bytes.
    Projected(ProjectedRecords),
    /// Lean refused strict decoding, the world/mission binding, a row's re-judgement, the Canon
    /// refold, or the commit ordering.
    Rejected,
}

/// Whether the linked archive exports the Records read model and the Lean runtime initialized.
pub fn poa_records_project_available() -> bool {
    ffi_poa_records::poa_records_project_present() && lean_init_once().is_ok()
}

/// Run the Lean export and return its raw canonical output or empty refusal sentinel.
pub fn shadow_poa_records_project(wire: &str) -> Result<String, String> {
    validate_transport_input(wire.len(), wire.as_bytes().contains(&0))?;
    ensure_lean_init()?;
    ffi_poa_records::lean_poa_records_project(wire)
}

fn validate_transport_input(len: usize, has_interior_nul: bool) -> Result<(), String> {
    if has_interior_nul {
        return Err("PoA Records wire has interior NUL".into());
    }
    if len > MAX_POA_RECORDS_WIRE_BYTES {
        return Err(format!(
            "dregg_poa_records_project input exceeds {MAX_POA_RECORDS_WIRE_BYTES}-byte transport ceiling"
        ));
    }
    Ok(())
}

/// Run the Lean read model, preserving refusal separately from transport unavailability.
pub fn project_poa_records(wire: &str) -> Result<PoaRecordsVerdict, String> {
    let view = shadow_poa_records_project(wire)?;
    Ok(decode_reply(wire, view))
}

fn decode_reply(request: &str, view: String) -> PoaRecordsVerdict {
    if view.is_empty() {
        PoaRecordsVerdict::Rejected
    } else {
        PoaRecordsVerdict::Projected(ProjectedRecords {
            view,
            projected_request_digest: *blake3::hash(request.as_bytes()).as_bytes(),
        })
    }
}

#[cfg(all(lean_lib_present, dregg_poa_records_project_present))]
mod ffi_poa_records {
    use std::ffi::CString;
    use std::os::raw::c_char;

    use super::MAX_POA_RECORDS_WIRE_BYTES;

    const MAX_BUFFER_CAP: usize = MAX_POA_RECORDS_WIRE_BYTES + 1;

    extern "C" {
        fn dregg_poa_records_project_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
    }

    pub fn poa_records_project_present() -> bool {
        true
    }

    pub fn lean_poa_records_project(wire: &str) -> Result<String, String> {
        let c_in =
            CString::new(wire).map_err(|e| format!("PoA Records wire has interior NUL: {e}"))?;
        let requested = wire
            .len()
            .checked_mul(2)
            .and_then(|n| n.checked_add(1024))
            .unwrap_or(MAX_BUFFER_CAP);
        let mut cap = requested.clamp(1024, MAX_BUFFER_CAP);

        loop {
            let mut buf = vec![0u8; cap];
            let full = unsafe {
                dregg_poa_records_project_str(c_in.as_ptr(), buf.as_mut_ptr().cast::<c_char>(), cap)
            };
            if full == usize::MAX {
                return Err(
                    "dregg_poa_records_project_str refused an unusable or over-limit transport"
                        .into(),
                );
            }
            if full > MAX_POA_RECORDS_WIRE_BYTES {
                return Err(format!(
                    "dregg_poa_records_project output exceeds {MAX_POA_RECORDS_WIRE_BYTES}-byte transport ceiling"
                ));
            }
            if full < cap {
                return String::from_utf8(buf[..full].to_vec())
                    .map_err(|e| format!("PoA Records result is not UTF-8: {e}"));
            }
            cap = full
                .checked_add(1)
                .filter(|next| *next <= MAX_BUFFER_CAP)
                .ok_or_else(|| "dregg_poa_records_project output length overflow".to_owned())?;
        }
    }
}

#[cfg(not(all(lean_lib_present, dregg_poa_records_project_present)))]
mod ffi_poa_records {
    pub fn poa_records_project_present() -> bool {
        false
    }

    pub fn lean_poa_records_project(_wire: &str) -> Result<String, String> {
        Err(
            "dregg_poa_records_project not exported by the linked archive; the PoA Records read refuses"
                .into(),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_lean_reply_is_rejected_not_projected() {
        assert_eq!(
            decode_reply("request", String::new()),
            PoaRecordsVerdict::Rejected
        );
    }

    #[test]
    fn nonempty_lean_reply_is_preserved_opaquely_and_bound_to_its_request() {
        let view = r#"{"format":"POA-RECORDS-OUT-1"}"#.to_owned();
        let PoaRecordsVerdict::Projected(projected) = decode_reply("exact request", view.clone())
        else {
            panic!("a nonempty native reply must be projected");
        };
        assert_eq!(projected.as_str(), view);
        assert!(projected.was_projected_for(b"exact request"));
        assert!(!projected.was_projected_for(b"another request"));
    }

    #[test]
    fn interior_nul_and_oversize_are_transport_faults() {
        assert!(validate_transport_input(4, true).is_err());
        assert!(validate_transport_input(MAX_POA_RECORDS_WIRE_BYTES + 1, false).is_err());
        assert!(validate_transport_input(MAX_POA_RECORDS_WIRE_BYTES, false).is_ok());
    }
}
