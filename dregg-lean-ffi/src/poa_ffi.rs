//! Internal Path of Angels Signal evaluator boundary.
//!
//! The only semantic implementation is
//! `Dregg2.Games.PathOfAngels.NetworkJudge.signalJudgeFFI`. This module supplies bounded UTF-8
//! transport and preserves its two outcomes: a nonempty canonical successor is [`Accepted`], and
//! Lean's empty refusal sentinel is [`Rejected`]. Archive absence, initialization failure, an
//! interior NUL, or a transport-limit fault is an `Err`; none has a Rust semantic fallback.
//!
//! Availability is not authority. The Lean evaluator assumes `FinalizedCarrier` came from the
//! finalized SignedTurn path. This wrapper must remain internal until a node adapter replaces all
//! caller state with persisted Canon/config and derives the carrier from authenticated finality.

use crate::{ensure_lean_init, lean_init_once};

/// Hard host-transport ceiling for both canonical input and canonical output.
///
/// This is intentionally not game semantics. Lean independently refuses input above its 16 MiB
/// pre-parser `WIRE_BYTE_LIMIT` and enforces its element/count bounds. The looser host ceiling
/// prevents a malformed foreign caller or corrupted output length from driving unbounded allocation
/// before/after the FFI call; a value between 16 and 64 MiB still reaches Lean only to be rejected.
pub const MAX_POA_SIGNAL_WIRE_BYTES: usize = 64 * 1024 * 1024;

/// A nonempty canonical reply produced by native Lean for one exact input.
///
/// The fields are deliberately private.  Persistence accepts this carrier,
/// rather than arbitrary output bytes, when it prepares a durable Signal
/// transition.  This prevents a downstream Rust caller from laundering
/// caller-authored bytes as a Lean verdict while still permitting strict
/// node-side parsing through [`Self::as_str`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AcceptedPoaSignalOutput {
    output: String,
    judged_input_digest: [u8; 32],
}

impl AcceptedPoaSignalOutput {
    /// Exact canonical bytes returned by native Lean.
    pub fn as_str(&self) -> &str {
        &self.output
    }

    /// Whether these bytes were produced by judging this exact input.
    pub fn was_judged_for(&self, input: &[u8]) -> bool {
        self.judged_input_digest == *blake3::hash(input).as_bytes()
    }

    /// Consume the authority carrier and retain the exact Lean bytes.
    pub fn into_string(self) -> String {
        self.output
    }
}

/// The only two semantic outcomes exposed by the internal evaluator.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PoaSignalVerdict {
    /// Lean replayed the complete transition and emitted these canonical `POA-RUN-OUT-1` bytes.
    Accepted(AcceptedPoaSignalOutput),
    /// Lean refused strict decoding, semantic reconstruction, game replay, or Canon application.
    Rejected,
}

/// Whether the linked archive exports the PoA Signal evaluator and the Lean runtime initialized.
///
/// `true` says only that an evaluator is callable. It does not authenticate any carrier/state
/// supplied on its wire.
pub fn poa_signal_judge_available() -> bool {
    ffi_poa::poa_signal_judge_present() && lean_init_once().is_ok()
}

/// Run the Lean export and return its raw canonical output or empty refusal sentinel.
pub fn shadow_poa_signal_judge(wire: &str) -> Result<String, String> {
    validate_transport_input(wire.len(), wire.as_bytes().contains(&0))?;
    ensure_lean_init()?;
    ffi_poa::lean_poa_signal_judge(wire)
}

fn validate_transport_input(len: usize, has_interior_nul: bool) -> Result<(), String> {
    if has_interior_nul {
        return Err("PoA Signal wire has interior NUL".into());
    }
    if len > MAX_POA_SIGNAL_WIRE_BYTES {
        return Err(format!(
            "dregg_poa_signal_judge input exceeds {MAX_POA_SIGNAL_WIRE_BYTES}-byte transport ceiling"
        ));
    }
    Ok(())
}

/// Run the internal Lean evaluator, preserving refusal separately from transport unavailability.
///
/// There is deliberately no Rust parser or reimplementation here. Nonempty bytes are exactly what
/// the Lean encoder returned; callers that need semantic authority must recompute and bind those
/// bytes from authenticated node state outside this module.
pub fn judge_poa_signal(wire: &str) -> Result<PoaSignalVerdict, String> {
    let output = shadow_poa_signal_judge(wire)?;
    Ok(decode_reply(wire, output))
}

fn decode_reply(input: &str, output: String) -> PoaSignalVerdict {
    if output.is_empty() {
        PoaSignalVerdict::Rejected
    } else {
        PoaSignalVerdict::Accepted(AcceptedPoaSignalOutput {
            output,
            judged_input_digest: *blake3::hash(input.as_bytes()).as_bytes(),
        })
    }
}

#[cfg(all(lean_lib_present, dregg_poa_signal_judge_present))]
mod ffi_poa {
    use std::ffi::CString;
    use std::os::raw::c_char;

    use super::MAX_POA_SIGNAL_WIRE_BYTES;

    const MAX_BUFFER_CAP: usize = MAX_POA_SIGNAL_WIRE_BYTES + 1;

    extern "C" {
        fn dregg_poa_signal_judge_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
    }

    pub fn poa_signal_judge_present() -> bool {
        true
    }

    pub fn lean_poa_signal_judge(wire: &str) -> Result<String, String> {
        let c_in =
            CString::new(wire).map_err(|e| format!("PoA Signal wire has interior NUL: {e}"))?;
        let requested = wire
            .len()
            .checked_mul(2)
            .and_then(|n| n.checked_add(1024))
            .unwrap_or(MAX_BUFFER_CAP);
        let mut cap = requested.clamp(1024, MAX_BUFFER_CAP);

        loop {
            let mut buf = vec![0u8; cap];
            let full = unsafe {
                dregg_poa_signal_judge_str(c_in.as_ptr(), buf.as_mut_ptr().cast::<c_char>(), cap)
            };
            if full == usize::MAX {
                return Err(
                    "dregg_poa_signal_judge_str refused an unusable or over-limit transport".into(),
                );
            }
            if full > MAX_POA_SIGNAL_WIRE_BYTES {
                return Err(format!(
                    "dregg_poa_signal_judge output exceeds {MAX_POA_SIGNAL_WIRE_BYTES}-byte transport ceiling"
                ));
            }
            if full < cap {
                return String::from_utf8(buf[..full].to_vec())
                    .map_err(|e| format!("PoA Signal result is not UTF-8: {e}"));
            }
            cap = full
                .checked_add(1)
                .filter(|next| *next <= MAX_BUFFER_CAP)
                .ok_or_else(|| "dregg_poa_signal_judge output length overflow".to_owned())?;
        }
    }
}

#[cfg(not(all(lean_lib_present, dregg_poa_signal_judge_present)))]
mod ffi_poa {
    pub fn poa_signal_judge_present() -> bool {
        false
    }

    pub fn lean_poa_signal_judge(_wire: &str) -> Result<String, String> {
        Err(
            "dregg_poa_signal_judge not exported by the linked archive; internal PoA evaluation refuses"
                .into(),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_lean_reply_is_rejected_not_accepted() {
        assert_eq!(
            decode_reply("input", String::new()),
            PoaSignalVerdict::Rejected
        );
    }

    #[test]
    fn nonempty_lean_reply_is_preserved_opaquely() {
        let reply = r#"{"format":"POA-RUN-OUT-1"}"#.to_owned();
        let PoaSignalVerdict::Accepted(accepted) = decode_reply("exact input", reply.clone())
        else {
            panic!("nonempty native reply must be accepted");
        };
        assert_eq!(accepted.as_str(), reply);
        assert!(accepted.was_judged_for(b"exact input"));
        assert!(!accepted.was_judged_for(b"different input"));
    }

    #[test]
    fn interior_nul_is_a_pre_ffi_transport_refusal() {
        let error = shadow_poa_signal_judge("a\0b").unwrap_err();
        assert!(error.contains("interior NUL"));
    }

    #[test]
    fn over_64_mib_is_a_pre_ffi_transport_refusal_without_allocating_it() {
        let error = validate_transport_input(MAX_POA_SIGNAL_WIRE_BYTES + 1, false).unwrap_err();
        assert!(error.contains("transport ceiling"));
    }

    /// The absent-export arm must be a visible refusal, never an alternate evaluator or a skip.
    /// Exercise with `--features no-lean-link` on a native host.
    #[cfg(not(all(lean_lib_present, dregg_poa_signal_judge_present)))]
    #[test]
    fn absent_export_is_fail_closed() {
        assert!(!poa_signal_judge_available());
        let error = judge_poa_signal("{}").unwrap_err();
        assert!(
            error.contains("not linked")
                || error.contains("not present")
                || error.contains("not exported"),
            "absence must surface as a named transport error, got: {error}"
        );
    }
}
