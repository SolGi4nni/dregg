//! `dregg-lean-ffi` library — marshal codec + optional Lean kernel shadow execution.
//!
//! When `libdregg_lean.a` is present at build time (`cfg(lean_lib_present)`), the crate
//! links the verified Lean kernel and exposes `shadow_exec_full_forest_auth`. When the
//! archive is absent the crate still builds (marshal-only); `lean_available()` is false.

#[path = "marshal.rs"]
pub mod marshal;

pub use marshal::TurnStatus;

/// Decoded Lean gated-forest verdict (T9 output envelope).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShadowVerdict {
    /// `true` ONLY when the gated forest BODY committed (`status == BodyCommitted`). A
    /// prologue-only result (forged credential / violated caveat / failed effect → the fee was
    /// charged as anti-spam but the body rolled back) is `committed == false` — the turn is
    /// REJECTED, NOT accepted (boundary-P1 bug 2).
    pub committed: bool,
    pub loglen: u64,
    /// The three-way status (boundary-P1 bug 2). `None` only for the legacy no-`status` wire.
    pub status: Option<TurnStatus>,
    pub divergence_note: Option<String>,
}

impl ShadowVerdict {
    /// Whether the prologue (fee/nonce) was committed but the BODY FAILED — the fee was charged
    /// as anti-spam but the turn is REJECTED (must NOT be treated as accepted).
    pub fn prologue_only(&self) -> bool {
        self.status == Some(TurnStatus::PrologueCommittedBodyFailed)
    }
    /// Whether the body genuinely committed (the turn is ACCEPTED).
    pub fn body_committed(&self) -> bool {
        // Fall back to `committed` for the legacy no-`status` wire.
        match self.status {
            Some(s) => s == TurnStatus::BodyCommitted,
            None => self.committed,
        }
    }
}

/// Whether the Lean static archive was linked and runtime init succeeded.
pub fn lean_available() -> bool {
    lean_init_once().is_ok()
}

/// Marshal a wire string through `dregg_exec_full_forest_auth_str` and return the raw
/// output wire. Requires `lean_available()`.
pub fn shadow_exec_full_forest_auth(wire: &str) -> Result<String, String> {
    ensure_lean_init()?;
    lean_forest_auth(wire)
}

/// Handler-cutover shadow path — admission ∘ `execHandlerTurn` on the same wire.
///
/// Available only when the linked archive exports `dregg_exec_handler_turn`
/// (cfg `dregg_handler_present`, set by build.rs). The forest-auth gate
/// ([`shadow_exec_full_forest_auth`]) is the load-bearing path and is always present.
pub fn shadow_exec_handler_turn(wire: &str) -> Result<String, String> {
    ensure_lean_init()?;
    lean_handler_turn(wire)
}

/// Parse a shadow output wire into a [`ShadowVerdict`], surfacing marshal/parse errors.
pub fn decode_shadow_verdict(output: &str) -> Result<ShadowVerdict, String> {
    match marshal::unmarshal_result(output) {
        Ok(r) => Ok(ShadowVerdict {
            // `committed` is the body-committed bit (status:2). The Lean export's `ok` already
            // narrows to BodyCommitted, but we recompute from `status` when present so a
            // prologue-only result (status:1) is NEVER reported as committed.
            committed: match r.status {
                Some(s) => s == TurnStatus::BodyCommitted,
                None => r.committed,
            },
            loglen: r.loglen,
            status: r.status,
            divergence_note: None,
        }),
        Err(e) => Err(e.to_string()),
    }
}

// =============================================================================
// Lean FFI (present only when libdregg_lean.a was linked at build time)
// =============================================================================

#[cfg(lean_lib_present)]
mod ffi {
    use std::ffi::CString;
    use std::os::raw::c_char;
    use std::sync::OnceLock;

    extern "C" {
        fn dregg_ffi_init() -> i32;
        fn dregg_exec_full_forest_auth_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
        #[cfg(dregg_handler_present)]
        fn dregg_exec_handler_turn_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
    }

    static INIT: OnceLock<Result<(), String>> = OnceLock::new();

    pub fn lean_init_once() -> Result<(), String> {
        INIT.get_or_init(|| {
            let rc = unsafe { dregg_ffi_init() };
            if rc == 0 {
                Ok(())
            } else {
                Err(format!("dregg_ffi_init failed (rc={rc})"))
            }
        })
        .clone()
    }

    fn lean_string_bridge(
        wire: &str,
        f: unsafe extern "C" fn(*const c_char, *mut c_char, usize) -> usize,
        err_label: &str,
    ) -> Result<String, String> {
        let c_in = CString::new(wire).map_err(|e| format!("wire has interior NUL: {e}"))?;
        let mut cap = wire.len() * 2 + 1024;
        loop {
            let mut buf = vec![0u8; cap];
            let full = unsafe { f(c_in.as_ptr(), buf.as_mut_ptr() as *mut c_char, cap) };
            if full == usize::MAX {
                return Err(format!("{err_label}: unusable output buffer"));
            }
            if full < cap {
                let nul = buf.iter().position(|&b| b == 0).unwrap_or(full);
                return String::from_utf8(buf[..nul].to_vec())
                    .map_err(|e| format!("result not UTF-8: {e}"));
            }
            cap = full + 1;
        }
    }

    pub fn lean_forest_auth(wire: &str) -> Result<String, String> {
        lean_string_bridge(wire, dregg_exec_full_forest_auth_str, "dregg_exec_full_forest_auth_str")
    }

    #[cfg(dregg_handler_present)]
    pub fn lean_handler_turn(wire: &str) -> Result<String, String> {
        lean_string_bridge(wire, dregg_exec_handler_turn_str, "dregg_exec_handler_turn_str")
    }

    #[cfg(not(dregg_handler_present))]
    pub fn lean_handler_turn(_wire: &str) -> Result<String, String> {
        Err("dregg_exec_handler_turn not exported by the linked archive (rebuild to enable)".into())
    }
}

#[cfg(not(lean_lib_present))]
mod ffi {
    pub fn lean_init_once() -> Result<(), String> {
        Err("libdregg_lean.a was not present at build time".into())
    }

    pub fn lean_forest_auth(_wire: &str) -> Result<String, String> {
        Err("Lean static lib not linked".into())
    }

    pub fn lean_handler_turn(_wire: &str) -> Result<String, String> {
        Err("Lean static lib not linked".into())
    }
}

fn lean_init_once() -> Result<(), String> {
    ffi::lean_init_once()
}

fn ensure_lean_init() -> Result<(), String> {
    lean_init_once()
}

fn lean_forest_auth(wire: &str) -> Result<String, String> {
    ffi::lean_forest_auth(wire)
}

fn lean_handler_turn(wire: &str) -> Result<String, String> {
    ffi::lean_handler_turn(wire)
}