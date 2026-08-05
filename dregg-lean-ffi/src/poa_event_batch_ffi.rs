//! Fail-closed transport for the Lean-owned Path of Angels EventBatch planner.
//!
//! This module does not authenticate the JSON authority envelope and does not construct durable
//! batch types. The node must build the envelope from a finalized commit record plus an accepted
//! game result, then strictly decode the returned canonical plan before persistence.

use crate::{ensure_lean_init, lean_init_once};

pub const MAX_POA_EVENT_BATCH_WIRE_BYTES: usize = 64 * 1024 * 1024;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PoaEventBatchPlanVerdict {
    Planned(PoaEventBatchPlan),
    Rejected,
}

/// Opaque evidence that the native Lean planner returned a nonempty canonical plan. The bytes are
/// still host-authority dependent; persistence must strictly decode and carrier-bind them.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PoaEventBatchPlan(String);

impl PoaEventBatchPlan {
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PoaEventBatchInitialHeadsDigestVerdict {
    Digested(PoaEventBatchInitialHeadsDigest),
    Rejected,
}

/// Opaque canonical response from Lean's exact initial-head-set digest adapter. The host must
/// strictly decode the versioned response and bind it into the privileged planner envelope.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PoaEventBatchInitialHeadsDigest(String);

impl PoaEventBatchInitialHeadsDigest {
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

pub fn poa_event_batch_runtime_available() -> bool {
    ffi::present() && lean_init_once().is_ok()
}

pub fn poa_event_batch_initial_heads_digest_available() -> bool {
    ffi_initial_heads_digest::present() && lean_init_once().is_ok()
}

pub fn plan_poa_event_batch(wire: &str) -> Result<PoaEventBatchPlanVerdict, String> {
    if wire.as_bytes().contains(&0) {
        return Err("PoA EventBatch wire has interior NUL".into());
    }
    if wire.len() > MAX_POA_EVENT_BATCH_WIRE_BYTES {
        return Err(format!(
            "PoA EventBatch wire exceeds {MAX_POA_EVENT_BATCH_WIRE_BYTES}-byte transport ceiling"
        ));
    }
    ensure_lean_init()?;
    let output = ffi::call(wire)?;
    if output.is_empty() {
        Ok(PoaEventBatchPlanVerdict::Rejected)
    } else {
        Ok(PoaEventBatchPlanVerdict::Planned(PoaEventBatchPlan(output)))
    }
}

pub fn digest_poa_event_batch_initial_heads(
    wire: &str,
) -> Result<PoaEventBatchInitialHeadsDigestVerdict, String> {
    if wire.as_bytes().contains(&0) {
        return Err("PoA EventBatch initial-heads wire has interior NUL".into());
    }
    if wire.len() > MAX_POA_EVENT_BATCH_WIRE_BYTES {
        return Err(format!(
            "PoA EventBatch initial-heads wire exceeds {MAX_POA_EVENT_BATCH_WIRE_BYTES}-byte transport ceiling"
        ));
    }
    ensure_lean_init()?;
    let output = ffi_initial_heads_digest::call(wire)?;
    if output.is_empty() {
        Ok(PoaEventBatchInitialHeadsDigestVerdict::Rejected)
    } else {
        Ok(PoaEventBatchInitialHeadsDigestVerdict::Digested(
            PoaEventBatchInitialHeadsDigest(output),
        ))
    }
}

#[cfg(all(lean_lib_present, dregg_poa_event_batch_runtime_plan_present))]
mod ffi {
    use std::ffi::CString;
    use std::os::raw::c_char;

    unsafe extern "C" {
        fn dregg_poa_event_batch_runtime_plan_str(
            input: *const c_char,
            output: *mut c_char,
            output_cap: usize,
        ) -> usize;
    }

    pub fn present() -> bool {
        true
    }

    pub fn call(wire: &str) -> Result<String, String> {
        let input = CString::new(wire).map_err(|error| format!("EventBatch wire NUL: {error}"))?;
        let mut cap = 4096usize;
        loop {
            let mut output = vec![0u8; cap];
            let full = unsafe {
                dregg_poa_event_batch_runtime_plan_str(
                    input.as_ptr(),
                    output.as_mut_ptr().cast(),
                    cap,
                )
            };
            if full == usize::MAX {
                return Err("dregg_poa_event_batch_runtime_plan_str refused transport".into());
            }
            if full > super::MAX_POA_EVENT_BATCH_WIRE_BYTES {
                return Err("EventBatch planner output exceeds transport ceiling".into());
            }
            if full < cap {
                return String::from_utf8(output[..full].to_vec())
                    .map_err(|error| format!("EventBatch planner output is not UTF-8: {error}"));
            }
            cap = full
                .checked_add(1)
                .filter(|next| *next <= super::MAX_POA_EVENT_BATCH_WIRE_BYTES + 1)
                .ok_or_else(|| "EventBatch planner output length overflow".to_owned())?;
        }
    }
}

#[cfg(all(
    lean_lib_present,
    dregg_poa_event_batch_runtime_initial_heads_digest_present
))]
mod ffi_initial_heads_digest {
    use std::ffi::CString;
    use std::os::raw::c_char;

    unsafe extern "C" {
        fn dregg_poa_event_batch_runtime_initial_heads_digest_str(
            input: *const c_char,
            output: *mut c_char,
            output_cap: usize,
        ) -> usize;
    }

    pub fn present() -> bool {
        true
    }

    pub fn call(wire: &str) -> Result<String, String> {
        let input = CString::new(wire)
            .map_err(|error| format!("EventBatch initial-heads wire NUL: {error}"))?;
        let mut cap = 256usize;
        loop {
            let mut output = vec![0u8; cap];
            let full = unsafe {
                dregg_poa_event_batch_runtime_initial_heads_digest_str(
                    input.as_ptr(),
                    output.as_mut_ptr().cast(),
                    cap,
                )
            };
            if full == usize::MAX {
                return Err(
                    "dregg_poa_event_batch_runtime_initial_heads_digest_str refused transport"
                        .into(),
                );
            }
            if full > super::MAX_POA_EVENT_BATCH_WIRE_BYTES {
                return Err("EventBatch initial-heads output exceeds transport ceiling".into());
            }
            if full < cap {
                return String::from_utf8(output[..full].to_vec()).map_err(|error| {
                    format!("EventBatch initial-heads output is not UTF-8: {error}")
                });
            }
            cap = full
                .checked_add(1)
                .filter(|next| *next <= super::MAX_POA_EVENT_BATCH_WIRE_BYTES + 1)
                .ok_or_else(|| "EventBatch initial-heads output length overflow".to_owned())?;
        }
    }
}

#[cfg(not(all(
    lean_lib_present,
    dregg_poa_event_batch_runtime_initial_heads_digest_present
)))]
mod ffi_initial_heads_digest {
    pub fn present() -> bool {
        false
    }

    pub fn call(_wire: &str) -> Result<String, String> {
        Err(
            "dregg_poa_event_batch_runtime_initial_heads_digest is absent; PoA planning refuses"
                .into(),
        )
    }
}

#[cfg(not(all(lean_lib_present, dregg_poa_event_batch_runtime_plan_present)))]
mod ffi {
    pub fn present() -> bool {
        false
    }

    pub fn call(_wire: &str) -> Result<String, String> {
        Err("dregg_poa_event_batch_runtime_plan is absent; PoA persistence refuses".into())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(all(lean_lib_present, dregg_poa_event_batch_runtime_plan_present))]
    #[test]
    fn native_export_is_linked_and_refuses_malformed_input() {
        assert!(poa_event_batch_runtime_available());
        assert_eq!(
            plan_poa_event_batch("{}").unwrap(),
            PoaEventBatchPlanVerdict::Rejected
        );
    }

    #[cfg(all(
        lean_lib_present,
        dregg_poa_event_batch_runtime_initial_heads_digest_present
    ))]
    #[test]
    fn native_initial_heads_export_is_linked_and_refuses_malformed_input() {
        assert!(poa_event_batch_initial_heads_digest_available());
        assert_eq!(
            digest_poa_event_batch_initial_heads("{}").unwrap(),
            PoaEventBatchInitialHeadsDigestVerdict::Rejected
        );
    }

    #[cfg(not(all(lean_lib_present, dregg_poa_event_batch_runtime_plan_present)))]
    #[test]
    fn absent_export_refuses_without_rust_planner() {
        assert!(!ffi::present());
        assert!(ffi::call("{}").unwrap_err().contains("absent"));
    }

    #[cfg(not(all(
        lean_lib_present,
        dregg_poa_event_batch_runtime_initial_heads_digest_present
    )))]
    #[test]
    fn absent_initial_heads_export_refuses_without_rust_digest_twin() {
        assert!(!ffi_initial_heads_digest::present());
        assert!(ffi_initial_heads_digest::call("{}")
            .unwrap_err()
            .contains("absent"));
    }

    #[test]
    fn transport_bounds_refuse_before_call() {
        assert!(plan_poa_event_batch("a\0b").unwrap_err().contains("NUL"));
        assert!(digest_poa_event_batch_initial_heads("a\0b")
            .unwrap_err()
            .contains("NUL"));
    }
}
