//! Fail-closed transport for Lean-owned Path of Angels activated-content membership.
//!
//! The caller supplies canonical manifest bytes and the exact all-five-field world already
//! authenticated by persistence. Lean alone validates manifest structure and hashes, binds its
//! root/scope to that world, and extracts the reserved canonical Galley policy. There is no Rust
//! manifest or policy decision twin.

use crate::{ensure_lean_init, lean_init_once};

pub const MAX_POA_ACTIVATED_CONTENT_WIRE_BYTES: usize = 4 * 1024 * 1024;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PoaActivatedContentVerdict {
    Authorized(PoaActivatedContentAuthority),
    Rejected,
}

/// Opaque bytes returned by the Lean authority. Persistence must still strictly decode the
/// versioned envelope and bind it to the world held under its same-writer audit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PoaActivatedContentAuthority(String);

impl PoaActivatedContentAuthority {
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

pub fn poa_activated_content_runtime_available() -> bool {
    ffi::present() && lean_init_once().is_ok()
}

pub fn authorize_poa_activated_content(wire: &str) -> Result<PoaActivatedContentVerdict, String> {
    if wire.as_bytes().contains(&0) {
        return Err("PoA activated-content wire has interior NUL".into());
    }
    if wire.len() > MAX_POA_ACTIVATED_CONTENT_WIRE_BYTES {
        return Err(format!(
            "PoA activated-content wire exceeds {MAX_POA_ACTIVATED_CONTENT_WIRE_BYTES}-byte transport ceiling"
        ));
    }
    ensure_lean_init()?;
    let output = ffi::call(wire)?;
    if output.is_empty() {
        Ok(PoaActivatedContentVerdict::Rejected)
    } else {
        Ok(PoaActivatedContentVerdict::Authorized(
            PoaActivatedContentAuthority(output),
        ))
    }
}

#[cfg(all(lean_lib_present, dregg_poa_activated_content_authorize_present))]
mod ffi {
    use std::ffi::CString;
    use std::os::raw::c_char;

    unsafe extern "C" {
        fn dregg_poa_activated_content_authorize_str(
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
            .map_err(|error| format!("PoA activated-content wire NUL: {error}"))?;
        let mut cap = 4096usize;
        loop {
            let mut output = vec![0u8; cap];
            let full = unsafe {
                dregg_poa_activated_content_authorize_str(
                    input.as_ptr(),
                    output.as_mut_ptr().cast(),
                    cap,
                )
            };
            if full == usize::MAX {
                return Err("dregg_poa_activated_content_authorize_str refused transport".into());
            }
            if full > super::MAX_POA_ACTIVATED_CONTENT_WIRE_BYTES {
                return Err("PoA activated-content output exceeds transport ceiling".into());
            }
            if full < cap {
                return String::from_utf8(output[..full].to_vec()).map_err(|error| {
                    format!("PoA activated-content output is not UTF-8: {error}")
                });
            }
            cap = full
                .checked_add(1)
                .filter(|next| *next <= super::MAX_POA_ACTIVATED_CONTENT_WIRE_BYTES + 1)
                .ok_or_else(|| "PoA activated-content output length overflow".to_owned())?;
        }
    }
}

#[cfg(not(all(lean_lib_present, dregg_poa_activated_content_authorize_present)))]
mod ffi {
    pub fn present() -> bool {
        false
    }

    pub fn call(_wire: &str) -> Result<String, String> {
        Err(
            "dregg_poa_activated_content_authorize is absent; PoA content installation refuses"
                .into(),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn transport_rejects_interior_nul_before_lean() {
        assert!(authorize_poa_activated_content("a\0b")
            .unwrap_err()
            .contains("NUL"));
    }

    #[test]
    fn transport_rejects_oversized_input_before_lean() {
        let oversized = "x".repeat(MAX_POA_ACTIVATED_CONTENT_WIRE_BYTES + 1);
        assert!(authorize_poa_activated_content(&oversized)
            .unwrap_err()
            .contains("ceiling"));
    }

    #[cfg(all(lean_lib_present, dregg_poa_activated_content_authorize_present))]
    #[test]
    fn native_export_is_linked_and_refuses_malformed_input() {
        assert!(poa_activated_content_runtime_available());
        assert_eq!(
            authorize_poa_activated_content("{}").unwrap(),
            PoaActivatedContentVerdict::Rejected
        );
    }

    #[cfg(not(all(lean_lib_present, dregg_poa_activated_content_authorize_present)))]
    #[test]
    fn absent_export_refuses_without_rust_semantic_twin() {
        assert!(!ffi::present());
        assert!(ffi::call("{}").unwrap_err().contains("absent"));
    }
}
