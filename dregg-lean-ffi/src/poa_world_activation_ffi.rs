//! Fail-closed transport for the Lean-owned Path of Angels active-world authority.
//!
//! Ed25519 verification and durable-history construction live at the persistence boundary. This
//! module only calls the extracted Lean transition judge with the exact canonical wire; there is
//! deliberately no Rust transition twin and an absent export is a hard refusal.

use crate::{ensure_lean_init, lean_init_once};

pub const MAX_POA_WORLD_ACTIVATION_WIRE_BYTES: usize = 16 * 1024 * 1024;

pub fn poa_world_activation_available() -> bool {
    ffi::present() && lean_init_once().is_ok()
}

pub fn poa_world_authorization_available() -> bool {
    ffi_authorize::present() && lean_init_once().is_ok()
}

pub fn judge_poa_world_activation(wire: &str) -> Result<String, String> {
    if wire.as_bytes().contains(&0) {
        return Err("PoA world-activation wire has interior NUL".into());
    }
    if wire.len() > MAX_POA_WORLD_ACTIVATION_WIRE_BYTES {
        return Err(format!(
            "PoA world-activation wire exceeds {MAX_POA_WORLD_ACTIVATION_WIRE_BYTES}-byte transport ceiling"
        ));
    }
    ensure_lean_init()?;
    ffi::call(wire)
}

/// Ask Lean whether the final identity in a fully replayed lineage is the exact candidate.
pub fn authorize_poa_world(wire: &str) -> Result<bool, String> {
    if wire.as_bytes().contains(&0) {
        return Err("PoA world-authorization wire has interior NUL".into());
    }
    if wire.len() > MAX_POA_WORLD_ACTIVATION_WIRE_BYTES {
        return Err(format!(
            "PoA world-authorization wire exceeds {MAX_POA_WORLD_ACTIVATION_WIRE_BYTES}-byte transport ceiling"
        ));
    }
    ensure_lean_init()?;
    match ffi_authorize::call(wire)?.as_str() {
        "1" => Ok(true),
        "0" => Ok(false),
        _ => Err("PoA world-authorization judge returned a non-canonical verdict".into()),
    }
}

#[cfg(all(lean_lib_present, dregg_poa_world_activation_judge_present))]
mod ffi {
    use std::ffi::CString;
    use std::os::raw::c_char;

    unsafe extern "C" {
        fn dregg_poa_world_activation_judge_str(
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
            .map_err(|error| format!("PoA world-activation wire NUL: {error}"))?;
        let mut cap = 4096usize;
        loop {
            let mut output = vec![0u8; cap];
            let full = unsafe {
                dregg_poa_world_activation_judge_str(
                    input.as_ptr(),
                    output.as_mut_ptr().cast(),
                    cap,
                )
            };
            if full == usize::MAX {
                return Err("dregg_poa_world_activation_judge_str refused transport".into());
            }
            if full > super::MAX_POA_WORLD_ACTIVATION_WIRE_BYTES {
                return Err("PoA world-activation output exceeds transport ceiling".into());
            }
            if full < cap {
                return String::from_utf8(output[..full].to_vec())
                    .map_err(|error| format!("PoA world-activation output is not UTF-8: {error}"));
            }
            cap = full
                .checked_add(1)
                .filter(|next| *next <= super::MAX_POA_WORLD_ACTIVATION_WIRE_BYTES + 1)
                .ok_or_else(|| "PoA world-activation output length overflow".to_owned())?;
        }
    }
}

#[cfg(all(lean_lib_present, dregg_poa_world_activation_authorizes_present))]
mod ffi_authorize {
    use std::ffi::CString;
    use std::os::raw::c_char;

    unsafe extern "C" {
        fn dregg_poa_world_activation_authorizes_str(
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
            .map_err(|error| format!("PoA world-authorization wire NUL: {error}"))?;
        let mut output = [0u8; 2];
        let full = unsafe {
            dregg_poa_world_activation_authorizes_str(
                input.as_ptr(),
                output.as_mut_ptr().cast(),
                output.len(),
            )
        };
        if full == usize::MAX {
            return Err("dregg_poa_world_activation_authorizes_str refused transport".into());
        }
        if full > 1 {
            return Err("PoA world-authorization output has non-canonical length".into());
        }
        String::from_utf8(output[..full].to_vec())
            .map_err(|error| format!("PoA world-authorization output is not UTF-8: {error}"))
    }
}

#[cfg(not(all(lean_lib_present, dregg_poa_world_activation_authorizes_present)))]
mod ffi_authorize {
    pub fn present() -> bool {
        false
    }

    pub fn call(_wire: &str) -> Result<String, String> {
        Err("dregg_poa_world_activation_authorizes is absent; exact-world admission refuses".into())
    }
}

#[cfg(not(all(lean_lib_present, dregg_poa_world_activation_judge_present)))]
mod ffi {
    pub fn present() -> bool {
        false
    }

    pub fn call(_wire: &str) -> Result<String, String> {
        Err("dregg_poa_world_activation_judge is absent; active-world authority refuses".into())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn transport_rejects_interior_nul_before_lean() {
        assert!(judge_poa_world_activation("a\0b")
            .unwrap_err()
            .contains("NUL"));
    }

    #[test]
    fn authorization_transport_rejects_interior_nul_before_lean() {
        assert!(authorize_poa_world("a\0b").unwrap_err().contains("NUL"));
    }

    #[cfg(all(lean_lib_present, dregg_poa_world_activation_judge_present))]
    #[test]
    fn native_export_is_linked_and_refuses_malformed_input() {
        assert!(poa_world_activation_available());
        assert_eq!(
            judge_poa_world_activation("{}").unwrap(),
            r#"{"format":"POA-WORLD-ACTIVATION-OUT-1","status":"refused","reason":"malformed-wire"}"#
        );
    }

    #[cfg(all(lean_lib_present, dregg_poa_world_activation_authorizes_present))]
    #[test]
    fn native_exact_world_export_is_linked_and_refuses_malformed_input() {
        assert!(poa_world_authorization_available());
        assert!(!authorize_poa_world("{}").unwrap());
    }

    #[cfg(not(all(lean_lib_present, dregg_poa_world_activation_judge_present)))]
    #[test]
    fn absent_export_refuses_without_rust_transition_twin() {
        assert!(!ffi::present());
        assert!(ffi::call("{}").unwrap_err().contains("absent"));
    }

    #[cfg(not(all(lean_lib_present, dregg_poa_world_activation_authorizes_present)))]
    #[test]
    fn absent_exact_world_export_refuses_without_rust_equality_twin() {
        assert!(!ffi_authorize::present());
        assert!(ffi_authorize::call("{}").unwrap_err().contains("absent"));
    }
}
