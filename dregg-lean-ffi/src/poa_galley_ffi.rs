//! Fail-closed transport for the Lean-owned Path of Angels Galley daily.
//!
//! The public export cannot receive holder authority.  The former sponsor export accepted
//! caller-authored JSON as its alleged seal and is intentionally absent until the host can supply
//! an atomically consumable wallet capability.

use crate::{ensure_lean_init, lean_init_once};

pub const MAX_POA_GALLEY_WIRE_BYTES: usize = 1024 * 1024;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PoaGalleyVerdict {
    Accepted(String),
    Rejected,
}

pub fn poa_galley_daily_available() -> bool {
    ffi_public::present() && lean_init_once().is_ok()
}

pub fn poa_galley_daily_sponsor_available() -> bool {
    false
}

fn validate_input(label: &str, wire: &str, limit: usize) -> Result<(), String> {
    if wire.as_bytes().contains(&0) {
        return Err(format!("{label} has interior NUL"));
    }
    if wire.len() > limit {
        return Err(format!("{label} exceeds {limit}-byte transport ceiling"));
    }
    Ok(())
}

fn decode_reply(output: String) -> PoaGalleyVerdict {
    if output.is_empty() {
        PoaGalleyVerdict::Rejected
    } else {
        PoaGalleyVerdict::Accepted(output)
    }
}

pub fn judge_poa_galley_daily(wire: &str) -> Result<PoaGalleyVerdict, String> {
    validate_input("PoA Galley wire", wire, MAX_POA_GALLEY_WIRE_BYTES)?;
    ensure_lean_init()?;
    ffi_public::call(wire).map(decode_reply)
}

pub fn judge_poa_galley_daily_sponsor(
    _wire: &str,
    _server_seal: &str,
) -> Result<PoaGalleyVerdict, String> {
    Err(
        "PoA Galley holder sponsorship is disabled until an atomically consumable wallet capability exists"
            .into(),
    )
}

fn call_string_bridge(
    label: &str,
    mut invoke: impl FnMut(*mut std::os::raw::c_char, usize) -> usize,
) -> Result<String, String> {
    const MAX_BUFFER_CAP: usize = MAX_POA_GALLEY_WIRE_BYTES + 1;
    let mut cap = 4096usize;
    loop {
        let mut output = vec![0u8; cap];
        let full = invoke(output.as_mut_ptr().cast(), cap);
        if full == usize::MAX {
            return Err(format!("{label} refused transport"));
        }
        if full > MAX_POA_GALLEY_WIRE_BYTES {
            return Err(format!("{label} output exceeds transport ceiling"));
        }
        if full < cap {
            return String::from_utf8(output[..full].to_vec())
                .map_err(|error| format!("{label} result is not UTF-8: {error}"));
        }
        cap = full
            .checked_add(1)
            .filter(|next| *next <= MAX_BUFFER_CAP)
            .ok_or_else(|| format!("{label} output length overflow"))?;
    }
}

#[cfg(all(lean_lib_present, dregg_poa_galley_daily_judge_present))]
mod ffi_public {
    use std::ffi::CString;
    use std::os::raw::c_char;

    unsafe extern "C" {
        fn dregg_poa_galley_daily_judge_str(
            input: *const c_char,
            output: *mut c_char,
            output_cap: usize,
        ) -> usize;
    }

    pub fn present() -> bool {
        true
    }

    pub fn call(wire: &str) -> Result<String, String> {
        let input = CString::new(wire).map_err(|error| format!("Galley wire NUL: {error}"))?;
        super::call_string_bridge("dregg_poa_galley_daily_judge_str", |output, cap| unsafe {
            dregg_poa_galley_daily_judge_str(input.as_ptr(), output, cap)
        })
    }
}

#[cfg(not(all(lean_lib_present, dregg_poa_galley_daily_judge_present)))]
mod ffi_public {
    pub fn present() -> bool {
        false
    }

    pub fn call(_wire: &str) -> Result<String, String> {
        Err("dregg_poa_galley_daily_judge is absent; public Galley play refuses".into())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_reply_is_semantic_refusal() {
        assert_eq!(decode_reply(String::new()), PoaGalleyVerdict::Rejected);
    }

    #[test]
    fn nonempty_reply_is_preserved_opaquely() {
        let output = r#"{"format":"POA-GALLEY-DAILY-OUT-1"}"#.to_owned();
        assert_eq!(
            decode_reply(output.clone()),
            PoaGalleyVerdict::Accepted(output)
        );
    }

    #[test]
    fn public_transport_bounds_are_enforced() {
        assert!(validate_input("wire", "a\0b", MAX_POA_GALLEY_WIRE_BYTES).is_err());
    }

    #[cfg(all(lean_lib_present, dregg_poa_galley_daily_judge_present))]
    #[test]
    fn native_public_export_is_linked_and_refuses_malformed_input() {
        assert!(poa_galley_daily_available());
        assert_eq!(
            judge_poa_galley_daily("{}").unwrap(),
            PoaGalleyVerdict::Rejected
        );
    }

    #[test]
    fn sponsor_path_is_unconditionally_disabled() {
        assert!(!poa_galley_daily_sponsor_available());
        let error = judge_poa_galley_daily_sponsor("valid-looking input", "valid-looking seal")
            .expect_err("caller JSON must never reach a sponsor authority constructor");
        assert!(error.contains("atomically consumable wallet capability"));
    }

    #[cfg(not(all(lean_lib_present, dregg_poa_galley_daily_judge_present)))]
    #[test]
    fn missing_public_export_refuses_without_a_twin() {
        assert!(!ffi_public::present());
        let error = ffi_public::call("{}").unwrap_err();
        assert!(error.contains("absent"));
    }
}
