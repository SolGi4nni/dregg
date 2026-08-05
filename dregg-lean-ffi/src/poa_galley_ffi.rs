//! Fail-closed transport for the Lean-owned Path of Angels Galley daily.
//!
//! Public play and holder sponsorship are different Lean exports. The public export cannot receive
//! a holder admission at all. The sponsor export accepts a server-authored, deployment-bound seal;
//! this module merely transports it and never manufactures, parses, or weakens that authority.

use crate::{ensure_lean_init, lean_init_once};

pub const MAX_POA_GALLEY_WIRE_BYTES: usize = 1024 * 1024;
pub const MAX_POA_GALLEY_SPONSOR_SEAL_BYTES: usize = 16 * 1024;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PoaGalleyVerdict {
    Accepted(String),
    Rejected,
}

pub fn poa_galley_daily_available() -> bool {
    ffi_public::present() && lean_init_once().is_ok()
}

pub fn poa_galley_daily_sponsor_available() -> bool {
    ffi_sponsor::present() && lean_init_once().is_ok()
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
    wire: &str,
    server_seal: &str,
) -> Result<PoaGalleyVerdict, String> {
    validate_input("PoA Galley wire", wire, MAX_POA_GALLEY_WIRE_BYTES)?;
    validate_input(
        "PoA Galley sponsor seal",
        server_seal,
        MAX_POA_GALLEY_SPONSOR_SEAL_BYTES,
    )?;
    ensure_lean_init()?;
    ffi_sponsor::call(wire, server_seal).map(decode_reply)
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

#[cfg(all(lean_lib_present, dregg_poa_galley_daily_sponsor_judge_present))]
mod ffi_sponsor {
    use std::ffi::CString;
    use std::os::raw::c_char;

    unsafe extern "C" {
        fn dregg_poa_galley_daily_sponsor_judge_str(
            input: *const c_char,
            seal: *const c_char,
            output: *mut c_char,
            output_cap: usize,
        ) -> usize;
    }

    pub fn present() -> bool {
        true
    }

    pub fn call(wire: &str, seal: &str) -> Result<String, String> {
        let input = CString::new(wire).map_err(|error| format!("Galley wire NUL: {error}"))?;
        let seal = CString::new(seal).map_err(|error| format!("Galley seal NUL: {error}"))?;
        super::call_string_bridge(
            "dregg_poa_galley_daily_sponsor_judge_str",
            |output, cap| unsafe {
                dregg_poa_galley_daily_sponsor_judge_str(input.as_ptr(), seal.as_ptr(), output, cap)
            },
        )
    }
}

#[cfg(not(all(lean_lib_present, dregg_poa_galley_daily_sponsor_judge_present)))]
mod ffi_sponsor {
    pub fn present() -> bool {
        false
    }

    pub fn call(_wire: &str, _seal: &str) -> Result<String, String> {
        Err("dregg_poa_galley_daily_sponsor_judge is absent; holder sponsorship refuses".into())
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
    fn public_and_seal_transport_bounds_are_independent() {
        assert!(validate_input("wire", "a\0b", MAX_POA_GALLEY_WIRE_BYTES).is_err());
        assert!(validate_input(
            "seal",
            &"x".repeat(MAX_POA_GALLEY_SPONSOR_SEAL_BYTES + 1),
            MAX_POA_GALLEY_SPONSOR_SEAL_BYTES,
        )
        .is_err());
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

    #[cfg(all(lean_lib_present, dregg_poa_galley_daily_sponsor_judge_present))]
    #[test]
    fn native_sponsor_export_is_linked_and_refuses_malformed_input() {
        assert!(poa_galley_daily_sponsor_available());
        assert_eq!(
            judge_poa_galley_daily_sponsor("{}", "{}").unwrap(),
            PoaGalleyVerdict::Rejected
        );
    }

    #[cfg(not(all(lean_lib_present, dregg_poa_galley_daily_judge_present)))]
    #[test]
    fn missing_public_export_refuses_without_a_twin() {
        assert!(!ffi_public::present());
        let error = ffi_public::call("{}").unwrap_err();
        assert!(error.contains("absent"));
    }

    #[cfg(not(all(lean_lib_present, dregg_poa_galley_daily_sponsor_judge_present)))]
    #[test]
    fn missing_sponsor_export_refuses_without_downgrading_to_public_play() {
        assert!(!ffi_sponsor::present());
        let error = ffi_sponsor::call("{}", "{}").unwrap_err();
        assert!(error.contains("absent"));
    }
}
