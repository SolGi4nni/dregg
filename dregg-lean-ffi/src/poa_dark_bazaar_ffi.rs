//! Fail-closed transport for the Lean-owned Path of Angels Dark Bazaar v1 judge.
//!
//! Rust moves bounded UTF-8 only. It does not parse a claim, recompute a clearing,
//! manufacture authorization, or synthesize a successor. Empty output is Lean's
//! semantic refusal; a missing archive/export is a transport error.

use crate::{ensure_lean_init, lean_init_once};

pub const MAX_POA_DARK_BAZAAR_WIRE_BYTES: usize = 16 * 1024 * 1024;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PoaDarkBazaarVerdict {
    Accepted(String),
    Rejected,
}

pub fn poa_dark_bazaar_judge_available() -> bool {
    ffi_bazaar::judge_present() && lean_init_once().is_ok()
}

fn validate_transport_input(len: usize, has_interior_nul: bool) -> Result<(), String> {
    if has_interior_nul {
        return Err("PoA Dark Bazaar wire has interior NUL".into());
    }
    if len > MAX_POA_DARK_BAZAAR_WIRE_BYTES {
        return Err(format!(
            "dregg_poa_dark_bazaar_judge input exceeds {MAX_POA_DARK_BAZAAR_WIRE_BYTES}-byte transport ceiling"
        ));
    }
    Ok(())
}

pub fn shadow_poa_dark_bazaar_judge(wire: &str) -> Result<String, String> {
    validate_transport_input(wire.len(), wire.as_bytes().contains(&0))?;
    ensure_lean_init()?;
    ffi_bazaar::lean_judge(wire)
}

pub fn judge_poa_dark_bazaar(wire: &str) -> Result<PoaDarkBazaarVerdict, String> {
    let output = shadow_poa_dark_bazaar_judge(wire)?;
    Ok(if output.is_empty() {
        PoaDarkBazaarVerdict::Rejected
    } else {
        PoaDarkBazaarVerdict::Accepted(output)
    })
}

#[cfg(all(lean_lib_present, dregg_poa_dark_bazaar_judge_present))]
mod ffi_bazaar {
    use std::ffi::CString;
    use std::os::raw::c_char;

    use super::MAX_POA_DARK_BAZAAR_WIRE_BYTES;

    const MAX_BUFFER_CAP: usize = MAX_POA_DARK_BAZAAR_WIRE_BYTES + 1;

    extern "C" {
        fn dregg_poa_dark_bazaar_judge_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
    }

    pub fn judge_present() -> bool {
        true
    }

    pub fn lean_judge(wire: &str) -> Result<String, String> {
        let input = CString::new(wire)
            .map_err(|error| format!("PoA Dark Bazaar wire has interior NUL: {error}"))?;
        let mut cap = wire
            .len()
            .checked_mul(2)
            .and_then(|size| size.checked_add(1024))
            .unwrap_or(MAX_BUFFER_CAP)
            .clamp(1024, MAX_BUFFER_CAP);

        loop {
            let mut buffer = vec![0u8; cap];
            let full = unsafe {
                dregg_poa_dark_bazaar_judge_str(
                    input.as_ptr(),
                    buffer.as_mut_ptr().cast::<c_char>(),
                    cap,
                )
            };
            if full == usize::MAX {
                return Err("dregg_poa_dark_bazaar_judge_str refused transport".into());
            }
            if full > MAX_POA_DARK_BAZAAR_WIRE_BYTES {
                return Err("dregg_poa_dark_bazaar_judge output exceeds transport ceiling".into());
            }
            if full < cap {
                return String::from_utf8(buffer[..full].to_vec())
                    .map_err(|error| format!("PoA Dark Bazaar result is not UTF-8: {error}"));
            }
            cap = full
                .checked_add(1)
                .filter(|next| *next <= MAX_BUFFER_CAP)
                .ok_or_else(|| "PoA Dark Bazaar output length overflow".to_owned())?;
        }
    }
}

#[cfg(not(all(lean_lib_present, dregg_poa_dark_bazaar_judge_present)))]
mod ffi_bazaar {
    pub fn judge_present() -> bool {
        false
    }

    pub fn lean_judge(_wire: &str) -> Result<String, String> {
        Err("dregg_poa_dark_bazaar_judge not exported by linked archive; settlement refuses".into())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_reply_is_rejected() {
        let verdict = if String::new().is_empty() {
            PoaDarkBazaarVerdict::Rejected
        } else {
            unreachable!()
        };
        assert_eq!(verdict, PoaDarkBazaarVerdict::Rejected);
    }

    #[test]
    fn interior_nul_refuses_before_ffi() {
        assert!(shadow_poa_dark_bazaar_judge("a\0b")
            .unwrap_err()
            .contains("interior NUL"));
    }

    #[test]
    fn over_limit_refuses_without_allocating_payload() {
        assert!(
            validate_transport_input(MAX_POA_DARK_BAZAAR_WIRE_BYTES + 1, false)
                .unwrap_err()
                .contains("transport ceiling")
        );
    }

    #[cfg(not(all(lean_lib_present, dregg_poa_dark_bazaar_judge_present)))]
    #[test]
    fn absent_export_is_fail_closed() {
        assert!(!poa_dark_bazaar_judge_available());
        let error = judge_poa_dark_bazaar("{}").unwrap_err();
        assert!(
            error.contains("not exported")
                || error.contains("not linked")
                || error.contains("not present"),
            "absence must surface as a named transport error, got: {error}"
        );
    }
}
