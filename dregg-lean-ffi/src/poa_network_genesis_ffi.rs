//! Fail-closed native transport for the Lean-owned Path of Angels Signal genesis ceremony.
//!
//! The only semantic implementation is
//! `Dregg2.Games.PathOfAngels.NetworkGenesis.networkGenesisFFI`. Rust transports one bounded
//! canonical input string and the exact bounded output string. It does not parse or reconstruct
//! `SignalConfigDto`, `CanonStateDto`, their hashes, or their faithful coordinates. In particular,
//! symbol availability does not verify the deployment manifest, genesis bytes, content envelope,
//! detached curator signature, or rollback policy; those form the ceremony's external atomic
//! precondition before this evaluator is invoked.

use crate::{ensure_lean_init, lean_init_once};

/// Host ceiling for both canonical input and Lean emission.
///
/// This equals the Lean surface's 16 MiB UTF-8 byte ceiling. It is transport policy rather than a
/// substitute for Lean's strict syntax, mission, tuple-binding, and empty-head checks.
pub const MAX_POA_NETWORK_GENESIS_WIRE_BYTES: usize = 16 * 1024 * 1024;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PoaNetworkGenesisVerdict {
    /// Exact opaque `POA-SIGNAL-GENESIS-OUT-1` bytes emitted by Lean.
    Emitted(String),
    /// Lean's empty semantic-refusal sentinel.
    Rejected,
}

/// Whether the separately named genesis export is linked and runtime initialization succeeded.
pub fn poa_network_genesis_available() -> bool {
    ffi_genesis::genesis_present() && lean_init_once().is_ok()
}

fn validate_transport_input(len: usize, has_interior_nul: bool) -> Result<(), String> {
    if has_interior_nul {
        return Err("PoA network genesis wire has interior NUL".into());
    }
    if len > MAX_POA_NETWORK_GENESIS_WIRE_BYTES {
        return Err(format!(
            "dregg_poa_network_genesis input exceeds {MAX_POA_NETWORK_GENESIS_WIRE_BYTES}-byte transport ceiling"
        ));
    }
    Ok(())
}

fn validate_transport_output(len: usize) -> Result<(), String> {
    if len > MAX_POA_NETWORK_GENESIS_WIRE_BYTES {
        return Err(format!(
            "dregg_poa_network_genesis output exceeds {MAX_POA_NETWORK_GENESIS_WIRE_BYTES}-byte transport ceiling"
        ));
    }
    Ok(())
}

/// Call the real Lean export and preserve its returned bytes without semantic reconstruction.
pub fn shadow_poa_network_genesis(wire: &str) -> Result<String, String> {
    validate_transport_input(wire.len(), wire.as_bytes().contains(&0))?;
    ensure_lean_init()?;
    let output = ffi_genesis::lean_genesis(wire)?;
    validate_transport_output(output.len())?;
    Ok(output)
}

/// Evaluate the externally prepared ceremony tuple, distinguishing Lean refusal from transport
/// absence/failure. No `Emitted` value is persisted by this module.
pub fn evaluate_poa_network_genesis(wire: &str) -> Result<PoaNetworkGenesisVerdict, String> {
    let output = shadow_poa_network_genesis(wire)?;
    Ok(if output.is_empty() {
        PoaNetworkGenesisVerdict::Rejected
    } else {
        PoaNetworkGenesisVerdict::Emitted(output)
    })
}

#[cfg(all(lean_lib_present, dregg_poa_network_genesis_present))]
mod ffi_genesis {
    use std::ffi::CString;
    use std::os::raw::c_char;

    use super::MAX_POA_NETWORK_GENESIS_WIRE_BYTES;

    const MAX_BUFFER_CAP: usize = MAX_POA_NETWORK_GENESIS_WIRE_BYTES + 1;

    extern "C" {
        fn dregg_poa_network_genesis_str(
            in_utf8: *const c_char,
            out: *mut c_char,
            out_cap: usize,
        ) -> usize;
    }

    pub fn genesis_present() -> bool {
        true
    }

    pub fn lean_genesis(wire: &str) -> Result<String, String> {
        let input = CString::new(wire)
            .map_err(|error| format!("PoA network genesis wire has interior NUL: {error}"))?;
        let mut cap = wire
            .len()
            .checked_mul(2)
            .and_then(|size| size.checked_add(1024))
            .unwrap_or(MAX_BUFFER_CAP)
            .clamp(1024, MAX_BUFFER_CAP);

        loop {
            let mut buffer = vec![0u8; cap];
            let full = unsafe {
                dregg_poa_network_genesis_str(
                    input.as_ptr(),
                    buffer.as_mut_ptr().cast::<c_char>(),
                    cap,
                )
            };
            if full == usize::MAX {
                return Err("dregg_poa_network_genesis_str refused transport".into());
            }
            if full > MAX_POA_NETWORK_GENESIS_WIRE_BYTES {
                return Err("dregg_poa_network_genesis output exceeds transport ceiling".into());
            }
            if full < cap {
                return String::from_utf8(buffer[..full].to_vec())
                    .map_err(|error| format!("PoA network genesis result is not UTF-8: {error}"));
            }
            cap = full
                .checked_add(1)
                .filter(|next| *next <= MAX_BUFFER_CAP)
                .ok_or_else(|| "PoA network genesis output length overflow".to_owned())?;
        }
    }
}

#[cfg(not(all(lean_lib_present, dregg_poa_network_genesis_present)))]
mod ffi_genesis {
    pub fn genesis_present() -> bool {
        false
    }

    pub fn lean_genesis(_wire: &str) -> Result<String, String> {
        Err(
            "dregg_poa_network_genesis not exported by linked archive; genesis ceremony refuses"
                .into(),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_reply_is_semantic_refusal() {
        assert_eq!(
            if String::new().is_empty() {
                PoaNetworkGenesisVerdict::Rejected
            } else {
                unreachable!()
            },
            PoaNetworkGenesisVerdict::Rejected
        );
    }

    #[test]
    fn interior_nul_refuses_before_ffi() {
        assert!(shadow_poa_network_genesis("a\0b")
            .unwrap_err()
            .contains("interior NUL"));
    }

    #[test]
    fn over_limit_input_refuses_without_allocating_payload() {
        assert!(
            validate_transport_input(MAX_POA_NETWORK_GENESIS_WIRE_BYTES + 1, false)
                .unwrap_err()
                .contains("input exceeds")
        );
    }

    #[test]
    fn over_limit_output_refuses_without_allocating_payload() {
        assert!(
            validate_transport_output(MAX_POA_NETWORK_GENESIS_WIRE_BYTES + 1)
                .unwrap_err()
                .contains("output exceeds")
        );
    }

    /// Native `--features no-lean-link` must name absence and refuse; it must never run a twin.
    #[cfg(not(all(lean_lib_present, dregg_poa_network_genesis_present)))]
    #[test]
    fn absent_named_export_is_fail_closed() {
        assert!(!poa_network_genesis_available());
        let error = evaluate_poa_network_genesis("{}").unwrap_err();
        assert!(
            error.contains("not exported")
                || error.contains("not linked")
                || error.contains("not present"),
            "absence must surface as a named transport error, got: {error}"
        );
    }
}
