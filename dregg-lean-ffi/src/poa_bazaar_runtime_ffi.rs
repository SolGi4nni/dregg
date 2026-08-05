//! Fail-closed host surface for the Lean-owned persistent PoA Bazaar.
//!
//! Lean owns the complete `StateKey` codec and the dependent admission
//! constructors. Rust exposes only an opaque replayed head and a canonicality
//! query; it has no public constructor for accepted state bytes and no game
//! transition twin.

use crate::poa_bazaar_restart_portal::{
    load_configured_canonical_head, recover_configured_runtime_store, BazaarRestartError,
};
use crate::{ensure_lean_init, lean_init_once};

pub const MAX_POA_BAZAAR_STATE_WIRE_BYTES: usize = 16 * 1024 * 1024;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PoaBazaarCanonicalHead(String);

impl PoaBazaarCanonicalHead {
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

/// Non-authoritative report from the operator-only recovery path. It exposes
/// no state carrier and cannot create a game admission.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoaBazaarRecoveryReport {
    pub record_count: u64,
}

pub fn poa_bazaar_runtime_available() -> bool {
    ffi::present() && lean_init_once().is_ok()
}

pub fn validate_poa_bazaar_state_key(wire: &str) -> Result<bool, String> {
    if wire.is_empty() {
        return Ok(false);
    }
    if wire.as_bytes().contains(&0) {
        return Err("PoA Bazaar StateKey wire has interior NUL".into());
    }
    if wire.len() > MAX_POA_BAZAAR_STATE_WIRE_BYTES {
        return Err(format!(
            "PoA Bazaar StateKey exceeds {MAX_POA_BAZAAR_STATE_WIRE_BYTES}-byte ceiling"
        ));
    }
    ensure_lean_init()?;
    ffi::validate(wire)
}

/// Replay the complete native CAS journal, verify its head cache, then ask
/// Lean to recognize the exact canonical `StateKey` image before exposing it.
/// This does not reconstruct the private typed game state.
pub fn load_poa_bazaar_canonical_head() -> Result<Option<PoaBazaarCanonicalHead>, String> {
    if !ffi::present() {
        return Err("PoA Bazaar Lean runtime is absent; journal load refuses".into());
    }
    ensure_lean_init()?;
    let Some(head) = load_configured_canonical_head()
        .map_err(|error| format!("PoA Bazaar journal replay refused: {error}"))?
    else {
        return Ok(None);
    };
    let wire = String::from_utf8(head.into_bytes())
        .map_err(|error| format!("PoA Bazaar journal tail is not UTF-8: {error}"))?;
    if !ffi::validate(&wire)? {
        return Err("PoA Bazaar journal tail is not a canonical Lean StateKey".into());
    }
    Ok(Some(PoaBazaarCanonicalHead(wire)))
}

/// Recover a sticky Bazaar cache after an indeterminate write.
///
/// This is an administrative operation, not a game transition. It accepts no
/// caller state: the native side fully replays the pinned journal and asks the
/// Lean codec to recognize every replacement image before rebuilding the exact
/// tail cache. The sticky lock is cleared only after replay and cache
/// verification both succeed.
pub fn recover_poa_bazaar_store() -> Result<PoaBazaarRecoveryReport, String> {
    if !ffi::present() {
        return Err("PoA Bazaar Lean runtime is absent; recovery refuses".into());
    }
    ensure_lean_init()?;
    let recovered = recover_configured_runtime_store(|bytes| {
        if bytes.len() > MAX_POA_BAZAAR_STATE_WIRE_BYTES {
            return Ok(false);
        }
        let wire = std::str::from_utf8(bytes).map_err(|_| {
            BazaarRestartError::InvalidWire("journal replacement StateKey is not UTF-8")
        })?;
        if wire.as_bytes().contains(&0) {
            return Ok(false);
        }
        ffi::validate(wire).map_err(|error| {
            BazaarRestartError::Configuration(format!(
                "Lean StateKey validator failed during recovery: {error}"
            ))
        })
    })
    .map_err(|error| format!("PoA Bazaar recovery refused: {error}"))?;
    Ok(PoaBazaarRecoveryReport {
        record_count: recovered.record_count,
    })
}

#[cfg(all(lean_lib_present, dregg_poa_bazaar_runtime_present))]
mod ffi {
    use std::ffi::CString;
    use std::os::raw::c_char;

    unsafe extern "C" {
        fn dregg_poa_bazaar_state_key_validate_str(
            input: *const c_char,
            output: *mut c_char,
            output_cap: usize,
        ) -> usize;
        #[cfg(test)]
        fn dregg_poa_bazaar_runtime_fixture_str(
            input: *const c_char,
            output: *mut c_char,
            output_cap: usize,
        ) -> usize;
    }

    pub fn present() -> bool {
        true
    }

    pub fn validate(wire: &str) -> Result<bool, String> {
        let input =
            CString::new(wire).map_err(|error| format!("PoA Bazaar StateKey wire NUL: {error}"))?;
        let mut output = [0u8; 2];
        let full = unsafe {
            dregg_poa_bazaar_state_key_validate_str(
                input.as_ptr(),
                output.as_mut_ptr().cast(),
                output.len(),
            )
        };
        match (full, output[0]) {
            (1, b'1') => Ok(true),
            (1, b'0') => Ok(false),
            _ => Err("PoA Bazaar StateKey validator returned a non-canonical verdict".into()),
        }
    }

    #[cfg(test)]
    pub fn fixture(command: &str) -> Result<String, String> {
        let input = CString::new(command)
            .map_err(|error| format!("PoA Bazaar fixture command NUL: {error}"))?;
        let mut output = [0u8; 65];
        let full = unsafe {
            dregg_poa_bazaar_runtime_fixture_str(
                input.as_ptr(),
                output.as_mut_ptr().cast(),
                output.len(),
            )
        };
        if full == usize::MAX || full >= output.len() {
            return Err("PoA Bazaar runtime fixture failed closed".into());
        }
        String::from_utf8(output[..full].to_vec())
            .map_err(|error| format!("PoA Bazaar fixture returned non-UTF-8: {error}"))
    }
}

#[cfg(not(all(lean_lib_present, dregg_poa_bazaar_runtime_present)))]
mod ffi {
    pub fn present() -> bool {
        false
    }

    pub fn validate(_wire: &str) -> Result<bool, String> {
        Err("PoA Bazaar Lean runtime is absent; StateKey admission refuses".into())
    }

    #[cfg(test)]
    pub fn fixture(_command: &str) -> Result<String, String> {
        Err("PoA Bazaar Lean runtime is absent; persistence admission refuses".into())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(all(lean_lib_present, dregg_poa_bazaar_runtime_present))]
    #[test]
    fn linked_fixture_applies_genesis_successor_refuses_stale_and_replays_exact_head() {
        let temp_root = std::fs::canonicalize(std::env::temp_dir()).unwrap();
        let root = temp_root.join(format!("dregg-poa-bazaar-linked-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&root);
        std::fs::create_dir(&root).unwrap();
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            std::fs::set_permissions(&root, std::fs::Permissions::from_mode(0o700)).unwrap();
        }
        std::env::set_var(
            crate::poa_bazaar_restart_portal::BAZAAR_STORE_DIR_ENV,
            &root,
        );
        std::env::set_var(
            crate::poa_bazaar_restart_portal::BAZAAR_STORE_ID_ENV,
            "17".repeat(32),
        );

        assert!(poa_bazaar_runtime_available());
        assert_eq!(ffi::fixture("genesis").unwrap(), "applied");
        assert_eq!(ffi::fixture("successor").unwrap(), "applied");
        assert_eq!(ffi::fixture("stale").unwrap(), "refused");

        let head = load_poa_bazaar_canonical_head()
            .unwrap()
            .expect("successor must be replayable");
        assert!(validate_poa_bazaar_state_key(head.as_str()).unwrap());
        assert!(!validate_poa_bazaar_state_key(&(head.as_str().to_owned() + " ")).unwrap());
        assert!(!validate_poa_bazaar_state_key("{}").unwrap());

        std::fs::remove_dir_all(&root).unwrap();
    }

    #[cfg(not(all(lean_lib_present, dregg_poa_bazaar_runtime_present)))]
    #[test]
    fn absent_archive_refuses_without_a_rust_codec_fallback() {
        assert!(!poa_bazaar_runtime_available());
        assert!(validate_poa_bazaar_state_key("{}").is_err());
        assert!(load_poa_bazaar_canonical_head().is_err());
        assert!(recover_poa_bazaar_store().is_err());
    }
}
