//! Internal native callbacks for the checked-Bool Bazaar Lean primitives.
//!
//! Kept separate from `poa_bazaar_restart_portal.rs` so that file's standalone
//! codec/store integration tests cannot duplicate these process-global symbols.

use crate::poa_bazaar_restart_portal::{
    configured_runtime_store, load_configured_canonical_head, parse_hex_digest, BazaarCasOutcome,
    BazaarCasRequest, BazaarRestartError, CanonicalEventBytes, CanonicalStateBytes,
    MAX_CANONICAL_EVENT_BYTES, MAX_CANONICAL_STATE_BYTES,
};

fn bytes_from_ffi(pointer: *const u8, length: usize) -> Result<Vec<u8>, BazaarRestartError> {
    if length == 0 {
        return Err(BazaarRestartError::InvalidWire("empty canonical state"));
    }
    if length > MAX_CANONICAL_STATE_BYTES {
        return Err(BazaarRestartError::InvalidWire(
            "canonical state exceeds maximum",
        ));
    }
    if pointer.is_null() {
        return Err(BazaarRestartError::InvalidWire(
            "null canonical-state pointer",
        ));
    }
    // SAFETY: the C shim passes a Lean string's live byte buffer and exact
    // `lean_string_size - 1` while retaining that Lean object for this call.
    Ok(unsafe { std::slice::from_raw_parts(pointer, length) }.to_vec())
}

fn text_from_ffi(
    pointer: *const u8,
    length: usize,
    maximum: usize,
    empty_reason: &'static str,
    oversized_reason: &'static str,
) -> Result<String, BazaarRestartError> {
    if length == 0 {
        return Err(BazaarRestartError::InvalidWire(empty_reason));
    }
    if length > maximum {
        return Err(BazaarRestartError::InvalidWire(oversized_reason));
    }
    if pointer.is_null() {
        return Err(BazaarRestartError::InvalidWire("null text pointer"));
    }
    // SAFETY: the checked C shim retains each Lean string for the duration of
    // this call and passes its exact non-NUL byte length.
    let bytes = unsafe { std::slice::from_raw_parts(pointer, length) };
    std::str::from_utf8(bytes)
        .map(str::to_owned)
        .map_err(|_| BazaarRestartError::InvalidWire("text is not UTF-8"))
}

/// Native half of the private Lean `performCasChecked` primitive.
/// `1` means durably applied, `0` means stale/refused, and `-1` is failure.
#[no_mangle]
pub extern "C" fn dregg_poa_bazaar_native_perform_cas(
    expected_present: u8,
    expected_pointer: *const u8,
    expected_length: usize,
    replacement_pointer: *const u8,
    replacement_length: usize,
) -> i32 {
    std::panic::catch_unwind(|| {
        let expected = match expected_present {
            0 if expected_length == 0 => None,
            1 => Some(CanonicalStateBytes::new_checked(bytes_from_ffi(
                expected_pointer,
                expected_length,
            )?)?),
            _ => {
                return Err(BazaarRestartError::InvalidWire(
                    "native expected tag/length mismatch",
                ));
            }
        };
        let replacement = CanonicalStateBytes::new_checked(bytes_from_ffi(
            replacement_pointer,
            replacement_length,
        )?)?;
        let request = BazaarCasRequest::new_checked(expected, replacement);
        match configured_runtime_store()?.compare_and_swap(&request)? {
            BazaarCasOutcome::Applied { .. } => Ok(1),
            BazaarCasOutcome::Stale { .. } => Ok(0),
        }
    })
    .unwrap_or(Err(BazaarRestartError::InvalidWire(
        "panic in native Bazaar CAS",
    )))
    .unwrap_or(-1)
}

/// Event-bearing v3 CAS. The context spellings and command payload all come
/// from independent Lean exports over the same private typed request.
#[no_mangle]
pub extern "C" fn dregg_poa_bazaar_native_perform_journaled_cas(
    expected_present: u8,
    expected_pointer: *const u8,
    expected_length: usize,
    replacement_pointer: *const u8,
    replacement_length: usize,
    event_pointer: *const u8,
    event_length: usize,
    store_pointer: *const u8,
    store_length: usize,
    deployment_pointer: *const u8,
    deployment_length: usize,
) -> i32 {
    std::panic::catch_unwind(|| {
        let expected = match expected_present {
            0 if expected_length == 0 => None,
            1 => Some(CanonicalStateBytes::new_checked(bytes_from_ffi(
                expected_pointer,
                expected_length,
            )?)?),
            _ => {
                return Err(BazaarRestartError::InvalidWire(
                    "native expected tag/length mismatch",
                ));
            }
        };
        let replacement = CanonicalStateBytes::new_checked(bytes_from_ffi(
            replacement_pointer,
            replacement_length,
        )?)?;
        let event = CanonicalEventBytes::new_checked(
            text_from_ffi(
                event_pointer,
                event_length,
                MAX_CANONICAL_EVENT_BYTES,
                "empty canonical event",
                "canonical event exceeds maximum",
            )?
            .into_bytes(),
        )?;
        let store_hex = text_from_ffi(
            store_pointer,
            store_length,
            64,
            "empty store identity",
            "store identity exceeds maximum",
        )?;
        let deployment_hex = text_from_ffi(
            deployment_pointer,
            deployment_length,
            64,
            "empty deployment identity",
            "deployment identity exceeds maximum",
        )?;
        let store_identity = parse_hex_digest(&store_hex, "command event store identity")?;
        let deployment_id = parse_hex_digest(&deployment_hex, "command event deployment identity")?;
        let store = configured_runtime_store()?;
        store.require_replay_context(&store_identity, &deployment_id)?;
        let request = BazaarCasRequest::new_checked(expected, replacement);
        match store.compare_and_swap_journaled(&request, event)? {
            BazaarCasOutcome::Applied { .. } => Ok(1),
            BazaarCasOutcome::Stale { .. } => Ok(0),
        }
    })
    .unwrap_or(Err(BazaarRestartError::InvalidWire(
        "panic in native journaled Bazaar CAS",
    )))
    .unwrap_or(-1)
}

/// Native half of the private Lean `admitDurableLoadChecked` primitive.
/// It checks only the exact tail after complete journal replay.
#[no_mangle]
pub extern "C" fn dregg_poa_bazaar_native_durable_load_matches(
    canonical_pointer: *const u8,
    canonical_length: usize,
) -> i32 {
    std::panic::catch_unwind(|| {
        let candidate =
            CanonicalStateBytes::new_checked(bytes_from_ffi(canonical_pointer, canonical_length)?)?;
        Ok(i32::from(
            load_configured_canonical_head()?.as_ref() == Some(&candidate),
        ))
    })
    .unwrap_or(Err(BazaarRestartError::InvalidWire(
        "panic in native Bazaar durable load",
    )))
    .unwrap_or(-1)
}
