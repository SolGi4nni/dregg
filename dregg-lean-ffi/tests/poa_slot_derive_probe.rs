//! Exact native probe for the Path of Angels per-run instance derivation.
//!
//! These fixture bytes are `SlotDeriveRuntime.fixtureRequestBytes` and
//! `(derive fixtureRequest).toJson`, emitted by Lean itself.
//!
//! # ⚑ Why this file exists at all
//!
//! Until the `@[export]` landed, the ONLY export-specific test on this seam was
//! `poa_slot_derive_ffi::tests::absent_export_refuses_rather_than_deriving`, and it is
//! gated `#[cfg(not(all(lean_lib_present, dregg_poa_signal_slot_derive_present)))]`.
//! Landing the export therefore DELETED the seam's only test — the mirror image of the
//! failure `build.rs`'s own required-export panic describes, where flipping a cfg makes
//! a test module cease to exist and `cargo test` reports the survivors as green.
//!
//! This test occupies the other polarity: it exists only when the export is present, it
//! asserts availability rather than skipping on it, and it compares against frozen Lean
//! bytes. Between the two, one of them always runs.
//!
//! It neither constructs authority nor reimplements the derivation: the whole point of
//! the seam is that Rust computes nothing here.
#![cfg(feature = "lean-lib")]

use dregg_lean_ffi::poa_slot_derive_ffi::{derive_poa_slot_instance, poa_slot_derive_available};

const REQUEST_FILE: &str = include_str!("fixtures/poa-slot-derive-request-v1.json");
const REPLY_FILE: &str = include_str!("fixtures/poa-slot-derive-reply-v1.json");

fn without_fixture_newline(bytes: &'static str) -> &'static str {
    bytes
        .strip_suffix('\n')
        .expect("committed PoA fixture must have exactly one file newline")
}

#[test]
fn frozen_lean_derivation_is_linked_and_exact() {
    assert!(
        poa_slot_derive_available(),
        "dregg_poa_signal_slot_derive is absent or failed initialization; this is a refusal, \
         not a skip — every scored Signal run cannot be prepared at all"
    );
    let request = without_fixture_newline(REQUEST_FILE);
    let expected = without_fixture_newline(REPLY_FILE);
    let reply = derive_poa_slot_instance(request)
        .expect("linked Lean derivation must be callable")
        .expect("frozen canonical request must be accepted");
    assert_eq!(reply, expected);
}

#[test]
fn trailing_byte_is_a_semantic_refusal_not_a_transport_success() {
    assert!(poa_slot_derive_available());
    let mut noncanonical = without_fixture_newline(REQUEST_FILE).to_owned();
    noncanonical.push('\n');
    assert_eq!(
        derive_poa_slot_instance(&noncanonical).expect("linked Lean derivation must be callable"),
        None
    );
}

/// Key ORDER is part of the canonical seal, not merely key membership. A caller that
/// serializes the same eight fields through a map that reorders them is REFUSED, which
/// is the fail-closed direction and worth pinning: it is the difference between "the
/// node derived this" and "some encoder happened to agree".
#[test]
fn transposed_keys_are_refused() {
    assert!(poa_slot_derive_available());
    let request = without_fixture_newline(REQUEST_FILE);
    let transposed = request.replace(
        "\"slot\":9,\"secret\":",
        "\"secret_placeholder\":0,\"slot\":9,\"secret\":",
    );
    assert_ne!(
        transposed, request,
        "the fixture spelling changed; fix this probe"
    );
    assert_eq!(
        derive_poa_slot_instance(&transposed).expect("linked Lean derivation must be callable"),
        None
    );
}
