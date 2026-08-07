//! Exact native probe for the Path of Angels mid-run LOCKED/DRIFT oracle.
//!
//! These fixture bytes are `SignalFeedbackRuntime.fixtureRequestBytes` and the reply
//! Lean emits for them. The request's first eight fields are byte-identical to
//! `tests/fixtures/poa-slot-derive-request-v1.json`, and its `commitment` is that
//! fixture's derived commitment — so the two probes are provably about ONE instance and
//! the expected classification below can be read off the derivation fixture's
//! `"target":{"low":2,"mid":5,"high":1}` by hand.
//!
//! # Why this file exists (the same polarity argument as the derivation probe)
//!
//! The seam's in-module test `absent_export_refuses_rather_than_classifying` is gated
//! `#[cfg(not(all(lean_lib_present, dregg_poa_signal_feedback_present)))]`, so landing
//! the export deletes it. This test occupies the other polarity: it exists only when
//! the export is present, it ASSERTS availability rather than skipping on it, and it
//! compares against frozen Lean bytes. Between the two, one of them always runs.
//!
//! It reimplements no part of the rule. Rust computes nothing on this path.
#![cfg(feature = "lean-lib")]

use dregg_lean_ffi::poa_signal_feedback_ffi::{
    classify_poa_signal_guess, poa_signal_feedback_available,
};

const REQUEST_FILE: &str = include_str!("fixtures/poa-signal-feedback-request-v1.json");
const REPLY_FILE: &str = include_str!("fixtures/poa-signal-feedback-reply-v1.json");
const DERIVE_REQUEST_FILE: &str = include_str!("fixtures/poa-slot-derive-request-v1.json");

fn without_fixture_newline(bytes: &'static str) -> &'static str {
    bytes
        .strip_suffix('\n')
        .expect("committed PoA fixture must have exactly one file newline")
}

#[test]
fn frozen_lean_classification_is_linked_and_exact() {
    assert!(
        poa_signal_feedback_available(),
        "dregg_poa_signal_feedback is absent or failed initialization; this is a refusal, \
         not a skip — judged sessions cannot be served at all and judged play reverts to \
         a blind 1-in-216 claim"
    );
    let request = without_fixture_newline(REQUEST_FILE);
    let expected = without_fixture_newline(REPLY_FILE);
    let reply = classify_poa_signal_guess(request)
        .expect("linked Lean oracle must be callable")
        .expect("frozen canonical request must be accepted");
    assert_eq!(reply, expected);
}

/// ⚑ THE ORACLE IS AN ORACLE. Two guesses against one instance get different answers,
/// so `frozen_lean_classification_is_linked_and_exact` is not pinning a constant.
#[test]
fn a_different_guess_is_classified_differently() {
    assert!(poa_signal_feedback_available());
    let request = without_fixture_newline(REQUEST_FILE);
    let other = request.replace(
        "\"guess\":{\"low\":0,\"mid\":1,\"high\":2}",
        "\"guess\":{\"low\":3,\"mid\":3,\"high\":3}",
    );
    assert_ne!(
        other, request,
        "the fixture spelling changed; fix this probe"
    );
    let first = classify_poa_signal_guess(request).unwrap().unwrap();
    let second = classify_poa_signal_guess(&other).unwrap().unwrap();
    assert_ne!(first, second);
}

/// ⚑ THE ANSWER SOLVES, AND THE REPLY SAYS SO WITH `exact:3`. The target comes from the
/// DERIVATION fixture beside this one, which is the whole point: the oracle classifies
/// against the instance the judge will score, not a second instance of its own.
#[test]
fn the_derived_target_locks_all_three_bands() {
    assert!(poa_signal_feedback_available());
    let derived = without_fixture_newline(DERIVE_REQUEST_FILE);
    assert!(
        derived.contains("\"player_key\":\"5555"),
        "the derivation fixture no longer names this probe's player; fix this probe"
    );
    let request = without_fixture_newline(REQUEST_FILE).replace(
        "\"guess\":{\"low\":0,\"mid\":1,\"high\":2}",
        // `poa-slot-derive-reply-v1.json`'s `"target":{"low":2,"mid":5,"high":1}`.
        "\"guess\":{\"low\":2,\"mid\":5,\"high\":1}",
    );
    let reply = classify_poa_signal_guess(&request).unwrap().unwrap();
    assert_eq!(
        reply, "{\"format\":\"POA-SIGNAL-FEEDBACK-OUT-1\",\"exact\":3,\"present\":0}",
        "the derivation fixture's target must LOCK all three bands on the oracle"
    );
}

/// ⚠ THE REPLY IS THE CLASSIFICATION AND NOTHING ELSE. The secret, the derived run seed
/// and the derived target's canonical spelling are all absent from the served bytes.
/// Lean proves the general statement; this asserts it on the live linked export, which
/// is the thing a route actually returns.
#[test]
fn the_served_bytes_carry_no_secret_no_seed_and_no_target() {
    assert!(poa_signal_feedback_available());
    let reply = classify_poa_signal_guess(without_fixture_newline(REQUEST_FILE))
        .unwrap()
        .unwrap();
    for forbidden in [
        // the slot secret
        "7777777777777777777777777777777777777777777777777777777777777777",
        // `poa-slot-derive-reply-v1.json`'s run_seed
        "b09bafac1e1f699a7c398bcd0da6ae769eaf7ba08375c1c06015cec9c6ab4e77",
        // and its commitment, which is public and still does not belong here
        "bc7742888f4ed90ace371abf4b0be7dec5e22d47723bcfd01903a8aa2332a491",
        // the canonical spelling of the target on this very wire
        "{\"low\":2,\"mid\":5,\"high\":1}",
    ] {
        assert!(
            !reply.contains(forbidden),
            "the feedback reply leaked {forbidden}: {reply}"
        );
    }
    assert_eq!(
        reply.len(),
        "{\"format\":\"POA-SIGNAL-FEEDBACK-OUT-1\",\"exact\":0,\"present\":2}".len(),
        "the reply is a fixed-length two-count document; a length that varies is a field \
         by another name"
    );
}

/// A node whose secret does not open the stated commitment is served NOTHING. The
/// oracle is a classification against an instance the curator committed to in advance,
/// or it is a refusal.
#[test]
fn a_commitment_the_secret_does_not_open_is_refused() {
    assert!(poa_signal_feedback_available());
    let request = without_fixture_newline(REQUEST_FILE).replace(
        "bc7742888f4ed90ace371abf4b0be7dec5e22d47723bcfd01903a8aa2332a491",
        "00000000000000000000000000000000000000000000000000000000000000ff",
    );
    assert_eq!(
        classify_poa_signal_guess(&request).expect("linked Lean oracle must be callable"),
        None
    );
}

/// A band outside `0..5` is refused rather than reduced modulo six — a wrapped band
/// would be a second spelling of a legal guess and would hand the player a free round.
#[test]
fn an_out_of_range_band_is_refused() {
    assert!(poa_signal_feedback_available());
    let request = without_fixture_newline(REQUEST_FILE).replace("\"high\":2}}", "\"high\":6}}");
    assert_eq!(classify_poa_signal_guess(&request).unwrap(), None);
}

#[test]
fn trailing_byte_is_a_semantic_refusal_not_a_transport_success() {
    assert!(poa_signal_feedback_available());
    let mut noncanonical = without_fixture_newline(REQUEST_FILE).to_owned();
    noncanonical.push('\n');
    assert_eq!(
        classify_poa_signal_guess(&noncanonical).expect("linked Lean oracle must be callable"),
        None
    );
}

/// Key ORDER is part of the canonical seal, not merely key membership.
#[test]
fn transposed_keys_are_refused() {
    assert!(poa_signal_feedback_available());
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
        classify_poa_signal_guess(&transposed).expect("linked Lean oracle must be callable"),
        None
    );
}
