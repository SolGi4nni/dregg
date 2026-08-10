//! Exact native probe for the internal Path of Angels Signal evaluator.
//!
//! These fixture bytes are emitted by the frozen Lean `fixtureInputBytes` / `fixtureOutputBytes`.
//! The test neither constructs authority nor parses/reimplements game semantics: it proves that the
//! archive symbol actually linked into this process returns the exact Lean successor, and that a
//! noncanonical transport is the explicit `Rejected` outcome.
#![cfg(feature = "lean-lib")]

use dregg_lean_ffi::poa_ffi::{judge_poa_signal, poa_signal_judge_available, PoaSignalVerdict};

const INPUT_FILE: &str = include_str!("fixtures/poa-signal-input-v1.json");
const OUTPUT_FILE: &str = include_str!("fixtures/poa-signal-output-v1.json");

/// ⚠ Lean emits these two fixtures with NO trailing newline (its siblings under
/// `fixtures/` still have one, so the shape is the GENERATOR's, not the wire's). An
/// `.expect` here panics on a re-emit and pins whitespace rather than content — which is
/// exactly what happened when `059f62db3` re-cut both files onto the `POA-RUN-IN-1` wire.
/// `bytes` is already a binding, so the one-expression form is the right one here; the
/// `include_str!`-inline sites need a `let raw` first (see `node/src/poa_signal_adapter.rs`).
fn without_fixture_newline(bytes: &'static str) -> &'static str {
    bytes.strip_suffix('\n').unwrap_or(bytes)
}

#[test]
fn frozen_lean_fixture_is_linked_and_exact() {
    assert!(
        poa_signal_judge_available(),
        "dregg_poa_signal_judge is absent or failed initialization; this is a refusal, not a skip"
    );
    let input = without_fixture_newline(INPUT_FILE);
    let expected = without_fixture_newline(OUTPUT_FILE);
    let PoaSignalVerdict::Accepted(accepted) =
        judge_poa_signal(input).expect("linked Lean evaluator must be callable")
    else {
        panic!("frozen canonical fixture must be accepted");
    };
    assert_eq!(accepted.as_str(), expected);
    assert!(accepted.was_judged_for(input.as_bytes()));
}

#[test]
fn trailing_byte_is_a_semantic_refusal_not_a_transport_success() {
    let mut noncanonical = without_fixture_newline(INPUT_FILE).to_owned();
    noncanonical.push('\n');
    assert_eq!(
        judge_poa_signal(&noncanonical).expect("linked Lean evaluator must be callable"),
        PoaSignalVerdict::Rejected
    );
}
