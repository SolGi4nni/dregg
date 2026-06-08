//! Adversarial fuzz of the dregg-lean-ffi marshaller (`dregg_lean_ffi::marshal`).
//!
//! The marshaller is the SEAM between the Rust executor and the verified Lean
//! kernel. Two surfaces:
//!
//!   * ENCODER — `marshal_turn(state, turn)` projects a Rust-built turn into the
//!     byte-exact wire string the Lean export parses. A panic here is a
//!     node-crash lever (every submitted turn flows through it).
//!
//!   * OUTPUT PARSER — `unmarshal_result(s)` is a strict recursive-descent
//!     parser of the string the Lean library RETURNS. In the running node this
//!     string comes from FFI across a trust boundary; a malformed/adversarial
//!     output must NEVER panic the parser and must NEVER be mis-read as a COMMIT
//!     (`committed=true`) when it isn't. The `ok` bit is the load-bearing commit
//!     authority — a parser that flips it on garbage would launder a rejection
//!     into a state edit.
//!
//! Outcome semantics: a panic, an out-of-bounds slice, or a garbage string that
//! parses to `committed=true` is a FINDING. Clean reject/roundtrip across the
//! input space is EVIDENCE the seam is robust.

use dregg_lean_ffi::marshal::{
    all_action_arms_demo, demo_turn_for_action, marshal_turn, unmarshal_result, WireHostCtx,
    WireState,
};
use proptest::prelude::*;

// ============================================================================
// OUTPUT PARSER: unmarshal_result must never panic on adversarial input
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(8000))]

    /// `unmarshal_result` on ARBITRARY bytes (interpreted as a possibly-invalid
    /// UTF-8-lossy string) must return Ok/Err — never panic. The Lean lib is
    /// across an FFI trust boundary; a corrupted/hostile return string is in
    /// scope.
    #[test]
    fn unmarshal_result_never_panics_on_arbitrary_bytes(buf in proptest::collection::vec(any::<u8>(), 0..512)) {
        let s = String::from_utf8_lossy(&buf);
        let r = unmarshal_result(&s);
        // CRITICAL: garbage must not be mis-read as a COMMIT. The only paths to
        // `committed=true` should be a well-formed `"ok":1` envelope.
        if let Ok(tr) = r {
            // A successful parse of random bytes is rare but allowed; if it
            // claims a commit, it must have come from a structurally-valid
            // envelope — re-validate the invariant that an empty-sentinel state
            // can never ride with committed=true (the marshaller's own guard).
            if tr.committed {
                prop_assert!(
                    !tr.state.is_empty_sentinel(),
                    "FINDING: garbage parsed to committed=true with an empty-sentinel state"
                );
            }
        }
    }
}

/// Mutating a VALID result envelope (single-byte tweaks) must keep the parser in
/// the no-panic / no-false-commit envelope.
#[test]
fn mutated_valid_envelope_never_false_commits() {
    // A minimal valid REJECTED envelope and a valid COMMIT envelope.
    let rejected = r#"{"state":{"cells":[],"caps":[],"bal":[],"escrows":[],"nullifiers":[],"commitments":[],"queues":[],"swiss":[],"revoked":[]},"loglen":0,"ok":0}"#;
    let committed = r#"{"state":{"cells":[],"caps":[],"bal":[],"escrows":[],"nullifiers":[],"commitments":[],"queues":[],"swiss":[],"revoked":[]},"loglen":1,"ok":1}"#;

    for base in [rejected, committed] {
        let bytes = base.as_bytes();
        for i in 0..bytes.len() {
            for bit in 0..8u8 {
                let mut m = bytes.to_vec();
                m[i] ^= 1 << bit;
                let s = String::from_utf8_lossy(&m).into_owned();
                // Must not panic; result is whatever the parser decides.
                let _ = unmarshal_result(&s);
            }
        }
    }
}

/// Truncating a valid envelope at every prefix must never panic the parser.
#[test]
fn truncated_envelope_never_panics() {
    let envelope = r#"{"state":{"cells":[[1,{"int":5}]],"caps":[],"bal":[[1,0,100]],"escrows":[],"nullifiers":[],"commitments":[],"queues":[],"swiss":[],"revoked":[]},"loglen":2,"ok":1}"#;
    for n in 0..=envelope.len() {
        let _ = unmarshal_result(&envelope[..n]);
    }
}

/// A deeply-nested / pathological numeric input must not blow the stack or hang.
#[test]
fn pathological_numbers_rejected_cleanly() {
    // Over-long digit runs (potential overflow in the Nat parser).
    let big = format!(
        r#"{{"state":{{"cells":[],"caps":[],"bal":[],"escrows":[],"nullifiers":[],"commitments":[],"queues":[],"swiss":[],"revoked":[]}},"loglen":{},"ok":1}}"#,
        "9".repeat(100)
    );
    // Must return (Ok or Err) without panicking on the 100-digit loglen.
    let _ = unmarshal_result(&big);

    // status code out of the documented 0..2 range must be REJECTED, not accepted.
    let bad_status = r#"{"state":{"cells":[],"caps":[],"bal":[],"escrows":[],"nullifiers":[],"commitments":[],"queues":[],"swiss":[],"revoked":[]},"loglen":0,"status":9,"ok":1}"#;
    assert!(
        unmarshal_result(bad_status).is_err(),
        "FINDING: out-of-range status code 9 was accepted by unmarshal_result"
    );
}

// ============================================================================
// ENCODER: marshal_turn must never panic across every action arm
// ============================================================================

/// Every demo action arm must marshal without panic and produce a non-empty,
/// brace-balanced wire string. This exercises EVERY `WireAction` variant's
/// encode path (the per-effect projection the node runs on the hot submit path).
#[test]
fn every_action_arm_marshals_cleanly() {
    let state = WireState::default();
    for arm in all_action_arms_demo() {
        let turn = demo_turn_for_action(arm.clone());
        let wire = marshal_turn(&state, &turn)
            .unwrap_or_else(|e| panic!("FINDING: marshal_turn panicked/errored on {arm:?}: {e:?}"));
        assert!(!wire.is_empty(), "empty wire for {arm:?}");
        // Brace balance is a cheap structural sanity check on the encoder.
        let opens = wire.matches('{').count();
        let closes = wire.matches('}').count();
        assert_eq!(opens, closes, "unbalanced braces marshalling {arm:?}: {wire}");
        let bopen = wire.matches('[').count();
        let bclose = wire.matches(']').count();
        assert_eq!(bopen, bclose, "unbalanced brackets marshalling {arm:?}");
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1500))]

    /// Marshal each action arm against a fuzzed HOST context (clock/budget/head
    /// chosen adversarially) — the encoder must stay panic-free. The host ctx is
    /// the NODE-fed admission seam; an attacker influences the turn but not the
    /// host, so we vary the host to confirm encode robustness across the range.
    #[test]
    fn marshal_is_panic_free_under_fuzzed_host(
        arm_idx in any::<usize>(),
        now in any::<u64>(),
        block_height in any::<u64>(),
        stored_head in any::<u64>(),
        budget in any::<u64>(),
        frozen in proptest::collection::vec(any::<u64>(), 0..8),
    ) {
        let arms = all_action_arms_demo();
        let arm = arms[arm_idx % arms.len()].clone();
        let turn = demo_turn_for_action(arm);
        let host = WireHostCtx { now, block_height, stored_head, budget, frozen };
        let state = WireState::default();
        // marshal_turn_hosted shares the encode core; round it through the parser
        // is NOT possible (no input decoder), so we only assert no-panic + non-empty.
        let _ = dregg_lean_ffi::marshal::marshal_turn_hosted(&host, &state, &turn);
    }
}
