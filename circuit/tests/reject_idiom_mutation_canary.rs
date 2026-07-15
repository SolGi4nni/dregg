//! **THE MUTATION CANARY for the P1b reject idiom** (CRATE-EXCELLENCE-PLAN §2 P1(b), §4 Move 3).
//!
//! The plan's claimed payoff for killing the reject idiom is exact:
//!
//! > "Then a stray `unwrap` in trace assembly reds the suite instead of silently satisfying every
//! > forgery test."
//!
//! This file PROVES that payoff rather than asserting it, by running BOTH shapes — the old idiom
//! and the `refusal` discriminator — against the SAME injected fault, and requiring that they
//! disagree. If they ever agree, the discriminator has stopped discriminating and this file reds.
//!
//! The injected fault is modelled, not hypothetical: `stray_unwrap_in_trace_assembly` reproduces
//! what a `.unwrap()` on a `None` (or a producer-side `debug_assert!`) inside `fill_chip_lanes` /
//! `fold_chain` does — it unwinds out of the prove call before the constraint system is ever
//! consulted. Two REAL instances of exactly this were found in-tree while landing the
//! discriminator, and both had kept an adversarially-named tooth green at HEAD:
//!
//!   * `descriptor_ir2::tests::ir2_forged_map_opening_refuses` — satisfied by
//!     `debug_assert_eq!(end, root, "old path must authenticate against root8")`.
//!   * `descriptor_ir2::tests::deployed_heap_splice_rejects_content_mismatch` — satisfied by
//!     `debug_assert_eq!(end, new_root, "new path must recompose to new_root8")`.
//!
//! Neither ever reached `prove_batch`. That is the wild form of this canary; the tests below are
//! the mechanical proof that the new shape cannot be fooled the same way.

use dregg_circuit::refusal::{Outcome, classify, must_refuse, must_refuse_or_unsat_panic};

/// A forged witness that the constraint system genuinely refuses: the p3 batch prover's
/// DOCUMENTED unsat verdict (`lookup/src/debug_util.rs:82`). This is a REAL refusal.
fn constraint_system_refuses() -> Result<(), String> {
    panic!(
        "Lookup mismatch (global lookup 'ir2_p2'): tuple [\"2\", \"11\"] has net multiplicity \
         2013265917. Locations: [Location {{ instance: 1, lookup: 0, row: 0 }}]"
    )
}

/// THE FAULT: a stray `unwrap`/`debug_assert` in trace assembly. The prove call unwinds before
/// the constraint system is consulted, so NOTHING has been proved about the forgery.
fn stray_unwrap_in_trace_assembly() -> Result<(), String> {
    let lane: Option<u32> = None;
    let _ = lane.unwrap(); // as if inside `fill_chip_lanes`
    Ok(())
}

/// The OLD idiom, verbatim — reproduced here as the thing under test, not as production code.
/// `true` == "the tooth reported the forgery as refused".
fn old_idiom_says_refused(f: impl FnOnce() -> Result<(), String>) -> bool {
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(f)) {
        Err(_) => true,     // ANY panic counted as a refusal — the defect
        Ok(Err(_)) => true, // any error counted as a refusal
        Ok(Ok(())) => false,
    }
}

/// The NEW shape. `true` == refused; a stray panic PANICS out (the suite reds) rather than
/// returning `true`.
fn new_shape_says_refused(f: impl FnOnce() -> Result<(), String>) -> bool {
    match classify("canary", f) {
        Outcome::UnsatPanic(_) | Outcome::Err(_) => true,
        Outcome::Accepted(_) => false,
    }
}

/// **THE HONEST POLE (S1).** Both shapes must AGREE that a genuine constraint-system refusal IS a
/// refusal. Without this, the canary below is vacuous: a discriminator that rejected *everything*
/// would "detect the mutation" while being useless.
#[test]
fn both_shapes_accept_a_genuine_constraint_refusal() {
    assert!(
        old_idiom_says_refused(constraint_system_refuses),
        "the old idiom must report a real unsat verdict as refused"
    );
    assert!(
        new_shape_says_refused(constraint_system_refuses),
        "the discriminator must report a real unsat verdict as refused — if this reds, the \
         discriminator is over-strict and every genuine tooth would red with it"
    );
}

/// **THE CANARY, POLE 1 — the defect, reproduced.** With the fault injected, the OLD idiom
/// reports "refused" and the tooth stays GREEN, having proved nothing. This test passing IS the
/// P1b anti-pattern, demonstrated rather than described.
#[test]
fn old_idiom_stays_green_under_a_stray_trace_assembly_unwrap() {
    assert!(
        old_idiom_says_refused(stray_unwrap_in_trace_assembly),
        "the old idiom reports a stray unwrap as a refusal — this is the P1b defect, and if this \
         assertion ever fails the premise of this whole lane has changed"
    );
}

/// **THE CANARY, POLE 2 — the fix bites.** The SAME fault, through the discriminator, REDS.
/// `must_refuse` panics rather than returning, so a forgery test built on it cannot be satisfied
/// by a crash in trace assembly.
#[test]
#[should_panic(expected = "expected a fail-closed Err refusal, but the call PANICKED")]
fn must_refuse_reds_under_a_stray_trace_assembly_unwrap() {
    must_refuse("forged witness", stray_unwrap_in_trace_assembly);
}

/// Even the panic-TOLERANT variant — the one reserved for sites where the p3 debug prover's
/// unsat panic is genuinely the mechanism — refuses to launder a stray unwrap into a refusal.
/// This is the load-bearing half: those sites must accept *a* panic, so they are the ones most at
/// risk of accepting *any* panic.
#[test]
#[should_panic(expected = "NOT with the p3 debug prover's documented unsat panic")]
fn unsat_tolerant_variant_reds_under_a_stray_trace_assembly_unwrap() {
    must_refuse_or_unsat_panic("forged witness", stray_unwrap_in_trace_assembly);
}

/// `classify` — the primitive under the `rejects()`/`refuse()` helpers across both crates' emit
/// gates — must red too. Those helpers keep a `bool` API (S1's honest pole is `!rejects(..)`), so
/// this is where a stray unwrap would otherwise flow straight back as `true` == "rejected".
#[test]
#[should_panic(expected = "NOT with the p3 debug prover's documented unsat panic")]
fn classify_reds_under_a_stray_trace_assembly_unwrap() {
    new_shape_says_refused(stray_unwrap_in_trace_assembly);
}

/// **THE DISAGREEMENT, stated as one assertion.** The two shapes must reach OPPOSITE verdicts on
/// the injected fault: old says "refused" (green, vacuous), new refuses to say anything at all
/// (reds). This is the plan's payoff as a single checkable claim.
#[test]
fn the_two_shapes_disagree_exactly_where_the_plan_says_they_must() {
    // The fault is invisible to the old idiom...
    let old_verdict = old_idiom_says_refused(stray_unwrap_in_trace_assembly);
    assert!(old_verdict, "old idiom: stray unwrap reads as 'refused'");

    // ...and fatal to the new one.
    let new_verdict =
        std::panic::catch_unwind(|| new_shape_says_refused(stray_unwrap_in_trace_assembly));
    assert!(
        new_verdict.is_err(),
        "the discriminator must REFUSE TO RETURN a verdict for a stray unwrap — if it returned \
         one, a stray unwrap in trace assembly would once again satisfy every forgery test"
    );

    // And on a GENUINE refusal they agree — so the difference is precisely the fault, not
    // blanket strictness.
    assert_eq!(
        old_idiom_says_refused(constraint_system_refuses),
        new_shape_says_refused(constraint_system_refuses),
        "on a real unsat verdict the two shapes must agree"
    );
}
