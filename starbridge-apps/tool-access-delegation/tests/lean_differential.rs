//! ROUTE + DIFFERENTIAL tests over the delegated tool-access admission boundary.
//!
//! `deleg_admit` / `deleg_corpus` / `admit_table` no longer decide anything: they marshal across
//! `dregg_deleg_admit` to `Dregg2.Apps.DelegAdmit.delegAdmit`, the predicate the Lean
//! `tool_invocation_commit_iff_admit` and its three rejection teeth are proven over. What this file
//! checks is therefore split in two, and the distinction is load-bearing:
//!
//!   * **ROUTE** ([`corpus_matches_lean_pinned_literal`], the three tooth tests) — the boundary is
//!     actually reached and the verdicts that come back are the ones the Lean `#guard`s witness. The
//!     pinned vector here is the IDENTICAL literal the Lean
//!     `#guard AppDiffPinned (mandateSpec demoGrant 50 77 5) [...]` pins, so a Lean `delegAdmit`
//!     change trips the `#guard` at `lake build` AND this literal here.
//!   * **DIFFERENTIAL** ([`wire_marshalling_agrees_with_the_policy_over_a_grid_sweep`]) — a
//!     test-local restatement of the five conjuncts swept over a grid, compared cell-for-cell with
//!     what the oracle answers. It is a MARSHALLING check: it catches a mangled wire, an argument
//!     swapped in transit, a sign lost on a negative id. It is **not** refinement, **not**
//!     translation validation, and **not** verification — there is no formal semantics of Rust, and
//!     a sweep says nothing about the inputs it does not enumerate. The thing that covers those is
//!     that the answering function IS the one the theorems are stated over.
//!
//! Before this routing there were THREE Rust re-implementations of the policy in the workspace and
//! this file compared one of them to a literal. That comparison was the whole assurance story, and
//! it was a drift detector wearing a proof's clothes.

use starbridge_tool_access_delegation::{Grant, admit_table, deleg_admit, deleg_corpus};

/// The Lean `demoGrant`: tool 77, rate 3, deadline 100.
const DEMO: Grant = Grant {
    tool_id: 77,
    rate_limit: 3,
    deadline: 100,
};

/// The linked archive answers, or the test is honestly skipped — and PANICS under
/// `DREGG_TEST_REQUIRE_LEAN=1`, so a verification lane cannot report a hollow `ok` for a gate that
/// never ran.
fn lean_answers() -> bool {
    dregg_lean_ffi::demand_lean(
        dregg_lean_ffi::deleg_admit_available(),
        "dregg_deleg_admit (the delegated tool-access admission oracle)",
    )
}

/// One admission verdict from the Lean oracle; an `Err` here is NO VERDICT and must fail the test
/// loudly rather than read as a refusal.
fn admits(g: &Grant, now: i64, tool: i64, old: i64, new: i64) -> bool {
    deleg_admit(g, now, tool, old, new).expect("the Lean oracle reached a verdict")
}

/// The EXACT vector the Lean `AppDiffPinned (mandateSpec demoGrant 50 77 5)` `#guard` pins, row-major
/// over old {0,1,2,3} × new {1,2,3,4} (16 cells; exactly the 3 diagonal advances `(c, c+1)` with
/// `c+1 <= 3` are true; `(3,4)` is over-rate ⇒ false).
const PINNED_CORPUS_IN_SCOPE_IN_TIME: [bool; 16] = [
    // old = 0:  →1 true,  →2,→3,→4 false
    true, false, false, false, //
    // old = 1:  →2 true
    false, true, false, false, //
    // old = 2:  →3 true
    false, false, true, false, //
    // old = 3:  none (3→4 over-rate)
    false, false, false, false,
];

#[test]
fn corpus_matches_lean_pinned_literal() {
    if !lean_answers() {
        return;
    }
    assert_eq!(
        deleg_corpus(&DEMO, 50, 77)
            .expect("the Lean oracle reached a verdict")
            .as_slice(),
        &PINNED_CORPUS_IN_SCOPE_IN_TIME[..],
        "the routed corpus diverged from the Lean-pinned AppDiffPinned vector — either the Lean \
         delegAdmit changed (re-pin both sides) or the wire marshalling is wrong"
    );
}

#[test]
fn rate_tooth_bites() {
    if !lean_answers() {
        return;
    }
    // Lean `tool_invocation_over_rate_rejected` witness: the (N+1)-th invocation is rejected.
    assert!(admits(&DEMO, 50, 77, 2, 3)); // the 3rd (last legal) call
    assert!(!admits(&DEMO, 50, 77, 3, 4)); // the 4th — over the granted rate
}

#[test]
fn deadline_tooth_bites() {
    if !lean_answers() {
        return;
    }
    // Lean `tool_invocation_past_deadline_rejected`: now 101 > deadline 100 ⇒ EMPTY table.
    assert!(admits(&DEMO, 100, 77, 0, 1)); // exactly at the deadline still admits
    assert!(!admits(&DEMO, 101, 77, 0, 1)); // one past — rejected
    assert_eq!(admit_table(&DEMO, 101, 77).unwrap().len(), 0);
}

#[test]
fn scope_tooth_bites() {
    if !lean_answers() {
        return;
    }
    // Lean `tool_invocation_out_of_scope_rejected`: tool 99 ≠ granted 77 ⇒ EMPTY table.
    assert!(admits(&DEMO, 50, 77, 0, 1)); // the granted tool admits
    assert!(!admits(&DEMO, 50, 99, 0, 1)); // a different tool — rejected
    assert_eq!(admit_table(&DEMO, 50, 99).unwrap().len(), 0);
}

#[test]
fn corpus_is_non_vacuous() {
    if !lean_answers() {
        return;
    }
    // The corpus contains BOTH true and false (it is neither all-admit nor all-reject).
    let c = deleg_corpus(&DEMO, 50, 77).expect("the Lean oracle reached a verdict");
    assert!(
        c.iter().any(|&b| b),
        "corpus has no admitted cell (vacuous-reject)"
    );
    assert!(
        c.iter().any(|&b| !b),
        "corpus has no rejected cell (vacuous-admit)"
    );
    assert_eq!(
        c.iter().filter(|&&b| b).count(),
        3,
        "exactly 3 legal advances"
    );
}

/// A **DIFFERENTIAL TEST** of the WIRE, not a verification of the policy.
///
/// Sweeps a range of grants/presentations and compares each of the oracle's verdicts against a
/// test-local restatement of the five conjuncts. What it can catch is marshalling damage: a swapped
/// argument, a dropped sign, a truncated field, a grant flattened in the wrong order. What it
/// CANNOT do is establish that the policy is right — the enumerated cells say nothing about the
/// rest, and Rust has no formal semantics for a case test to generalize over. The Lean side is where
/// "for all inputs" lives (`tool_invocation_commit_iff_admit`); this is a boundary smoke test with a
/// wide nozzle.
#[test]
fn wire_marshalling_agrees_with_the_policy_over_a_grid_sweep() {
    if !lean_answers() {
        return;
    }
    for rate in 1..=5i64 {
        for deadline in 0..=4i64 {
            let g = Grant {
                tool_id: 7,
                rate_limit: rate,
                deadline,
            };
            for now in 0..=5i64 {
                for tool in 6..=8i64 {
                    for old in 0..=rate {
                        for new in 1..=(rate + 1) {
                            let restated = tool == g.tool_id
                                && now <= g.deadline
                                && new == old + 1
                                && 0 <= old
                                && new <= g.rate_limit;
                            assert_eq!(
                                admits(&g, now, tool, old, new),
                                restated,
                                "the routed verdict disagreed with the restated policy at \
                                 g={g:?} now={now} tool={tool} {old}->{new} — suspect the WIRE \
                                 (argument order, sign, truncation), not the proof"
                            );
                        }
                    }
                }
            }
        }
    }
}

/// NEGATIVE ids survive the signed wire — the marshalling case a `Nat`-shaped wire would have eaten
/// silently. (`Grant.tool_id` and the presented tool are `Int` on both sides.)
#[test]
fn negative_ids_round_trip_the_wire() {
    if !lean_answers() {
        return;
    }
    let g = Grant {
        tool_id: -5,
        rate_limit: 2,
        deadline: 100,
    };
    assert!(
        admits(&g, 50, -5, 0, 1),
        "the granted negative tool id admits"
    );
    assert!(
        !admits(&g, 50, 5, 0, 1),
        "the positive twin is out of scope"
    );
}
