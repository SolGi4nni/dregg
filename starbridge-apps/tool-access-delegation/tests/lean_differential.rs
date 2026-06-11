//! Differential test: the Rust `deleg_admit` / `deleg_corpus` mirror agrees, cell-for-cell, with the
//! verified Lean `Dregg2.Apps.ToolAccessDelegation.delegAdmit` / `mandateSpec.diffCorpus`.
//!
//! The pinned vector here is the IDENTICAL literal the Lean
//! `#guard AppDiffPinned (mandateSpec demoGrant 50 77 5) [...]` pins. Drift on either side fails:
//!   * a Rust `deleg_admit` change ≠ this literal ⇒ this test FAILS;
//!   * a Lean `delegAdmit` change ⇒ the Lean `#guard` trips at `lake build` ⇒ forced re-pin.
//!
//! This is the anti-drift tooth that keeps the running Rust admission mirror == the proven Lean policy,
//! so the formal `tool_invocation_commit_iff_admit` / `tool_invocation_*_rejected` guarantees actually
//! describe what the deployed app enforces.

use starbridge_tool_access_delegation::{Grant, admit_table, deleg_admit, deleg_corpus};

/// The Lean `demoGrant`: tool 77, rate 3, deadline 100.
const DEMO: Grant = Grant {
    tool_id: 77,
    rate_limit: 3,
    deadline: 100,
};

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
    assert_eq!(
        deleg_corpus(&DEMO, 50, 77).as_slice(),
        &PINNED_CORPUS_IN_SCOPE_IN_TIME[..],
        "Rust deleg_corpus diverged from the Lean-pinned AppDiffPinned vector — \
         either the Rust mirror or the Lean delegAdmit drifted"
    );
}

#[test]
fn rate_tooth_bites() {
    // Lean `tool_invocation_over_rate_rejected` witness: the (N+1)-th invocation is rejected.
    assert!(deleg_admit(&DEMO, 50, 77, 2, 3)); // the 3rd (last legal) call
    assert!(!deleg_admit(&DEMO, 50, 77, 3, 4)); // the 4th — over the granted rate
}

#[test]
fn deadline_tooth_bites() {
    // Lean `tool_invocation_past_deadline_rejected`: now 101 > deadline 100 ⇒ EMPTY table.
    assert!(deleg_admit(&DEMO, 100, 77, 0, 1)); // exactly at the deadline still admits
    assert!(!deleg_admit(&DEMO, 101, 77, 0, 1)); // one past — rejected
    assert_eq!(admit_table(&DEMO, 101, 77).len(), 0);
}

#[test]
fn scope_tooth_bites() {
    // Lean `tool_invocation_out_of_scope_rejected`: tool 99 ≠ granted 77 ⇒ EMPTY table.
    assert!(deleg_admit(&DEMO, 50, 77, 0, 1)); // the granted tool admits
    assert!(!deleg_admit(&DEMO, 50, 99, 0, 1)); // a different tool — rejected
    assert_eq!(admit_table(&DEMO, 50, 99).len(), 0);
}

#[test]
fn corpus_is_non_vacuous() {
    // The corpus contains BOTH true and false (it is neither all-admit nor all-reject).
    let c = deleg_corpus(&DEMO, 50, 77);
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

/// Sweep a range of grants and confirm the Rust admission is exactly the folded policy on every cell —
/// the property the Lean `app_commit_iff_admit` proves over the whole grid (here checked by brute force
/// as the differential witness that the Rust mirror has no off-by-one against the Lean predicate).
#[test]
fn folded_policy_holds_over_grid_sweep() {
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
                            let expected = tool == g.tool_id
                                && now <= g.deadline
                                && new == old + 1
                                && 0 <= old
                                && new <= g.rate_limit;
                            assert_eq!(
                                deleg_admit(&g, now, tool, old, new),
                                expected,
                                "deleg_admit disagreed at g={g:?} now={now} tool={tool} {old}->{new}"
                            );
                        }
                    }
                }
            }
        }
    }
}
