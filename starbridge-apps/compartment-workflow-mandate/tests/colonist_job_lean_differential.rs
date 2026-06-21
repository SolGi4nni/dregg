//! COLONIST-JOB ⟷ LEAN DIFFERENTIAL — the mirror-drift tooth for `job_advance_admits`.
//!
//! `src/colonist_job.rs::job_advance_admits` is a HAND-PORT of the proven Lean `jobAdvanceAdmits`
//! (`metatheory/Dregg2/Apps/ColonistJob.lean`): DAG-prerequisite ∧ per-verb clearance ∧ in-budget.
//! A hand port can SILENTLY DRIFT — drop the budget leg (letting an overspend through), drop the
//! clearance leg (letting a hauler craft) — and the proven `job_*` theorems would never notice.
//! That is the out-of-band seam this test kills.
//!
//! The Lean side emits a `#guard`-PINNED decision vector `jobDiffCorpus` over the grid of three job
//! specs × cursors `{0,1,2,3}` (row-major). This test enumerates the IDENTICAL grid through
//! `job_advance_admits` (= `job_diff_corpus`) and asserts the SAME vector. Drift on EITHER side
//! fails:
//!   * `job_advance_admits` changes → Rust vector ≠ `JOB_LEAN_DECISIONS` → FAIL here;
//!   * `jobAdvanceAdmits` changes    → its `#guard jobDiffCorpus == [...]` trips at Lean build,
//!     forcing a re-pin that re-exposes any Rust drift.
//!
//! Grid (matches Lean `jobDiffSpecs × jobDiffCursors`, row-major):
//!   specs = [(crafter, full budget 9), (hauler, full budget 9), (crafter, tight budget 6)]
//!   cursors = [0, 1, 2, 3]   (job terminal = 3)

use starbridge_compartment_workflow_mandate::colonist_job::job_diff_corpus;

/// The PINNED 12-entry decision vector, copied VERBATIM from the Lean
/// `Dregg2.Apps.ColonistJob.jobDiffCorpus` `#guard`. Row-major over specs × cursors.
#[rustfmt::skip]
const JOB_LEAN_DECISIONS: [bool; 12] = [
    // crafterFull: gather✓ make✓ handoff✓ then terminal✗
    true,  true,  true,  false,
    // haulerFull: gather✓ make✗(no make-clearance) handoff✓(hauler clears it) terminal✗
    true,  false, true,  false,
    // crafterTight(6): gather✓ make✗(overspend 7>6) handoff✗(overspend, cumulative 9>6) terminal✗
    true,  false, false, false,
];

/// THE MIRROR-DRIFT TOOTH: the Rust `job_advance_admits` decision over the grid must equal the
/// Lean-pinned `jobDiffCorpus` exactly.
#[test]
fn job_advance_admits_matches_lean_corpus() {
    assert_eq!(
        job_diff_corpus().as_slice(),
        &JOB_LEAN_DECISIONS[..],
        "Rust job_advance_admits DRIFTED from the proven Lean jobAdvanceAdmits (jobDiffCorpus). The \
         hand-ported colonist-job admission no longer matches the verified predicate — a \
         DAG-prerequisite, clearance, or SPEND-BUDGET guarantee may be broken (e.g. a hauler could \
         craft, or an overspend could slip through). Reconcile colonist_job.rs job_advance_admits \
         with ColonistJob.lean jobAdvanceAdmits."
    );
}

/// Non-vacuity: the pinned corpus carries BOTH polarities, so the pin constrains the mirror (it is
/// not a tautology any vector satisfies).
#[test]
fn corpus_is_both_polarity() {
    assert!(JOB_LEAN_DECISIONS.contains(&true), "has a genuine-admit witness");
    assert!(JOB_LEAN_DECISIONS.contains(&false), "has a cheat-reject witness");
    assert_eq!(JOB_LEAN_DECISIONS.len(), 12, "3 specs × 4 cursors");
}
