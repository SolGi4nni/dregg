//! CWM ADVANCE ⟷ LEAN DIFFERENTIAL — the mirror-drift tooth for `cwm_advance_admits`.
//!
//! `src/lib.rs::cwm_advance_admits` is a HAND-PORT of the proven Lean `cwmAdvanceM`
//! (`metatheory/Dregg2/Apps/CompartmentWorkflowMandate/Core.lean`): DAG-prerequisite ∧
//! per-step compartment clearance ∧ cursor < terminal. A hand port can SILENTLY DRIFT — drop
//! the clearance leg (letting a clerk sign a document), admit past the terminal, or mis-order
//! the prerequisite check — and the proven `cwmAdvanceM` / `cwmAdvanceAdmits_iff` theorems
//! would never notice. That is the out-of-band seam this test kills.
//!
//! The Lean side emits a `#guard`-PINNED decision vector `cwmDiffCorpus` over a fixed grid of
//! `(mandate, cursor)`. This test enumerates the IDENTICAL grid through `cwm_advance_admits`
//! and asserts the SAME vector (`CWM_LEAN_DECISIONS`, copied from the Lean `#guard`). Drift on
//! EITHER side fails:
//!   * `cwm_advance_admits` changes  → Rust vector ≠ `CWM_LEAN_DECISIONS`           → FAIL here;
//!   * `cwmAdvanceM` changes          → its `#guard cwmDiffCorpus == [...]` trips at Lean build,
//!     forcing a re-pin that re-exposes any Rust drift.
//!
//! Grid (matches Lean `cwmDiffMandates × cwmDiffCursors`, row-major):
//!   mandates = [officer (clears review/redact/sign), clerk (clears ONLY review)]
//!   cursors  = [0, 1, 2, 3]   (charter terminal = 3)

use starbridge_compartment_workflow_mandate::{
    FieldElement, clerk_label, cwm_advance_admits, officer_label,
};

const CHARTER_TERMINAL: u64 = 3;

/// Officer carries the ROLE label `officer` — exactly the Lean `charterMandate3.actorLabels =
/// [Label.named "officer"]`. Its clearance over review/redact/sign is EARNED by walking the
/// `charter_clearance_graph` dominance edges (officer ⊐ review/redact/sign), NOT by feeding the
/// compartment labels back in and resolving them reflexively. Feeding compartment labels made the
/// graph a dead input: every row resolved `review ⊐ review` without traversing a single edge, so
/// zeroing the graph left the pinned vector unmoved. With the role label, the corpus traverses the
/// real graph and a dropped/over-permissive edge flips the vector.
fn officer_labels() -> Vec<FieldElement> {
    vec![officer_label()]
}

/// Clerk carries the ROLE label `clerk` — the Lean `clerkMandate3.actorLabels = [Label.named
/// "clerk"]`; it dominates ONLY `review` via the single `clerk → review` graph edge.
fn clerk_labels() -> Vec<FieldElement> {
    vec![clerk_label()]
}

const CURSORS: [u64; 4] = [0, 1, 2, 3];

/// The PINNED 8-row decision vector, copied VERBATIM from the Lean
/// `Dregg2.Apps.CompartmentWorkflowMandate.cwmDiffCorpus` `#guard`. Each entry is
/// `(admitted, new_cursor)`; `new_cursor = 0` on reject. Row-major over mandates × cursors.
#[rustfmt::skip]
const CWM_LEAN_DECISIONS: [(bool, u64); 8] = [
    // officer (clears review/redact/sign): linear DAG advances 0→1→2→3, then stops at terminal
    (true, 1), (true, 2), (true, 3), (false, 0),
    // clerk (clears ONLY review): step 0 admits; step 1 (redact) lacks clearance → stop
    (true, 1), (false, 0), (false, 0), (false, 0),
];

/// THE MIRROR-DRIFT TOOTH: the Rust `cwm_advance_admits` decision over the grid must equal the
/// Lean-pinned `cwmDiffCorpus` exactly.
#[test]
fn cwm_advance_admits_matches_lean_corpus() {
    let mandates: [Vec<FieldElement>; 2] = [officer_labels(), clerk_labels()];

    let mut rust: Vec<(bool, u64)> = Vec::with_capacity(8);
    for labels in &mandates {
        for &cursor in &CURSORS {
            match cwm_advance_admits(cursor, CHARTER_TERMINAL, labels) {
                // admitted: the cursor advances by exactly one step.
                Some(_phase) => rust.push((true, cursor + 1)),
                None => rust.push((false, 0)),
            }
        }
    }

    assert_eq!(
        rust.as_slice(),
        &CWM_LEAN_DECISIONS[..],
        "Rust cwm_advance_admits DRIFTED from the proven Lean cwmAdvanceM (cwmDiffCorpus). The \
         hand-ported workflow admission no longer matches the verified predicate — a \
         DAG-prerequisite or compartment-clearance guarantee may be broken (e.g. a clerk could \
         advance past their clearance). Reconcile lib.rs cwm_advance_admits with Core.lean \
         cwmAdvanceM."
    );
}

/// Spot tooth: a clerk (clears only `review`) MUST NOT be admitted to advance the `redact`
/// step (cursor 1) — the clearance leg is load-bearing.
#[test]
fn cwm_clerk_cannot_advance_past_clearance() {
    let labels = clerk_labels();
    assert!(
        cwm_advance_admits(0, CHARTER_TERMINAL, &labels).is_some(),
        "clerk should be admitted at review (cursor 0)"
    );
    assert!(
        cwm_advance_admits(1, CHARTER_TERMINAL, &labels).is_none(),
        "clerk lacks redact clearance and MUST be rejected at cursor 1"
    );
}

/// Spot tooth: advancing AT the terminal (cursor == terminal) is rejected — no overrun.
#[test]
fn cwm_no_advance_past_terminal() {
    let labels = officer_labels();
    assert!(
        cwm_advance_admits(CHARTER_TERMINAL, CHARTER_TERMINAL, &labels).is_none(),
        "advancing at the terminal cursor MUST be rejected"
    );
}
