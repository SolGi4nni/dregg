//! **THE COUNCIL-VOTE POLES, AGAINST THE REAL LEAN ORACLE.**
//!
//! `collective-choice`'s poll program carries the SOUND QUORUM GATE
//! `AnyOf[Immutable{RESOLVED}, CountGe{min_distinct, VOTER_SET_COMMITMENT}]` — the `CountGe` mint that
//! retires the `AffineLe`-over-`Monotonic` quorum forgery. `CountGe` is class-c on BOTH sides:
//! `constraint_oracle::lift_simple` declines it by name, and `Dregg2.Exec.DeployedConstraint` has no
//! `countGe` branch atom AT ALL (the marshalled `DCtx` is four typed context fields and carries no
//! witness blob, so the set-exhibit `Cleartext` commitment cannot cross the wire — it is one of the
//! eleven, by name, in that module's own class list). `encode_branches` therefore declines the WHOLE
//! combinator rather than half-routing it.
//!
//! `cell/src/program/eval.rs::constraint_in_lean_subset` did not recurse into branches, so it
//! claimed every `AnyOf` for the Lean subset. A declined subset constraint FAILS CLOSED — correctly,
//! that gate exists to stop an out-of-envelope `AffineLe` reaching the wrapping Rust accumulator — so
//! a node with the oracle installed answered `ProgramError::ConstraintOracleUnavailable` to EVERY
//! ballot cast against a poll cell. The DreggNet Council opened proposals (its own cell program is
//! `Monotonic` + `WriteOnce`, all Lean-routed, through the SAME oracle) and could not vote on them.
//!
//! Both poles, on the REAL `LeanConstraintOracle` and the REAL `CellProgram::evaluate`:
//!
//! * **LANDS** — a ballot leaves `RESOLVED` untouched, so the gate's cheap branch holds and the turn
//!   is admitted. RED before the fix (`ConstraintOracleUnavailable`).
//! * **STILL REFUSES** — arming `RESOLVED` with no exhibited distinct-voter set closes both branches
//!   and the turn is refused. Falling through to the trusted-Rust slot is a CLASSIFICATION, not a
//!   permissive fallback; if this pole ever reads `Ok` the quorum gate has stopped biting.
//!
//! And the DRIFT GUARD the original defect needed: the two classifications — `admits` returning
//! `None` and `constraint_in_lean_subset` answering `false` — must AGREE about this shape, which is
//! the invariant nothing checked when the mirror was written by hand in another crate.

use dregg_cell::program::{
    CellProgram, ConstraintOracle, SimpleStateConstraint, TransitionMeta,
    constraint_in_lean_subset, constraint_oracle_installed,
};
use dregg_cell::state::CellState;
use dregg_cell::{StateConstraint, field_from_u64};
use dregg_exec_lean::{LeanConstraintOracle, register_constraint_oracle};

/// `collective_choice::RESOLVED_SLOT`. Restated rather than imported: `dregg-exec-lean` sits far
/// below `collective-choice`, and what this file pins is the CLASS of the combinator, not the poll's
/// slot map.
const RESOLVED_SLOT: u8 = 7;
/// `collective_choice::VOTER_SET_COMMITMENT_SLOT`.
const VOTER_SET_COMMITMENT_SLOT: u8 = 1;
/// A tally slot the ballot bumps (`collective_choice::TALLY_BASE`).
const TALLY_SLOT: u8 = 8;

/// The exact shape `collective_choice::VoteEngine::poll_program` installs.
fn poll_quorum_gate() -> StateConstraint {
    StateConstraint::AnyOf {
        variants: vec![
            SimpleStateConstraint::Immutable {
                index: RESOLVED_SLOT,
            },
            SimpleStateConstraint::CountGe {
                threshold: 2,
                set_commitment_slot: VOTER_SET_COMMITMENT_SLOT,
            },
        ],
    }
}

/// Install once for this binary. Both exits are LOUD and armed by `DREGG_TEST_REQUIRE_LEAN=1` — a
/// `#[test]` that returns early on a missing precondition is indistinguishable from one that ran and
/// passed, which is how five reality gates once self-skipped to green for four days.
fn ensure_oracle() -> bool {
    if !dregg_lean_ffi::demand_lean(
        dregg_lean_ffi::constraint_admits_available(),
        "dregg_constraint_admits export (the council-vote combinator poles)",
    ) {
        return false;
    }
    let _ = register_constraint_oracle();
    dregg_lean_ffi::demand_lean(
        constraint_oracle_installed(),
        "installed constraint oracle (register_constraint_oracle ran but \
         dregg_cell::program::constraint_oracle_installed() is still false)",
    )
}

/// A ballot's `(old, new)`: `RESOLVED` untouched, one tally slot bumped.
fn ballot_states() -> (CellState, CellState) {
    let mut old = CellState::default();
    old.fields[RESOLVED_SLOT as usize] = field_from_u64(0);
    let mut new = old.clone();
    new.fields[TALLY_SLOT as usize] = field_from_u64(1);
    (old, new)
}

#[test]
fn a_ballot_lands_through_the_quorum_gates_cheap_branch() {
    if !ensure_oracle() {
        return;
    }
    let (old, new) = ballot_states();
    let program = CellProgram::Predicate(vec![poll_quorum_gate()]);

    let result = program.evaluate(&new, Some(&old), None);

    assert!(
        result.is_ok(),
        "a ballot that leaves RESOLVED untouched satisfies the quorum gate's cheap branch and must \
         LAND — this is the council vote the live surface refused; got {result:?}"
    );
}

#[test]
fn arming_resolved_with_no_exhibited_voter_set_is_still_refused() {
    if !ensure_oracle() {
        return;
    }
    let (old, _) = ballot_states();
    let mut forged = old.clone();
    // THE FORGERY: flip RESOLVED (closing the `Immutable` branch) without exhibiting a set of
    // distinct voters that opens the commitment slot.
    forged.fields[RESOLVED_SLOT as usize] = field_from_u64(1);
    let program = CellProgram::Predicate(vec![poll_quorum_gate()]);

    let result = program.evaluate(&forged, Some(&old), None);

    assert!(
        result.is_err(),
        "arming RESOLVED with no exhibited distinct-voter set must be REFUSED: routing the \
         combinator to the trusted-Rust slot classifies it, it does not wave it through; \
         got {result:?}"
    );
}

/// ⚑ **THE DRIFT GUARD.** `constraint_in_lean_subset` (in `dregg-cell`) is a hand-written mirror of
/// `encode_constraint`/`lift_simple` (in this crate), and nothing compared them — which is exactly
/// how the outage got in. The invariant, stated over the real oracle:
///
/// * a constraint the oracle DECIDES must be in the Lean subset (else a Lean-decided answer would be
///   classified as trusted-Rust — harmless here, but the mirror would be lying);
/// * a constraint the mirror calls NOT-subset must be one the oracle declines (else a class-c
///   classification would swallow a Lean decision).
///
/// The two directions together are `admits.is_some() == subset` for everything except the named
/// ENVELOPE declines, which are subset constraints the WIRE cannot carry and must keep failing
/// closed. Those are listed here BY SHAPE, so a new envelope decline has to be added deliberately.
#[test]
fn the_subset_mirror_agrees_with_the_marshallers_own_routing() {
    if !dregg_lean_ffi::demand_lean(
        dregg_lean_ffi::constraint_admits_available(),
        "dregg_constraint_admits export (the subset-mirror drift guard)",
    ) {
        return;
    }
    let oracle = LeanConstraintOracle;
    let (old, new) = ballot_states();
    let meta = TransitionMeta::wildcard();

    // (shape, is an ENVELOPE decline — a Lean-subset constraint the wire cannot carry)
    let shapes: Vec<(StateConstraint, bool)> = vec![
        // The council's quorum gate: a CLASS decline. Mirror must say NOT-subset.
        (poll_quorum_gate(), false),
        // A combinator whose every branch is Lean-routable: decided, and subset.
        (
            StateConstraint::AnyOf {
                variants: vec![
                    SimpleStateConstraint::Immutable {
                        index: RESOLVED_SLOT,
                    },
                    SimpleStateConstraint::SenderIs { pk: [3u8; 32] },
                ],
            },
            false,
        ),
        // `AllOf` over the same class-c atom, under a `Not`: parity is peeled, the class does not
        // change.
        (
            StateConstraint::AllOf {
                variants: vec![SimpleStateConstraint::Not(Box::new(
                    SimpleStateConstraint::CountGe {
                        threshold: 1,
                        set_commitment_slot: VOTER_SET_COMMITMENT_SLOT,
                    },
                ))],
            },
            false,
        ),
        // A plain pure arm: decided, subset.
        (
            StateConstraint::Immutable {
                index: RESOLVED_SLOT,
            },
            false,
        ),
        // A combinator with a SINGLE-KEY `HeapField` branch: DECIDED, and subset.
        //
        // ⚑ This entry used to sit below among the envelope declines, with `key: 4096` and the note
        // "the wire header carries one heap key pair". The header does — and the verified evaluator
        // reads exactly that pair for a `.heapField` branch (`parseConstraint` falls through to
        // `parseHeapAtom`; `branchAdmits` → `heapAdmits atom i.heapOld i.heapNew`), so ONE key is
        // faithfully carried and the decline was the marshaller not asking. `dungeon_program.json`
        // emits 576 of these and every Descent verb touched one, so the decline refused the whole
        // game (HORIZONLOG E2). `combinator_heap_key` now resolves the branches' key into the header.
        (
            StateConstraint::AnyOf {
                variants: vec![
                    SimpleStateConstraint::HeapField {
                        key: 4096,
                        atom: dregg_cell::program::HeapAtom::Immutable,
                    },
                    SimpleStateConstraint::SenderIs { pk: [3u8; 32] },
                ],
            },
            false,
        ),
        // ⚠ THE ENVELOPE DECLINES — subset atoms the WIRE cannot carry. `admits` is `None` and the
        // mirror still says SUBSET, so they fail closed. That asymmetry is deliberate; it is the
        // whole reason the mirror exists.
        //
        // The heap one is now the MULTI-KEY combinator, and it is a genuine wire limit rather than a
        // missing Rust case: `DInput` carries ONE `(heapOld, heapNew)` pair, so encoding two keys
        // would evaluate branch 2 against branch 1's cell — silently wrong in both directions.
        // Carrying it needs a per-branch cell run in `Dregg2.Exec.DeployedConstraint`'s
        // `DInput`/`parseBranches`, i.e. a LEAN change; nothing deployed emits this shape (measured
        // 2026-07-30: every heap-bearing combinator in `dungeon_program.json` names one key).
        (
            StateConstraint::AnyOf {
                variants: vec![
                    SimpleStateConstraint::HeapField {
                        key: 4096,
                        atom: dregg_cell::program::HeapAtom::Immutable,
                    },
                    SimpleStateConstraint::HeapField {
                        key: 4097,
                        atom: dregg_cell::program::HeapAtom::Immutable,
                    },
                ],
            },
            true,
        ),
        (
            StateConstraint::AffineLe {
                terms: vec![(i64::MAX, 0), (i64::MAX, 1)],
                c: 0,
            },
            true,
        ),
    ];

    let mut decided = 0usize;
    let mut class_declined = 0usize;
    for (shape, envelope) in &shapes {
        let admits = oracle
            .admits(shape, &new, Some(&old), None, &meta)
            .is_some();
        let subset = constraint_in_lean_subset(shape);
        if admits {
            decided += 1;
            assert!(
                subset,
                "the oracle DECIDED {shape:?} but the mirror calls it trusted-Rust — the mirror is \
                 lying about what Lean answers"
            );
        } else if *envelope {
            assert!(
                subset,
                "{shape:?} is an ENVELOPE decline (a Lean-subset constraint the wire cannot carry) \
                 and must stay subset ⇒ fail closed, never fall through to the unverified twin"
            );
        } else {
            class_declined += 1;
            assert!(
                !subset,
                "the oracle declines {shape:?} for its CLASS (a class-c branch atom the deployed \
                 wire has no encoding for), so the mirror must classify it as trusted-Rust — \
                 calling it subset refuses an honest turn forever"
            );
        }
    }

    // Anti-vacuity: the table must actually contain both kinds, or the guard proves nothing.
    assert!(
        decided >= 2,
        "the drift guard exercised no Lean-decided shapes ({decided}) — it would pass vacuously"
    );
    assert!(
        class_declined >= 2,
        "the drift guard exercised no CLASS-declined shapes ({class_declined}) — the very case the \
         council outage was"
    );
}
