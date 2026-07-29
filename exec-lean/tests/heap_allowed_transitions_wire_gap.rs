//! **The one thing about `HeapAtom::AllowedTransitions` that is NOT closed, measured.**
//!
//! `cell::HeapAtom::AllowedTransitions` is the deployed twin of the Lean-authored
//! `Dregg2.Games.Dungeon.Prog.HeapAtom.allowedTransitions` (the Descent's per-relic custody hop
//! table). `cell/tests/heap_allowed_transitions_lean_sourced.rs` drives both poles of the deployed
//! evaluator against the Lean rule. This file measures what that one cannot see from `dregg-cell`:
//! **the verified oracle does not decide this atom, and on a native RELEASE build that means the
//! Descent's custody teeth refuse.**
//!
//! # Why it declines, and why declining is the right answer
//!
//! The deployed constraint wire is authored on both sides — `encode_heap_atom` here,
//! `parseHeapAtom` in `metatheory/Dregg2/Exec/DeployedConstraint.lean`. That file's heap
//! vocabulary `DHeapAtom` has ELEVEN arms (equals / gte / lte / memberOf / inRange / immutable /
//! writeOnce / monotonic / strictMonotonic / deltaBounded / deltaEquals) — exactly `cell`'s
//! previous eleven — and no transition table. Its register-indexed `allowedTransitions` is not a
//! substitute: it answers `.badIndex` for any `idx ≥ stateSlots`, i.e. for every heap key.
//!
//! So there is no token the verified decider would read correctly, and minting one here would be a
//! Rust-authored constraint wearing a Lean tag — the exact laundering the oracle exists to prevent.
//! `None` routes to `ConstraintOracleUnavailable`, which is FAIL CLOSED: the correct disposition
//! for a Lean-subset constraint the verified evaluator did not decide.
//!
//! # What must happen when the Lean arm lands
//!
//! [`the_transition_table_atom_is_not_yet_on_the_deployed_wire`] GOES RED. That is deliberate: a
//! `DHeapAtom` arm plus its wire token turns the decline into a decision, and this test is the
//! thing that notices. Delete it then, and add the atom to
//! `constraint_oracle_differential.rs`'s corpus instead — where it will be held to both poles
//! against the Lean evaluator, which is where it belongs once Lean can answer.
//!
//! ⚑ A DECLINE IS NOT A REFUSAL AND THIS TEST DISTINGUISHES THEM. Asking the oracle and getting
//! `None` proves nothing on its own — an oracle that declined *everything* would look identical.
//! So every case here is paired with a sibling heap atom over the SAME key and the SAME states
//! that the oracle DOES answer.

use dregg_cell::program::{ConstraintOracle, HeapAtom, StateConstraint, TransitionMeta};
use dregg_cell::state::CellState;
use dregg_cell::{StateConstraint as SC, field_from_u64};
use dregg_exec_lean::LeanConstraintOracle;

/// `>= STATE_SLOTS(16)` ⇒ the `fields_map` tail: the heap plane, which is the whole point.
const RELIC_KEY: u64 = 20;

fn heap(v: u64) -> CellState {
    let mut s = CellState::default();
    s.set_field_ext(RELIC_KEY, field_from_u64(v));
    s
}

fn ask(c: &StateConstraint, new: &CellState, old: &CellState) -> Option<Result<(), ()>> {
    LeanConstraintOracle
        .admits(c, new, Some(old), None, &TransitionMeta::wildcard())
        .map(|r| r.map_err(|_| ()))
}

#[test]
fn the_transition_table_atom_is_not_yet_on_the_deployed_wire() {
    // Loud AND armable, exactly as the whole-corpus differential does it: without the export there
    // is no oracle to ask, and a silent `ok` would report "the gap is measured" having measured
    // nothing.
    if !dregg_lean_ffi::demand_lean(
        dregg_lean_ffi::constraint_admits_available(),
        "dregg_constraint_admits export (the heap transition-table wire-gap measurement)",
    ) {
        return;
    }

    let (new, old) = (heap(13), heap(8));

    // ── THE CONTROL. A sibling heap atom, same key, same two states: the oracle ANSWERS. Without
    // this, the decline below is indistinguishable from a dead oracle.
    let sibling = SC::HeapField {
        key: RELIC_KEY,
        atom: HeapAtom::MemberOf {
            set: vec![13, 14, 15, 16],
        },
    };
    assert_eq!(
        ask(&sibling, &new, &old),
        Some(Ok(())),
        "the verified oracle must decide an ordinary heap atom over this key, or this file is \
         measuring an absent oracle rather than an absent wire token"
    );
    // …and it decides, rather than rubber-stamping: the same atom over a value outside the set is
    // a real refusal from the same source.
    assert_eq!(
        ask(&sibling, &heap(99), &old),
        Some(Err(())),
        "the control must be able to answer NO, or `Some(Ok(()))` above is not evidence"
    );

    // ── THE GAP. The transition table over the SAME key and the SAME states: no answer at all.
    let table = SC::HeapField {
        key: RELIC_KEY,
        atom: HeapAtom::AllowedTransitions {
            allowed: vec![(8, 13), (8, 14), (8, 15), (8, 16)],
        },
    };
    assert_eq!(
        ask(&table, &new, &old),
        None,
        "⚑ THE LEAN ARM HAS LANDED — `DHeapAtom` can now carry a transition table, so this decline \
         is stale. Delete this test and add the atom to `constraint_oracle_differential.rs`'s \
         corpus, where both poles are held against the Lean evaluator."
    );
    // An honest hop and a forbidden one decline IDENTICALLY: the oracle is not half-deciding.
    assert_eq!(ask(&table, &heap(99), &old), None);
}
