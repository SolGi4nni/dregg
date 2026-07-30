//! **`HeapAtom::AllowedTransitions` — the deployed twin of a LEAN-AUTHORED atom, both poles, plus
//! the one thing about it that is NOT closed.**
//!
//! # Substrate: Lean authors this rule; Rust follows it
//!
//! The author is `metatheory/Dregg2/Games/DungeonProgram.lean`'s
//! `Dregg2.Games.Dungeon.Prog.HeapAtom.allowedTransitions`, added in `b15c958fe` because a relic's
//! custody code is HEAP-resident (the descent schema declares each `relic_*` a `.collection(..)`),
//! so the per-relic hop table had been written as a tooth about a register with no slot. Its
//! meaning is fixed by that file's `HeapAtom.toExec`:
//!
//! ```text
//! | .allowedTransitions al => .allowedTransitions k.field (…)
//! ```
//!
//! — the EXISTING name-keyed `Dregg2.Exec.StateConstraint.allowedTransitions` at the heap key's
//! field name, whose evaluator (`Dregg2/Exec/Program.lean`) is
//!
//! ```text
//! | .allowedTransitions f allowed, old, new =>
//!     match old.scalar f, new.scalar f with
//!     | some a, some b => allowed.any (fun p => p.1 == a && p.2 == b)
//!     | _, _ => false
//! ```
//!
//! Every case below is that rule read off that text. Nothing here is a new rule, and this file is
//! not a proof of anything: it is a correspondence check on cases, which is what a Rust test can
//! be. The theorem content lives in Lean.
//!
//! # Why this file exists at all
//!
//! Measured 2026-07-29: `dungeon-on-dregg/program/dungeon_program.json` — a CACHE of that Lean
//! emission — had carried `{"kind":"allowedTransitions"}` heap atoms since the day it was
//! re-emitted, and the Rust loader's `SymAtom` had five arms and did not know it. So
//! `serde_json::from_str` failed and `descent.rs`'s `family()` PANICKED at load, in every build:
//!
//! ```text
//! dungeon_program.json (Lean-emitted) parses: Error("unknown variant `allowedTransitions`,
//!   expected one of `equals`, `immutable`, `monotonic`, `memberOf`, `deltaEquals`")
//! ```
//!
//! Ten of the Discord bot's nineteen reds were that one line. Rust was behind; Lean was right.

use dregg_cell::program::{
    CellProgram, HashKind, HeapAtom, StateConstraint, constraint_in_lean_subset,
};
use dregg_cell::state::CellState;
use dregg_cell::{StateConstraint as SC, field_from_u64};

/// `>= STATE_SLOTS(16)` ⇒ the unbounded `fields_map` tail, i.e. genuinely the heap plane and not a
/// register wearing a key. That distinction is the whole reason this atom had to exist:
/// `StateConstraint::AllowedTransitions` takes a `slot_index: u8` and reads `fields[idx]`.
const RELIC_KEY: u64 = 20;

fn heap(v: u64) -> CellState {
    let mut s = CellState::default();
    s.set_field_ext(RELIC_KEY, field_from_u64(v));
    s
}

/// The descent's own day-0 table for `relic_1` (`custodyHops 1` in the Lean source): CARRIED(8) may
/// become any of the four hung-in-a-door codes, and nothing else.
fn custody_hops() -> StateConstraint {
    SC::HeapField {
        key: RELIC_KEY,
        atom: HeapAtom::AllowedTransitions {
            allowed: vec![(8, 13), (8, 14), (8, 15), (8, 16)],
        },
    }
}

fn decide(c: &StateConstraint, new: &CellState, old: Option<&CellState>) -> bool {
    CellProgram::Predicate(vec![c.clone()])
        .evaluate(new, old, None)
        .is_ok()
}

#[test]
fn a_listed_hop_is_admitted_and_an_unlisted_one_is_refused() {
    let c = custody_hops();

    // ── ADMIT: every listed pair, so the table is read as a table and not as one lucky row.
    for to in [13u64, 14, 15, 16] {
        assert!(
            decide(&c, &heap(to), Some(&heap(8))),
            "the Lean-emitted custody table lists 8 -> {to}; the deployed evaluator must admit it"
        );
    }

    // ── REFUSE: the same destinations from the WRONG origin. This is the half that makes the atom
    // relational — a `memberOf` over {13,14,15,16} would admit every one of these, and a relic that
    // was banked or in the pack could hang itself in a door.
    for to in [13u64, 14, 15, 16] {
        assert!(
            !decide(&c, &heap(to), Some(&heap(9))),
            "9 -> {to} is not in the table; admitting it would make the atom a value allowlist"
        );
    }

    // ── REFUSE: a listed origin to an unlisted destination.
    assert!(
        !decide(&c, &heap(17), Some(&heap(8))),
        "8 -> 17 is not a listed hop"
    );

    // ── REFUSE: the identity hop nobody listed. A table that quietly admits "no change" would let
    // a guarded turn satisfy the tooth by doing nothing.
    assert!(
        !decide(&c, &heap(8), Some(&heap(8))),
        "8 -> 8 is not listed, so it is not admitted"
    );
}

#[test]
fn an_absent_key_on_either_side_refuses_with_no_genesis_escape() {
    let c = custody_hops();
    let empty = CellState::default();

    // Lean's `| _, _ => false`: BOTH `old.scalar f` and `new.scalar f` must be `some`. The
    // register-indexed twin reads FIELD_ZERO for an absent old, because a register always exists
    // once the state does — a heap key legitimately does not, so there is no such default here.
    assert!(
        !decide(&c, &heap(13), None),
        "no old state at all: absent old must refuse, not read as 0"
    );
    assert!(
        !decide(&c, &heap(13), Some(&empty)),
        "an old state without the key must refuse"
    );
    assert!(
        !decide(&c, &empty, Some(&heap(8))),
        "an erased post-state key must refuse (no erasure escape)"
    );

    // The refusal is NOT vacuous — the same shapes with the key present on both sides admit.
    assert!(
        decide(&c, &heap(13), Some(&heap(8))),
        "the instrument is not simply saying no"
    );

    // ⚑ AND THE ZERO CASE, WHICH IS THE ONE A FIELD_ZERO DEFAULT WOULD HIDE. A table that DOES
    // list `0 -> 13` must still refuse an absent old, or "absent" has silently become "present
    // zero" and a relic could be conjured into a door out of a key that was never minted.
    let from_zero = SC::HeapField {
        key: RELIC_KEY,
        atom: HeapAtom::AllowedTransitions {
            allowed: vec![(0, 13)],
        },
    };
    assert!(
        decide(&from_zero, &heap(13), Some(&heap(0))),
        "present-zero old is a real 0 and the listed hop admits"
    );
    assert!(
        !decide(&from_zero, &heap(13), None),
        "absent old must NOT be read as the listed 0 — this is the escape the Lean `_ , _ => false` \
         closes, and the assertion above proves the test can tell the two apart"
    );
}

#[test]
fn an_empty_table_is_the_canonical_bottom() {
    // The `Simple` position has no relational form on either substrate, so Lean's
    // `HeapAtom.toExecSimple` lowers a transition table to `memberOf f []` — `new ∈ ∅`. The
    // top-level form's empty table has to be the same bottom, or "fail closed" would depend on
    // which of the two lowerings a tooth happened to take.
    let bottom = SC::HeapField {
        key: RELIC_KEY,
        atom: HeapAtom::AllowedTransitions { allowed: vec![] },
    };
    assert!(!decide(&bottom, &heap(13), Some(&heap(8))));
    assert!(!decide(&bottom, &heap(8), Some(&heap(8))));
    assert!(!decide(&bottom, &CellState::default(), None));
}

/// ⚠ **THE MEASURED GAP — HALF CLOSED. THE REMAINING HALF, NOT A COMMENT ABOUT ONE.**
///
/// This atom answers `true` to [`constraint_in_lean_subset`] — it IS a pure state/heap rule, so a
/// native RELEASE build routes it to the verified `dregg_constraint_admits` and FAILS CLOSED if the
/// oracle does not decide it. The LEAN SIDE now does: `Dregg2/Exec/DeployedConstraint.lean`'s
/// `DHeapAtom` carries a twelfth arm, `allowedTransitions (allowed : List (Nat × Nat))` (u64 lane,
/// both sides present, no genesis escape), with a `HAT` wire token in `parseHeapAtom` and a PROVED
/// encode/decode round-trip over every `allowed` list (not an example corpus). Its register-indexed
/// sibling `allowedTransitions` still answers `.badIndex` for any `idx ≥ stateSlots` — it was never
/// a substitute — but the heap arm is real now.
///
/// `dregg-exec-lean`'s `encode_heap_atom` gained the matching `HAT` arm in `6e27f4983`, so the
/// oracle is ASKED now and this atom is decided by the verified evaluator on the deployed path —
/// pinned end-to-end in `exec-lean/tests/heap_allowed_transitions_wire_gap.rs`.
///
/// ⚠ **AND THE ATOM ENCODING WAS NOT ENOUGH TO LIFT THE OUTAGE**, which is the durable lesson of
/// this file. The Descent's custody teeth sit on the same `SlotChanged{spent}` rider as 24 `AnyOf`s
/// over `HeapField` branches, and `encode_branches` declined THOSE — so with `HAT` landed, every
/// verb still refused. Both halves were found by INSPECTION, one guess per round. The measurement
/// that names all of them at once is `dreggnet-web/tests/deployed_program_oracle_decidable.rs`,
/// which walks the real emitted program through the real marshaller; prefer extending it to
/// guessing at a third arm.
///
/// This test pins the SUBSET half from `dregg-cell` (which cannot see the encoder): the atom is
/// Lean's territory, so a decline must FAIL CLOSED rather than reach the unverified twin.
#[test]
fn the_atom_is_in_the_lean_subset_so_a_release_build_needs_an_oracle_that_decides_it() {
    assert!(
        constraint_in_lean_subset(&custody_hops()),
        "a pure heap rule is Lean-decided territory: if this ever answers false, the atom has been \
         quietly moved into the trusted-Rust slot, which is a soundness posture change and not a \
         wiring detail"
    );
    // The negative control — the classifier is not simply saying yes to everything.
    assert!(
        !constraint_in_lean_subset(&SC::PreimageGate {
            commitment_index: 0,
            hash_kind: HashKind::Blake3,
        }),
        "the instrument must be able to answer false"
    );
}
