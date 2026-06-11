//! Integration differential for the **policy-combinator core** —
//! `MemberOf` / `PrefixOf` / `InRangeTwoSided` / `DeltaBounded` / `AffineLe` /
//! `AffineEq` / `Reachable` / `AllOf` — the Rust mirror of the verified Lean
//! atom set (`metatheory/Dregg2/Exec/Program.lean`).
//!
//! Each test is the admit/reject NON-VACUITY pair that the Lean side proves by
//! `#guard`/`by decide` (`roleProgram`, `nsProgram`, `priceProgram`,
//! `jitterProgram`, `bandProgram`, `consvProgram`, `workflowProgram`). Running
//! them here through the full `CellProgram::evaluate` → `evaluate_constraint_full`
//! dispatch is the executable Rust↔Lean differential: the two transcriptions of
//! the same atom semantics must AGREE on admit AND reject.
//!
//! (An integration target — it links only the crate's public API, so it is
//! independent of any in-crate `#[cfg(test)]` module.)

use dregg_cell::{
    CellProgram, CellState, StateConstraint,
    program::{SimpleStateConstraint, field_from_u64},
};

/// `MemberOf` — Lean `roleProgram`: role ∈ {1,2,3}.
#[test]
fn member_of_differential() {
    let p = CellProgram::Predicate(vec![StateConstraint::MemberOf {
        index: 0,
        set: vec![1, 2, 3],
    }]);
    let mut s = CellState::new(0);
    s.fields[0] = field_from_u64(2);
    assert!(p.evaluate(&s, None, None).is_ok(), "2 ∈ set ⇒ admit");
    s.fields[0] = field_from_u64(9);
    assert!(p.evaluate(&s, None, None).is_err(), "9 ∉ set ⇒ reject");
}

/// `PrefixOf` — Lean `nsProgram`: path must start with [10,20]; fail-closed when shorter.
#[test]
fn prefix_of_differential() {
    let p = CellProgram::Predicate(vec![StateConstraint::PrefixOf {
        seg_indices: vec![0, 1, 2],
        prefix: vec![10, 20],
    }]);
    let mut s = CellState::new(0);
    s.fields[0] = field_from_u64(10);
    s.fields[1] = field_from_u64(20);
    s.fields[2] = field_from_u64(7);
    assert!(
        p.evaluate(&s, None, None).is_ok(),
        "[10,20,7] starts with [10,20]"
    );
    s.fields[1] = field_from_u64(99);
    assert!(p.evaluate(&s, None, None).is_err(), "[10,99,7] ⇏ prefix");

    let p_short = CellProgram::Predicate(vec![StateConstraint::PrefixOf {
        seg_indices: vec![0],
        prefix: vec![10, 20],
    }]);
    assert!(
        p_short.evaluate(&s, None, None).is_err(),
        "path shorter than prefix ⇒ fail-closed"
    );
}

/// `InRangeTwoSided` — Lean `priceProgram`: 100 ≤ price ≤ 200.
#[test]
fn in_range_two_sided_differential() {
    let p = CellProgram::Predicate(vec![StateConstraint::InRangeTwoSided {
        index: 0,
        lo: 100,
        hi: 200,
    }]);
    let mut s = CellState::new(0);
    s.fields[0] = field_from_u64(150);
    assert!(p.evaluate(&s, None, None).is_ok());
    s.fields[0] = field_from_u64(250);
    assert!(p.evaluate(&s, None, None).is_err(), "250 > 200 ⇒ reject");
}

/// `DeltaBounded` — Lean `jitterProgram`: |new − old| ≤ 5 (REAL two-sided).
#[test]
fn delta_bounded_differential() {
    let p = CellProgram::Predicate(vec![StateConstraint::DeltaBounded { index: 0, d: 5 }]);
    let mut old = CellState::new(1);
    old.fields[0] = field_from_u64(100);
    let mut new_s = CellState::new(2);
    for (v, ok) in [(104u64, true), (96, true), (110, false), (90, false)] {
        new_s.fields[0] = field_from_u64(v);
        assert_eq!(
            p.evaluate(&new_s, Some(&old), None).is_ok(),
            ok,
            "delta to {v} (from 100) admit={ok}"
        );
    }
}

/// `AffineLe` — Lean `bandProgram`: 2·bid − ask ≤ 100.
#[test]
fn affine_le_differential() {
    let p = CellProgram::Predicate(vec![StateConstraint::AffineLe {
        terms: vec![(2, 0), (-1, 1)],
        c: 100,
    }]);
    let mut s = CellState::new(0);
    s.fields[0] = field_from_u64(60);
    s.fields[1] = field_from_u64(40); // 120−40 = 80 ≤ 100
    assert!(p.evaluate(&s, None, None).is_ok());
    s.fields[0] = field_from_u64(90); // 180−40 = 140 > 100
    assert!(p.evaluate(&s, None, None).is_err());
}

/// `AffineEq` — Lean `consvProgram`: inp − o0 − o1 = 0 (conservation).
#[test]
fn affine_eq_differential() {
    let p = CellProgram::Predicate(vec![StateConstraint::AffineEq {
        terms: vec![(1, 0), (-1, 1), (-1, 2)],
        c: 0,
    }]);
    let mut s = CellState::new(0);
    s.fields[0] = field_from_u64(10);
    s.fields[1] = field_from_u64(6);
    s.fields[2] = field_from_u64(4); // 10−6−4 = 0
    assert!(p.evaluate(&s, None, None).is_ok());
    s.fields[2] = field_from_u64(3); // 10−6−3 = 1 ≠ 0
    assert!(p.evaluate(&s, None, None).is_err());
}

/// `Reachable` — Lean `workflowProgram`: step must reach prerequisite 1 in DAG 3→2→1.
#[test]
fn reachable_differential() {
    let p = CellProgram::Predicate(vec![StateConstraint::Reachable {
        from_index: 0,
        to_label: 1,
        edges: vec![(3, 2), (2, 1)],
    }]);
    let mut s = CellState::new(0);
    s.fields[0] = field_from_u64(3); // publish reaches drafted (3→2→1)
    assert!(p.evaluate(&s, None, None).is_ok());
    s.fields[0] = field_from_u64(4); // 4 ∉ DAG ⇒ unreachable
    assert!(p.evaluate(&s, None, None).is_err());
}

/// `AllOf` — the n-ary Boolean conjunction (mirrors Lean `Pred.allOf`): 10 ≤ v ≤ 20.
/// Empty `AllOf` admits (mirrors `Pred.allOf_nil_admits`).
#[test]
fn all_of_differential() {
    let p = CellProgram::Predicate(vec![StateConstraint::AllOf {
        variants: vec![
            SimpleStateConstraint::FieldGte {
                index: 0,
                value: field_from_u64(10),
            },
            SimpleStateConstraint::FieldLte {
                index: 0,
                value: field_from_u64(20),
            },
        ],
    }]);
    let mut s = CellState::new(0);
    s.fields[0] = field_from_u64(15);
    assert!(p.evaluate(&s, None, None).is_ok());
    s.fields[0] = field_from_u64(25);
    assert!(
        p.evaluate(&s, None, None).is_err(),
        "25 > 20 ⇒ second conjunct fails"
    );

    let p_empty = CellProgram::Predicate(vec![StateConstraint::AllOf { variants: vec![] }]);
    assert!(
        p_empty.evaluate(&s, None, None).is_ok(),
        "empty AllOf admits (vacuous AND)"
    );
}

// ───────────────────────────────────────────────────────────────────────────
// FieldLteOther — the RECORD-LEVEL relational caveat (cross-slot
// `new[index] <= new[other] + delta`). The Rust mirror of the verified Lean
// atom `Dregg2.Exec.RelationalCaveat.RelCaveat.fieldLteOther`. Exercised THROUGH
// the live `CellProgram::evaluate` → `evaluate_constraint_full` dispatch — the
// actual executor enforcement path, not a standalone re-implementation.
// ───────────────────────────────────────────────────────────────────────────

// Queue cell slot layout (mirrors Lean `rq0` / the `relational_caveat.rs`
// harness): head_seq, tail_seq, capacity.
const Q_HEAD: usize = 0;
const Q_TAIL: usize = 1;
const Q_CAP: usize = 2;

/// `FieldLteOther` enforces a queue's CAPACITY bound through the live program
/// evaluator: a factory cell carrying `head <= cap` admits an in-bound write
/// and rejects an over-bound one. Mirrors Lean `relStateStepGuarded_capacity_enforced`
/// + the `rq0` #guard (iii)/(iv).
#[test]
fn field_lte_other_capacity_live_path() {
    // A factory-style queue cell program: head_seq must stay <= capacity.
    // (`delta = 0` folds the committed `tail = 0`, so the bound is head <= cap.)
    let p = CellProgram::Predicate(vec![StateConstraint::FieldLteOther {
        index: Q_HEAD as u8,
        other: Q_CAP as u8,
        delta: 0,
    }]);

    // In-bound post-state: head 2, cap 2 (occupancy = capacity) ⇒ admits.
    let mut in_bound = CellState::new(0);
    in_bound.fields[Q_HEAD] = field_from_u64(2);
    in_bound.fields[Q_TAIL] = field_from_u64(0);
    in_bound.fields[Q_CAP] = field_from_u64(2);
    assert!(
        p.evaluate(&in_bound, None, None).is_ok(),
        "head 2 <= cap 2 ⇒ in-bound write admitted through the live evaluator"
    );

    // Over-bound post-state: head 3, cap 2 (occupancy > capacity) ⇒ rejected.
    let mut over_bound = in_bound.clone();
    over_bound.fields[Q_HEAD] = field_from_u64(3);
    assert!(
        p.evaluate(&over_bound, None, None).is_err(),
        "head 3 > cap 2 ⇒ over-bound write rejected by the capacity caveat"
    );
}

/// The `+delta` framing: `FieldLteOther head cap tail` ≡ the capacity bound
/// `head - tail <= cap`, with `tail` carried in `delta`. Mirrors Lean
/// `fieldLteOther_expresses_capacity`.
#[test]
fn field_lte_other_capacity_with_tail_delta_live() {
    // With tail = 1 folded into delta, the bound is head <= cap + 1.
    let p = CellProgram::Predicate(vec![StateConstraint::FieldLteOther {
        index: Q_HEAD as u8,
        other: Q_CAP as u8,
        delta: 1,
    }]);
    let mut s = CellState::new(0);
    s.fields[Q_CAP] = field_from_u64(2);
    s.fields[Q_HEAD] = field_from_u64(3); // 3 <= cap 2 + delta 1 = 3 ⇒ admit (occupancy 2 = cap)
    assert!(
        p.evaluate(&s, None, None).is_ok(),
        "head 3 <= cap 2 + tail 1"
    );
    s.fields[Q_HEAD] = field_from_u64(4); // 4 > 3 ⇒ reject (occupancy 3 > cap 2)
    assert!(
        p.evaluate(&s, None, None).is_err(),
        "head 4 > cap 2 + tail 1 ⇒ reject"
    );
}

/// `FieldLteOther tail head 0` ≡ the NO-UNDERFLOW bound `tail <= head` through
/// the live evaluator. Mirrors Lean `fieldLteOther_expresses_underflow`.
#[test]
fn field_lte_other_no_underflow_live_path() {
    let p = CellProgram::Predicate(vec![StateConstraint::FieldLteOther {
        index: Q_TAIL as u8,
        other: Q_HEAD as u8,
        delta: 0,
    }]);
    let mut s = CellState::new(0);
    s.fields[Q_HEAD] = field_from_u64(1);
    s.fields[Q_TAIL] = field_from_u64(1); // tail 1 = head 1 ⇒ admit (empty queue)
    assert!(
        p.evaluate(&s, None, None).is_ok(),
        "tail 1 <= head 1 ⇒ admit"
    );
    s.fields[Q_TAIL] = field_from_u64(2); // tail 2 > head 1 ⇒ reject (FIFO underflow)
    assert!(
        p.evaluate(&s, None, None).is_err(),
        "tail 2 > head 1 ⇒ reject"
    );
}

/// SUPERSET: an empty `Predicate([])` (no relational caveat) admits an
/// otherwise-over-bound state — the relational gate only ever TIGHTENS a write.
/// Mirrors Lean `relStateStepGuarded_nil_eq`.
#[test]
fn field_lte_other_empty_program_recovers_unconstrained() {
    let p = CellProgram::Predicate(vec![]);
    let mut s = CellState::new(0);
    s.fields[Q_HEAD] = field_from_u64(99);
    s.fields[Q_CAP] = field_from_u64(2);
    assert!(
        p.evaluate(&s, None, None).is_ok(),
        "no relational caveat ⇒ head 99 admitted (the gate only tightens)"
    );
}

/// Multiple `FieldLteOther` caveats AND together through the live evaluator: a
/// write must satisfy BOTH the capacity AND the no-underflow bound; breaking
/// either rejects (fail-closed conjunction).
#[test]
fn field_lte_other_conjunction_live_path() {
    let p = CellProgram::Predicate(vec![
        StateConstraint::FieldLteOther {
            index: Q_HEAD as u8,
            other: Q_CAP as u8,
            delta: 0,
        }, // capacity: head <= cap
        StateConstraint::FieldLteOther {
            index: Q_TAIL as u8,
            other: Q_HEAD as u8,
            delta: 0,
        }, // no-underflow: tail <= head
    ]);
    let mut s = CellState::new(0);
    s.fields[Q_HEAD] = field_from_u64(2);
    s.fields[Q_TAIL] = field_from_u64(1);
    s.fields[Q_CAP] = field_from_u64(2);
    assert!(
        p.evaluate(&s, None, None).is_ok(),
        "head 2 <= cap 2 AND tail 1 <= head 2 ⇒ admit"
    );
    // Break capacity (head 3 > cap 2): rejected even though tail <= head.
    s.fields[Q_HEAD] = field_from_u64(3);
    assert!(
        p.evaluate(&s, None, None).is_err(),
        "head 3 > cap 2 breaks capacity ⇒ rejected"
    );
}

/// Fail-closed: a `FieldLteOther` naming a slot `>= STATE_SLOTS` surfaces
/// `InvalidFieldIndex` through the live evaluator rather than silently passing.
#[test]
fn field_lte_other_out_of_range_fails_closed_live() {
    use dregg_cell::state::STATE_SLOTS;
    let p = CellProgram::Predicate(vec![StateConstraint::FieldLteOther {
        index: STATE_SLOTS as u8, // out of range
        other: Q_CAP as u8,
        delta: 0,
    }]);
    let s = CellState::new(0);
    assert!(
        p.evaluate(&s, None, None).is_err(),
        "out-of-range slot index ⇒ fail closed through the live evaluator"
    );
}
