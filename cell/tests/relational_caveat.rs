//! Integration differential for the **record-level relational caveat** —
//! `FieldLteOther` — the Rust mirror of the verified Lean atom set
//! (`metatheory/Dregg2/Exec/RelationalCaveat.lean`).
//!
//! # Why a record-level caveat?
//!
//! The per-slot caveat surface (Lean `RecordKernel.SlotCaveat.eval`, Rust
//! `StateConstraint` for `Immutable` / `Monotonic` / `WriteOnce` / …) reads,
//! for a write to ITS slot, only that slot's `(actor, old, new)`. It is
//! structurally blind to every other slot's value, so it cannot express a
//! cross-slot relation like a queue's capacity bound `head − tail ≤ cap` or
//! its no-underflow `tail ≤ head` (the falsification the queue probe isolated,
//! `metatheory/Dregg2/Verify/QueueFactoryProbe.lean`, §0 / §VERDICT).
//!
//! A **record-level** caveat reads the WHOLE post-write record, so it can
//! compare two slots. The single instance the queue / inbox / pubsub families
//! need is `FieldLteOther { index, other, delta }`:
//!
//!   in the post-write record, `record[index] ≤ record[other] + delta`.
//!
//!   * `FieldLteOther head cap tail` ≡ the CAPACITY bound `head − tail ≤ cap`.
//!   * `FieldLteOther tail head 0`   ≡ the NO-UNDERFLOW bound `tail ≤ head`.
//!
//! # Relation to the existing `program.rs` surface
//!
//! `cell::program::StateConstraint` already carries record-level relational
//! atoms that see the whole post-state — `FieldLteField { left, right }`
//! (`new[left] ≤ new[right]`, no `delta`) and `AffineLe { terms, c }`
//! (`Σ kᵢ·new[fᵢ] ≤ c`). This test promotes the Lean `FieldLteOther` `+delta`
//! shape — exactly the queue capacity/underflow framing — and shows it is a
//! strict SUPERSET of the per-slot surface: the relational gate only ever
//! TIGHTENS a write, never loosens it (an in-bound write commits, an over-bound
//! write is rejected, an empty caveat list recovers the per-slot behavior).
//!
//! The evaluator below is the executable Rust transcription of the Lean
//! `RelCaveat.eval` / `relCaveatsAdmit`. Field reads use the crate's public
//! `field_from_u64` / `field_to_u64` big-endian-u64 lane (mirroring Lean's
//! `fieldOf`, absent ⇒ 0). It links only the crate's PUBLIC API, so it is
//! independent of any in-crate `#[cfg(test)]` module and needs no edit to
//! `lib.rs` / `program.rs`.

use dregg_cell::program::field_from_u64;
use dregg_cell::state::{CellState, FieldElement, STATE_SLOTS};

/// Read a field as a signed i128 over the big-endian-u64 lane (the last 8
/// bytes), mirroring Lean `fieldOf` (`Value.scalar`, absent ⇒ 0). Used so the
/// relational comparison `record[index] ≤ record[other] + delta` is a real
/// signed-integer inequality.
fn field_i128(field: &FieldElement) -> i128 {
    let mut bytes = [0u8; 8];
    bytes.copy_from_slice(&field[24..32]);
    u64::from_be_bytes(bytes) as i128
}

/// **The record-level relational caveat** — the Rust mirror of Lean
/// `Dregg2.Exec.RelationalCaveat.RelCaveat`. Unlike a per-slot
/// `StateConstraint`, the evaluator reads the WHOLE post-write record, so it
/// can compare two slots.
#[derive(Clone, Debug, PartialEq, Eq)]
enum RelCaveat {
    /// `FieldLteOther { index, other, delta }` — in the post-write record,
    /// `record[index] ≤ record[other] + delta`. Mirrors Lean
    /// `RelCaveat.fieldLteOther`. `index`/`other` are slot indices into the
    /// fixed `STATE_SLOTS` field array; `delta` is a signed offset.
    FieldLteOther { index: u8, other: u8, delta: i64 },
}

/// Outcome of a record-level relational caveat evaluation: a slot index was
/// out of range (fail-closed), or the relation held / was violated.
#[derive(Clone, Debug, PartialEq, Eq)]
enum RelError {
    /// A slot index referenced by the caveat is out of `STATE_SLOTS` range.
    InvalidFieldIndex { index: u8 },
    /// The cross-slot relation was violated on the post-write record.
    RelationViolated { caveat: RelCaveat, detail: String },
}

impl RelCaveat {
    /// Evaluate this record-level caveat against the WHOLE post-write record.
    /// Mirrors Lean `RelCaveat.eval`: reads the named slots as signed i128
    /// (the big-endian-u64 lane) and checks the relation. FAIL-CLOSED: a bad
    /// slot index, or a violated relation, returns `Err`.
    fn eval(&self, record: &CellState) -> Result<(), RelError> {
        match self {
            RelCaveat::FieldLteOther {
                index,
                other,
                delta,
            } => {
                let i = check_index(*index)?;
                let o = check_index(*other)?;
                let lhs = field_i128(&record.fields[i]);
                let rhs = field_i128(&record.fields[o]) + *delta as i128;
                if lhs <= rhs {
                    Ok(())
                } else {
                    Err(RelError::RelationViolated {
                        caveat: self.clone(),
                        detail: format!(
                            "record[{index}] = {lhs} > record[{other}] + {delta} = {rhs}"
                        ),
                    })
                }
            }
        }
    }
}

fn check_index(index: u8) -> Result<usize, RelError> {
    let idx = index as usize;
    if idx >= STATE_SLOTS {
        return Err(RelError::InvalidFieldIndex { index });
    }
    Ok(idx)
}

/// Do ALL record-level relational caveats admit the post-write record?
/// FAIL-CLOSED: the first violated relation rejects. Mirrors Lean
/// `relCaveatsAdmit` (`List.all`).
fn rel_caveats_admit(caveats: &[RelCaveat], record: &CellState) -> Result<(), RelError> {
    for cav in caveats {
        cav.eval(record)?;
    }
    Ok(())
}

/// A relationally-guarded field write — the executable shadow of Lean
/// `relStateStepGuarded`. Here the per-slot gate is modeled as a plain field
/// write (the per-slot `StateConstraint` surface is already covered by the
/// in-crate tests + `integration_policy_combinators.rs`); this harness
/// isolates the RECORD-LEVEL relational gate. It (1) applies the write to a
/// copy of the cell, then (2) checks the record-level relational caveats on
/// the post-write record, committing the new record iff they admit.
///
/// Returns `Some(post_state)` on a committed write, `None` when the relational
/// gate rejects — mirroring Lean's `Option RecChainedState` fail-closed shape.
fn rel_guarded_write(
    state: &CellState,
    caveats: &[RelCaveat],
    slot: u8,
    value: u64,
) -> Option<CellState> {
    let idx = slot as usize;
    if idx >= STATE_SLOTS {
        return None;
    }
    let mut post = state.clone();
    post.fields[idx] = field_from_u64(value);
    match rel_caveats_admit(caveats, &post) {
        Ok(()) => Some(post),
        Err(_) => None,
    }
}

// ── Slot layout for the queue cell (mirrors the Lean `qworld` / `rq0`). ──
const HEAD: u8 = 0; // queue.head_seq — total enqueued
const TAIL: u8 = 1; // queue.tail_seq — total dequeued
const CAP: u8 = 2; // queue.capacity — max occupancy

/// A queue cell: head_seq 1, tail_seq 0 (occupancy 1), capacity 2 (room for
/// one more) — mirrors Lean `rq0` cell 0.
fn queue_cell() -> CellState {
    let mut s = CellState::new(0);
    s.fields[HEAD as usize] = field_from_u64(1);
    s.fields[TAIL as usize] = field_from_u64(0);
    s.fields[CAP as usize] = field_from_u64(2);
    s
}

/// The capacity caveat for the queue cell: `head ≤ cap + tail`. With `tail = 0`
/// folded into `delta = 0`, this is `head ≤ cap`. Mirrors Lean `rqCapCav`.
fn capacity_caveat() -> Vec<RelCaveat> {
    vec![RelCaveat::FieldLteOther {
        index: HEAD,
        other: CAP,
        delta: 0,
    }]
}

// ───────────────────────────────────────────────────────────────────────────
// §EXPRESSES — the atom expresses the capacity + underflow bounds.
// ───────────────────────────────────────────────────────────────────────────

/// `FieldLteOther head cap tail` expresses the capacity bound `head − tail ≤
/// cap`. Mirrors Lean `fieldLteOther_expresses_capacity`.
#[test]
fn field_lte_other_expresses_capacity() {
    let q = queue_cell(); // head 1, tail 0, cap 2 → occupancy 1 ≤ cap 2 ⇒ holds
    let tail = field_i128(&q.fields[TAIL as usize]) as i64;
    let cap_cav = RelCaveat::FieldLteOther {
        index: HEAD,
        other: CAP,
        delta: tail, // delta carries the second cross-slot term (tail)
    };
    assert!(cap_cav.eval(&q).is_ok(), "occupancy 1 ≤ cap 2 must hold");

    // A FULL queue (head 2, tail 0, cap 2 → occupancy 2 = cap) still holds;
    // head 3 (occupancy 3 > cap 2) violates.
    let mut full = q.clone();
    full.fields[HEAD as usize] = field_from_u64(2);
    assert!(cap_cav.eval(&full).is_ok(), "occupancy 2 = cap 2 holds");
    let mut over = q.clone();
    over.fields[HEAD as usize] = field_from_u64(3);
    assert!(cap_cav.eval(&over).is_err(), "occupancy 3 > cap 2 violates");
}

/// `FieldLteOther tail head 0` expresses the no-underflow bound `tail ≤ head`.
/// Mirrors Lean `fieldLteOther_expresses_underflow`.
#[test]
fn field_lte_other_expresses_underflow() {
    let underflow_cav = RelCaveat::FieldLteOther {
        index: TAIL,
        other: HEAD,
        delta: 0,
    };
    let q = queue_cell(); // tail 0 ≤ head 1 ⇒ holds
    assert!(underflow_cav.eval(&q).is_ok(), "tail 0 ≤ head 1 holds");

    // tail overtaking head (tail 2 > head 1) violates the FIFO bound.
    let mut under = q.clone();
    under.fields[TAIL as usize] = field_from_u64(2);
    assert!(
        underflow_cav.eval(&under).is_err(),
        "tail 2 > head 1 violates no-underflow"
    );
}

// ───────────────────────────────────────────────────────────────────────────
// §SOUNDNESS — an over-bound write is rejected; an in-bound write commits.
// ───────────────────────────────────────────────────────────────────────────

/// An IN-BOUND enqueue (head 1 → 2, occupancy → 2 = cap) COMMITS under the
/// capacity caveat. Mirrors Lean `rq0` #guard (iii).
#[test]
fn in_bound_write_commits() {
    let q = queue_cell();
    let post = rel_guarded_write(&q, &capacity_caveat(), HEAD, 2)
        .expect("head 1→2 (occupancy 2 = cap 2) must commit");
    assert_eq!(
        field_i128(&post.fields[HEAD as usize]),
        2,
        "the committed write advanced head to 2"
    );
}

/// An OVER-BOUND write (head → 3 > cap 2) is REJECTED by the relational gate —
/// the capacity bound bites. Mirrors Lean `rq0` #guard (iv).
#[test]
fn over_bound_write_rejected() {
    let q = queue_cell();
    assert!(
        rel_guarded_write(&q, &capacity_caveat(), HEAD, 3).is_none(),
        "head → 3 (occupancy 3 > cap 2) must be rejected by the capacity caveat"
    );
}

/// The dual no-underflow bound: a dequeue advancing tail past head is rejected.
#[test]
fn underflow_write_rejected() {
    let q = queue_cell(); // head 1, tail 0
    let no_underflow = vec![RelCaveat::FieldLteOther {
        index: TAIL,
        other: HEAD,
        delta: 0,
    }];
    // tail 0 → 1 (= head 1) commits; tail → 2 (> head 1) is rejected.
    assert!(
        rel_guarded_write(&q, &no_underflow, TAIL, 1).is_some(),
        "tail 0→1 (= head 1) must commit"
    );
    assert!(
        rel_guarded_write(&q, &no_underflow, TAIL, 2).is_none(),
        "tail → 2 (> head 1) must be rejected by no-underflow"
    );
}

// ───────────────────────────────────────────────────────────────────────────
// §SUPERSET — an empty caveat list recovers the per-slot (gate-free) behavior.
// ───────────────────────────────────────────────────────────────────────────

/// With an EMPTY relational-caveat list the write is unconstrained by the
/// record-level gate: head → 3 commits (no cross-slot bound declared). Mirrors
/// Lean `relStateStepGuarded_nil_eq` + `rq0` #guard (v).
#[test]
fn empty_caveat_list_recovers_per_slot() {
    let q = queue_cell();
    let post =
        rel_guarded_write(&q, &[], HEAD, 3).expect("with no relational caveat, head → 3 commits");
    assert_eq!(
        field_i128(&post.fields[HEAD as usize]),
        3,
        "the unconstrained write advanced head to 3"
    );
}

/// Multiple relational caveats AND together: a write must satisfy BOTH the
/// capacity AND the no-underflow bound. A write satisfying one but breaking the
/// other is rejected (fail-closed on the first violation).
#[test]
fn multiple_caveats_and_together() {
    let q = queue_cell(); // head 1, tail 0, cap 2
    let both = vec![
        RelCaveat::FieldLteOther {
            index: HEAD,
            other: CAP,
            delta: 0,
        }, // capacity: head ≤ cap
        RelCaveat::FieldLteOther {
            index: TAIL,
            other: HEAD,
            delta: 0,
        }, // no-underflow: tail ≤ head
    ];
    // head 1 → 2 keeps head ≤ cap (2 ≤ 2) and tail ≤ head (0 ≤ 2): commits.
    assert!(
        rel_guarded_write(&q, &both, HEAD, 2).is_some(),
        "head → 2 satisfies both bounds"
    );
    // head 1 → 3 breaks capacity (3 > 2): rejected even though tail ≤ head.
    assert!(
        rel_guarded_write(&q, &both, HEAD, 3).is_none(),
        "head → 3 breaks capacity; rejected"
    );
}

/// Fail-closed on an out-of-range slot index — a caveat naming a slot
/// `>= STATE_SLOTS` rejects rather than silently passing.
#[test]
fn out_of_range_slot_fails_closed() {
    let q = queue_cell();
    let bad = vec![RelCaveat::FieldLteOther {
        index: STATE_SLOTS as u8, // out of range
        other: CAP,
        delta: 0,
    }];
    assert_eq!(
        rel_caveats_admit(&bad, &q),
        Err(RelError::InvalidFieldIndex {
            index: STATE_SLOTS as u8
        }),
        "an out-of-range slot index must fail closed"
    );
}
