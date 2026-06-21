//! Held-promise continuation — the headless model of the partial-turn lift.
//!
//! # What this IS
//!
//! A turn is the exercise of an attenuable proof-carrying token over owned state, leaving a
//! verifiable receipt. A *partial* turn holds a promise: it awaits a value, but the SHAPE of how
//! that value is consumed — which field it lands in, whose write, under which guard — is fixed
//! when the hole is created. This module is the gpui-free model of a held-promise continuation:
//! a staged partial turn the cockpit can suspend, inspect, fill, and (only when complete) drain.
//!
//! It mirrors the proven Lean keystone `Dregg2.Exec.Holes.GuardedHole` / `fillGuarded` and its
//! theorems `holeFill_binds_in_circuit` (a fill binds BOTH its δ and its guard) and
//! `holeFill_rejects_guard_violation` (a guard-violating value does NOT fill — fail-closed). The
//! shape is the study's verdict: **determination is EAGER, witness is LAZY**. The hole's field,
//! actor, target, and guard are fixed up front; only the value arrives late.
//!
//! # What this is NOT
//!
//! This is NOT the executor, the circuit, or the ledger. It is the continuation's control model:
//! the held-promise lifecycle (EMPTY → HELD → READY) and the fail-closed fill. It carries ONLY
//! the weak guarded hole — a guard on a late VALUE — never a STRONG hole (an undetermined δ / a
//! lazy SHAPE), which dregg forbids by inexpressibility (see `docs/deos/PARTIAL-TURN-LIFT.md` §5).
//! There is no constructor for an open-δ hole here: a hole carries a value and a guard, full stop.

/// A reference to a value that a future turn will produce — the model's `EventualRef`.
///
/// Names the slot a hole awaits. `source` is the staged step that will produce the value;
/// `output_slot` is which of its outputs fills the hole. A hole with an unresolved `Slot`
/// reference is OPEN; resolving the reference (filling the slot) closes it.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Slot {
    /// Index of the staged step that produces the awaited value.
    pub source: usize,
    /// Which output of that step fills this hole.
    pub output_slot: u32,
}

impl Slot {
    /// A reference to output `output_slot` of staged step `source`.
    pub fn new(source: usize, output_slot: u32) -> Self {
        Self { source, output_slot }
    }
}

/// A two-valued guard over a late-arriving fill value — the model's `PredCaveat`.
///
/// Deliberately minimal: enough to make the tooth bite TRUE and FALSE (the both-polarity
/// requirement — a guard that admits everything is vacuous and forbidden as a held-promise
/// guard; see [`Guard::admits`]). Mirrors `predCaveatsAdmit` at the value granularity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Guard {
    /// Admit iff the fill value is within `[lo, hi]` inclusive (a range caveat — the model's
    /// `vCaveat`: e.g. admits `50`, rejects `55`).
    InRange { lo: i64, hi: i64 },
    /// Admit iff the fill value equals `expected` exactly (an equality caveat — a beacon/time-lock
    /// hole resolved only by the committed value).
    Equals { expected: i64 },
    /// Admit iff the fill value is at least `threshold` (a deadline/quorum-style monotone guard).
    AtLeast { threshold: i64 },
}

impl Guard {
    /// Does this guard admit `value`? The fail-closed predicate — a fill is committed IFF this
    /// returns `true`. Every guard variant is genuinely two-valued (admits some values, rejects
    /// others): there is no "admit everything" guard, so a held-promise hole can never be vacuous.
    pub fn admits(&self, value: i64) -> bool {
        match self {
            Guard::InRange { lo, hi } => value >= *lo && value <= *hi,
            Guard::Equals { expected } => value == *expected,
            Guard::AtLeast { threshold } => value >= *threshold,
        }
    }
}

/// A late-filled slot carrying the EAGER SHAPE a future fill must honor — the model's
/// `GuardedHole`.
///
/// The shape (`field`, `actor`, `target`, `guard`, and the awaited `slot`) is fixed when the
/// hole is created; only `value` arrives late. A `value` of `None` is OPEN; `Some(_)` means the
/// guard-admitted value has been bound. The fill cannot mutate any part of the shape — exactly
/// the "lazy witness over an eager shape" of `holeFill_binds_in_circuit`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Hole {
    /// The field the fill writes (the awaited value's landing field).
    pub field: String,
    /// Who fills (the actor whose write the value becomes).
    pub actor: u64,
    /// The cell written.
    pub target: u64,
    /// The slot reference this hole awaits (the producer step + output).
    pub slot: Slot,
    /// The predicate the late value MUST discharge before it can fill.
    pub guard: Guard,
    /// The bound value — `None` while OPEN, `Some(v)` once a guard-admitted value filled it.
    pub value: Option<i64>,
}

impl Hole {
    /// Create an OPEN hole: the eager shape is fixed, the value is not yet known.
    pub fn open(field: impl Into<String>, actor: u64, target: u64, slot: Slot, guard: Guard) -> Self {
        Self {
            field: field.into(),
            actor,
            target,
            slot,
            guard,
            value: None,
        }
    }

    /// `true` iff this hole still awaits its value.
    pub fn is_open(&self) -> bool {
        self.value.is_none()
    }
}

/// The outcome of attempting to fill a hole — the model's `Option RecChainedState` return of
/// `fillGuarded`, with the rejection reason surfaced for the cockpit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FillOutcome {
    /// The value was guard-admitted and bound into the hole. Mirrors `fillGuarded = some _`.
    Bound,
    /// The value VIOLATED the hole's guard — the hole stays OPEN, no state changed. Mirrors
    /// `fillGuarded = none` / `holeFill_rejects_guard_violation` (fail-closed).
    GuardViolation { field: String, value: i64 },
    /// No hole awaits the named slot (or it was already filled). A no-op, not a state change.
    NoSuchOpenSlot { slot: Slot },
}

impl FillOutcome {
    /// `true` iff the fill bound a value (advanced toward READY).
    pub fn bound(&self) -> bool {
        matches!(self, FillOutcome::Bound)
    }
}

/// The held-promise continuation: a staged partial turn that may carry open holes.
///
/// Lifecycle (see `docs/deos/PARTIAL-TURN-LIFT.md` §3):
/// - **EMPTY** — `holes` is empty AND no concrete steps staged: nothing held.
/// - **HELD** — ≥1 hole is OPEN: a promise is held; the world head is frozen, nothing drains.
/// - **READY** — every hole is filled (`is_ready()`): the continuation is concrete and may drain.
///
/// The model enforces the fail-closed line structurally: [`HeldPromise::is_ready`] is `false`
/// while any hole is open, so a continuation with an unresolved promise can NEVER drain.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct HeldPromise {
    /// The holes staged in this continuation (the promises awaiting values).
    holes: Vec<Hole>,
    /// Count of concrete (hole-free) staged steps — present so an all-concrete continuation
    /// reads as HELD (something staged) rather than EMPTY.
    concrete_steps: usize,
}

impl HeldPromise {
    /// An empty continuation — nothing staged.
    pub fn new() -> Self {
        Self {
            holes: Vec::new(),
            concrete_steps: 0,
        }
    }

    /// Stage a partial turn carrying `hole` (a held promise). Returns the hole's index.
    pub fn stage_hole(&mut self, hole: Hole) -> usize {
        let idx = self.holes.len();
        self.holes.push(hole);
        idx
    }

    /// Stage a concrete (hole-free) step. Does not add a promise; only marks the continuation
    /// non-empty (the flat-`VecDeque<Turn>` case the cockpit already handles).
    pub fn stage_concrete(&mut self) {
        self.concrete_steps += 1;
    }

    /// `true` iff nothing is staged (neither holes nor concrete steps) — the EMPTY state.
    pub fn is_empty(&self) -> bool {
        self.holes.is_empty() && self.concrete_steps == 0
    }

    /// `true` iff ≥1 hole is still OPEN — the HELD state (a promise is held, cannot drain).
    pub fn is_held(&self) -> bool {
        self.holes.iter().any(Hole::is_open)
    }

    /// `true` iff something is staged AND no hole remains open — the READY state (may drain).
    /// This is the structural fail-closed: a continuation with an open hole is NEVER ready.
    pub fn is_ready(&self) -> bool {
        !self.is_empty() && !self.is_held()
    }

    /// Number of holes still awaiting a value.
    pub fn open_hole_count(&self) -> usize {
        self.holes.iter().filter(|h| h.is_open()).count()
    }

    /// The open holes (for the cockpit to render the eager shape awaiting each value).
    pub fn open_holes(&self) -> impl Iterator<Item = &Hole> {
        self.holes.iter().filter(|h| h.is_open())
    }

    /// **Fill the hole awaiting `slot` with `value`** — the model's `fillGuarded`.
    ///
    /// Binds `value` into the awaiting OPEN hole IFF the hole's guard admits it
    /// ([`Guard::admits`]). On a guard violation the hole stays OPEN and NO state changes —
    /// fail-closed, mirroring `holeFill_rejects_guard_violation`. The eager shape (field, actor,
    /// target, guard, slot) is never mutated; only `value` transitions `None → Some`, mirroring
    /// `holeFill_binds_in_circuit` (the fill binds δ — the bound value — AND the discharged guard).
    pub fn fill(&mut self, slot: &Slot, value: i64) -> FillOutcome {
        let Some(hole) = self
            .holes
            .iter_mut()
            .find(|h| h.is_open() && &h.slot == slot)
        else {
            return FillOutcome::NoSuchOpenSlot { slot: slot.clone() };
        };

        if !hole.guard.admits(value) {
            // Fail-closed: the late witness cannot escape the eager shape. Hole stays OPEN.
            return FillOutcome::GuardViolation {
                field: hole.field.clone(),
                value,
            };
        }

        hole.value = Some(value);
        FillOutcome::Bound
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn demo_hole(slot: Slot, guard: Guard) -> Hole {
        Hole::open("v", 0, 0, slot, guard)
    }

    // ── Lifecycle: EMPTY → HELD → READY ─────────────────────────────────────────

    #[test]
    fn empty_continuation_is_empty_not_held_not_ready() {
        let c = HeldPromise::new();
        assert!(c.is_empty());
        assert!(!c.is_held());
        assert!(!c.is_ready()); // nothing staged → nothing to drain
    }

    #[test]
    fn staging_a_hole_makes_it_held_and_not_ready() {
        let mut c = HeldPromise::new();
        c.stage_hole(demo_hole(Slot::new(0, 0), Guard::InRange { lo: 1, hi: 100 }));
        assert!(!c.is_empty());
        assert!(c.is_held()); // a promise is held
        assert!(!c.is_ready()); // CANNOT drain — the structural fail-closed
        assert_eq!(c.open_hole_count(), 1);
    }

    #[test]
    fn all_concrete_continuation_is_held_then_ready() {
        // The flat-queue case: concrete steps, no holes — non-empty, no open promise → READY.
        let mut c = HeldPromise::new();
        c.stage_concrete();
        assert!(!c.is_empty());
        assert!(!c.is_held()); // no open promise
        assert!(c.is_ready()); // may drain immediately
    }

    // ── The POSITIVE tooth: a guard-admitted value FILLS and advances toward READY ──

    #[test]
    fn guard_admitted_value_binds_and_reaches_ready() {
        let mut c = HeldPromise::new();
        let slot = Slot::new(0, 0);
        c.stage_hole(demo_hole(slot.clone(), Guard::InRange { lo: 1, hi: 100 }));

        let outcome = c.fill(&slot, 50); // 50 ∈ [1,100] → admitted
        assert_eq!(outcome, FillOutcome::Bound);
        assert!(outcome.bound());

        // The promise resolved: no open hole remains → READY (may drain).
        assert!(!c.is_held());
        assert!(c.is_ready());
        assert_eq!(c.open_hole_count(), 0);
    }

    // ── The NEGATIVE tooth: a guard-VIOLATING value is REJECTED, fail-closed ────────

    #[test]
    fn guard_violating_value_is_rejected_and_stays_held() {
        let mut c = HeldPromise::new();
        let slot = Slot::new(0, 0);
        c.stage_hole(demo_hole(slot.clone(), Guard::InRange { lo: 1, hi: 100 }));

        let outcome = c.fill(&slot, 555); // 555 ∉ [1,100] → guard violation
        assert!(matches!(outcome, FillOutcome::GuardViolation { value: 555, .. }));
        assert!(!outcome.bound());

        // Fail-closed: the hole stays OPEN, the continuation stays HELD, CANNOT drain.
        assert!(c.is_held());
        assert!(!c.is_ready());
        assert_eq!(c.open_hole_count(), 1);
    }

    // ── The guard is genuinely TWO-VALUED on the same hole (not vacuous) ────────────

    #[test]
    fn guard_admits_one_value_rejects_another_two_valued() {
        // Mirrors GuardedHole.lean's vCaveat: admits 50, rejects 55.
        let g = Guard::InRange { lo: 40, hi: 52 };
        assert!(g.admits(50)); // TRUE
        assert!(!g.admits(55)); // FALSE — the tooth bites both polarities
    }

    #[test]
    fn equals_guard_two_valued() {
        let g = Guard::Equals { expected: 7 };
        assert!(g.admits(7));
        assert!(!g.admits(8));
    }

    #[test]
    fn at_least_guard_two_valued() {
        // A deadline/quorum-style monotone guard (beacon-after-t shape).
        let g = Guard::AtLeast { threshold: 100 };
        assert!(g.admits(100));
        assert!(g.admits(250));
        assert!(!g.admits(99));
    }

    // ── Multi-hole: READY requires ALL holes filled (one open hole blocks the drain) ─

    #[test]
    fn two_holes_one_filled_still_held() {
        let mut c = HeldPromise::new();
        let s0 = Slot::new(0, 0);
        let s1 = Slot::new(1, 0);
        c.stage_hole(demo_hole(s0.clone(), Guard::AtLeast { threshold: 10 }));
        c.stage_hole(demo_hole(s1.clone(), Guard::AtLeast { threshold: 10 }));

        assert_eq!(c.fill(&s0, 20), FillOutcome::Bound);
        // One hole still open → NOT ready.
        assert!(c.is_held());
        assert!(!c.is_ready());
        assert_eq!(c.open_hole_count(), 1);

        assert_eq!(c.fill(&s1, 30), FillOutcome::Bound);
        // Both filled → READY.
        assert!(c.is_ready());
        assert_eq!(c.open_hole_count(), 0);
    }

    // ── Filling an unknown / already-filled slot is a no-op, not a state change ─────

    #[test]
    fn fill_unknown_slot_is_noop() {
        let mut c = HeldPromise::new();
        let slot = Slot::new(0, 0);
        c.stage_hole(demo_hole(slot.clone(), Guard::AtLeast { threshold: 0 }));

        let bogus = Slot::new(9, 9);
        assert_eq!(c.fill(&bogus, 1), FillOutcome::NoSuchOpenSlot { slot: bogus });
        // The real hole is untouched.
        assert_eq!(c.open_hole_count(), 1);
        assert!(c.is_held());
    }

    #[test]
    fn refilling_a_bound_hole_is_noop() {
        let mut c = HeldPromise::new();
        let slot = Slot::new(0, 0);
        c.stage_hole(demo_hole(slot.clone(), Guard::Equals { expected: 42 }));

        assert_eq!(c.fill(&slot, 42), FillOutcome::Bound);
        assert!(c.is_ready());
        // The hole is no longer OPEN, so a second fill finds no open slot — the bound value
        // cannot be silently overwritten.
        assert_eq!(
            c.fill(&slot, 99),
            FillOutcome::NoSuchOpenSlot { slot: slot.clone() }
        );
    }

    // ── The eager shape is never mutated by a fill (lazy witness over eager shape) ──

    #[test]
    fn fill_binds_value_without_mutating_shape() {
        let mut c = HeldPromise::new();
        let slot = Slot::new(3, 1);
        c.stage_hole(Hole::open("balance", 7, 9, slot.clone(), Guard::InRange { lo: 0, hi: 1000 }));

        assert_eq!(c.fill(&slot, 500), FillOutcome::Bound);
        let h = &c.holes[0];
        // δ bound:
        assert_eq!(h.value, Some(500));
        // shape untouched (field/actor/target/guard/slot all as staged):
        assert_eq!(h.field, "balance");
        assert_eq!(h.actor, 7);
        assert_eq!(h.target, 9);
        assert_eq!(h.slot, slot);
        assert_eq!(h.guard, Guard::InRange { lo: 0, hi: 1000 });
    }
}
