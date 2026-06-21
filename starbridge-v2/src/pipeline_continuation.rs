//! Held-promise continuation over a real `dregg_turn::Pipeline` — the partial-turn lift,
//! wired (not modelled).
//!
//! # What this IS (the lift §1, §7 of `docs/deos/PARTIAL-TURN-LIFT.md`)
//!
//! [`crate::held_promise`] is the *standalone* model: holes + guards + the EMPTY→HELD→READY
//! lifecycle, with no dependency on the executor. This module is the LIFT it names in §8: the
//! held-promise continuation carried by a real [`dregg_turn::Pipeline`] — a staged batch of real
//! [`Turn`]s whose holes are real [`EventualRef`]s on [`Target::Eventual`] / `PipelinedSend`
//! targets. The suspend continuation today is a flat `VecDeque<Turn>` (every staged turn already
//! concrete). This makes the continuation able to carry a **Pipeline-WITH-HOLES**: a turn that
//! *awaits* a value, holding a promise, resolved once at resume / quorum-after-t, fail-closed.
//!
//! A hole IS a nullifier; resolution IS a spend; one-shot linearity IS the double-resolve the
//! continuation refuses. The eager SHAPE (which `EventualRef` slot, which field, whose write,
//! under which guard) is fixed when the hole is staged; only the VALUE arrives late — exactly the
//! "determination is EAGER, witness is LAZY" of `Dregg2.Exec.Holes.GuardedHole`. A successful
//! resolution binds BOTH its δ (the value) AND its guard (`holeFill_binds_in_circuit`); a
//! guard-violating value does NOT resolve (`holeFill_rejects_guard_violation`, fail-closed).
//!
//! # What this is NOT
//!
//! Not the executor, the circuit, or the ledger. It is the continuation's CONTROL model over the
//! real pipeline shapes: it decides WHEN a staged Pipeline-with-holes becomes a drainable concrete
//! Pipeline. The drain itself (handing the resolved [`Pipeline`] to `execute_pipeline` /
//! `World::resume`) is the caller's; this module guarantees the caller only ever receives a
//! pipeline whose every `Eventual` target has been resolved on the terms its hole fixed up front.
//!
//! It carries ONLY the weak guarded hole — a guard on a late VALUE — never a STRONG hole (an
//! undetermined δ / a lazy SHAPE), which dregg forbids by inexpressibility
//! (`docs/deos/PARTIAL-TURN-LIFT.md` §5). There is no constructor for an open-δ hole here.

use std::collections::HashMap;

use dregg_turn::eventual::{EventualRef, Pipeline, Target};
use dregg_turn::turn::Turn;

pub use crate::held_promise::Guard;

/// A hole in the staged pipeline: a real [`EventualRef`] slot awaiting its value, carrying the
/// EAGER SHAPE the late value must honor — the lift's `GuardedHole` over the real promise ref.
///
/// `eref` is the *identity* of the hole (the `(source_turn, output_slot)` the pipeline executor
/// would resolve). The shape (`field`, `actor`, `target`, `guard`) is fixed when the hole is
/// staged; only `value` arrives late. The resolution cannot mutate any part of the shape — the
/// lazy witness over an eager shape.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PipelineHole {
    /// The real promise reference this hole awaits (its identity in the pipeline).
    pub eref: EventualRef,
    /// The field the resolved value writes (the awaited value's landing field).
    pub field: String,
    /// Who fills (the actor whose write the value becomes).
    pub actor: u64,
    /// The cell written.
    pub target: u64,
    /// The predicate the late value MUST discharge before it can resolve the hole.
    pub guard: Guard,
    /// The bound value — `None` while OPEN, `Some(v)` once a guard-admitted value resolved it.
    pub value: Option<i64>,
}

impl PipelineHole {
    /// Stage an OPEN hole on `eref`: the eager shape is fixed, the value is not yet known.
    pub fn open(
        eref: EventualRef,
        field: impl Into<String>,
        actor: u64,
        target: u64,
        guard: Guard,
    ) -> Self {
        Self {
            eref,
            field: field.into(),
            actor,
            target,
            guard,
            value: None,
        }
    }

    /// `true` iff this hole still awaits its value.
    pub fn is_open(&self) -> bool {
        self.value.is_none()
    }
}

/// The outcome of attempting to resolve a hole — the lift's `fillGuarded` return, with the
/// rejection reason surfaced for the cockpit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResolveOutcome {
    /// The value was guard-admitted and bound into the hole. Mirrors `fillGuarded = some _` /
    /// `holeFill_binds_in_circuit` (binds δ AND guard).
    Bound,
    /// The value VIOLATED the hole's guard — the hole stays OPEN, no state changed. Mirrors
    /// `fillGuarded = none` / `holeFill_rejects_guard_violation` (fail-closed).
    GuardViolation { field: String, value: i64 },
    /// No OPEN hole awaits the named `eref` (unknown, or already bound). A no-op, not a state
    /// change — a bound value can never be silently overwritten (one-shot linearity).
    NoSuchOpenHole { eref: EventualRef },
}

impl ResolveOutcome {
    /// `true` iff the resolution bound a value (advanced the continuation toward READY).
    pub fn bound(&self) -> bool {
        matches!(self, ResolveOutcome::Bound)
    }
}

/// Why a continuation could not be drained into a concrete pipeline.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DrainError {
    /// At least one hole is still OPEN — the structural fail-closed: a held promise can never
    /// drain. Carries the count of still-open holes for the cockpit.
    StillHeld { open_holes: usize },
    /// Nothing is staged — there is no continuation to drain.
    Empty,
}

/// A held-promise continuation carried by a real [`Pipeline`].
///
/// The continuation stages real [`Turn`]s (the concrete part) AND real [`PipelineHole`]s (the
/// promises awaiting values). Lifecycle (`docs/deos/PARTIAL-TURN-LIFT.md` §3):
/// - **EMPTY** — no turns staged AND no holes: nothing held.
/// - **HELD** — ≥1 hole is OPEN: a promise is held; the world head is frozen, nothing drains.
/// - **READY** — turns staged AND every hole resolved: [`Self::is_ready`]; the continuation is a
///   concrete pipeline (no `Eventual` target remains) and may [`Self::drain`].
///
/// The fail-closed line is structural: [`Self::is_ready`] is `false` while any hole is open, so
/// [`Self::drain`] (the only path to a runnable [`Pipeline`]) refuses a held continuation.
#[derive(Clone, Debug, Default)]
pub struct HeldPipeline {
    /// The staged turns (the pipeline body). Built in arrival order; the continuation drains them
    /// as a single [`Pipeline`].
    turns: Vec<Turn>,
    /// Dependency edges between staged turns, carried verbatim into the drained pipeline.
    dependencies: Vec<(usize, usize)>,
    /// When true, the drained pipeline is atomic (all-or-nothing).
    atomic: bool,
    /// The holes staged in this continuation (the promises awaiting values), keyed for resolution
    /// by their `EventualRef`. A `Vec` (not a map) so render order is stable and a hole's full
    /// eager shape is inspectable.
    holes: Vec<PipelineHole>,
}

impl HeldPipeline {
    /// An empty continuation — nothing staged.
    pub fn new() -> Self {
        Self::default()
    }

    /// Mark the drained pipeline atomic (all staged turns succeed together or all roll back).
    pub fn atomic(mut self) -> Self {
        self.atomic = true;
        self
    }

    /// Stage a concrete (hole-free) [`Turn`] into the continuation. Returns its pipeline index
    /// (usable as a dependency edge endpoint). This is the flat-`VecDeque<Turn>` case the cockpit
    /// already handles — present so an all-concrete continuation drains unchanged.
    pub fn stage_turn(&mut self, turn: Turn) -> usize {
        let idx = self.turns.len();
        self.turns.push(turn);
        idx
    }

    /// Declare that staged turn `dependent` runs after `dependency` (carried into the pipeline).
    pub fn add_dependency(&mut self, dependent: usize, dependency: usize) {
        self.dependencies.push((dependent, dependency));
    }

    /// Stage a partial turn carrying `hole` (a held promise on a real [`EventualRef`]).
    ///
    /// The hole awaits the value a future resolution provides; the eager shape (its `eref`, field,
    /// actor, target, guard) is fixed now. `turn` is the partial turn itself — it carries the
    /// `Target::Eventual(hole.eref)` / `PipelinedSend { target: hole.eref, .. }` whose slot the
    /// hole names. Returns the turn's pipeline index.
    ///
    /// The continuation does not (and must not) inspect the turn's internals to confirm the
    /// eref appears — the hole declares the obligation; [`Self::drain`] enforces that every
    /// declared hole is resolved before the pipeline can run. (A staged turn whose eref is never
    /// resolved keeps the continuation HELD forever — fail-closed by construction.)
    pub fn stage_partial(&mut self, turn: Turn, hole: PipelineHole) -> usize {
        let idx = self.turns.len();
        self.turns.push(turn);
        self.holes.push(hole);
        idx
    }

    /// `true` iff nothing is staged (neither turns nor holes) — the EMPTY state.
    pub fn is_empty(&self) -> bool {
        self.turns.is_empty() && self.holes.is_empty()
    }

    /// `true` iff ≥1 hole is still OPEN — the HELD state (a promise is held, cannot drain).
    pub fn is_held(&self) -> bool {
        self.holes.iter().any(PipelineHole::is_open)
    }

    /// `true` iff something is staged AND no hole remains open — the READY state (may drain).
    /// The structural fail-closed: a continuation with an open hole is NEVER ready.
    pub fn is_ready(&self) -> bool {
        !self.is_empty() && !self.is_held()
    }

    /// Number of holes still awaiting a value.
    pub fn open_hole_count(&self) -> usize {
        self.holes.iter().filter(|h| h.is_open()).count()
    }

    /// The open holes (for the cockpit to render the eager shape awaiting each value).
    pub fn open_holes(&self) -> impl Iterator<Item = &PipelineHole> {
        self.holes.iter().filter(|h| h.is_open())
    }

    /// **Resolve the hole awaiting `eref` with `value`** — the lift's `fillGuarded` over the real
    /// promise ref.
    ///
    /// Binds `value` into the awaiting OPEN hole IFF the hole's guard admits it ([`Guard::admits`]).
    /// On a guard violation the hole stays OPEN and NO state changes — fail-closed, mirroring
    /// `holeFill_rejects_guard_violation`. The eager shape (eref, field, actor, target, guard) is
    /// never mutated; only `value` transitions `None → Some`, mirroring `holeFill_binds_in_circuit`
    /// (the resolution binds δ — the bound value — AND the discharged guard). A second resolve of a
    /// bound hole finds no OPEN hole and is a no-op (one-shot linearity: a hole is a nullifier,
    /// resolution is its single spend; the value cannot be silently overwritten).
    pub fn resolve(&mut self, eref: &EventualRef, value: i64) -> ResolveOutcome {
        let Some(hole) = self
            .holes
            .iter_mut()
            .find(|h| h.is_open() && &h.eref == eref)
        else {
            return ResolveOutcome::NoSuchOpenHole { eref: eref.clone() };
        };

        if !hole.guard.admits(value) {
            // Fail-closed: the late witness cannot escape the eager shape. Hole stays OPEN.
            return ResolveOutcome::GuardViolation {
                field: hole.field.clone(),
                value,
            };
        }

        hole.value = Some(value);
        ResolveOutcome::Bound
    }

    /// Resolve a beacon/quorum-after-t hole with the beacon value at the tick — the §4 connection.
    ///
    /// A beacon value is a promise resolved AT THE TICK: a hole whose guard is the threshold
    /// (`Guard::AtLeast`) the tick must reach, filled at quorum-after-t. This is exactly
    /// [`Self::resolve`] with the beacon's `(tick, value)` — the eager shape (which `eref`, under
    /// the threshold guard) was fixed when the chain was staged; the value arrives at the tick.
    /// `tick_value` is the beacon output projected to the guard's domain (the value the threshold
    /// committee produced at this tick); it resolves the hole IFF it clears the threshold guard.
    pub fn resolve_at_tick(&mut self, eref: &EventualRef, tick_value: i64) -> ResolveOutcome {
        self.resolve(eref, tick_value)
    }

    /// **Drain the continuation into a runnable concrete [`Pipeline`]** — the READY→commit edge.
    ///
    /// Succeeds IFF the continuation is READY (something staged, no open hole). The returned
    /// [`Pipeline`] carries every staged turn (with its dependencies + atomic flag) and is the
    /// caller's to hand to `execute_pipeline` / `World::resume`. While any hole is OPEN this is
    /// [`DrainError::StillHeld`] — the structural fail-closed: a held promise can never reach the
    /// drain. An empty continuation is [`DrainError::Empty`].
    pub fn drain(&self) -> Result<Pipeline, DrainError> {
        if self.is_empty() {
            return Err(DrainError::Empty);
        }
        if self.is_held() {
            return Err(DrainError::StillHeld {
                open_holes: self.open_hole_count(),
            });
        }
        let mut pipeline = Pipeline::new();
        pipeline.turns = self.turns.clone();
        pipeline.dependencies = self.dependencies.clone();
        pipeline.atomic = self.atomic;
        Ok(pipeline)
    }

    /// The bound values, keyed by their hole's `EventualRef` — for the caller that rewrites the
    /// pipeline's `Eventual` targets into concretes before drain, or records the resolution.
    /// Only resolved holes appear.
    pub fn bound_values(&self) -> HashMap<EventualRef, i64> {
        self.holes
            .iter()
            .filter_map(|h| h.value.map(|v| (h.eref.clone(), v)))
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_turn::action::{
        Action, Authorization, CommitmentMode, DelegationMode, Effect,
    };
    use dregg_turn::forest::CallForest;
    use dregg_cell::{CellId, Preconditions};

    fn test_cell(b: u8) -> CellId {
        CellId::derive_raw(&[b; 32], &[0u8; 32])
    }

    /// A minimal real `Turn` (concrete) — the flat-queue body.
    fn concrete_turn(agent: CellId, nonce: u64) -> Turn {
        let action = Action {
            target: agent,
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![],
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
            witness_blobs: vec![],
        };
        let mut forest = CallForest::new();
        forest.add_root(action);
        Turn {
            agent,
            nonce,
            call_forest: forest,
            fee: 0,
            memo: None,
            valid_until: None,
            depends_on: vec![],
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
            previous_receipt_hash: None,
        }
    }

    /// A real PARTIAL turn: a `PipelinedSend` whose target is the eventual `eref` (the hole).
    fn partial_turn(agent: CellId, nonce: u64, eref: EventualRef) -> Turn {
        let inner = Action {
            target: agent,
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![],
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
            witness_blobs: vec![],
        };
        let outer = Action {
            target: agent,
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![Effect::PipelinedSend {
                target: eref,
                action: Box::new(inner),
            }],
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
            witness_blobs: vec![],
        };
        let mut forest = CallForest::new();
        forest.add_root(outer);
        Turn {
            agent,
            nonce,
            call_forest: forest,
            fee: 0,
            memo: None,
            valid_until: None,
            depends_on: vec![],
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
            previous_receipt_hash: None,
        }
    }

    fn demo_eref(slot: u32) -> EventualRef {
        EventualRef::new([7u8; 32], slot)
    }

    // ── Lifecycle: EMPTY → HELD → READY ─────────────────────────────────────────

    #[test]
    fn empty_continuation_is_empty_not_held_not_ready() {
        let c = HeldPipeline::new();
        assert!(c.is_empty());
        assert!(!c.is_held());
        assert!(!c.is_ready());
        assert_eq!(c.drain().unwrap_err(), DrainError::Empty);
    }

    #[test]
    fn all_concrete_continuation_drains_immediately() {
        // The flat-queue case: concrete turns, no holes → READY, drains to a real Pipeline.
        let agent = test_cell(1);
        let mut c = HeldPipeline::new();
        let i0 = c.stage_turn(concrete_turn(agent, 0));
        let i1 = c.stage_turn(concrete_turn(agent, 1));
        c.add_dependency(i1, i0);

        assert!(!c.is_empty());
        assert!(!c.is_held());
        assert!(c.is_ready());

        let pipeline = c.drain().expect("all-concrete drains");
        assert_eq!(pipeline.turns.len(), 2);
        assert_eq!(pipeline.dependencies, vec![(1, 0)]);
        assert!(pipeline.validate().is_ok());
    }

    #[test]
    fn staging_a_partial_turn_holds_the_promise_and_blocks_drain() {
        let agent = test_cell(1);
        let eref = demo_eref(0);
        let mut c = HeldPipeline::new();
        c.stage_partial(
            partial_turn(agent, 0, eref.clone()),
            PipelineHole::open(eref, "balance", 1, 1, Guard::InRange { lo: 1, hi: 100 }),
        );

        assert!(!c.is_empty());
        assert!(c.is_held()); // a promise is held
        assert!(!c.is_ready());
        assert_eq!(c.open_hole_count(), 1);
        // Fail-closed: a held promise CANNOT drain.
        assert_eq!(
            c.drain().unwrap_err(),
            DrainError::StillHeld { open_holes: 1 }
        );
    }

    // ── POSITIVE tooth: a guard-admitted value RESOLVES and reaches READY ────────

    #[test]
    fn guard_admitted_value_resolves_and_drains() {
        let agent = test_cell(1);
        let eref = demo_eref(0);
        let mut c = HeldPipeline::new();
        c.stage_partial(
            partial_turn(agent, 0, eref.clone()),
            PipelineHole::open(eref.clone(), "balance", 1, 1, Guard::InRange { lo: 1, hi: 100 }),
        );

        let outcome = c.resolve(&eref, 50); // 50 ∈ [1,100] → admitted
        assert_eq!(outcome, ResolveOutcome::Bound);
        assert!(outcome.bound());

        // The promise resolved: no open hole → READY → drains to a runnable pipeline.
        assert!(!c.is_held());
        assert!(c.is_ready());
        assert_eq!(c.open_hole_count(), 0);
        let pipeline = c.drain().expect("resolved continuation drains");
        assert_eq!(pipeline.turns.len(), 1);
        assert_eq!(c.bound_values().get(&eref), Some(&50));
    }

    // ── NEGATIVE tooth: a guard-VIOLATING value is REJECTED, fail-closed ─────────

    #[test]
    fn guard_violating_value_is_rejected_and_stays_held() {
        let agent = test_cell(1);
        let eref = demo_eref(0);
        let mut c = HeldPipeline::new();
        c.stage_partial(
            partial_turn(agent, 0, eref.clone()),
            PipelineHole::open(eref.clone(), "balance", 1, 1, Guard::InRange { lo: 1, hi: 100 }),
        );

        let outcome = c.resolve(&eref, 555); // 555 ∉ [1,100] → guard violation
        assert!(matches!(
            outcome,
            ResolveOutcome::GuardViolation { value: 555, .. }
        ));
        assert!(!outcome.bound());

        // Fail-closed: the hole stays OPEN, the continuation stays HELD, CANNOT drain.
        assert!(c.is_held());
        assert!(!c.is_ready());
        assert_eq!(c.open_hole_count(), 1);
        assert_eq!(
            c.drain().unwrap_err(),
            DrainError::StillHeld { open_holes: 1 }
        );
        // No δ bound — the rejected value did not leak into the resolution table.
        assert!(c.bound_values().is_empty());
    }

    // ── One-shot linearity: a resolved hole cannot be re-resolved (no overwrite) ─

    #[test]
    fn double_resolve_is_noop_value_not_overwritten() {
        let agent = test_cell(1);
        let eref = demo_eref(0);
        let mut c = HeldPipeline::new();
        c.stage_partial(
            partial_turn(agent, 0, eref.clone()),
            PipelineHole::open(eref.clone(), "v", 1, 1, Guard::Equals { expected: 42 }),
        );

        assert_eq!(c.resolve(&eref, 42), ResolveOutcome::Bound);
        assert!(c.is_ready());
        // A second resolution finds no OPEN hole — the bound value cannot be silently overwritten.
        assert_eq!(
            c.resolve(&eref, 99),
            ResolveOutcome::NoSuchOpenHole { eref: eref.clone() }
        );
        assert_eq!(c.bound_values().get(&eref), Some(&42));
    }

    #[test]
    fn resolving_unknown_eref_is_noop() {
        let agent = test_cell(1);
        let eref = demo_eref(0);
        let mut c = HeldPipeline::new();
        c.stage_partial(
            partial_turn(agent, 0, eref.clone()),
            PipelineHole::open(eref, "v", 1, 1, Guard::AtLeast { threshold: 0 }),
        );

        let bogus = demo_eref(9);
        assert_eq!(
            c.resolve(&bogus, 1),
            ResolveOutcome::NoSuchOpenHole { eref: bogus }
        );
        assert_eq!(c.open_hole_count(), 1); // the real hole is untouched
        assert!(c.is_held());
    }

    // ── Multi-hole: READY requires ALL holes resolved (one open hole blocks drain) ─

    #[test]
    fn two_holes_one_resolved_still_held() {
        let agent = test_cell(1);
        let e0 = demo_eref(0);
        let e1 = demo_eref(1);
        let mut c = HeldPipeline::new();
        c.stage_partial(
            partial_turn(agent, 0, e0.clone()),
            PipelineHole::open(e0.clone(), "v", 1, 1, Guard::AtLeast { threshold: 10 }),
        );
        c.stage_partial(
            partial_turn(agent, 1, e1.clone()),
            PipelineHole::open(e1.clone(), "v", 1, 1, Guard::AtLeast { threshold: 10 }),
        );

        assert_eq!(c.resolve(&e0, 20), ResolveOutcome::Bound);
        assert!(c.is_held()); // one hole still open → still held
        assert!(!c.is_ready());
        assert_eq!(c.open_hole_count(), 1);
        assert!(c.drain().is_err());

        assert_eq!(c.resolve(&e1, 30), ResolveOutcome::Bound);
        assert!(c.is_ready()); // both resolved → READY
        assert_eq!(c.open_hole_count(), 0);
        assert!(c.drain().is_ok());
    }

    // ── The beacon/quorum-after-t connection (§4): a tick value resolves the hole ─

    #[test]
    fn beacon_tick_resolves_threshold_hole() {
        // A beacon hole's guard is the threshold the tick must reach; the value arrives at quorum.
        let agent = test_cell(1);
        let eref = demo_eref(0);
        let mut c = HeldPipeline::new();
        c.stage_partial(
            partial_turn(agent, 0, eref.clone()),
            PipelineHole::open(eref.clone(), "beacon", 1, 1, Guard::AtLeast { threshold: 100 }),
        );

        // Below the threshold (quorum not yet reached) → fail-closed, stays HELD.
        assert!(matches!(
            c.resolve_at_tick(&eref, 99),
            ResolveOutcome::GuardViolation { .. }
        ));
        assert!(c.is_held());

        // At/above the threshold (quorum-after-t) → resolves, drains.
        assert_eq!(c.resolve_at_tick(&eref, 100), ResolveOutcome::Bound);
        assert!(c.is_ready());
        assert!(c.drain().is_ok());
    }

    // ── Mixed: a concrete turn + a partial turn; drain blocked until the hole fills ─

    #[test]
    fn mixed_concrete_and_partial_drains_only_when_resolved() {
        let agent = test_cell(1);
        let eref = demo_eref(0);
        let mut c = HeldPipeline::new().atomic();
        let i_concrete = c.stage_turn(concrete_turn(agent, 0));
        let i_partial = c.stage_partial(
            partial_turn(agent, 1, eref.clone()),
            PipelineHole::open(eref.clone(), "v", 1, 1, Guard::InRange { lo: 0, hi: 1000 }),
        );
        c.add_dependency(i_partial, i_concrete);

        // The concrete turn is staged but the partial holds a promise → HELD, cannot drain.
        assert!(c.is_held());
        assert!(c.drain().is_err());

        assert_eq!(c.resolve(&eref, 500), ResolveOutcome::Bound);
        let pipeline = c.drain().expect("drains once the hole is resolved");
        assert_eq!(pipeline.turns.len(), 2);
        assert!(pipeline.atomic);
        assert_eq!(pipeline.dependencies, vec![(i_partial, i_concrete)]);
    }

    // ── The eager shape is never mutated by a resolution (lazy witness, eager shape) ─

    #[test]
    fn resolution_binds_value_without_mutating_shape() {
        let agent = test_cell(1);
        let eref = demo_eref(3);
        let mut c = HeldPipeline::new();
        c.stage_partial(
            partial_turn(agent, 0, eref.clone()),
            PipelineHole::open(eref.clone(), "balance", 7, 9, Guard::InRange { lo: 0, hi: 1000 }),
        );

        assert_eq!(c.resolve(&eref, 500), ResolveOutcome::Bound);
        let h = &c.holes[0];
        assert_eq!(h.value, Some(500)); // δ bound
        // shape untouched:
        assert_eq!(h.eref, eref);
        assert_eq!(h.field, "balance");
        assert_eq!(h.actor, 7);
        assert_eq!(h.target, 9);
        assert_eq!(h.guard, Guard::InRange { lo: 0, hi: 1000 });
    }
}
