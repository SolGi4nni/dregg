//! # colonist_job — the executable Rust mirror of a COLONIST'S JOB (ORGAN 2 of the room).
//!
//! The world read as a place: an inhabitant acts ONLY through a MANDATE proven safe-forever, and a
//! workflow-mandate IS a colonist's JOB — a DAG of steps with prerequisites, a per-step clearance,
//! AND a spend budget it provably can't exceed. This module is the executable mirror of the proven
//! Lean job-spec `metatheory/Dregg2/Apps/ColonistJob.lean`: ONE concrete job —
//!
//! ```text
//! gather → make → hand-off
//! ```
//!
//! — driven by the REAL embedded executor (`EmbeddedExecutor` from `dregg-app-framework`), so the
//! colonist advances its cursor through the DAG via genuine signed turns, and the three admission
//! legs BITE in-band:
//!
//!   1. **DAG / no-skip** — `MonotonicSequence(JOB_CURSOR)` (exact `+1`) + `FieldLteField(JOB_CURSOR
//!      <= JOB_TERMINAL)` (no overrun): a skipped prerequisite or a past-terminal advance is a real
//!      executor refusal.
//!   2. **CLEARANCE** — `ClearanceDominates` (root-bound): the acting role's clearance must dominate
//!      the entered verb's compartment in the job graph; a HAULER attempting the `make` (crafting)
//!      verb is refused (mirrors Lean `stepClearanceOK`).
//!   3. **SPEND BUDGET** (the genuinely-new biting leg) — `FieldLteField(SPEND_ACCUM <= BUDGET)`: the
//!      cumulative fuel spent across the job may never exceed the colonist's budget. An OVERSPEND is a
//!      real executor refusal, exactly as a skipped step is (mirrors Lean `jobInBudget`, the leg the
//!      compartment-workflow mandate's decorative `Slice` demo never wove into admission).
//!
//! The predicate-layer hand-port `job_advance_admits` mirrors Lean `jobAdvanceAdmits` (DAG ∧
//! clearance ∧ in-budget) and is pinned against the proven Lean `jobDiffCorpus` by the differential
//! test `tests/colonist_job_lean_differential.rs`. Both polarities are exercised through the REAL
//! executor in `tests/colonist_job_seam.rs`: the colonist advances gather→make→hand-off iff the three
//! legs all pass (genuine ✓); a skip, an out-of-clearance verb, and an overspend are each REFUSED in
//! the submission path (cheat ✗).

#![allow(clippy::needless_range_loop)]

use dregg_app_framework::{
    Action, AppCipherclerk, CellId, CellProgram, Effect, EmbeddedExecutor, Event, FieldElement,
    StateConstraint, TransitionCase, TransitionGuard, field_from_u64, symbol,
};

use std::collections::HashSet;

use crate::{clearance_label, may_read};

// =============================================================================
// The job DAG (gather → make → hand-off) — the colonist's verbs.
// =============================================================================

/// One verb in the colonist's job DAG. Mirrors Lean `jobSteps`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WorkflowVerb {
    /// Step 0 — `gather` compartment (no prerequisites). Cost 3 fuel.
    Gather,
    /// Step 1 — `make` compartment (requires gather). Cost 4 fuel. The CRAFTING verb.
    Make,
    /// Step 2 — `handoff` compartment (requires make). Cost 2 fuel.
    Handoff,
}

impl WorkflowVerb {
    /// Numeric step id (matches Lean `WorkflowStep.id`).
    pub const fn step_id(self) -> u64 {
        match self {
            Self::Gather => 0,
            Self::Make => 1,
            Self::Handoff => 2,
        }
    }

    /// Prerequisite step ids (Lean `WorkflowStep.needs`).
    pub const fn prerequisites(self) -> &'static [u64] {
        match self {
            Self::Gather => &[],
            Self::Make => &[0],
            Self::Handoff => &[1],
        }
    }

    /// Per-step fuel cost (Lean `stepCost`): gather 3, make 4, hand-off 2.
    pub const fn cost(self) -> u64 {
        match self {
            Self::Gather => 3,
            Self::Make => 4,
            Self::Handoff => 2,
        }
    }

    /// Clearance compartment label (Lean `WorkflowStep.compartment`).
    pub fn compartment_label(self) -> FieldElement {
        match self {
            Self::Gather => clearance_label("gather"),
            Self::Make => clearance_label("make"),
            Self::Handoff => clearance_label("handoff"),
        }
    }

    /// All verbs in job order.
    pub const JOB: [Self; 3] = [Self::Gather, Self::Make, Self::Handoff];

    /// The verb at a given cursor position, if within the job.
    pub fn at_cursor(cursor: u64) -> Option<Self> {
        Self::JOB.get(cursor as usize).copied()
    }
}

/// Job terminal (3 verbs: gather → make → hand-off). Mirrors Lean `jobSteps.length`.
pub const JOB_TERMINAL: u64 = 3;

/// The full budget that admits the whole job (3+4+2 = 9). Mirrors Lean `fullBudget`.
pub const FULL_BUDGET: u64 = 9;

/// A tight budget that admits gather (3) but NOT make (3+4 = 7 > 6). Mirrors Lean `tightBudget`.
pub const TIGHT_BUDGET: u64 = 6;

// =============================================================================
// Acting roles — the colonist's clearance.
// =============================================================================

/// The crafter clearance label — clears every verb (may run the whole job). Lean `crafterLabel`.
pub fn crafter_label() -> FieldElement {
    clearance_label("crafter")
}

/// The hauler clearance label — clears only gather + hand-off (REFUSED at `make`). Lean `haulerLabel`.
pub fn hauler_label() -> FieldElement {
    clearance_label("hauler")
}

/// **The job clearance graph** — `(dominator, dominated)` edges of Lean `jobGraph`:
/// crafter ⊐ {gather, make, handoff}, hauler ⊐ {gather, handoff}. The crafter clears the crafting
/// verb; the hauler does not. This is the graph the job cell commits in its clearance-root slot and
/// the executor's `ClearanceDominates` walks.
pub fn job_clearance_graph() -> Vec<(FieldElement, FieldElement)> {
    vec![
        (crafter_label(), WorkflowVerb::Gather.compartment_label()),
        (crafter_label(), WorkflowVerb::Make.compartment_label()),
        (crafter_label(), WorkflowVerb::Handoff.compartment_label()),
        (hauler_label(), WorkflowVerb::Gather.compartment_label()),
        (hauler_label(), WorkflowVerb::Handoff.compartment_label()),
    ]
}

/// The canonical commitment of the job clearance graph — the value the job cell pins and the
/// executor's `ClearanceDominates` recomputes + compares (load-bearing root).
pub fn job_clearance_root() -> FieldElement {
    dregg_app_framework::clearance_graph_root(&job_clearance_graph())
}

// =============================================================================
// Predicate-layer admission (the hand-port of Lean jobAdvanceAdmits).
// =============================================================================

/// Completed step ids implied by the monotonic cursor (Lean `completedOf`). A set —
/// membership is the only query, so the admission check is O(1) per prerequisite.
pub fn completed_of(cursor: u64) -> HashSet<u64> {
    (0..cursor).collect()
}

/// **`step_admissible`** — DAG prerequisites satisfied and target not yet done (Lean
/// `stepAdmissible`): all `needs` ∈ `completed`, and `step_id ∉ completed`.
pub fn step_admissible(verb: WorkflowVerb, completed: &HashSet<u64>) -> bool {
    verb.prerequisites()
        .iter()
        .all(|need| completed.contains(need))
        && !completed.contains(&verb.step_id())
}

/// **`step_clearance_ok`** — the acting role's labels CLEAR the verb's compartment in the job
/// clearance graph (Lean `stepClearanceOK`): some held label dominates the verb compartment via the
/// reflexive-transitive closure. Decided the SAME way as the executor's `ClearanceDominates` tooth
/// (both walk [`dominates`]).
pub fn step_clearance_ok(verb: WorkflowVerb, actor_labels: &[FieldElement]) -> bool {
    may_read(
        &job_clearance_graph(),
        actor_labels,
        verb.compartment_label(),
    )
}

/// Cumulative fuel spent across the completed prefix `0..cursor` (Lean `spentThrough`).
pub fn spent_through(cursor: u64) -> u64 {
    (0..cursor)
        .filter_map(WorkflowVerb::at_cursor)
        .map(|v| v.cost())
        .sum()
}

/// **`job_in_budget`** — entering the verb AT `cursor` keeps the spend within `budget`: the prefix
/// already spent PLUS this verb's cost is `<= budget` (Lean `jobInBudget`). The genuinely-new leg.
pub fn job_in_budget(budget: u64, cursor: u64) -> bool {
    match WorkflowVerb::at_cursor(cursor) {
        Some(v) => spent_through(cursor) + v.cost() <= budget,
        // Past the job there is no verb to enter; nothing to spend (the DAG-bounds leg rejects it).
        None => true,
    }
}

/// **`job_advance_admits`** — predicate-level one-step admission folding DAG ∧ clearance ∧ in-budget
/// (Lean `jobAdvanceAdmits`). The colonist may advance at `cursor` iff: the cursor is within the
/// terminal, the verb's prerequisites are complete and the verb is not yet done, the acting role
/// clears the verb's compartment, AND the verb keeps the job within budget. Returns the entered verb.
pub fn job_advance_admits(
    cursor: u64,
    terminal: u64,
    budget: u64,
    actor_labels: &[FieldElement],
) -> Option<WorkflowVerb> {
    if cursor >= terminal {
        return None;
    }
    let verb = WorkflowVerb::at_cursor(cursor)?;
    let completed = completed_of(cursor);
    if step_admissible(verb, &completed)
        && step_clearance_ok(verb, actor_labels)
        && job_in_budget(budget, cursor)
    {
        Some(verb)
    } else {
        None
    }
}

// =============================================================================
// Slot layout (the job cell).
// =============================================================================

/// Slot 0 — `job_cursor`. Advanced exactly +1 per `advance_step`.
pub const JOB_CURSOR_SLOT: u8 = 0;
/// Slot 1 — `job_terminal`. Immutable upper bound on the cursor (the DAG length).
pub const JOB_TERMINAL_SLOT: u8 = 1;
/// Slot 2 — `clearance_graph_root`. Immutable Merkle root over the job clearance edges.
pub const CLEARANCE_GRAPH_ROOT_SLOT: u8 = 2;
/// Slot 3 — `budget`. Immutable total spend budget the job draws against.
pub const BUDGET_SLOT: u8 = 3;
/// Slot 4 — `spend_accum`. Cumulative fuel spent so far (monotone; bounded by `budget`).
pub const SPEND_ACCUM_SLOT: u8 = 4;
/// Slot 5 — `actor_clearance`. The acting role's clearance label (bound per advancing turn).
pub const ACTOR_CLEARANCE_SLOT: u8 = 5;
/// Slot 6 — `step_compartment`. The compartment of the verb being entered (bound per turn).
pub const STEP_COMPARTMENT_SLOT: u8 = 6;

// =============================================================================
// The job cell program — the three biting legs.
// =============================================================================

/// The root-bound clearance constraint the executor re-enforces on every `advance_step`: the actor
/// clearance dominates the entered verb's compartment in the job graph whose commitment must equal
/// the stored root. Mirrors Lean `stepClearanceOK` made an inline tooth.
pub fn clearance_dominates_constraint() -> StateConstraint {
    StateConstraint::ClearanceDominates {
        actor_label_index: ACTOR_CLEARANCE_SLOT,
        box_index: STEP_COMPARTMENT_SLOT,
        root_index: CLEARANCE_GRAPH_ROOT_SLOT,
        edges: job_clearance_graph(),
    }
}

/// **The job cell program** — the three admission legs as executor-enforced constraints:
///
///   - `Always` invariants: the config slots (`job_terminal`, `clearance_graph_root`, `budget`) are
///     `WriteOnce` (bound once at seed, frozen); `FieldLteField(JOB_CURSOR <= JOB_TERMINAL)` (no
///     overrun); and **`FieldLteField(SPEND_ACCUM <= BUDGET)` — THE BUDGET TOOTH** (the cumulative
///     spend may never exceed the budget); `spend_accum` is `Monotonic` (spend never un-spends).
///   - `advance_step`-scoped: `MonotonicSequence(JOB_CURSOR)` (exact `+1`, no skip/repeat/rewind) +
///     the root-bound clearance tooth.
///
/// So an overspend, a skip, a past-terminal advance, and an out-of-clearance verb are ALL real
/// executor refusals on the produced transition.
pub fn job_cell_program() -> CellProgram {
    CellProgram::Cases(vec![
        TransitionCase {
            guard: TransitionGuard::Always,
            constraints: vec![
                StateConstraint::WriteOnce {
                    index: JOB_TERMINAL_SLOT,
                },
                StateConstraint::WriteOnce {
                    index: CLEARANCE_GRAPH_ROOT_SLOT,
                },
                StateConstraint::WriteOnce { index: BUDGET_SLOT },
                StateConstraint::FieldLteField {
                    left_index: JOB_CURSOR_SLOT,
                    right_index: JOB_TERMINAL_SLOT,
                },
                // THE BUDGET TOOTH (Lean `jobInBudget`): cumulative spend <= budget. An overspend
                // (the spend accumulator passing the pinned budget) is refused on the post-state.
                StateConstraint::FieldLteField {
                    left_index: SPEND_ACCUM_SLOT,
                    right_index: BUDGET_SLOT,
                },
                // Spend never un-spends (anti-rollback on the accumulator).
                StateConstraint::Monotonic {
                    index: SPEND_ACCUM_SLOT,
                },
            ],
        },
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol("advance_step"),
            },
            constraints: vec![
                StateConstraint::MonotonicSequence {
                    seq_index: JOB_CURSOR_SLOT,
                },
                clearance_dominates_constraint(),
            ],
        },
    ])
}

// =============================================================================
// Turn builders.
// =============================================================================

/// **`advance_effects`** — the multi-effect advance body entering the verb at `new_cursor` (the verb
/// whose `step_id == new_cursor - 1`): advance `JOB_CURSOR` to `new_cursor` (`MonotonicSequence`
/// enforces the exact `+1`), set `SPEND_ACCUM` to the new cumulative fuel (the budget tooth checks it
/// against `BUDGET`), materialize the actor clearance + the entered verb's compartment (the clearance
/// tooth reads them from post-state), and emit `job-step-advanced`. This is the ONE coherent
/// transition the installed program admits when all three legs pass.
pub fn advance_effects(
    cell: CellId,
    new_cursor: u64,
    actor_clearance: FieldElement,
    verb_compartment: FieldElement,
) -> Vec<Effect> {
    // The new cumulative spend = spend through the prefix INCLUDING the verb just entered.
    let new_spend = spent_through(new_cursor);
    let old_field = field_from_u64(new_cursor.saturating_sub(1));
    let new_field = field_from_u64(new_cursor);
    vec![
        Effect::SetField {
            cell,
            index: JOB_CURSOR_SLOT as usize,
            value: new_field,
        },
        Effect::SetField {
            cell,
            index: SPEND_ACCUM_SLOT as usize,
            value: field_from_u64(new_spend),
        },
        Effect::SetField {
            cell,
            index: ACTOR_CLEARANCE_SLOT as usize,
            value: actor_clearance,
        },
        Effect::SetField {
            cell,
            index: STEP_COMPARTMENT_SLOT as usize,
            value: verb_compartment,
        },
        Effect::EmitEvent {
            cell,
            event: Event::new(
                symbol("job-step-advanced"),
                vec![
                    old_field,
                    new_field,
                    field_from_u64(new_spend),
                    verb_compartment,
                ],
            ),
        },
    ]
}

/// The compartment label of the verb ENTERED at `cursor` (the verb whose `step_id == cursor - 1`).
fn verb_compartment_for(cursor: u64) -> FieldElement {
    cursor
        .checked_sub(1)
        .and_then(WorkflowVerb::at_cursor)
        .map(|v| v.compartment_label())
        .unwrap_or([0u8; 32])
}

/// Build the on-ledger `advance_step` action entering the verb at `current_cursor + 1`, presenting
/// `actor_clearance` as the acting role's clearance.
pub fn build_advance_step_action(
    cipherclerk: &AppCipherclerk,
    job_cell: CellId,
    current_cursor: u64,
    actor_clearance: FieldElement,
) -> Action {
    let new_cursor = current_cursor + 1;
    let effects = advance_effects(
        job_cell,
        new_cursor,
        actor_clearance,
        verb_compartment_for(new_cursor),
    );
    cipherclerk.make_action(job_cell, "advance_step", effects)
}

// =============================================================================
// Executor driving — seed + advance through the REAL embedded executor.
// =============================================================================

/// **Seed the JOB cell** so the program bites: install [`job_cell_program`], then bind the config
/// (`job_terminal`, `clearance_graph_root`, `budget` — `WriteOnce`, frozen after), set `job_cursor =
/// 0` and `spend_accum = 0`. Returns the seeded budget.
pub fn seed_job(
    executor: &EmbeddedExecutor,
    terminal: u64,
    clearance_root: FieldElement,
    budget: u64,
) -> u64 {
    let cell = executor.cell_id();
    executor.install_program(cell, job_cell_program());
    executor.with_ledger_mut(|ledger| {
        if let Some(c) = ledger.get_mut(&cell) {
            c.state
                .set_field(JOB_TERMINAL_SLOT as usize, field_from_u64(terminal));
            c.state
                .set_field(CLEARANCE_GRAPH_ROOT_SLOT as usize, clearance_root);
            c.state
                .set_field(BUDGET_SLOT as usize, field_from_u64(budget));
            c.state
                .set_field(JOB_CURSOR_SLOT as usize, field_from_u64(0));
            c.state
                .set_field(SPEND_ACCUM_SLOT as usize, field_from_u64(0));
        }
    });
    budget
}

/// Read a `u64` from the last 8 big-endian bytes of a field element (inverse of `field_from_u64`).
pub fn field_to_u64(f: &FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&f[24..32]);
    u64::from_be_bytes(b)
}

/// **Advance the colonist's job by one step through the REAL executor** — read the live cursor, build
/// the full advance turn (cursor + spend + clearance materialization), submit it as a signed action.
/// The executor RE-ENFORCES [`job_cell_program`], so a skip (`MonotonicSequence`), a past-terminal
/// advance (`FieldLteField(cursor <= terminal)`), an out-of-clearance verb (`ClearanceDominates`),
/// and an OVERSPEND (`FieldLteField(spend_accum <= budget)`) are each refused in-band. Returns the
/// turn receipt on commit, or the executor's rejection on any violated leg.
pub fn advance_job_step(
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
    actor_clearance: FieldElement,
) -> Result<dregg_app_framework::TurnReceipt, dregg_app_framework::ExecutorSubmitError> {
    let cell = cipherclerk.cell_id();
    let live = executor.cell_state(cell).expect("seeded job cell exists");
    let live_cursor = field_to_u64(&live.fields[JOB_CURSOR_SLOT as usize]);
    let next = live_cursor + 1;
    let effects = advance_effects(cell, next, actor_clearance, verb_compartment_for(next));
    let action = cipherclerk.make_action(cell, "advance_step", effects);
    executor.submit_action(cipherclerk, action)
}

// =============================================================================
// Differential corpus (the Rust-mirror drift tooth — pinned against Lean jobDiffCorpus).
// =============================================================================

/// Crafter clearance labels (clears every verb). Mirrors Lean `crafterJob.actorLabels`.
pub fn crafter_labels() -> Vec<FieldElement> {
    vec![crafter_label()]
}

/// Hauler clearance labels (clears only gather + hand-off). Mirrors Lean `haulerJob.actorLabels`.
pub fn hauler_labels() -> Vec<FieldElement> {
    vec![hauler_label()]
}

/// The diagonal admit-decision vector over the three job specs × cursors `{0,1,2,3}`, row-major —
/// the EXACT shape of Lean `jobDiffCorpus`. Specs: (crafter, full budget), (hauler, full budget),
/// (crafter, tight budget). The Rust differential test asserts this equals the Lean-pinned literal.
pub fn job_diff_corpus() -> Vec<bool> {
    let specs: [(Vec<FieldElement>, u64); 3] = [
        (crafter_labels(), FULL_BUDGET),
        (hauler_labels(), FULL_BUDGET),
        (crafter_labels(), TIGHT_BUDGET),
    ];
    let mut out = Vec::with_capacity(12);
    for (labels, budget) in &specs {
        for cursor in 0..4u64 {
            out.push(job_advance_admits(cursor, JOB_TERMINAL, *budget, labels).is_some());
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dag_admission_matches_lean() {
        // gather admits with no prereq; make needs gather; hand-off needs make.
        assert!(step_admissible(WorkflowVerb::Gather, &HashSet::new()));
        assert!(!step_admissible(WorkflowVerb::Make, &HashSet::new()));
        assert!(step_admissible(WorkflowVerb::Make, &HashSet::from([0])));
        assert!(step_admissible(
            WorkflowVerb::Handoff,
            &HashSet::from([0, 1])
        ));
    }

    #[test]
    fn budget_arithmetic_matches_lean() {
        assert_eq!(spent_through(0), 0);
        assert_eq!(spent_through(1), 3); // gather
        assert_eq!(spent_through(2), 7); // gather + make
        assert!(job_in_budget(FULL_BUDGET, 2)); // 7 + 2 = 9 <= 9
        assert!(!job_in_budget(TIGHT_BUDGET, 1)); // 3 + 4 = 7 > 6
    }

    #[test]
    fn clearance_bites_at_make_for_hauler() {
        let hauler = hauler_labels();
        assert!(step_clearance_ok(WorkflowVerb::Gather, &hauler));
        assert!(!step_clearance_ok(WorkflowVerb::Make, &hauler));
        assert!(step_clearance_ok(WorkflowVerb::Handoff, &hauler));
    }
}
