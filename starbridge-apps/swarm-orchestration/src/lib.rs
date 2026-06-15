//! # starbridge-swarm-orchestration
//!
//! **A verifiable agent-orchestration swarm** — multi-agent task coordination where the
//! coordination is cap-secured, receipted, and verifiable, run through the REAL verified executor.
//!
//! An agent loop (perceive / plan / act / reflect) lives ABOVE dregg and is the integrator's game.
//! dregg owns the ONE seam that matters — the tool-call / turn boundary — and this app makes that
//! seam legible: every coordinating action is a verified turn leaving a receipt, every dispatch is
//! bounded by a real capability, every spend is metered against a conserved budget, and an
//! over-reaching member is REFUSED by the executor, the no-amplification guarantee firing at the
//! swarm layer exactly as it fires for a transfer.
//!
//! This is the executable surface of two verified Lean developments:
//!
//! | Lean keystone                              | What it guarantees / What this crate enforces |
//! |--------------------------------------------|-----------------------------------------------|
//! | `AgentOrchestrationBudget.dispatchConstraints` | the dispatch-board POLICY as ONE program: budget + provenance + no-replay |
//! | `…affineLe [(1,spentA),(1,spentB)] mandate`    | **atomic budget**: `spent_a + spent_b <= budget` — an over-budget dispatch is UNSAT |
//! | `…immutable budgetF`                           | the mandate, once set, cannot be quietly widened mid-swarm |
//! | `…strictMono epochF`                           | **no replay**: every dispatch strictly advances the epoch |
//! | `…senderInField leadF`                         | signed provenance: a dispatch must come FROM the recorded lead |
//! | `AgentOrchestration.worker_authority_subset_orchestrator` | **non-amplification**: a worker's reach ⊆ the coordinator's (`derive_no_amplify`) |
//! | `AgentOrchestration.workForest_conserves`      | the swarm's value moves conserve (no mint/burn) |
//!
//! ## The two cells (the swarm's substrate)
//!
//! **The COORDINATOR — a dispatch-board cell.** Factory-born, its installed [`CellProgram`] IS the
//! swarm policy, re-checked by the verified executor on EVERY turn that touches it:
//!
//!   * `LEAD`     — the appointed coordinator's identity (the signed-provenance anchor); `WriteOnce`.
//!   * `BUDGET`   — the swarm's spend mandate (the conserved ceiling); `WriteOnce` — never widened.
//!   * `SPENT_A`  — worker-A's cumulative dispatched spend; `Monotonic` — never rolled back.
//!   * `SPENT_B`  — worker-B's cumulative dispatched spend; `Monotonic`.
//!   * `EPOCH`    — the strictly-monotone dispatch counter; `StrictMonotonic` — no replay.
//!
//! and the LIFE-OF-CELL budget gate: `AffineLe { spent_a + spent_b - budget <= 0 }` — the swarm can
//! NEVER collectively dispatch more than its mandate. A dispatch that would breach it is REFUSED by
//! the executor BEFORE it commits (fail-closed, no height advance).
//!
//! **The WORKERS — agent cells.** Each worker holds an ATTENUATED capability: the coordinator hands
//! a worker ONLY its sub-task's authority (a cap reaching exactly the cells the sub-task touches, at
//! exactly the rights it needs). A worker cannot exceed the authority it was handed
//! ([`SwarmError::OutOfMandate`], the executor's c-list gate); and a coordinator cannot hand a
//! worker MORE budget than the swarm's mandate (the `AffineLe` tooth).
//!
//! ## The async notify edge (coordination without synchronization)
//!
//! Workers coordinate via the async notify edge: the coordinator's dispatch carries an
//! `Effect::EmitEvent` targeting a worker, which deposits a pending wake in that worker's inbox; the
//! worker DRAINS it in its OWN, separate, receipted turn (a `SetField` ack). The two receipts are
//! INDEPENDENT on-ledger records — causality (coordinator → worker) is visible, synchronization is
//! NOT forced. The corrected `--wake` model: ASYNC ("recipient drains next turn"), not a joint turn.
//!
//! ## The narration-vs-truth property
//!
//! What the swarm DID is provable, not what it claims. The loop could lie about "I was authorized",
//! "I did X", "I stayed within budget" — but the cap-gate REFUSAL, the executor's receipt + the
//! `EventEmitted` dynamics, and the conserved spend against the mandate are the on-ledger truth.
//! An operator audits a swarm she did not write and could not trust, and is nonetheless never fooled.
//!
//! ## Pre-submission assurance (`dregg-userspace-verify`)
//!
//! Before a dispatch forest is submitted, it is linted by the userspace `analyze()` toolkit —
//! conservation (the value moves net to zero per asset), non-amplification (no in-forest grant
//! exceeds a delegated cap), and well-formedness — so a stranger can pre-flight the swarm's plan and
//! SEE it pass (or see a malformed plan's findings) before spending gas. See `tests/userspace_verify.rs`.

#![forbid(unsafe_code)]

use dregg_app_framework::{
    Action, AppCipherclerk, AuthRequired, CapTarget, CapTemplate, CapabilityRef, CellAffordance,
    CellId, CellMode, CellProgram, ChildVkStrategy, ConstantsModule, DeosApp, DeosCell, Effect,
    EmbeddedExecutor, Event, FactoryDescriptor, FieldElement, FireError, FireExecuteError,
    GatedAffordance, InspectorDescriptor, StarbridgeAppContext, StateConstraint, TurnReceipt,
    canonical_program_vk, field_from_u64, hex_encode_32, symbol,
};

pub use dregg_app_framework::field_from_bytes;

// =============================================================================
// Slot layout (the coordinator dispatch-board cell) — mirrors the Lean
// `AgentOrchestrationBudget` field names (`leadF`/`budgetF`/`spentAF`/`spentBF`/`epochF`).
// =============================================================================

/// Slot 0 — `LEAD`. The appointed coordinator's identity scalar (the signed-provenance anchor).
/// `WriteOnce`: bound once at board open (from zero), frozen thereafter. The Lean `leadF`.
pub const LEAD_SLOT: u8 = 0;
/// Slot 1 — `BUDGET`. The swarm's spend mandate (the conserved ceiling). `WriteOnce`: bound once at
/// board open, never widened mid-swarm. The Lean `budgetF`.
pub const BUDGET_SLOT: u8 = 1;
/// Slot 2 — `SPENT_A`. Worker-A's cumulative dispatched spend. `Monotonic`: never rolled back to
/// forge head-room. The Lean `spentAF`.
pub const SPENT_A_SLOT: u8 = 2;
/// Slot 3 — `SPENT_B`. Worker-B's cumulative dispatched spend. `Monotonic`. The Lean `spentBF`.
pub const SPENT_B_SLOT: u8 = 3;
/// Slot 4 — `EPOCH`. The strictly-monotone dispatch counter (no replay). `StrictMonotonic`: every
/// dispatch advances it. The Lean `epochF`.
pub const EPOCH_SLOT: u8 = 4;

/// The number of worker spend-meters the board tracks (A and B). The two-meter budget is what no
/// single-field counter sees — it is the affine-sum bound `spent_a + spent_b <= budget`.
pub const WORKER_METERS: usize = 2;

// =============================================================================
// The dispatch policy (the Lean `dispatchConstraints` mirror).
// =============================================================================

/// The swarm orchestration POLICY as a flat conjunction of slot caveats — the Rust transcription of
/// the Lean `AgentOrchestrationBudget.dispatchConstraints`. THIS is the exact predicate the executor
/// installs as the factory-born coordinator's `CellProgram` (`CellProgram::Predicate`) and re-checks
/// on EVERY turn that touches the board. Each clause is a primitive of the integrator wedge; each
/// refusal is a theorem on the Lean side and a real executor refusal here:
///
///   * **atomic budget** (`AffineLe`): `spent_a + spent_b - budget <= 0`, i.e. the swarm's total
///     declared spend never exceeds its mandate. An over-budget runaway is REFUSED; the whole turn
///     aborts (it is ONE predicate). The Lean `affineLe [(1,spentAF),(1,spentBF)] mandate`.
///   * **write-once mandate** (`WriteOnce BUDGET`): the ceiling is bound ONCE at board open (from
///     zero) then frozen — never widened mid-swarm. The Lean `immutable budgetF` (in the
///     birth-compatible form: a factory-born cell is born empty, so `Immutable` would freeze BUDGET
///     AT ZERO and refuse the open turn itself — mirror tool-access-delegation / bounty-board).
///   * **write-once lead** (`WriteOnce LEAD`): the appointed coordinator's identity is bound once at
///     board open then frozen — a rogue cannot recapture the provenance anchor. (Sender-binding to
///     this identity is the §8 crypto portal, the named seam; the slot pins WHO the lead is.)
///   * **monotone meters** (`Monotonic SPENT_A/SPENT_B`): a worker's cumulative spend only
///     accumulates; it can never be rolled back to forge budget head-room.
///   * **no replay** (`StrictMonotonic EPOCH`): every touching turn strictly advances the epoch; a
///     replayed (same / stale epoch) dispatch is REFUSED. The Lean `strictMono epochF`. (The board
///     opens at epoch 1 so the open turn itself strictly advances 0 -> 1; dispatches go 1 -> 2 -> …)
pub fn swarm_constraints() -> Vec<StateConstraint> {
    vec![
        // (3) ATOMIC BUDGET — spent_a + spent_b <= budget (the affine sum, the two-meter bound).
        StateConstraint::AffineLe {
            terms: vec![(1, SPENT_A_SLOT), (1, SPENT_B_SLOT), (-1, BUDGET_SLOT)],
            c: 0,
        },
        // the mandate is bound once at open (from zero) then frozen — never quietly widened.
        StateConstraint::WriteOnce { index: BUDGET_SLOT },
        // the appointed lead's identity is bound once at open then frozen (the provenance anchor).
        StateConstraint::WriteOnce { index: LEAD_SLOT },
        // the per-worker meters only accumulate (never roll back to forge head-room).
        StateConstraint::Monotonic {
            index: SPENT_A_SLOT,
        },
        StateConstraint::Monotonic {
            index: SPENT_B_SLOT,
        },
        // (no replay) every touching turn strictly advances the epoch.
        StateConstraint::StrictMonotonic { index: EPOCH_SLOT },
    ]
}

/// The COORDINATOR dispatch-board program — `swarm_constraints` as a `CellProgram::Predicate`,
/// identical to what the factory installs on the born cell (so the program VK names the exact
/// installed predicate).
pub fn coordinator_program() -> CellProgram {
    CellProgram::Predicate(swarm_constraints())
}

/// Canonical child program VK for the coordinator dispatch-board cell.
pub fn coordinator_child_program_vk() -> [u8; 32] {
    canonical_program_vk(&coordinator_program())
}

// =============================================================================
// Factory configuration (the dispatch-board factory).
// =============================================================================

/// The factory VK we publish for the swarm-orchestration coordinator factory.
pub const SWARM_FACTORY_VK: [u8; 32] = *b"starbridge-swarm-orchestr-factry";

/// Default per-epoch creation budget for the coordinator factory.
pub const DEFAULT_CREATION_BUDGET: u64 = 256;

/// Hash an agent identity string to its field-scalar value (the board stores `LEAD` as this scalar
/// — the Rust image of the Lean `leadPk` identity scalar).
pub fn identity_field(agent: &str) -> FieldElement {
    field_from_bytes(agent.as_bytes())
}

/// Build the [`FactoryDescriptor`] for swarm-orchestration coordinator (dispatch-board) cells.
///
/// A factory-born coordinator is born EMPTY; the `open_board` turn binds `LEAD` + `BUDGET` (from
/// zero, under `WriteOnce` — the birth-compatible "fixed at open" form) before any dispatch, and the
/// budget gate + meters + epoch caveats are installed at birth FOR LIFE (mirror
/// privacy-voting/bounty-board/tool-access-delegation: born empty, bound by the first turn, frozen).
pub fn swarm_factory_descriptor() -> FactoryDescriptor {
    FactoryDescriptor {
        factory_vk: SWARM_FACTORY_VK,
        child_program_vk: Some(coordinator_child_program_vk()),
        child_vk_strategy: Some(ChildVkStrategy::Fixed(Some(coordinator_child_program_vk()))),
        allowed_cap_templates: vec![CapTemplate {
            target: CapTarget::SelfCell,
            // The coordinator holds an attenuatable SelfCell cap — the ocap handle the swarm
            // operator dispatches under. Sub-delegation to workers narrows it (no amplification).
            max_permissions: AuthRequired::Signature,
            attenuatable: true,
        }],
        // Born empty: the `open_board` turn binds LEAD + BUDGET from zero under `WriteOnce`.
        field_constraints: vec![],
        // The life-of-cell swarm policy, installed at birth as the born cell's
        // `CellProgram::Predicate` and re-checked by the executor on every touching turn. This is
        // EXACTLY `swarm_constraints()` (and `coordinator_program()`'s predicate), so the advertised
        // program VK names the installed predicate byte-for-byte.
        state_constraints: swarm_constraints(),
        default_mode: CellMode::Sovereign,
        creation_budget: Some(DEFAULT_CREATION_BUDGET),
    }
}

/// All factory descriptors this starbridge-app contributes.
pub fn factory_descriptors() -> Vec<FactoryDescriptor> {
    vec![swarm_factory_descriptor()]
}

// =============================================================================
// The worker meter index (which spend-slot a worker draws against).
// =============================================================================

/// Which of the two worker meters a dispatch advances. The coordinator dispatches a sub-task to
/// exactly one worker; the worker's meter is the column the budget gate sums.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Worker {
    /// Worker A — its cumulative spend lives in `SPENT_A`.
    A,
    /// Worker B — its cumulative spend lives in `SPENT_B`.
    B,
}

impl Worker {
    /// The board slot this worker's cumulative spend accumulates in.
    pub fn spend_slot(self) -> u8 {
        match self {
            Worker::A => SPENT_A_SLOT,
            Worker::B => SPENT_B_SLOT,
        }
    }

    /// A short legible label for the activity feed / event topics.
    pub fn label(self) -> &'static str {
        match self {
            Worker::A => "worker-a",
            Worker::B => "worker-b",
        }
    }
}

// =============================================================================
// The off-ledger budget pre-check (fail-closed BEFORE the turn runs).
// =============================================================================

/// Whether a dispatch advancing `worker`'s meter from `prev_spent` by `cost`, given the OTHER
/// worker's current spend `other_spent`, would stay within `budget`. This is the userspace,
/// artifact-only mirror of the executor's `AffineLe` gate: `prev_spent + cost + other_spent <=
/// budget`. The coordinator checks this BEFORE building the turn (fail-closed — it does not even
/// submit an over-budget dispatch), AND the executor independently re-checks it on commit (the real
/// gate — even if the pre-check is wrong, the over-budget dispatch is refused). Two gates that
/// provably agree (the Lean `affineLe` is the single source of truth).
pub fn dispatch_within_budget(prev_spent: u64, cost: u64, other_spent: u64, budget: u64) -> bool {
    // saturating to avoid wrap; the executor reads the same big-endian u64 sum lifted to i128.
    prev_spent.saturating_add(cost).saturating_add(other_spent) <= budget
}

// =============================================================================
// Turn builders — OPEN BOARD / DISPATCH / DRAIN.
// =============================================================================

/// **OPEN BOARD** — the swarm operator opens the dispatch board by pinning the `LEAD` identity and
/// the `BUDGET` mandate (`WriteOnce`: bound once from zero, frozen thereafter), the two worker meters
/// born at 0, and the epoch advanced to 1 (so the open turn itself satisfies `StrictMonotonic(EPOCH)`,
/// 0 -> 1). Mirrors the initial board state in the Lean `AgentOrchestrationBudget`.
pub fn build_open_board_action(
    cipherclerk: &AppCipherclerk,
    board: CellId,
    lead: &str,
    budget: u64,
) -> Action {
    let effects = vec![
        Effect::SetField {
            cell: board,
            index: LEAD_SLOT as usize,
            value: identity_field(lead),
        },
        Effect::SetField {
            cell: board,
            index: BUDGET_SLOT as usize,
            value: field_from_u64(budget),
        },
        Effect::SetField {
            cell: board,
            index: SPENT_A_SLOT as usize,
            value: field_from_u64(0),
        },
        Effect::SetField {
            cell: board,
            index: SPENT_B_SLOT as usize,
            value: field_from_u64(0),
        },
        // open at epoch 1 — the open turn itself strictly advances the epoch 0 -> 1 (so the
        // `StrictMonotonic(EPOCH)` no-replay caveat holds on the very first touch); dispatches then
        // go 1 -> 2 -> 3 -> ….
        Effect::SetField {
            cell: board,
            index: EPOCH_SLOT as usize,
            value: field_from_u64(1),
        },
        Effect::EmitEvent {
            cell: board,
            event: Event::new(
                symbol("swarm-board-opened"),
                vec![identity_field(lead), field_from_u64(budget)],
            ),
        },
    ];
    cipherclerk.make_action(board, "open_board", effects)
}

/// **DISPATCH** — the coordinator dispatches a sub-task to `worker`: it advances the worker's
/// cumulative spend meter by `cost`, advances the epoch (no-replay), and (the async notify edge)
/// EMITS a wake targeting the worker cell carrying the sub-task topic. The executor admits this IFF
/// the budget gate holds (`spent_a + spent_b <= budget`), the epoch strictly advances, and the
/// meters are monotone — exactly the Lean dispatch gate.
///
/// `prev_spent` is the worker's current meter value; `new_epoch` is the strictly-greater epoch;
/// `worker_cell` is the worker agent cell the wake targets (the coordination edge); `topic` labels
/// the sub-task.
#[allow(clippy::too_many_arguments)]
pub fn build_dispatch_action(
    cipherclerk: &AppCipherclerk,
    board: CellId,
    worker: Worker,
    worker_cell: CellId,
    prev_spent: u64,
    cost: u64,
    new_epoch: u64,
    topic: &str,
) -> Action {
    let new_spent = prev_spent.saturating_add(cost);
    let effects = vec![
        // advance the worker's cumulative spend meter (Monotonic; summed by the budget gate).
        Effect::SetField {
            cell: board,
            index: worker.spend_slot() as usize,
            value: field_from_u64(new_spent),
        },
        // advance the dispatch epoch (StrictMonotonic — no replay).
        Effect::SetField {
            cell: board,
            index: EPOCH_SLOT as usize,
            value: field_from_u64(new_epoch),
        },
        // the ASYNC NOTIFY EDGE: wake the worker cell with the sub-task topic. The worker drains
        // this in its OWN separate receipted turn — causality visible, synchronization not forced.
        Effect::EmitEvent {
            cell: worker_cell,
            event: Event::new(
                symbol(&format!("dispatch/{}", topic)),
                vec![field_from_u64(cost), field_from_u64(new_epoch)],
            ),
        },
    ];
    cipherclerk.make_action(board, "dispatch", effects)
}

/// **DRAIN (the worker's own ack turn)** — the worker acknowledges a dispatch wake by writing a
/// content-addressed ack into its own cell. This is the async drain: the wake was deposited by the
/// COORDINATOR's committed dispatch; the drain is a WHOLLY INDEPENDENT future turn by the WORKER,
/// with its OWN receipt. `ack_slot` is the worker's ack counter; `wake_digest` is a content address
/// of the dispatch the worker is acknowledging (e.g. the dispatch topic hash). A cell always reaches
/// itself, so the drain is always in-mandate.
pub fn build_drain_action(
    cipherclerk: &AppCipherclerk,
    worker_cell: CellId,
    ack_slot: u8,
    wake_digest: FieldElement,
) -> Action {
    let effects = vec![
        Effect::SetField {
            cell: worker_cell,
            index: ack_slot as usize,
            value: wake_digest,
        },
        Effect::EmitEvent {
            cell: worker_cell,
            event: Event::new(symbol("dispatch-acked"), vec![wake_digest]),
        },
    ];
    cipherclerk.make_action(worker_cell, "drain_dispatch", effects)
}

// =============================================================================
// The deos-native surface — the dispatch BOARD as a composed `DeosApp`.
// =============================================================================
//
// `docs/deos/APPS-DEOS-INTEGRATION-CENSUS.md` (Tier-1 #3): swarm-orchestration's deos
// re-expression was the second deos-native test, but lived in `tests/reexpress_deos_app.rs`
// on the scaffold `emit`/`edit` placeholders (the "honest seam" it admitted). This
// PROMOTES `board_app` into `src/`: the same operations are ONE [`DeosApp`]
// ([`board_app`] below); the framework wires the rest — per-viewer projection, web-of-cells
// publish (the BOARD cell IS a `dregg://` sturdyref), per-viewer rehydration, the generated
// `<dregg-affordance-surface>` component, and the manifest — none of which the old bones
// had. `register(ctx)` now mounts it (see [`register_deos`]).
//
// **The seam is closed** — a TWO-TEMPO fire (mirror supply-chain-provenance). The two
// state-mutating operations (`dispatch`, `open_board`) are [`GatedAffordance`]s carrying a
// live-state PRECONDITION; the FULL swarm program ([`coordinator_program`] =
// [`swarm_constraints`]) is INSTALLED on the seeded board cell ([`seed_board`]) and
// RE-ENFORCED by the executor on every touching turn:
//
//   1. the deos PRECONDITION gate (the cap-gate `is_attenuation` AND the live-state
//      precondition `CellProgram::evaluate`) decides the button's verdict IN-BAND —
//      nothing submitted on a miss (anti-ghost; the htmx reactivity rides this);
//   2. [`fire_dispatch`] / [`fire_open_board`] then submit the FULL multi-effect
//      dispatch/open turn ([`dispatch_effects`] / [`open_board_effects`]), and the executor
//      RE-ENFORCES the full swarm program — so the atomic budget `AffineLe(spent_a + spent_b
//      <= budget)` (an over-budget runaway), the `StrictMonotonic(epoch)` (a replayed
//      dispatch), the `Monotonic(SPENT_*)` (a meter rollback), and the `WriteOnce(budget)`
//      (a quiet mandate widening) are all REAL executor refusals in the SUBMISSION path —
//      the half the floor's `program.evaluate`-only tests never exercised through a real
//      signed turn (see `tests/deos_seam.rs`).
//
// `grant_worker` carries the REAL [`Effect::GrantCapability`] (the `derive_no_amplify`
// worker delegation: an ATTENUATED slice to the worker cell) as a cap-only affordance.

/// The swarm rights tiers, ON THE REAL ATTENUATION LATTICE — these ARE the roles the floor
/// crate's cap-graph enforces (a worker holds only its attenuated slice):
///
///   - an OBSERVER (an operator auditing a swarm she did not write — the narration-vs-truth
///     reader) holds [`AuthRequired::Signature`] — the narrow tier: it can `view_board`
///     (read lead / budget / meters / epoch) and nothing else;
///   - a WORKER (a dispatched agent cell) holds [`AuthRequired::Either`] — it can
///     `ack_dispatch` (the async drain, in its OWN receipted turn) AND view;
///   - the LEAD / OPERATOR holds [`AuthRequired::None`]/root — it can `open_board` (pin the
///     lead + mandate), `dispatch` (advance a worker meter + wake the worker), and
///     `grant_worker` (hand a worker an attenuated slice) on top of everything a worker can do.
///
/// So `Signature ⊂ Either ⊂ None` IS the observer ⊂ worker ⊂ lead ladder.
pub const OBSERVER_RIGHTS: AuthRequired = AuthRequired::Signature;
/// The worker rights tier (sig-or-proof — ack + view). See [`OBSERVER_RIGHTS`].
pub const WORKER_RIGHTS: AuthRequired = AuthRequired::Either;
/// The lead/operator rights tier (root — open, dispatch, grant, +all). See [`OBSERVER_RIGHTS`].
pub const LEAD_RIGHTS: AuthRequired = AuthRequired::None;

/// The permissions a worker's attenuated capability carries (a `SelfCell` slice the lead
/// hands forward NARROWED, never widened — the Lean `derive_no_amplify`). Matches the
/// factory's `allowed_cap_templates` ceiling.
pub const WORKER_CAP_PERMISSIONS: AuthRequired = AuthRequired::Signature;

/// The `dispatch` **live-state precondition** — the board must be OPEN (`EPOCH >= 1`, the
/// lead + budget are pinned). A real [`CellProgram`] read against the cell's current state,
/// so a dispatch button is DARK before the board opens and LIT after (the htmx tooth). This
/// gates "may `dispatch` fire now"; the dispatch INVARIANTS (the `AffineLe` budget gate +
/// `StrictMonotonic(epoch)` etc.) are the installed [`coordinator_program`] the executor
/// re-enforces on the produced transition.
pub fn opened_precondition() -> CellProgram {
    CellProgram::Predicate(vec![StateConstraint::FieldGte {
        index: EPOCH_SLOT,
        value: field_from_u64(1),
    }])
}

/// The `open_board` **live-state precondition** — the board must NOT yet be open
/// (`EPOCH == 0`). So the `open_board` button is LIT only on a fresh board and goes DARK the
/// instant it opens (the htmx tooth). The executor's installed `StrictMonotonic(EPOCH)` +
/// `WriteOnce(BUDGET)` are the second guards (a re-open is a real refusal).
pub fn preopen_precondition() -> CellProgram {
    CellProgram::Predicate(vec![StateConstraint::FieldEquals {
        index: EPOCH_SLOT,
        value: field_from_u64(0),
    }])
}

/// **`grant_worker` effect** — the lead's real cap handoff: an [`Effect::GrantCapability`]
/// of an ATTENUATED slice of the board's authority to the worker cell, at the SAME
/// (`Signature`) permissions — narrowed, never widened (the Lean `derive_no_amplify`). This
/// is the deos affordance's effect-template for `grant_worker`, NOT a scaffold stand-in.
pub fn grant_worker_effect(board: CellId, worker_cell: CellId) -> Effect {
    Effect::GrantCapability {
        from: board,
        to: worker_cell,
        cap: CapabilityRef {
            target: board,
            slot: SPENT_A_SLOT as u32,
            permissions: WORKER_CAP_PERMISSIONS,
            breadstuff: None,
            expires_at: None,
            allowed_effects: None,
            stored_epoch: None,
        },
    }
}

/// **The swarm dispatch BOARD as a composed [`DeosApp`]** — the whole interaction surface,
/// on the deos bones. The board cell is the agent's OWN cell (`cipherclerk.cell_id()`) so
/// fires execute against the seeded embedded ledger.
///
/// Five operations on the BOARD cell, on the observer ⊂ worker ⊂ lead rights ladder:
///
///   - `view_board` — a cap-only affordance (an OBSERVER audits): `Signature`, an `EmitEvent`;
///   - `ack_dispatch` — a cap-only affordance (a WORKER drains a wake in its own turn):
///     `Either`, an `EmitEvent` (the async drain ack);
///   - `dispatch` — a [`GatedAffordance`] (the LEAD advances a worker meter): `None`/root, a
///     live-state PRECONDITION (the board is open); the real fire ([`fire_dispatch`]) submits
///     the FULL dispatch (meter + epoch + async wake), re-enforced by the executor's installed
///     swarm program (the `AffineLe` budget gate + `StrictMonotonic` epoch + `Monotonic` meters
///     BITE on the produced transition);
///   - `open_board` — a [`GatedAffordance`] (the LEAD pins lead + mandate): `None`/root, a
///     live-state PRECONDITION (the board is NOT yet open); the real fire ([`fire_open_board`])
///     submits the FULL open, re-enforced by the executor (`WriteOnce(BUDGET)` + `StrictMonotonic`);
///   - `grant_worker` — a cap-only affordance carrying the REAL [`Effect::GrantCapability`]
///     (the `derive_no_amplify` attenuated worker delegation): `None`/root.
///
/// The board cell is published into the web-of-cells at the observer tier (a federated peer
/// reacquires the dispatch board across the membrane) and is discoverable under
/// `orchestration` / `swarm`.
///
/// Seed the cell's program + opened state with [`seed_board`] (or fire `open_board`) so the
/// gated fires have a live state and the executor re-enforces the swarm policy.
pub fn board_app(cipherclerk: &AppCipherclerk, executor: &EmbeddedExecutor) -> DeosApp {
    let board = cipherclerk.cell_id();

    // `dispatch` — the LEAD advances worker-A's spend meter (the `AffineLe`-summed `SPENT_A`
    // slot). The GatedAffordance carries the DECISIVE effect (the meter write) as its surface
    // representative AND a live-state PRECONDITION ([`opened_precondition`]: the board is open)
    // — so the button is dark before the board opens and lit after, and the cap∧state gate
    // decides its verdict in-band. The actual fire ([`fire_dispatch`]) submits the FULL
    // dispatch ([`dispatch_effects`]: meter + epoch + async wake), which the executor
    // re-enforces the FULL swarm program on — so the `AffineLe` budget gate BITES: an
    // over-budget dispatch is REFUSED.
    let dispatch = GatedAffordance::new(
        CellAffordance::new(
            "dispatch",
            LEAD_RIGHTS,
            Effect::SetField {
                cell: board,
                index: SPENT_A_SLOT as usize,
                value: field_from_u64(1),
            },
        ),
        opened_precondition(),
    );
    // `open_board` — the LEAD pins the lead + mandate. The decisive effect advances `EPOCH`
    // 0 -> 1 (the lead/budget/meters are the full `open_board_effects` turn); gated on the
    // PRE-OPEN precondition ([`preopen_precondition`]: the board is not yet open, `EPOCH == 0`).
    // The executor re-enforces the installed program (so `StrictMonotonic(EPOCH)` +
    // `WriteOnce(BUDGET)` bite — a re-open is refused).
    let open = GatedAffordance::new(
        CellAffordance::new(
            "open_board",
            LEAD_RIGHTS,
            Effect::SetField {
                cell: board,
                index: EPOCH_SLOT as usize,
                value: field_from_u64(1),
            },
        ),
        preopen_precondition(),
    );
    // `grant_worker` — the lead hands a worker an attenuated slice. A real
    // `Effect::GrantCapability`, cap-only (the cap-graph half — no state mutation).
    let grant = CellAffordance::new(
        "grant_worker",
        LEAD_RIGHTS,
        grant_worker_effect(board, CellId::from_bytes([0x9a; 32])),
    );
    // `ack_dispatch` — a worker drains a wake in its own receipted turn. Cap-only.
    let ack = CellAffordance::new(
        "ack_dispatch",
        WORKER_RIGHTS,
        Effect::EmitEvent {
            cell: board,
            event: Event::new(symbol("dispatch-acked"), vec![]),
        },
    );
    // `view_board` — an observer audits. Cap-only.
    let view = CellAffordance::new(
        "view_board",
        OBSERVER_RIGHTS,
        Effect::EmitEvent {
            cell: board,
            event: Event::new(symbol("board-read"), vec![]),
        },
    );

    DeosApp::builder("swarm-orchestration", cipherclerk.clone(), executor.clone())
        .discoverable(vec!["orchestration".into(), "swarm".into()])
        .cell(
            DeosCell::new(board, "board")
                .affordance(view)
                .affordance(ack)
                .gated(dispatch)
                .gated(open)
                .affordance(grant)
                .publish(OBSERVER_RIGHTS),
        )
        .build()
}

/// **Seed the BOARD cell** so the gated fires have live state + the caveats bite: install
/// the full swarm [`coordinator_program`] on the seeded board cell (so the executor
/// re-enforces it on every touching turn), then open the genesis state (pin `LEAD` +
/// `BUDGET`, the two meters at 0, advance `EPOCH` to 1) directly into the embedded ledger.
///
/// After seeding, the board is open at epoch 1 with the given `budget` mandate — a real
/// `(old, new)` baseline against which `dispatch` advances a meter. Returns the seeded budget.
pub fn seed_board(executor: &EmbeddedExecutor, lead: &str, budget: u64) -> u64 {
    let board = executor.cell_id();
    executor.install_program(board, coordinator_program());
    executor.with_ledger_mut(|ledger| {
        if let Some(cell) = ledger.get_mut(&board) {
            cell.state
                .set_field(LEAD_SLOT as usize, identity_field(lead));
            cell.state
                .set_field(BUDGET_SLOT as usize, field_from_u64(budget));
            cell.state
                .set_field(SPENT_A_SLOT as usize, field_from_u64(0));
            cell.state
                .set_field(SPENT_B_SLOT as usize, field_from_u64(0));
            cell.state.set_field(EPOCH_SLOT as usize, field_from_u64(1));
        }
    });
    budget
}

/// **`open_board` effects** — the multi-effect open body: pin `LEAD` + `BUDGET`
/// (`WriteOnce`: bound once from zero, frozen), the two worker meters born at 0, advance
/// `EPOCH` 0 -> 1 (so `StrictMonotonic(EPOCH)` holds on the very first touch), and emit
/// `swarm-board-opened`. This is the ONE coherent transition the full swarm program admits.
/// The deos `open_board` gated affordance is the cap∧state PRECONDITION face; THIS is the
/// turn [`fire_open_board`] submits. (Identical shape to [`build_open_board_action`]'s body.)
pub fn open_board_effects(board: CellId, lead: &str, budget: u64) -> Vec<Effect> {
    vec![
        Effect::SetField {
            cell: board,
            index: LEAD_SLOT as usize,
            value: identity_field(lead),
        },
        Effect::SetField {
            cell: board,
            index: BUDGET_SLOT as usize,
            value: field_from_u64(budget),
        },
        Effect::SetField {
            cell: board,
            index: SPENT_A_SLOT as usize,
            value: field_from_u64(0),
        },
        Effect::SetField {
            cell: board,
            index: SPENT_B_SLOT as usize,
            value: field_from_u64(0),
        },
        Effect::SetField {
            cell: board,
            index: EPOCH_SLOT as usize,
            value: field_from_u64(1),
        },
        Effect::EmitEvent {
            cell: board,
            event: Event::new(
                symbol("swarm-board-opened"),
                vec![identity_field(lead), field_from_u64(budget)],
            ),
        },
    ]
}

/// **`dispatch` effects** — the multi-effect dispatch body: advance `worker`'s cumulative
/// spend meter to `new_spent` (`Monotonic`; summed by the `AffineLe` budget gate), strictly
/// advance `EPOCH` (no-replay), and (the async notify edge) EMIT a wake targeting the
/// `worker_cell` carrying the sub-task `topic`. This is the ONE coherent transition the full
/// swarm program admits — every clause holds together: `AffineLe(spent_a + spent_b <=
/// budget)`, `StrictMonotonic(EPOCH)`, `Monotonic(SPENT_*)`. The deos `dispatch` gated
/// affordance is the cap∧state PRECONDITION face; THIS is the turn [`fire_dispatch`] submits.
#[allow(clippy::too_many_arguments)]
pub fn dispatch_effects(
    board: CellId,
    worker: Worker,
    worker_cell: CellId,
    new_spent: u64,
    new_epoch: u64,
    cost: u64,
    topic: &str,
) -> Vec<Effect> {
    vec![
        Effect::SetField {
            cell: board,
            index: worker.spend_slot() as usize,
            value: field_from_u64(new_spent),
        },
        Effect::SetField {
            cell: board,
            index: EPOCH_SLOT as usize,
            value: field_from_u64(new_epoch),
        },
        Effect::EmitEvent {
            cell: worker_cell,
            event: Event::new(
                symbol(&format!("dispatch/{}", topic)),
                vec![field_from_u64(cost), field_from_u64(new_epoch)],
            ),
        },
    ]
}

/// **Fire `open_board`** — the deos cap∧state PRECONDITION gate (cap ⊇ root AND the board is
/// NOT yet open), then the FULL multi-effect open turn ([`open_board_effects`]). Like
/// [`fire_dispatch`], the gated affordance decides the button in-band and the executor's
/// program re-enforcement (`StrictMonotonic(EPOCH)` 0 -> 1 + `WriteOnce(BUDGET)`) is the
/// verified second gate. Install the program first (the executor re-enforces it); do NOT seed
/// the genesis state (open is what binds it).
pub fn fire_open_board(
    app: &DeosApp,
    held: &AuthRequired,
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
    lead: &str,
    budget: u64,
) -> Result<TurnReceipt, FireExecuteError> {
    let cell = &app.cells()[0];
    let board = cell.cell();
    if !cell
        .gated_fireable_names(held, executor)
        .iter()
        .any(|n| n == "open_board")
    {
        let ga = cell
            .gated_surface()
            .get("open_board")
            .expect("open_board is gated");
        let state = executor.cell_state(board).ok_or_else(|| {
            FireExecuteError::Gate(FireError::StateConditionUnmet {
                affordance: "open_board".into(),
                reason: "cell has no live state (fail-closed)".into(),
            })
        })?;
        return Err(FireExecuteError::Gate(
            ga.fire(board, held, &state, &state).unwrap_err(),
        ));
    }
    let action =
        cipherclerk.make_action(board, "open_board", open_board_effects(board, lead, budget));
    executor
        .submit_action(cipherclerk, action)
        .map_err(FireExecuteError::Executor)
}

/// **Fire `dispatch`** — the deos cap∧state PRECONDITION gate (anti-ghost, in-band), then
/// the FULL multi-effect dispatch turn the executor re-enforces the swarm program on. The
/// two-tempo bridge: the gated affordance decides the button's verdict (cap ⊇ root AND the
/// board is open) WITHOUT touching the executor; on both passing, the complete dispatch turn
/// ([`dispatch_effects`]: meter + epoch + async wake) is submitted, and the executor's
/// re-enforcement of [`coordinator_program`] is the SECOND, verified gate (the `AffineLe`
/// budget gate + `StrictMonotonic(epoch)` + `Monotonic(meters)` all bite on the produced
/// transition). Anti-ghost both ways: a precondition miss never submits; a budget breach (or
/// replay, or rollback) is a real executor refusal.
///
/// The dispatch cursor is read from the board's live state (current `EPOCH` ⇒ the next epoch,
/// the worker's current meter ⇒ the new meter), so the caller threads only the `cost`, the
/// target `worker` + `worker_cell`, and the sub-task `topic`. Use [`seed_board`] first.
#[allow(clippy::too_many_arguments)]
pub fn fire_dispatch(
    app: &DeosApp,
    held: &AuthRequired,
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
    worker: Worker,
    worker_cell: CellId,
    cost: u64,
    topic: &str,
) -> Result<TurnReceipt, FireExecuteError> {
    let cell = &app.cells()[0];
    let board = cell.cell();
    // Tooth 1+2: the deos cap∧state PRECONDITION gate, in-band, nothing submitted on a miss.
    if !cell
        .gated_fireable_names(held, executor)
        .iter()
        .any(|n| n == "dispatch")
    {
        let ga = cell
            .gated_surface()
            .get("dispatch")
            .expect("dispatch is a gated affordance");
        let state = executor.cell_state(board).ok_or_else(|| {
            FireExecuteError::Gate(FireError::StateConditionUnmet {
                affordance: "dispatch".into(),
                reason: "cell has no live state (fail-closed)".into(),
            })
        })?;
        return Err(FireExecuteError::Gate(
            ga.fire(board, held, &state, &state).unwrap_err(),
        ));
    }
    // The dispatch cursor, read from live state.
    let state = executor.cell_state(board).expect("checked above");
    let epoch = field_to_u64(&state.fields[EPOCH_SLOT as usize]);
    let prev_spent = field_to_u64(&state.fields[worker.spend_slot() as usize]);
    let new_spent = prev_spent.saturating_add(cost);
    // Submit the FULL multi-effect dispatch turn — the executor re-enforces the program (the
    // `AffineLe` budget gate sums the new meter against the OTHER meter + the budget).
    let effects = dispatch_effects(
        board,
        worker,
        worker_cell,
        new_spent,
        epoch + 1,
        cost,
        topic,
    );
    let action = cipherclerk.make_action(board, "dispatch", effects);
    executor
        .submit_action(cipherclerk, action)
        .map_err(FireExecuteError::Executor)
}

/// Read a `u64` from the last 8 big-endian bytes of a field element (the inverse of
/// [`field_from_u64`] for the epoch/meter counters the board stores).
fn field_to_u64(f: &FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&f[24..32]);
    u64::from_be_bytes(b)
}

/// **Mount the deos-native surface** ([`board_app`]) on a shared context: build the composed
/// [`DeosApp`] from the context's cipherclerk + executor, seed the board cell's program +
/// opened state (so the gated fires bite), and fold the app into the context's affordance
/// registry ([`DeosApp::register`]). Returns the live [`DeosApp`] (so a host can also
/// [`DeosApp::mount`] its axum router / [`DeosApp::publish_all`] into the web-of-cells). This
/// is the PROMOTION the census Tier-1 #3 asks for: the deos surface now ships from `src/`,
/// not from a side-proof in `tests/`.
pub fn register_deos(ctx: &StarbridgeAppContext) -> DeosApp {
    let app = board_app(ctx.cipherclerk(), ctx.executor());
    // Seed the board cell so the gated `dispatch` / `open_board` fires have a live
    // `(old, new)` and the full swarm program (installed here) is re-enforced by the executor
    // on every touching turn.
    seed_board(ctx.executor(), "lead", 1000);
    app.register(ctx);
    app
}

// =============================================================================
// StarbridgeAppContext mount.
// =============================================================================

/// The canonical web-constants module (slot layout + event topics + factory-vk hex).
pub fn web_constants() -> ConstantsModule {
    ConstantsModule::new("swarm-orchestration")
        .slot("LEAD_SLOT", LEAD_SLOT as u64)
        .slot("BUDGET_SLOT", BUDGET_SLOT as u64)
        .slot("SPENT_A_SLOT", SPENT_A_SLOT as u64)
        .slot("SPENT_B_SLOT", SPENT_B_SLOT as u64)
        .slot("EPOCH_SLOT", EPOCH_SLOT as u64)
        .string("FACTORY_VK_HEX", hex_encode_32(&SWARM_FACTORY_VK))
        .topic("BOARD_OPENED", "swarm-board-opened")
        .topic("ACKED", "dispatch-acked")
}

/// Register the swarm-orchestration starbridge-app on a shared context.
pub fn register(ctx: &StarbridgeAppContext) -> [u8; 32] {
    let factory_vk = ctx.register_factory(swarm_factory_descriptor());

    ctx.register_inspector(InspectorDescriptor {
        kind: "swarm-board".into(),
        descriptor: serde_json::json!({
            "component": "dregg-swarm-board",
            "module": "/starbridge-apps/swarm-orchestration/inspectors.js",
            "uri_prefix": "dregg://cell/",
            "summary_fields": ["lead", "budget", "spent_a", "spent_b", "epoch"],
            "slot_layout": {
                "lead": LEAD_SLOT,
                "budget": BUDGET_SLOT,
                "spent_a": SPENT_A_SLOT,
                "spent_b": SPENT_B_SLOT,
                "epoch": EPOCH_SLOT,
            },
            "factory_vk_hex": hex_encode_32(&factory_vk),
            "child_program_vk_hex": hex_encode_32(&coordinator_child_program_vk()),
            "methods": ["open_board", "dispatch", "drain_dispatch"],
        }),
    });

    // Mount the deos-native composition surface (the `DeosApp`) on the SAME context — the
    // census Tier-1 #3 promotion: the deos surface now ships from `src/`, not from a
    // side-proof in `tests/`. The factory + inspector are where SOUNDNESS lives (an
    // over-budget / replayed dispatch is a real executor refusal on the born cell); the
    // deos surface is the composition skin (per-viewer projection, the cap∧state gated
    // fires, the `dregg://` publish, the rehydratable snapshot, the manifest).
    register_deos(ctx);

    factory_vk
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::{AgentCipherclerk, Authorization, EmbeddedExecutor};

    fn test_cipherclerk() -> AppCipherclerk {
        AppCipherclerk::new(AgentCipherclerk::new(), [0x5au8; 32])
    }

    fn test_context() -> StarbridgeAppContext {
        let cipherclerk = test_cipherclerk();
        let executor = EmbeddedExecutor::new(&cipherclerk, "default");
        StarbridgeAppContext::new(cipherclerk, executor)
    }

    fn test_cell() -> CellId {
        CellId::from_bytes([7u8; 32])
    }

    // ── the dispatch policy mirrors the Lean dispatchConstraints ─────────────

    #[test]
    fn coordinator_program_has_the_six_policy_clauses() {
        // The board program is a flat predicate (exactly what the factory installs on the born
        // cell), so the advertised program VK names the installed predicate byte-for-byte.
        let CellProgram::Predicate(ks) = coordinator_program() else {
            panic!("coordinator program must be a flat Predicate");
        };
        assert_eq!(ks, swarm_constraints(), "the program IS swarm_constraints");
        // the affine budget gate is present.
        assert!(
            ks.iter().any(|k| matches!(
                k,
                StateConstraint::AffineLe { terms, c: 0 }
                    if terms.contains(&(1, SPENT_A_SLOT))
                        && terms.contains(&(1, SPENT_B_SLOT))
                        && terms.contains(&(-1, BUDGET_SLOT))
            )),
            "the budget gate spent_a + spent_b <= budget must be a clause"
        );
        // write-once mandate + lead (born-empty, bound once, frozen) + monotones + strict-mono epoch.
        assert!(
            ks.iter().any(
                |k| matches!(k, StateConstraint::WriteOnce { index } if *index == BUDGET_SLOT)
            )
        );
        assert!(
            ks.iter()
                .any(|k| matches!(k, StateConstraint::WriteOnce { index } if *index == LEAD_SLOT))
        );
        assert!(
            ks.iter().any(
                |k| matches!(k, StateConstraint::Monotonic { index } if *index == SPENT_A_SLOT)
            )
        );
        assert!(
            ks.iter().any(
                |k| matches!(k, StateConstraint::Monotonic { index } if *index == SPENT_B_SLOT)
            )
        );
        assert!(ks.iter().any(
            |k| matches!(k, StateConstraint::StrictMonotonic { index } if *index == EPOCH_SLOT)
        ));
    }

    // ── the budget pre-check mirrors the executor's AffineLe gate ────────────

    #[test]
    fn dispatch_within_budget_matches_the_affine_bound() {
        // budget 1000; a 600 dispatch to A then a 300 to B fits (900 <= 1000).
        assert!(dispatch_within_budget(0, 600, 0, 1000)); // A: 0 -> 600, B at 0
        assert!(dispatch_within_budget(0, 300, 600, 1000)); // B: 0 -> 300, A at 600 ⇒ 900
        // a 500 to B with A at 600 breaches (1100 > 1000) — the BUDGET TOOTH.
        assert!(!dispatch_within_budget(0, 500, 600, 1000));
        // exactly at the ceiling is admitted (<=).
        assert!(dispatch_within_budget(600, 400, 0, 1000));
        // one over the ceiling is refused.
        assert!(!dispatch_within_budget(600, 401, 0, 1000));
    }

    #[test]
    fn worker_spend_slots_are_distinct_meters() {
        assert_eq!(Worker::A.spend_slot(), SPENT_A_SLOT);
        assert_eq!(Worker::B.spend_slot(), SPENT_B_SLOT);
        assert_ne!(Worker::A.spend_slot(), Worker::B.spend_slot());
    }

    // ── the turn builders carry real effects + a real signature ──────────────

    #[test]
    fn open_board_action_pins_lead_and_budget() {
        let cclerk = test_cipherclerk();
        let action = build_open_board_action(&cclerk, test_cell(), "lead-pk", 1000);
        // lead, budget, spent_a(=0), spent_b(=0), epoch(=0), + event.
        assert_eq!(action.effects.len(), 6);
        assert!(matches!(
            &action.effects[0],
            Effect::SetField { index, value, .. } if *index == LEAD_SLOT as usize && *value == identity_field("lead-pk")
        ));
        assert!(matches!(
            &action.effects[1],
            Effect::SetField { index, value, .. } if *index == BUDGET_SLOT as usize && *value == field_from_u64(1000)
        ));
    }

    #[test]
    fn dispatch_action_advances_meter_epoch_and_emits_wake() {
        let cclerk = test_cipherclerk();
        let worker_cell = CellId::from_bytes([9u8; 32]);
        let action = build_dispatch_action(
            &cclerk,
            test_cell(),
            Worker::A,
            worker_cell,
            0,
            300,
            1,
            "index",
        );
        // spent_a := 300, epoch := 1, + wake on the WORKER cell.
        assert_eq!(action.effects.len(), 3);
        assert!(matches!(
            &action.effects[0],
            Effect::SetField { index, value, .. } if *index == SPENT_A_SLOT as usize && *value == field_from_u64(300)
        ));
        assert!(matches!(
            &action.effects[1],
            Effect::SetField { index, value, .. } if *index == EPOCH_SLOT as usize && *value == field_from_u64(1)
        ));
        // the wake targets the WORKER cell (the async notify edge), not the board.
        assert!(matches!(
            &action.effects[2],
            Effect::EmitEvent { cell, .. } if *cell == worker_cell
        ));
    }

    #[test]
    fn dispatch_action_carries_a_real_signature() {
        let cclerk = test_cipherclerk();
        let worker_cell = CellId::from_bytes([9u8; 32]);
        let action =
            build_dispatch_action(&cclerk, test_cell(), Worker::B, worker_cell, 0, 1, 1, "t");
        match action.authorization {
            Authorization::Signature(a, b) => assert!(a != [0u8; 32] || b != [0u8; 32]),
            other => panic!("expected Signature, got {other:?}"),
        }
    }

    #[test]
    fn register_installs_factory_and_inspector() {
        let ctx = test_context();
        let vk = register(&ctx);
        assert_eq!(vk, SWARM_FACTORY_VK);
        assert_eq!(ctx.factory_registry().len(), 1);
        assert!(ctx.inspector_registry().get("swarm-board").is_some());
    }
}
