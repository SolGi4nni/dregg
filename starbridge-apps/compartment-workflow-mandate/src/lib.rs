//! # starbridge-compartment-workflow-mandate
//!
//! Scaffold for the **Compartment Workflow Mandate** starbridge-app, mapping
//! `metatheory/Dregg2/Apps/CompartmentWorkflowMandate*.lean` onto dregg-native
//! primitives (`FactoryDescriptor`, `CellProgram`, `Effect::SetField`,
//! `Effect::EmitEvent`).
//!
//! The mandate cell carries:
//! - a **`step_cursor`** (`MonotonicSequence` — replay-safe `+1` advances);
//! - an immutable **`commitment_anchor`** (compartment tag);
//! - a pinned **`charter_terminal`** bound (DAG length — review → redact → sign).
//!
//! Predicate-layer admission (DAG prerequisites + clearance labels) is expressed
//! in Rust helpers that mirror the Lean `cwmAdvanceM` / `stepAdmissible` /
//! `stepClearanceOK` checks; executor-layer teeth use slot caveats from the
//! factory descriptor.

#![forbid(unsafe_code)]

/// ORGAN 2 — the colonist's JOB (gather → make → hand-off) as an executable workflow-mandate,
/// mirror of `metatheory/Dregg2/Apps/ColonistJob.lean`. DAG ∧ clearance ∧ SPEND-BUDGET, all three
/// biting through the real embedded executor.
pub mod colonist_job;

use dregg_app_framework::{
    Action, AppCipherclerk, AuthRequired, CapTarget, CapTemplate, CellAffordance, CellId, CellMode,
    CellProgram, ChildVkStrategy, ConstantsModule, DeosApp, DeosCell, Effect, EmbeddedExecutor,
    Event, FactoryDescriptor, FireExecuteError, GatedAffordance, InspectorDescriptor,
    StarbridgeAppContext, StateConstraint, TransitionCase, TransitionGuard, TurnReceipt,
    canonical_program_vk, clearance_graph_root, field_from_bytes, field_from_u64, hex_encode_32,
    symbol,
};

// Re-export the field type so differential tests can build the same clearance-label corpus the
// admission predicates consume, without depending directly on `dregg-app-framework`.
pub use dregg_app_framework::FieldElement;

// =============================================================================
// Charter domain (review → redact → sign)
// =============================================================================

/// One workflow phase in the canonical 3-step charter DAG.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WorkflowPhase {
    /// Step 0 — `review` compartment (no prerequisites).
    Review,
    /// Step 1 — `redact` compartment (requires review).
    Redact,
    /// Step 2 — `sign` compartment (requires redact).
    Sign,
}

impl WorkflowPhase {
    /// Numeric step id (matches Lean `CwmPhase.toStepId`).
    pub const fn step_id(self) -> u64 {
        match self {
            Self::Review => 0,
            Self::Redact => 1,
            Self::Sign => 2,
        }
    }

    /// Prerequisite step ids for DAG admissibility (`stepAdmissible`).
    pub const fn prerequisites(self) -> &'static [u64] {
        match self {
            Self::Review => &[],
            Self::Redact => &[0],
            Self::Sign => &[1],
        }
    }

    /// Clearance compartment label hash (Lean `WorkflowStep.compartment`).
    pub fn compartment_label(self) -> FieldElement {
        match self {
            Self::Review => clearance_label("review"),
            Self::Redact => clearance_label("redact"),
            Self::Sign => clearance_label("sign"),
        }
    }

    /// All phases in charter order.
    pub const CHARTER: [Self; 3] = [Self::Review, Self::Redact, Self::Sign];
}

/// Default charter length (review → redact → sign).
pub const DEFAULT_CHARTER_STEPS: u64 = 3;

/// Default Stingray per-step spend debit (Lean `charterMandate3.spendPolicy` demo).
pub const DEFAULT_STEP_SPEND_POLICY: u64 = 5;

/// Default commitment-anchor compartment tag (Lean `charterNul` / `cwmCompartmentTag`).
pub const DEFAULT_COMMITMENT_ANCHOR: u64 = 42;

// =============================================================================
// Slot layout (mandate cell)
// =============================================================================

/// Slot 0 — `step_cursor`. Advanced exactly +1 per `advance_step`.
pub const STEP_CURSOR_SLOT: u8 = 0;

/// Slot 1 — `commitment_anchor`. Immutable compartment tag.
pub const COMMITMENT_ANCHOR_SLOT: u8 = 1;

/// Slot 2 — `charter_terminal`. Immutable upper bound on the cursor.
pub const CHARTER_TERMINAL_SLOT: u8 = 2;

/// Slot 3 — `clearance_graph_root`. Immutable Merkle root over label-dominance edges.
pub const CLEARANCE_GRAPH_ROOT_SLOT: u8 = 3;

/// Slot 4 — `spend_policy`. Immutable per-step Stingray debit amount.
pub const SPEND_POLICY_SLOT: u8 = 4;

/// Slot 5 — `actor_clearance`. The acting officer's clearance label (the label
/// whose dominance over the entered step's compartment the executor checks).
/// Bound per turn by the advancing turn (the officer presents their clearance).
pub const ACTOR_CLEARANCE_SLOT: u8 = 5;

/// Slot 6 — `step_compartment`. The compartment label of the step being ENTERED,
/// materialized into state by the advancing turn so the executor's
/// [`StateConstraint::ClearanceDominates`] reads the required compartment for the
/// step (the per-step `needsAll g actorLabels [step.compartment]` of Lean
/// `stepClearanceOK`, made a state read).
pub const STEP_COMPARTMENT_SLOT: u8 = 6;

// =============================================================================
// Factory configuration
// =============================================================================

/// The factory VK we publish for the compartment-workflow mandate factory.
pub const CWM_FACTORY_VK: [u8; 32] = *b"starbridge-cwm-mandate-factory!!";

/// Default per-epoch creation budget.
pub const DEFAULT_CREATION_BUDGET: u64 = 256;

/// Hash a clearance compartment label (Lean `Label.named`).
pub fn clearance_label(name: &str) -> FieldElement {
    field_from_bytes(name.as_bytes())
}

/// Completed step ids implied by the monotonic cursor (Lean `completedOf`).
pub fn completed_of(cursor: u64) -> Vec<u64> {
    (0..cursor).collect()
}

/// **`step_admissible`** — DAG prerequisites satisfied and target not yet done.
///
/// Mirrors Lean `stepAdmissible`: all `needs` ∈ `completed`, and `step_id ∉ completed`.
pub fn step_admissible(step_id: u64, completed: &[u64], phase: WorkflowPhase) -> bool {
    if step_id != phase.step_id() {
        return false;
    }
    phase
        .prerequisites()
        .iter()
        .all(|need| completed.contains(need))
        && !completed.contains(&step_id)
}

/// The named clearance labels of the canonical charter graph (Lean
/// `charterGraph3`, `Apps/CompartmentWorkflowMandate/Core.lean:172`).
pub fn officer_label() -> FieldElement {
    clearance_label("officer")
}
/// The clerk clearance label (clears ONLY `review`). See [`officer_label`].
pub fn clerk_label() -> FieldElement {
    clearance_label("clerk")
}

/// **The canonical charter clearance graph** — the `(dominator, dominated)` edge
/// set of Lean `charterGraph3` (`Apps/CompartmentWorkflowMandate/Core.lean:172`):
///
///   officer ⊐ {review, redact, sign},   clerk ⊐ {review}.
///
/// An officer's clearance dominates every step compartment (it may run the whole
/// charter); a clerk's dominates only `review` (it may only do step 0). Dominance
/// is the reflexive-transitive closure of these edges — the proved-sound
/// `ClearanceGraph.dominatesD`. This IS the graph the cell commits in its
/// `CLEARANCE_GRAPH_ROOT_SLOT` ([`charter_clearance_root`]) and that the
/// executor's [`StateConstraint::ClearanceDominates`] walks.
pub fn charter_clearance_graph() -> Vec<(FieldElement, FieldElement)> {
    vec![
        (officer_label(), WorkflowPhase::Review.compartment_label()),
        (officer_label(), WorkflowPhase::Redact.compartment_label()),
        (officer_label(), WorkflowPhase::Sign.compartment_label()),
        (clerk_label(), WorkflowPhase::Review.compartment_label()),
    ]
}

/// The canonical commitment of the charter clearance graph — the value pinned in
/// the cell's `CLEARANCE_GRAPH_ROOT_SLOT`. The executor's `ClearanceDominates`
/// recomputes this from the carried edges and refuses any turn whose graph does
/// not match it (the stored root is LOAD-BEARING).
pub fn charter_clearance_root() -> FieldElement {
    clearance_graph_root(&charter_clearance_graph())
}

/// Fuel-bounded reflexive-transitive dominance over the clearance graph — the
/// hand-port of the proved-sound Lean `ClearanceGraph.dominatesD`/`dominatesFuel`
/// (`Authority/ClearanceGraph.lean:46,53`) over the felt-label substrate. `a`
/// dominates `b` iff `a == b` or some edge `(a, mid)` and `mid` dominates `b`,
/// bounded by `edges.len() + 1`. Reflexive (an actor holding exactly the box
/// label is cleared). Mirrors the executor's `dominates_closure`
/// (`cell/src/program.rs`) — the predicate layer and the executor decide
/// dominance the SAME way.
pub fn dominates(edges: &[(FieldElement, FieldElement)], a: FieldElement, b: FieldElement) -> bool {
    fn go(
        edges: &[(FieldElement, FieldElement)],
        a: FieldElement,
        b: FieldElement,
        fuel: usize,
    ) -> bool {
        if fuel == 0 {
            return false;
        }
        if a == b {
            return true;
        }
        edges
            .iter()
            .any(|(src, mid)| *src == a && go(edges, *mid, b, fuel - 1))
    }
    go(edges, a, b, edges.len() + 1)
}

/// **`mayRead`** — some held label dominates `box` in the graph (Lean
/// `ClearanceGraph.mayRead`).
pub fn may_read(
    edges: &[(FieldElement, FieldElement)],
    actor_labels: &[FieldElement],
    box_label: FieldElement,
) -> bool {
    actor_labels.iter().any(|&a| dominates(edges, a, box_label))
}

/// **`step_clearance_ok`** — the actor's held labels CLEAR the step's compartment
/// in the charter clearance graph: `needsAll g actorLabels [step.compartment]`
/// over a single required compartment (Lean `stepClearanceOK`,
/// `Apps/CompartmentWorkflowMandate/Core.lean:87`). NO LONGER a flat
/// `contains` — it walks the reflexive-transitive dominance closure of
/// [`charter_clearance_graph`], so an officer (whose clearance dominates the step
/// compartment) is cleared while a clerk is cleared only for `review`. This is
/// the predicate-layer twin of the executor's
/// [`StateConstraint::ClearanceDominates`] tooth (both decide via [`dominates`]).
pub fn step_clearance_ok(phase: WorkflowPhase, actor_label_hashes: &[FieldElement]) -> bool {
    may_read(
        &charter_clearance_graph(),
        actor_label_hashes,
        phase.compartment_label(),
    )
}

/// **`cwm_advance_admits`** — predicate-level one-step admission (Lean `cwmAdvanceM`).
pub fn cwm_advance_admits(
    cursor: u64,
    charter_terminal: u64,
    actor_labels: &[FieldElement],
) -> Option<WorkflowPhase> {
    if cursor >= charter_terminal {
        return None;
    }
    let phase = WorkflowPhase::CHARTER.get(cursor as usize)?;
    let completed = completed_of(cursor);
    if step_admissible(cursor, &completed, *phase) && step_clearance_ok(*phase, actor_labels) {
        Some(*phase)
    } else {
        None
    }
}

/// Cell-program skeleton: immutable anchor + monotonic-sequence cursor bounded by terminal.
pub fn cwm_cell_program() -> CellProgram {
    CellProgram::Cases(vec![
        TransitionCase {
            guard: TransitionGuard::Always,
            constraints: vec![
                // `WriteOnce` (not `Immutable`): a factory-born mandate is empty,
                // so the charter config slots are bound once by `init_mandate`
                // (from zero) and frozen thereafter — the birth-compatible form
                // of "fixed at creation".
                StateConstraint::WriteOnce {
                    index: COMMITMENT_ANCHOR_SLOT,
                },
                StateConstraint::WriteOnce {
                    index: CHARTER_TERMINAL_SLOT,
                },
                StateConstraint::WriteOnce {
                    index: CLEARANCE_GRAPH_ROOT_SLOT,
                },
                StateConstraint::WriteOnce {
                    index: SPEND_POLICY_SLOT,
                },
                StateConstraint::FieldLteField {
                    left_index: STEP_CURSOR_SLOT,
                    right_index: CHARTER_TERMINAL_SLOT,
                },
            ],
        },
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol("advance_step"),
            },
            constraints: vec![
                StateConstraint::MonotonicSequence {
                    seq_index: STEP_CURSOR_SLOT,
                },
                // THE CLEARANCE TOOTH (Lean `stepClearanceOK`, root-bound): the
                // acting officer's clearance (slot 5) must DOMINATE the entered
                // step's compartment (slot 6) in the charter clearance graph, and
                // that graph must commit to the root stored in
                // `CLEARANCE_GRAPH_ROOT_SLOT` (slot 3). The advancing turn
                // materializes both the actor clearance and the step compartment
                // into state (see [`advance_effects`]), so a clerk advancing to
                // `redact`/`sign` (clerk does not dominate them) is a REAL
                // executor refusal, while an officer advances; substitute an
                // over-permissive graph or tamper the root and it fails closed on
                // the root check.
                clearance_dominates_constraint(),
            ],
        },
    ])
}

/// The root-bound clearance constraint the executor re-enforces on every
/// `advance_step`: the actor clearance in `ACTOR_CLEARANCE_SLOT` dominates the
/// entered step's compartment in `STEP_COMPARTMENT_SLOT`, in the charter
/// clearance graph whose canonical commitment must equal
/// `CLEARANCE_GRAPH_ROOT_SLOT`. The Rust twin of Lean `stepClearanceOK` made an
/// inline executor tooth (`ClearanceGraph.dominatesD`, soundness
/// `dominates_of_dominatesD`), bound to the stored root so the slot is
/// LOAD-BEARING.
pub fn clearance_dominates_constraint() -> StateConstraint {
    StateConstraint::ClearanceDominates {
        actor_label_index: ACTOR_CLEARANCE_SLOT,
        box_index: STEP_COMPARTMENT_SLOT,
        root_index: CLEARANCE_GRAPH_ROOT_SLOT,
        edges: charter_clearance_graph(),
    }
}

/// Canonical child program VK.
pub fn cwm_child_program_vk() -> [u8; 32] {
    canonical_program_vk(&cwm_cell_program())
}

/// Build the `FactoryDescriptor` for compartment-workflow mandate cells.
pub fn cwm_factory_descriptor() -> FactoryDescriptor {
    FactoryDescriptor {
        factory_vk: CWM_FACTORY_VK,
        child_program_vk: Some(cwm_child_program_vk()),
        child_vk_strategy: Some(ChildVkStrategy::Fixed(Some(cwm_child_program_vk()))),
        allowed_cap_templates: vec![CapTemplate {
            target: CapTarget::SelfCell,
            max_permissions: AuthRequired::Signature,
            attenuatable: true,
        }],
        // No creation-time `field_constraints`: a factory-born mandate cell is
        // born empty and its first `init_mandate` turn binds `COMMITMENT_ANCHOR`
        // + `CHARTER_TERMINAL` (`WriteOnce`, frozen after), THEN `advance_step`
        // turns drive the cursor. The birth `NonZero`s validated against
        // `params.initial_fields`, forcing the seed path to mint placeholders.
        // Mirror privacy-voting/bounty-board.
        field_constraints: vec![],
        state_constraints: vec![
            // Compartment tag + charter bound are bound ONCE by `init_mandate`
            // (from zero) and frozen thereafter.
            StateConstraint::WriteOnce {
                index: COMMITMENT_ANCHOR_SLOT,
            },
            StateConstraint::WriteOnce {
                index: CHARTER_TERMINAL_SLOT,
            },
            // `Monotonic` (not `MonotonicSequence`): the installed flat program
            // fires on EVERY turn, so the `init_mandate` setup turn (cursor
            // 0 → 0) must be admitted while the cursor is still anti-rollback.
            // `MonotonicSequence`'s strict `+1` is enforced on the method-scoped
            // `advance_step` case of `cwm_cell_program`; the flat invariant here
            // is the weaker "cursor never decreases".
            StateConstraint::Monotonic {
                index: STEP_CURSOR_SLOT,
            },
            StateConstraint::FieldLteField {
                left_index: STEP_CURSOR_SLOT,
                right_index: CHARTER_TERMINAL_SLOT,
            },
        ],
        default_mode: CellMode::Sovereign,
        creation_budget: Some(DEFAULT_CREATION_BUDGET),
    }
}

/// All factory descriptors this starbridge-app contributes.
pub fn factory_descriptors() -> Vec<FactoryDescriptor> {
    vec![cwm_factory_descriptor()]
}

// =============================================================================
// Turn builders
// =============================================================================

/// Build the on-ledger [`Action`] that advances the mandate step cursor by one,
/// presenting `actor_clearance` as the acting officer's clearance label.
///
/// Effects (= [`advance_effects`]):
/// 1. `SetField(STEP_CURSOR_SLOT, new_cursor)` — `MonotonicSequence` enforces `+1`.
/// 2. `SetField(ACTOR_CLEARANCE_SLOT, actor_clearance)` — the officer's clearance.
/// 3. `SetField(STEP_COMPARTMENT_SLOT, phase.compartment)` — the entered step's box.
/// 4. `EmitEvent("workflow-step-advanced", [old_cursor, new_cursor, phase_label])`.
///
/// The executor's root-bound [`clearance_dominates_constraint`] then checks the
/// presented clearance dominates the entered compartment.
pub fn build_advance_step_action(
    cipherclerk: &AppCipherclerk,
    mandate_cell: CellId,
    current_cursor: u64,
    actor_clearance: FieldElement,
    phase: WorkflowPhase,
) -> Action {
    let new_cursor = current_cursor + 1;
    let effects = advance_effects(
        mandate_cell,
        new_cursor,
        actor_clearance,
        phase.compartment_label(),
    );
    cipherclerk.make_action(mandate_cell, "advance_step", effects)
}

/// Build an initialization action pinning the commitment anchor and charter metadata.
pub fn build_init_mandate_action(
    cipherclerk: &AppCipherclerk,
    mandate_cell: CellId,
    commitment_anchor: u64,
    charter_terminal: u64,
    clearance_graph_root: FieldElement,
    spend_policy: u64,
) -> Action {
    let effects = vec![
        Effect::SetField {
            cell: mandate_cell,
            index: COMMITMENT_ANCHOR_SLOT as usize,
            value: field_from_u64(commitment_anchor),
        },
        Effect::SetField {
            cell: mandate_cell,
            index: CHARTER_TERMINAL_SLOT as usize,
            value: field_from_u64(charter_terminal),
        },
        Effect::SetField {
            cell: mandate_cell,
            index: CLEARANCE_GRAPH_ROOT_SLOT as usize,
            value: clearance_graph_root,
        },
        Effect::SetField {
            cell: mandate_cell,
            index: SPEND_POLICY_SLOT as usize,
            value: field_from_u64(spend_policy),
        },
        Effect::EmitEvent {
            cell: mandate_cell,
            event: Event::new(
                symbol("workflow-mandate-initialized"),
                vec![
                    field_from_u64(commitment_anchor),
                    field_from_u64(charter_terminal),
                    clearance_graph_root,
                    field_from_u64(spend_policy),
                ],
            ),
        },
    ];

    cipherclerk.make_action(mandate_cell, "init_mandate", effects)
}

// =============================================================================
// StarbridgeAppContext mount
// =============================================================================

/// The canonical web-constants module — the single source of truth the
/// `pages/constants.generated.js` is rendered from (slot layout + the two
/// workflow event topics + the factory-vk hex).
pub fn web_constants() -> ConstantsModule {
    ConstantsModule::new("compartment-workflow-mandate")
        .slot("STEP_CURSOR_SLOT", STEP_CURSOR_SLOT as u64)
        .slot("COMMITMENT_ANCHOR_SLOT", COMMITMENT_ANCHOR_SLOT as u64)
        .slot("CHARTER_TERMINAL_SLOT", CHARTER_TERMINAL_SLOT as u64)
        .slot(
            "CLEARANCE_GRAPH_ROOT_SLOT",
            CLEARANCE_GRAPH_ROOT_SLOT as u64,
        )
        .slot("SPEND_POLICY_SLOT", SPEND_POLICY_SLOT as u64)
        .slot("ACTOR_CLEARANCE_SLOT", ACTOR_CLEARANCE_SLOT as u64)
        .slot("STEP_COMPARTMENT_SLOT", STEP_COMPARTMENT_SLOT as u64)
        .string("FACTORY_VK_HEX", hex_encode_32(&CWM_FACTORY_VK))
        .topic("INITIALIZED", "workflow-mandate-initialized")
        .topic("STEP_ADVANCED", "workflow-step-advanced")
}

/// Register the compartment-workflow-mandate starbridge-app on a shared context.
pub fn register(ctx: &StarbridgeAppContext) -> [u8; 32] {
    let factory_vk = ctx.register_factory(cwm_factory_descriptor());

    ctx.register_inspector(InspectorDescriptor {
        kind: "cwm-mandate".into(),
        descriptor: serde_json::json!({
            "component": "dregg-cwm-mandate",
            "module": "/starbridge-apps/compartment-workflow-mandate/inspectors.js",
            "uri_prefix": "dregg://cell/",
            "summary_fields": ["step_cursor", "commitment_anchor", "charter_terminal"],
            "slot_layout": {
                "step_cursor": STEP_CURSOR_SLOT,
                "commitment_anchor": COMMITMENT_ANCHOR_SLOT,
                "charter_terminal": CHARTER_TERMINAL_SLOT,
                "clearance_graph_root": CLEARANCE_GRAPH_ROOT_SLOT,
                "spend_policy": SPEND_POLICY_SLOT,
            },
            "factory_vk_hex": hex_encode_32(&factory_vk),
            "child_program_vk_hex": hex_encode_32(&cwm_child_program_vk()),
            "charter_phases": ["review", "redact", "sign"],
        }),
    });

    ctx.register_inspector_with("cwm-advance-form", || {
        serde_json::json!({
            "component": "dregg-cwm-advance-form",
            "module": "/starbridge-apps/compartment-workflow-mandate/inspectors.js",
            "uri_prefix": "dregg://cell/",
            "builders_module": "/starbridge-apps/compartment-workflow-mandate/turn-builders.js",
            "methods": ["advance_step", "init_mandate"],
        })
    });

    // Mount the deos-native composition surface (the `DeosApp`) on the SAME context —
    // the census promotion: the deos surface now ships from `src/`. The factory +
    // inspectors are where SOUNDNESS lives (a skipped/rewound step or a past-terminal
    // advance is a real executor refusal on the born cell); the deos surface is the
    // composition skin (per-viewer projection, the cap∧state gated fire, the `dregg://`
    // publish, the rehydratable snapshot, the manifest).
    register_deos(ctx);

    factory_vk
}

// =============================================================================
// The deos-native surface — the MANDATE as a composed `DeosApp`.
// =============================================================================
//
// `docs/deos/APPS-DEOS-INTEGRATION-CENSUS.md` (the workflow port): the compartment
// workflow MANDATE, re-expressed as a composed [`DeosApp`] and PROMOTED into
// `src/lib.rs`. The workflow operations are ONE [`DeosApp`] ([`workflow_app`] below);
// the framework wires the rest — per-viewer projection, web-of-cells publish (the
// MANDATE cell IS a `dregg://` sturdyref), the rehydratable frustum-snapshot, the
// generated `<dregg-affordance-surface>` component, and the manifest — none of which
// the floor's bones had.
//
// **The seam is closed** — a TWO-TEMPO fire (mirror supply-chain-provenance /
// subscription). The state-advancing operation (`advance_step`) is a
// [`GatedAffordance`] carrying a live-state PRECONDITION ([`not_at_terminal_precondition`]:
// the cursor has not reached the charter terminal); the FULL workflow program
// ([`cwm_cell_program`]: the `Always` invariants — `WriteOnce` config slots +
// `FieldLteField(STEP_CURSOR <= CHARTER_TERMINAL)` — AND the `advance_step`-scoped
// `MonotonicSequence(STEP_CURSOR)` exact-`+1`) is INSTALLED on the seeded mandate cell
// ([`seed_workflow`]) and RE-ENFORCED by the executor on every touching turn:
//
//   1. the deos PRECONDITION gate (the cap-gate `is_attenuation` AND the live-state
//      precondition `CellProgram::evaluate`) decides the button's verdict IN-BAND —
//      nothing submitted on a miss (anti-ghost; the htmx reactivity rides this);
//   2. [`fire_advance_step`] then submits the FULL multi-effect advance turn
//      ([`advance_effects`]: the cursor `SetField` + the step-advanced event), and the
//      executor RE-ENFORCES the installed program — so a SKIPPED/REPEATED step (a
//      cursor that does not advance by exactly `+1`, `MonotonicSequence(STEP_CURSOR)`),
//      a REWOUND cursor (`Monotonic`/`MonotonicSequence` anti-rollback), and a
//      PAST-TERMINAL advance (`FieldLteField(STEP_CURSOR <= CHARTER_TERMINAL)`) are all
//      REAL executor refusals in the SUBMISSION path — the half the floor's
//      `evaluate`-only / `cwm_advance_admits`-only tests never exercised through a real
//      signed turn (see `tests/deos_seam.rs`).
//
// Both gates are the genuine ones (`is_attenuation` + `CellProgram::evaluate`). The
// `advance_step` cursor advance is read from the cell's LIVE `STEP_CURSOR`, so each fire
// drives the SAME published button one step further along the charter DAG.

/// The workflow rights tiers, ON THE REAL ATTENUATION LATTICE:
///
///   - an OBSERVER (an auditor / a watcher) holds [`AuthRequired::Signature`] — the
///     narrow read tier: it can `view_workflow` (read the charter cursor) and nothing
///     else;
///   - an OPERATOR (a clerk/officer driving the charter) holds [`AuthRequired::None`]/root
///     — it can `advance_step` (advance the DAG cursor) on top of everything an observer
///     can do.
///
/// So `Signature ⊂ None` IS the observer ⊂ operator ladder.
pub const OBSERVER_RIGHTS: AuthRequired = AuthRequired::Signature;
/// The operator rights tier (root — advance the workflow cursor + view). See [`OBSERVER_RIGHTS`].
pub const OPERATOR_RIGHTS: AuthRequired = AuthRequired::None;

/// The `advance_step` **live-state precondition** — the cursor must NOT yet be AT the
/// charter terminal (`STEP_CURSOR <= CHARTER_TERMINAL - 1`, i.e. `STEP_CURSOR < CHARTER_TERMINAL`).
/// A real [`CellProgram`] read against the cell's current state, so the `advance_step`
/// button is LIT while steps remain and DARK once the cursor reaches the terminal (the
/// htmx tooth). This gates "may `advance_step` fire now"; the charter INVARIANT
/// (`FieldLteField(STEP_CURSOR <= CHARTER_TERMINAL)` + the `MonotonicSequence(STEP_CURSOR)`
/// exact-`+1`) is the installed [`cwm_cell_program`] the executor re-enforces on the
/// produced transition.
pub fn not_at_terminal_precondition() -> CellProgram {
    // `cursor < terminal` ≡ `cursor <= terminal - 1` ≡ `FieldLteOther { cursor, terminal, delta: -1 }`.
    CellProgram::Predicate(vec![StateConstraint::FieldLteOther {
        index: STEP_CURSOR_SLOT,
        other: CHARTER_TERMINAL_SLOT,
        delta: -1,
    }])
}

/// **`advance_step` effects** — the multi-effect advance body for a target cursor:
/// advance `STEP_CURSOR` to `new_cursor` (`MonotonicSequence` enforces the exact `+1`
/// on the produced transition), MATERIALIZE the acting officer's clearance label
/// into `ACTOR_CLEARANCE_SLOT` and the entered step's compartment into
/// `STEP_COMPARTMENT_SLOT` (so the executor's [`clearance_dominates_constraint`]
/// reads both from post-state), and emit `workflow-step-advanced`. This is the ONE
/// coherent transition the installed program admits (the cursor advances by exactly
/// one step, the config slots stay frozen, `STEP_CURSOR <= CHARTER_TERMINAL` preserved,
/// AND the actor's clearance dominates the entered step's compartment in the
/// root-bound charter graph). `new_anchor` is the compartment label for the step just
/// entered — it both labels the event AND is the box the clearance check reads. THIS
/// is the turn [`fire_advance_step`] submits.
pub fn advance_effects(
    cell: CellId,
    new_cursor: u64,
    actor_clearance: FieldElement,
    new_anchor: FieldElement,
) -> Vec<Effect> {
    let old_field = field_from_u64(new_cursor.saturating_sub(1));
    let new_field = field_from_u64(new_cursor);
    vec![
        Effect::SetField {
            cell,
            index: STEP_CURSOR_SLOT as usize,
            value: new_field,
        },
        // The acting officer presents their clearance label — the executor's
        // ClearanceDominates checks it dominates the entered step's compartment.
        Effect::SetField {
            cell,
            index: ACTOR_CLEARANCE_SLOT as usize,
            value: actor_clearance,
        },
        // The compartment of the step being ENTERED — the box the clearance check
        // reads (the per-step `needsAll [step.compartment]` of `stepClearanceOK`).
        Effect::SetField {
            cell,
            index: STEP_COMPARTMENT_SLOT as usize,
            value: new_anchor,
        },
        Effect::EmitEvent {
            cell,
            event: Event::new(
                symbol("workflow-step-advanced"),
                vec![old_field, new_field, new_anchor],
            ),
        },
    ]
}

/// The charter-phase compartment label for the step just ENTERED at `cursor` (the
/// post-advance cursor names the phase whose `step_id == cursor - 1`). Falls back to a
/// zero label past the charter (the executor refuses such an advance anyway).
fn phase_label_for(cursor: u64) -> FieldElement {
    cursor
        .checked_sub(1)
        .and_then(|i| WorkflowPhase::CHARTER.get(i as usize).copied())
        .map(|p| p.compartment_label())
        .unwrap_or([0u8; 32])
}

/// **The compartment workflow MANDATE as a composed [`DeosApp`]** — the whole
/// interaction surface, on the deos bones. The mandate cell is the agent's OWN cell
/// (`cipherclerk.cell_id()`) so fires execute against the seeded embedded ledger.
///
/// Two operations on the MANDATE cell, on the observer ⊂ operator rights ladder:
///
///   - `view_workflow` — a cap-only affordance (an OBSERVER reads the charter cursor):
///     `Signature`, an `EmitEvent`;
///   - `advance_step` — a [`GatedAffordance`] (an OPERATOR advances the DAG cursor):
///     `None`/operator, a live-state PRECONDITION (the cursor is not yet at the
///     terminal); the real fire ([`fire_advance_step`]) submits the FULL advance turn,
///     re-enforced by the executor's installed program (`MonotonicSequence(STEP_CURSOR)`
///     exact-`+1` AND `FieldLteField(STEP_CURSOR <= CHARTER_TERMINAL)` BITE on the
///     produced transition).
///
/// The mandate cell is published into the web-of-cells at the observer tier (an auditor
/// on another federation reacquires the workflow's charter state across the membrane) and
/// is discoverable under `workflow` / `compartment`.
///
/// Seed the cell's program + charter config with [`seed_workflow`] so the gated fire has
/// a live state and the executor re-enforces the program.
pub fn workflow_app(cipherclerk: &AppCipherclerk, executor: &EmbeddedExecutor) -> DeosApp {
    let cell = cipherclerk.cell_id();

    // `advance_step` — an OPERATOR advances the charter DAG cursor. The GatedAffordance
    // carries the DECISIVE effect (the cursor `SetField`) as its surface representative
    // AND a live-state PRECONDITION ([`not_at_terminal_precondition`]: the cursor has not
    // reached the charter terminal) — so the button is lit while steps remain and dark at
    // the terminal (the htmx tooth), and the cap∧state gate decides its verdict in-band.
    // The actual fire ([`fire_advance_step`]) submits the FULL advance turn
    // ([`advance_effects`]: cursor + step-advanced event) reading the LIVE cursor, which
    // the executor re-enforces the installed program on — so `MonotonicSequence(STEP_CURSOR)`
    // BITES: a skipped/repeated/rewound cursor is REFUSED.
    let advance = GatedAffordance::new(
        CellAffordance::new(
            "advance_step",
            OPERATOR_RIGHTS,
            Effect::SetField {
                cell,
                index: STEP_CURSOR_SLOT as usize,
                value: field_from_u64(1),
            },
        ),
        not_at_terminal_precondition(),
    );
    // `view_workflow` — an observer reads the charter cursor. Cap-only.
    let view = CellAffordance::new(
        "view_workflow",
        OBSERVER_RIGHTS,
        Effect::EmitEvent {
            cell,
            event: Event::new(symbol("workflow-read"), vec![]),
        },
    );

    DeosApp::builder(
        "compartment-workflow-mandate",
        cipherclerk.clone(),
        executor.clone(),
    )
    .discoverable(vec!["workflow".into(), "compartment".into()])
    .cell(
        DeosCell::new(cell, "workflow")
            .affordance(view)
            .gated(advance)
            .publish(AuthRequired::Signature),
    )
    .build()
}

/// **Seed the MANDATE cell** so the gated fire has live state + the program bites:
/// install the full workflow [`cwm_cell_program`] on the seeded mandate cell (so the
/// executor re-enforces it on every touching turn), then bind the charter config
/// (`COMMITMENT_ANCHOR`, `CHARTER_TERMINAL`, `CLEARANCE_GRAPH_ROOT`, `SPEND_POLICY` —
/// `WriteOnce`, frozen after) and set `STEP_CURSOR = 0` directly into the embedded
/// ledger.
///
/// `charter_terminal` is set to a small value (the seam drives the cursor up to and past
/// it). After seeding, the mandate is at cursor 0 with the charter pinned — a real
/// `(old, new)` baseline against which `advance_step` advances. Returns the seeded
/// `CHARTER_TERMINAL` value.
pub fn seed_workflow(
    executor: &EmbeddedExecutor,
    commitment_anchor: u64,
    charter_terminal: u64,
    clearance_graph_root: FieldElement,
    spend_policy: u64,
) -> u64 {
    let cell = executor.cell_id();
    executor.install_program(cell, cwm_cell_program());
    executor.with_ledger_mut(|ledger| {
        if let Some(c) = ledger.get_mut(&cell) {
            c.state.set_field(
                COMMITMENT_ANCHOR_SLOT as usize,
                field_from_u64(commitment_anchor),
            );
            c.state.set_field(
                CHARTER_TERMINAL_SLOT as usize,
                field_from_u64(charter_terminal),
            );
            c.state
                .set_field(CLEARANCE_GRAPH_ROOT_SLOT as usize, clearance_graph_root);
            c.state
                .set_field(SPEND_POLICY_SLOT as usize, field_from_u64(spend_policy));
            c.state
                .set_field(STEP_CURSOR_SLOT as usize, field_from_u64(0));
        }
    });
    charter_terminal
}

/// **Fire `advance_step`** — the deos cap∧state PRECONDITION gate (anti-ghost, in-band),
/// then the FULL multi-effect advance turn the executor re-enforces the workflow program
/// on. The two-tempo bridge: the gated affordance decides the button's verdict (cap ⊇
/// operator AND the cursor is not at the terminal) WITHOUT touching the executor; on both
/// passing, the complete cursor-advancing turn ([`advance_effects`]) is submitted reading
/// the LIVE `STEP_CURSOR`, and the executor's re-enforcement of [`cwm_cell_program`] is the
/// SECOND, verified gate (`MonotonicSequence(STEP_CURSOR)` exact-`+1` AND
/// `FieldLteField(STEP_CURSOR <= CHARTER_TERMINAL)` bite — a skipped/rewound cursor or a
/// past-terminal advance is REFUSED). Anti-ghost both ways: a precondition miss never
/// submits; a program violation is a real executor refusal.
///
/// The cursor is read from the cell's live state (current `STEP_CURSOR` ⇒ `+1`), so the
/// caller threads only WHICH actor is advancing — `actor_clearance` is the acting
/// officer's clearance label, materialized into `ACTOR_CLEARANCE_SLOT` so the
/// executor's [`clearance_dominates_constraint`] checks it dominates the entered step's
/// compartment in the root-bound charter graph (an officer advances every step; a clerk
/// is REFUSED past `review`). Use [`seed_workflow`] first.
pub fn fire_advance_step(
    app: &DeosApp,
    held: &AuthRequired,
    actor_clearance: FieldElement,
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
) -> Result<TurnReceipt, FireExecuteError> {
    let cell = &app.cells()[0];
    // The accumulating fire: the cap∧state gate is run in-band by
    // `fire_gated_through_executor_with`; on both passing, the closure derives the
    // advance effects from the LIVE cursor (so the button advances each time) and
    // materializes the actor clearance + entered step compartment for the executor's
    // root-bound ClearanceDominates tooth.
    cell.fire_gated_through_executor_with("advance_step", held, cipherclerk, executor, |live| {
        let live_cursor = field_to_u64(&live.fields[STEP_CURSOR_SLOT as usize]);
        let next = live_cursor + 1;
        advance_effects(cell.cell(), next, actor_clearance, phase_label_for(next))
    })
}

/// Read a `u64` from the last 8 big-endian bytes of a field element (the inverse of
/// [`field_from_u64`] for the `STEP_CURSOR` the workflow stores).
fn field_to_u64(f: &FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&f[24..32]);
    u64::from_be_bytes(b)
}

/// **Mount the deos-native surface** ([`workflow_app`]) on a shared context: build the
/// composed [`DeosApp`] from the context's cipherclerk + executor, seed the mandate
/// cell's program + charter config (so the gated fire bites), and fold the app into the
/// context's affordance registry ([`DeosApp::register`]). Returns the live [`DeosApp`]
/// (so a host can also [`DeosApp::mount`] its axum router / [`DeosApp::publish_all`]
/// into the web-of-cells). This is the PROMOTION the census asks for: the deos surface
/// now ships from `src/`, not from a side-proof in `tests/`.
///
/// Seeds a small charter terminal ([`DEFAULT_CHARTER_STEPS`] = 3) so the seam can drive
/// the cursor up to and past the terminal.
pub fn register_deos(ctx: &StarbridgeAppContext) -> DeosApp {
    let app = workflow_app(ctx.cipherclerk(), ctx.executor());
    // Seed the mandate cell so the gated `advance_step` fire has a live `(old, new)` and
    // the full workflow program (installed here) is re-enforced by the executor on every
    // touching turn. Charter terminal = 3 (review → redact → sign).
    seed_workflow(
        ctx.executor(),
        DEFAULT_COMMITMENT_ANCHOR,
        DEFAULT_CHARTER_STEPS,
        // The REAL charter clearance-graph commitment — so the executor's
        // root-bound ClearanceDominates admits a cleared officer and refuses a
        // clerk past `review` (a bogus root would fail EVERY advance closed).
        charter_clearance_root(),
        DEFAULT_STEP_SPEND_POLICY,
    );
    app.register(ctx);
    app
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::{AgentCipherclerk, Authorization, EmbeddedExecutor};

    fn test_cipherclerk() -> AppCipherclerk {
        AppCipherclerk::new(AgentCipherclerk::new(), [42u8; 32])
    }

    fn test_context() -> StarbridgeAppContext {
        let cipherclerk = test_cipherclerk();
        let executor = EmbeddedExecutor::new(&cipherclerk, "default");
        StarbridgeAppContext::new(cipherclerk, executor)
    }

    fn test_cell() -> CellId {
        CellId::from_bytes([7u8; 32])
    }

    #[test]
    fn factory_descriptor_is_stable() {
        let h1 = cwm_factory_descriptor().hash();
        let h2 = cwm_factory_descriptor().hash();
        assert_eq!(h1, h2);
    }

    #[test]
    fn step_admissible_matches_lean_charter() {
        assert!(step_admissible(0, &[], WorkflowPhase::Review));
        assert!(!step_admissible(1, &[], WorkflowPhase::Redact));
        assert!(step_admissible(1, &[0], WorkflowPhase::Redact));
        assert!(step_admissible(2, &[0, 1], WorkflowPhase::Sign));
        assert!(!step_admissible(2, &[0], WorkflowPhase::Sign));
    }

    #[test]
    fn cwm_advance_admits_officer_labels() {
        let officer = clearance_label("officer");
        let labels = [officer, clearance_label("review")];
        assert_eq!(
            cwm_advance_admits(0, DEFAULT_CHARTER_STEPS, &labels),
            Some(WorkflowPhase::Review)
        );
        // Scaffold clearance check uses compartment label membership; officer-only
        // demo in Lean passes review with officer label dominating review compartment
        // via the graph — here we include the phase label directly for the skeleton.
        let phase_labels = [clearance_label("review")];
        assert_eq!(
            cwm_advance_admits(0, DEFAULT_CHARTER_STEPS, &phase_labels),
            Some(WorkflowPhase::Review)
        );
    }

    #[test]
    fn advance_action_carries_set_field_and_emit_event() {
        let cipherclerk = test_cipherclerk();
        let action =
            build_advance_step_action(&cipherclerk, test_cell(), 0, officer_label(), WorkflowPhase::Review);
        // cursor + actor clearance + step compartment + event.
        assert_eq!(action.effects.len(), 4);
        assert!(matches!(
            &action.effects[0],
            Effect::SetField { index, .. } if *index == STEP_CURSOR_SLOT as usize
        ));
        assert!(matches!(
            &action.effects[1],
            Effect::SetField { index, .. } if *index == ACTOR_CLEARANCE_SLOT as usize
        ));
        assert!(matches!(
            &action.effects[2],
            Effect::SetField { index, .. } if *index == STEP_COMPARTMENT_SLOT as usize
        ));
        assert!(matches!(&action.effects[3], Effect::EmitEvent { .. }));
    }

    #[test]
    fn advance_action_carries_real_signature() {
        let cipherclerk = test_cipherclerk();
        let action =
            build_advance_step_action(&cipherclerk, test_cell(), 1, officer_label(), WorkflowPhase::Redact);
        match action.authorization {
            Authorization::Signature(a, b) => {
                assert!(a != [0u8; 32] || b != [0u8; 32]);
            }
            other => panic!("expected Signature, got {other:?}"),
        }
    }

    #[test]
    fn register_installs_factory_and_inspectors() {
        let ctx = test_context();
        let vk = register(&ctx);
        assert_eq!(vk, CWM_FACTORY_VK);
        assert_eq!(ctx.factory_registry().len(), 1);
        assert!(ctx.inspector_registry().get("cwm-mandate").is_some());
        assert!(ctx.inspector_registry().get("cwm-advance-form").is_some());
    }
}
