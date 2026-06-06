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

use dregg_app_framework::{
    Action, AppCipherclerk, AuthRequired, CapTarget, CapTemplate, CellId, CellMode, CellProgram,
    ChildVkStrategy, Effect, Event, FactoryDescriptor, FieldConstraint, FieldElement,
    InspectorDescriptor, StarbridgeAppContext, StateConstraint, TransitionCase, TransitionGuard,
    canonical_program_vk, field_from_bytes, field_from_u64, hex_encode_32, symbol,
};

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
    phase.prerequisites().iter().all(|need| completed.contains(need))
        && !completed.contains(&step_id)
}

/// **`step_clearance_ok`** — actor labels dominate the step's compartment.
///
/// Scaffold: checks that `actor_label_hashes` contains the step compartment.
/// Full `needsAll` over a `ClearanceGraph` lands when the graph root verifier
/// is wired (Lean `Authority/ClearanceGraph.lean`).
pub fn step_clearance_ok(phase: WorkflowPhase, actor_label_hashes: &[FieldElement]) -> bool {
    let required = phase.compartment_label();
    actor_label_hashes.contains(&required)
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
                StateConstraint::Immutable {
                    index: COMMITMENT_ANCHOR_SLOT,
                },
                StateConstraint::Immutable {
                    index: CHARTER_TERMINAL_SLOT,
                },
                StateConstraint::Immutable {
                    index: CLEARANCE_GRAPH_ROOT_SLOT,
                },
                StateConstraint::Immutable {
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
            constraints: vec![StateConstraint::MonotonicSequence {
                seq_index: STEP_CURSOR_SLOT,
            }],
        },
    ])
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
        field_constraints: vec![
            FieldConstraint::NonZero {
                field_index: COMMITMENT_ANCHOR_SLOT as u32,
            },
            FieldConstraint::NonZero {
                field_index: CHARTER_TERMINAL_SLOT as u32,
            },
        ],
        state_constraints: vec![
            StateConstraint::Immutable {
                index: COMMITMENT_ANCHOR_SLOT,
            },
            StateConstraint::MonotonicSequence {
                seq_index: STEP_CURSOR_SLOT,
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

/// Build the on-ledger [`Action`] that advances the mandate step cursor by one.
///
/// Effects:
/// 1. `SetField(STEP_CURSOR_SLOT, new_cursor)` — `MonotonicSequence` enforces `+1`.
/// 2. `EmitEvent("workflow-step-advanced", [old_cursor, new_cursor, phase_label])`.
pub fn build_advance_step_action(
    cipherclerk: &AppCipherclerk,
    mandate_cell: CellId,
    current_cursor: u64,
    phase: WorkflowPhase,
) -> Action {
    let new_cursor = current_cursor + 1;
    let old_field = field_from_u64(current_cursor);
    let new_field = field_from_u64(new_cursor);
    let phase_label = phase.compartment_label();

    let effects = vec![
        Effect::SetField {
            cell: mandate_cell,
            index: STEP_CURSOR_SLOT as usize,
            value: new_field,
        },
        Effect::EmitEvent {
            cell: mandate_cell,
            event: Event::new(
                symbol("workflow-step-advanced"),
                vec![old_field, new_field, phase_label],
            ),
        },
    ];

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

    factory_vk
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
        let action = build_advance_step_action(&cipherclerk, test_cell(), 0, WorkflowPhase::Review);
        assert_eq!(action.effects.len(), 2);
        assert!(matches!(
            &action.effects[0],
            Effect::SetField { index, .. } if *index == STEP_CURSOR_SLOT as usize
        ));
        assert!(matches!(&action.effects[1], Effect::EmitEvent { .. }));
    }

    #[test]
    fn advance_action_carries_real_signature() {
        let cipherclerk = test_cipherclerk();
        let action = build_advance_step_action(&cipherclerk, test_cell(), 1, WorkflowPhase::Redact);
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