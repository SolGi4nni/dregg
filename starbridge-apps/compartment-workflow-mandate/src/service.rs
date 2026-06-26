//! # compartment-workflow-mandate — the charter DAG as a SERVICE CELL on the
//! `invoke()` front door (AX3).
//!
//! The third axis of a modern starbridge-app: the mandate's `advance_step`
//! operation re-expressed as a CELLS-AS-SERVICE-OBJECTS citizen (after the
//! `bounty-board` / `kvstore` / `escrow-market` exemplars). A `service` module on
//! the existing crate publishes a first-class, typed [`InterfaceDescriptor`] and
//! drives the charter through the [`dregg_app_framework::invoke`] front door — the
//! userspace method-dispatch layer that sits *slightly above* the effect-VM and
//! desugars a method call to the ordinary verified effects it names. There is **no
//! `Effect::Invoke`**, no kernel change, no new circuit rung: the kernel and the
//! light client keep seeing only the
//! [`SetField`](dregg_app_framework::Effect::SetField) /
//! [`EmitEvent`](dregg_app_framework::Effect::EmitEvent) effects they already
//! enforce and witness.
//!
//! ## Non-degrading: the SAME canonical advance body
//!
//! `advance_step` desugars to the IDENTICAL [`crate::advance_effects`] body the lib
//! builder ([`crate::build_advance_step_action`]) and the deos fire
//! ([`crate::fire_advance_step`]) produce — the cursor `SetField`, the materialized
//! actor clearance + entered-step compartment (so the executor's root-bound
//! [`ClearanceDominates`](dregg_app_framework::StateConstraint::ClearanceDominates)
//! reads both), and the `workflow-step-advanced` event. So the workflow teeth
//! re-enforce on every invoke()-desugared turn exactly as on a deos-fired one: a
//! skipped/rewound cursor (`MonotonicSequence(STEP_CURSOR)`), a past-terminal
//! advance (`FieldLteField(STEP_CURSOR <= CHARTER_TERMINAL)`), and a clerk advancing
//! past `review` (the root-bound clearance tooth) are all REAL executor refusals.
//!
//! ## The published interface (the charter as typed methods)
//!
//! | method         | semantics                 | auth        | args                              | desugars to |
//! |----------------|---------------------------|-------------|-----------------------------------|-------------|
//! | `advance_step` | [`Semantics::Replayable`] | `Signature` | `(new_cursor, clearance, box)`    | [`crate::advance_effects`] |
//! | `view`         | [`Semantics::Serviced`]   | `None`      | `()`                              | — (the named OFE seam: a pure read, no turn) |
//!
//! The cap-gate (`Signature` on `advance_step`) is enforced twice over: at the
//! `invoke()` front door (an unauthorized caller is refused before any turn is
//! built — anti-ghost) and again by the executor (the desugared turn carries a real
//! signature the kernel verifies, and the installed program's clearance/monotonic
//! teeth bite on the commit path).

use dregg_app_framework::{
    AppCipherclerk, Effect, FieldElement, InterfaceRegistry, InvokeAuthority, InvokeRefused, Turn,
    field_from_u64, invoke_with_descriptor,
};
use dregg_cell::interface::{ArgsSchema, InterfaceDescriptor, MethodSig, Semantics, method_symbol};
use dregg_cell::permissions::AuthRequired;
use dregg_types::CellId;

use crate::{WorkflowPhase, advance_effects};

// =============================================================================
// Method names
// =============================================================================

/// The `advance_step` method — a [`Semantics::Replayable`], `Signature`-gated
/// mutator: advance the charter cursor by exactly one step, presenting the acting
/// officer's clearance for the executor's root-bound clearance tooth.
pub const METHOD_ADVANCE_STEP: &str = "advance_step";
/// The `view` method — a [`Semantics::Serviced`] read (the named OFE seam): read
/// the mandate's committed charter cursor. Never desugared.
pub const METHOD_VIEW: &str = "view";

// =============================================================================
// The published, typed interface
// =============================================================================

/// **The mandate's first-class typed interface** — the two methods it publishes,
/// with their auth and replayable-vs-serviced semantics.
///
/// The richer-than-derived descriptor: `derive_replayable` would make every method
/// `Replayable`/`None`, but the mandate wants `advance_step` `Signature`-gated and
/// `view` marked `Serviced`. An app registers THIS in an [`InterfaceRegistry`] so
/// the Service Explorer resolves the real auth + seam shape.
pub fn interface_descriptor() -> InterfaceDescriptor {
    InterfaceDescriptor::new(vec![
        // advance_step(new_cursor, clearance, box): advance the charter DAG cursor.
        MethodSig {
            args_schema: ArgsSchema::Fixed(3),
            auth_required: AuthRequired::Signature,
            ..MethodSig::replayable(method_symbol(METHOD_ADVANCE_STEP))
        },
        // view(): a pure read — the named OFE seam, never desugared.
        MethodSig {
            args_schema: ArgsSchema::Fixed(0),
            auth_required: AuthRequired::None,
            semantics: Semantics::Serviced,
            ..MethodSig::replayable(method_symbol(METHOD_VIEW))
        },
    ])
}

/// Register the mandate's [`interface_descriptor`] for `cell` in a userspace
/// [`InterfaceRegistry`] — the resolution path the Service Explorer consults before
/// falling back to derive-from-program. After this, the explorer resolves the
/// mandate's real `Signature`/`Serviced` shape.
pub fn register_interface(registry: &mut InterfaceRegistry, cell: CellId) {
    registry.register(cell, interface_descriptor());
}

// =============================================================================
// The service handle — building invocations through invoke()
// =============================================================================

/// **A handle to a deployed mandate cell** — bundles the mandate cell with its
/// published interface, and builds method invocations through the `invoke()` front
/// door.
///
/// Each builder returns a fully-signed [`Turn`] (the build half); submit it through
/// an executor ([`dregg_app_framework::EmbeddedExecutor::submit_turn`], a node
/// `/turns/submit`, …) to actually commit. A refusal at the front door (unknown
/// method, insufficient authority, a serviced seam) is surfaced as an
/// [`InvokeRefused`] before any turn is built — fail-closed.
#[derive(Clone, Debug)]
pub struct WorkflowService {
    /// The mandate cell this handle drives.
    pub cell: CellId,
    /// The mandate's published typed interface (the richer-than-derived one).
    pub descriptor: InterfaceDescriptor,
}

impl WorkflowService {
    /// A handle to the mandate cell `cell`, carrying the mandate's published
    /// [`interface_descriptor`].
    pub fn new(cell: CellId) -> Self {
        WorkflowService {
            cell,
            descriptor: interface_descriptor(),
        }
    }

    /// **Invoke `advance_step(new_cursor, clearance, box)`** — advance the charter
    /// cursor from `current_cursor` to `current_cursor + 1`, entering `phase`'s
    /// compartment and presenting `actor_clearance` as the acting officer's
    /// clearance label. Routes through the verified DFA, cap-gates on `Signature`,
    /// and desugars to the SAME [`crate::advance_effects`] body the lib builder
    /// produces — so the executor re-enforces the installed workflow program
    /// (`MonotonicSequence(STEP_CURSOR)` exact-`+1`, `FieldLteField(STEP_CURSOR <=
    /// CHARTER_TERMINAL)`, and the root-bound `ClearanceDominates`) on the commit
    /// path. A clerk advancing past `review`, a skipped/rewound cursor, or a
    /// past-terminal advance is a REAL executor refusal, not a userspace check.
    pub fn advance_step(
        &self,
        cipherclerk: &AppCipherclerk,
        current_cursor: u64,
        actor_clearance: FieldElement,
        phase: WorkflowPhase,
        authority: InvokeAuthority,
    ) -> Result<Turn, WorkflowServiceError> {
        let new_cursor = current_cursor + 1;
        let box_label = phase.compartment_label();
        let effects = advance_effects(self.cell, new_cursor, actor_clearance, box_label);
        self.invoke(
            cipherclerk,
            METHOD_ADVANCE_STEP,
            vec![field_from_u64(new_cursor), actor_clearance, box_label],
            effects,
            authority,
        )
    }

    /// **Attempt to invoke `view()`** — which ALWAYS refuses with
    /// [`InvokeRefused::ServicedSeam`]: `view` is a [`Semantics::Serviced`] read,
    /// answered by the OFE cross-cell-read (the mandate's committed charter cursor),
    /// not a replay desugar. This method exists to make the seam legible (and
    /// testable): a serviced read is not a turn, and `invoke()` will not pretend
    /// otherwise. To actually READ the mandate, read the committed
    /// [`STEP_CURSOR_SLOT`](crate::STEP_CURSOR_SLOT).
    pub fn view(&self, cipherclerk: &AppCipherclerk) -> Result<Turn, WorkflowServiceError> {
        self.invoke(
            cipherclerk,
            METHOD_VIEW,
            vec![],
            vec![],
            InvokeAuthority::None,
        )
    }

    /// Route → cap-gate → desugar → sign, through the `invoke()` front door against
    /// this mandate's published descriptor.
    fn invoke(
        &self,
        cipherclerk: &AppCipherclerk,
        method: &str,
        args: Vec<FieldElement>,
        effects: Vec<Effect>,
        authority: InvokeAuthority,
    ) -> Result<Turn, WorkflowServiceError> {
        invoke_with_descriptor(
            cipherclerk,
            self.cell,
            &self.descriptor,
            method,
            args,
            effects,
            authority,
        )
        .map_err(WorkflowServiceError::Refused)
    }
}

/// Why a [`WorkflowService`] invocation could not be built.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WorkflowServiceError {
    /// The `invoke()` front door refused (unknown method, insufficient authority,
    /// or a serviced seam) — fail-closed, no turn built.
    Refused(InvokeRefused),
}

impl std::fmt::Display for WorkflowServiceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            WorkflowServiceError::Refused(r) => write!(f, "invoke refused: {r}"),
        }
    }
}

impl std::error::Error for WorkflowServiceError {}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::AgentCipherclerk;

    use crate::officer_label;

    #[test]
    fn interface_publishes_two_typed_methods() {
        let iface = interface_descriptor();
        assert_eq!(iface.methods.len(), 2);
        assert!(iface.verify_id());

        let advance = iface.method(&method_symbol(METHOD_ADVANCE_STEP)).unwrap();
        assert_eq!(advance.semantics, Semantics::Replayable);
        assert_eq!(advance.auth_required, AuthRequired::Signature);

        let view = iface.method(&method_symbol(METHOD_VIEW)).unwrap();
        assert_eq!(view.semantics, Semantics::Serviced);
        assert_eq!(view.auth_required, AuthRequired::None);
    }

    #[test]
    fn unauthorized_advance_refused_at_the_front_door() {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x11; 32]);
        let svc = WorkflowService::new(cclerk.cell_id());
        // `advance_step` needs `Signature`; a `None` holder is refused before any
        // turn is built (anti-ghost).
        assert!(matches!(
            svc.advance_step(
                &cclerk,
                0,
                officer_label(),
                WorkflowPhase::Review,
                InvokeAuthority::None
            ),
            Err(WorkflowServiceError::Refused(InvokeRefused::Unauthorized {
                required: AuthRequired::Signature,
                ..
            }))
        ));
    }

    #[test]
    fn view_is_a_serviced_seam_never_desugared() {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x11; 32]);
        let svc = WorkflowService::new(cclerk.cell_id());
        assert!(matches!(
            svc.view(&cclerk),
            Err(WorkflowServiceError::Refused(
                InvokeRefused::ServicedSeam { .. }
            ))
        ));
    }
}
