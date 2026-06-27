//! # agent-orchestration — the coordinator board as a SERVICE CELL on the `invoke()`
//! front door.
//!
//! The third axis (AX3) of a modern starbridge-app: the durable+auditable coordinator
//! board re-expressed as a CELLS-AS-SERVICE-OBJECTS citizen (after the `bounty-board` /
//! `swarm-orchestration` / `escrow-market` exemplars). A `service` module on the
//! existing crate: it publishes a first-class, typed [`InterfaceDescriptor`] and drives
//! the orchestration through the [`dregg_app_framework::invoke`] front door — the
//! userspace method-dispatch layer that sits *slightly above* the effect-VM and
//! desugars a method call to the ordinary verified effects it names. There is **no
//! `Effect::Invoke`**, no kernel change, no new circuit rung: the kernel and the light
//! client keep seeing only the
//! [`SetField`](dregg_app_framework::Effect::SetField) /
//! [`EmitEvent`](dregg_app_framework::Effect::EmitEvent) /
//! [`GrantCapability`](dregg_app_framework::Effect::GrantCapability) effects they
//! already enforce and witness. The one extra fact — that an invoked method is a member
//! of the cell's interface — is decided by the SAME verified DFA router
//! ([`InterfaceDescriptor::route_method`]) the protocol already uses.
//!
//! ## Non-degrading: the SAME canonical coordinator program
//!
//! The service face installs/assumes the IDENTICAL canonical
//! [`coordinator_program`](crate::coordinator_program) (=
//! [`coordinator_constraints`](crate::coordinator_constraints)) the
//! [`FactoryDescriptor`](crate::orchestration_factory_descriptor) bakes into every
//! factory-born coordinator cell. So the swarm teeth re-enforce on every
//! invoke()-desugared turn exactly as they do on a factory-born cell's turns:
//!
//! | Slot      | Caveat            | Bites on |
//! |-----------|-------------------|----------|
//! | `LEAD`    | `WriteOnce`       | `open_board` (admit-from-zero), then frozen |
//! | `BUDGET`  | `WriteOnce`       | `open_board` (admit-from-zero), then frozen — never widened |
//! | `SPENT_A` | `Monotonic`       | `worker_step` to worker A (never rolled back) |
//! | `SPENT_B` | `Monotonic`       | `worker_step` to worker B (never rolled back) |
//! | `EPOCH`   | `StrictMonotonic` | every turn (no replay — each step strictly advances) |
//! | budget    | `AffineLe`        | every `worker_step` (`spent_a + spent_b <= budget`) |
//!
//! The `FactoryDescriptor` federation surface, the
//! [`DeosApp`](dregg_app_framework::DeosApp) composition skin
//! ([`orchestration_app`](crate::deos::orchestration_app)), the durable workflow engine
//! ([`OrchestrationEngine`](crate::OrchestrationEngine)), and the inspector are
//! UNCHANGED — this module is the service-object FACE of the same coordinator primitive.
//!
//! ## The published interface (the orchestration as typed methods)
//!
//! | method             | semantics                | auth        | args             | desugars to |
//! |--------------------|--------------------------|-------------|------------------|-------------|
//! | `open_board`       | [`Semantics::Replayable`]| `Signature` | `(lead, budget)` | [`open_board_effects`](crate::open_board_effects) |
//! | `worker_step`      | [`Semantics::Replayable`]| `Signature` | `(cost, epoch)`  | [`worker_step_effects`](crate::worker_step_effects) |
//! | `delegate_mandate` | [`Semantics::Replayable`]| `Signature` | `()`             | [`delegate_mandate_effect`](crate::deos::delegate_mandate_effect) |
//! | `view`             | [`Semantics::Serviced`]  | `None`      | `()`             | — (the named OFE seam: a pure read, no turn) |
//!
//! `open_board`/`worker_step`/`delegate_mandate` are **replayable**: they desugar (via
//! `invoke()`) to a verified turn whose post-state the executor checks against the
//! coordinator [`CellProgram`](dregg_cell::program::CellProgram). `view` is **serviced**:
//! the board's committed lead/budget/meter/epoch state IS the answer (it rides the OFE
//! cross-cell-read), so `invoke()` refuses to desugar it and names the seam honestly
//! rather than faking a write.
//!
//! ## The verified guarantee (the program bites)
//!
//! The cap-gate (`Signature` on every mutator) is enforced twice over: at the `invoke()`
//! front door (an unauthorized caller is refused before any turn is built — anti-ghost)
//! and again by the executor (the desugared turn carries a real signature the kernel
//! verifies). The atomic budget is rollback-proof at the verified commit path: an
//! over-budget `worker_step` is an EXECUTOR REFUSAL on the
//! `AffineLe(spent_a + spent_b <= budget)` gate, a replayed step is refused on
//! `StrictMonotonic(EPOCH)`, and a meter rollback on `Monotonic(SPENT_*)` — none of them
//! a userspace check.

use dregg_app_framework::{
    AppCipherclerk, Effect, FieldElement, InterfaceRegistry, InvokeAuthority, InvokeRefused,
    field_from_u64, invoke_with_descriptor,
};
use dregg_cell::interface::{ArgsSchema, InterfaceDescriptor, MethodSig, Semantics, method_symbol};
use dregg_cell::permissions::AuthRequired;
use dregg_cell::program::CellProgram;
use dregg_turn::Turn;
use dregg_types::CellId;

use crate::deos::{WORKER_RIGHTS, delegate_mandate_effect};
use crate::{
    Tool, WorkerSlot, coordinator_program, identity_field, open_board_effects, worker_step_effects,
};

// =============================================================================
// Method names
// =============================================================================

/// The `open_board` method — a [`Semantics::Replayable`], `Signature`-gated mutator:
/// the coordinator pins the `LEAD` identity + the `BUDGET` mandate (both `WriteOnce`),
/// the two meters at 0, and advances `EPOCH` 0 -> 1.
pub const METHOD_OPEN_BOARD: &str = "open_board";
/// The `worker_step` method — a [`Semantics::Replayable`], `Signature`-gated mutator: a
/// worker advances its spend meter (`Monotonic`, summed by the budget gate), strictly
/// advances `EPOCH` (no replay), and records the tool/cost/sub-task it acted on.
pub const METHOD_WORKER_STEP: &str = "worker_step";
/// The `delegate_mandate` method — a [`Semantics::Replayable`], `Signature`-gated
/// mutator: the coordinator hands a worker an ATTENUATED slice of the board's authority
/// (the `derive_no_amplify` delegation), a real [`Effect::GrantCapability`].
pub const METHOD_DELEGATE_MANDATE: &str = "delegate_mandate";
/// The `view` method — a [`Semantics::Serviced`] read (the named OFE seam): read the
/// board's committed lead / budget / meters / epoch state. Never desugared.
pub const METHOD_VIEW: &str = "view";

// =============================================================================
// The published, typed interface
// =============================================================================

/// **The coordinator board's first-class typed interface** — the four methods it
/// publishes, with their auth and replayable-vs-serviced semantics.
///
/// This is the richer-than-derived descriptor: `derive_replayable` would make every
/// method `Replayable`/`None`, but the board wants its three mutators `Signature`-gated
/// and `view` marked `Serviced`. An app registers THIS in an [`InterfaceRegistry`] so
/// the Service Explorer resolves the real auth + seam shape, not the permissive derived
/// default.
pub fn interface_descriptor() -> InterfaceDescriptor {
    let mutator = |name: &str, args: u8| MethodSig {
        args_schema: ArgsSchema::Fixed(args),
        auth_required: AuthRequired::Signature,
        ..MethodSig::replayable(method_symbol(name))
    };
    InterfaceDescriptor::new(vec![
        // open_board(lead, budget): pin the lead + mandate, open the board.
        mutator(METHOD_OPEN_BOARD, 2),
        // worker_step(cost, epoch): advance a worker meter + the epoch, record the step.
        mutator(METHOD_WORKER_STEP, 2),
        // delegate_mandate(): hand a worker an attenuated slice (the cap delegation).
        mutator(METHOD_DELEGATE_MANDATE, 0),
        // view(): a pure read — the named OFE seam, never desugared.
        MethodSig {
            args_schema: ArgsSchema::Fixed(0),
            auth_required: AuthRequired::None,
            semantics: Semantics::Serviced,
            ..MethodSig::replayable(method_symbol(METHOD_VIEW))
        },
    ])
}

/// The cell program the coordinator-board SERVICE face installs/assumes — the SAME
/// canonical [`coordinator_program`](crate::coordinator_program) the
/// [`FactoryDescriptor`](crate::orchestration_factory_descriptor) bakes into every
/// factory-born coordinator cell. The runtime axes (deos / service / reactor) all
/// install/assume this one program, so the budget gate + meters + epoch caveats
/// re-enforce identically on every invoke-desugared turn.
pub fn board_service_program() -> CellProgram {
    coordinator_program()
}

/// Register the board's [`interface_descriptor`] for `cell` in a userspace
/// [`InterfaceRegistry`] — the resolution path the Service Explorer consults before
/// falling back to derive-from-program. After this, the explorer resolves the board's
/// real `Signature`/`Serviced` shape.
pub fn register_interface(registry: &mut InterfaceRegistry, cell: CellId) {
    registry.register(cell, interface_descriptor());
}

// =============================================================================
// The service handle — building invocations through invoke()
// =============================================================================

/// **A handle to a deployed coordinator board cell** — bundles the board cell with its
/// published interface, and builds method invocations through the `invoke()` front door.
///
/// Each builder returns a fully-signed [`Turn`] (the build half); submit it through an
/// executor ([`dregg_app_framework::EmbeddedExecutor::submit_turn`], a node
/// `/turns/submit`, …) to actually commit. A refusal at the front door (unknown method,
/// insufficient authority, a serviced seam) is surfaced as an [`InvokeRefused`] before
/// any turn is built — fail-closed.
#[derive(Clone, Debug)]
pub struct BoardService {
    /// The coordinator board cell this handle drives.
    pub cell: CellId,
    /// The board's published typed interface (the richer-than-derived one).
    pub descriptor: InterfaceDescriptor,
}

impl BoardService {
    /// A handle to the board cell `cell`, carrying the board's published
    /// [`interface_descriptor`].
    pub fn new(cell: CellId) -> Self {
        BoardService {
            cell,
            descriptor: interface_descriptor(),
        }
    }

    /// **Invoke `open_board(lead, budget)`** — pin the `LEAD` identity + the `BUDGET`
    /// mandate (both `WriteOnce`, admitted from zero on this first turn), the two meters
    /// at 0, and advance `EPOCH` 0 -> 1. Routes through the verified DFA, cap-gates on
    /// `Signature`, and desugars to [`open_board_effects`](crate::open_board_effects).
    pub fn open_board(
        &self,
        cipherclerk: &AppCipherclerk,
        lead: &str,
        budget: u64,
        authority: InvokeAuthority,
    ) -> Result<Turn, BoardServiceError> {
        if lead.is_empty() {
            return Err(BoardServiceError::EmptyField);
        }
        let effects = open_board_effects(self.cell, lead, budget);
        self.invoke(
            cipherclerk,
            METHOD_OPEN_BOARD,
            vec![identity_field(lead), field_from_u64(budget)],
            effects,
            authority,
        )
    }

    /// **Invoke `worker_step(...)`** — a worker performs one mandated step: advance its
    /// cumulative meter to `new_spent` (`Monotonic`, summed by the `AffineLe` budget
    /// gate), strictly advance `EPOCH` to `new_epoch` (no replay), and record the `tool`,
    /// `cost`, and `sub_task`. An over-budget step is an executor refusal
    /// (`AffineLe(spent_a + spent_b <= budget)`); a replay is refused on
    /// `StrictMonotonic(EPOCH)`.
    #[allow(clippy::too_many_arguments)]
    pub fn worker_step(
        &self,
        cipherclerk: &AppCipherclerk,
        worker: WorkerSlot,
        tool: Tool,
        new_spent: u64,
        cost: u64,
        new_epoch: u64,
        sub_task: &str,
        authority: InvokeAuthority,
    ) -> Result<Turn, BoardServiceError> {
        let effects = worker_step_effects(
            self.cell, worker, tool, new_spent, cost, new_epoch, sub_task,
        );
        self.invoke(
            cipherclerk,
            METHOD_WORKER_STEP,
            vec![field_from_u64(cost), field_from_u64(new_epoch)],
            effects,
            authority,
        )
    }

    /// **Invoke `delegate_mandate(worker_cell)`** — the coordinator hands `worker_cell`
    /// an ATTENUATED slice of the board's authority (the `derive_no_amplify` delegation:
    /// narrowed to the worker tier, never widened), a real [`Effect::GrantCapability`].
    pub fn delegate_mandate(
        &self,
        cipherclerk: &AppCipherclerk,
        worker_cell: CellId,
        authority: InvokeAuthority,
    ) -> Result<Turn, BoardServiceError> {
        let effects = vec![delegate_mandate_effect(
            self.cell,
            worker_cell,
            WORKER_RIGHTS,
        )];
        self.invoke(
            cipherclerk,
            METHOD_DELEGATE_MANDATE,
            vec![],
            effects,
            authority,
        )
    }

    /// **Attempt to invoke `view()`** — which ALWAYS refuses with
    /// [`InvokeRefused::ServicedSeam`]: `view` is a [`Semantics::Serviced`] read,
    /// answered by the OFE cross-cell-read (the board's committed lead / budget / meters
    /// / epoch), not a replay desugar. This method exists to make the seam legible (and
    /// testable): a serviced read is not a turn, and `invoke()` will not pretend
    /// otherwise. To actually READ the board, read the committed state at the board's
    /// slots ([`EPOCH_SLOT`](crate::EPOCH_SLOT), …).
    pub fn view(&self, cipherclerk: &AppCipherclerk) -> Result<Turn, BoardServiceError> {
        self.invoke(
            cipherclerk,
            METHOD_VIEW,
            vec![],
            vec![],
            InvokeAuthority::None,
        )
    }

    /// Route → cap-gate → desugar → sign, through the `invoke()` front door against this
    /// board's published descriptor.
    fn invoke(
        &self,
        cipherclerk: &AppCipherclerk,
        method: &str,
        args: Vec<FieldElement>,
        effects: Vec<Effect>,
        authority: InvokeAuthority,
    ) -> Result<Turn, BoardServiceError> {
        invoke_with_descriptor(
            cipherclerk,
            self.cell,
            &self.descriptor,
            method,
            args,
            effects,
            authority,
        )
        .map_err(BoardServiceError::Refused)
    }
}

/// Why a [`BoardService`] invocation could not be built.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BoardServiceError {
    /// A required text field (the lead identity) was empty.
    EmptyField,
    /// The `invoke()` front door refused (unknown method, insufficient authority, or a
    /// serviced seam) — fail-closed, no turn built.
    Refused(InvokeRefused),
}

impl std::fmt::Display for BoardServiceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BoardServiceError::EmptyField => write!(f, "a required text field must be non-empty"),
            BoardServiceError::Refused(r) => write!(f, "invoke refused: {r}"),
        }
    }
}

impl std::error::Error for BoardServiceError {}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::AgentCipherclerk;

    #[test]
    fn interface_publishes_four_typed_methods() {
        let iface = interface_descriptor();
        assert_eq!(iface.methods.len(), 4);
        assert!(iface.verify_id());

        for m in [
            METHOD_OPEN_BOARD,
            METHOD_WORKER_STEP,
            METHOD_DELEGATE_MANDATE,
        ] {
            let sig = iface.method(&method_symbol(m)).unwrap();
            assert_eq!(sig.semantics, Semantics::Replayable, "{m} is replayable");
            assert_eq!(
                sig.auth_required,
                AuthRequired::Signature,
                "{m} is sig-gated"
            );
        }
        let view = iface.method(&method_symbol(METHOD_VIEW)).unwrap();
        assert_eq!(view.semantics, Semantics::Serviced);
        assert_eq!(view.auth_required, AuthRequired::None);
    }

    #[test]
    fn the_interface_names_the_orchestration_vocabulary() {
        let iface = interface_descriptor();
        for m in [
            METHOD_OPEN_BOARD,
            METHOD_WORKER_STEP,
            METHOD_DELEGATE_MANDATE,
            METHOD_VIEW,
        ] {
            assert!(iface.method(&method_symbol(m)).is_some(), "{m} published");
        }
        assert!(
            iface.method(&method_symbol("frobnicate")).is_none(),
            "an unknown method is not a member of the interface"
        );
    }

    #[test]
    fn the_service_program_is_the_canonical_coordinator_program() {
        // The service face installs the SAME program the factory bakes — no divergent
        // program is invented (the non-degrading invariant).
        assert_eq!(board_service_program(), coordinator_program());
    }

    #[test]
    fn empty_lead_rejected_before_any_turn() {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x11; 32]);
        let svc = BoardService::new(cclerk.cell_id());
        assert!(matches!(
            svc.open_board(&cclerk, "", 1000, InvokeAuthority::Signature),
            Err(BoardServiceError::EmptyField)
        ));
    }

    #[test]
    fn unauthorized_worker_step_refused_at_the_front_door() {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x11; 32]);
        let svc = BoardService::new(cclerk.cell_id());
        // `worker_step` needs `Signature`; a `None` holder is refused before any turn.
        assert!(matches!(
            svc.worker_step(
                &cclerk,
                WorkerSlot::A,
                Tool::Search,
                100,
                100,
                2,
                "index",
                InvokeAuthority::None
            ),
            Err(BoardServiceError::Refused(
                InvokeRefused::Unauthorized { .. }
            ))
        ));
    }

    #[test]
    fn view_is_a_serviced_seam_never_desugared() {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x11; 32]);
        let svc = BoardService::new(cclerk.cell_id());
        assert!(matches!(
            svc.view(&cclerk),
            Err(BoardServiceError::Refused(
                InvokeRefused::ServicedSeam { .. }
            ))
        ));
    }
}
