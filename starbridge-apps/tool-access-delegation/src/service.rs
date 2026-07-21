//! # tool-access-delegation — the delegation lifecycle as a SERVICE CELL on the
//! `invoke()` front door (AX3).
//!
//! The verifiable tool-access mandate re-expressed as a CELLS-AS-SERVICE-OBJECTS
//! citizen (after the `bounty-board` / `kvstore` / `escrow-market` exemplars). This
//! module publishes a first-class, typed [`InterfaceDescriptor`] and drives the
//! delegation vocabulary through the [`dregg_app_framework::invoke`] front door — the
//! userspace method-dispatch layer that sits *slightly above* the effect-VM and
//! desugars a method call to the ordinary verified effects it names. There is **no
//! `Effect::Invoke`**, no kernel change, no new circuit rung: the kernel and the light
//! client keep seeing only the [`SetField`](dregg_app_framework::Effect::SetField) /
//! [`GrantCapability`](dregg_app_framework::Effect::GrantCapability) /
//! [`RevokeDelegation`](dregg_app_framework::Effect::RevokeDelegation) effects they
//! already enforce and witness. The one extra fact — that an invoked method is a member
//! of the cell's interface — is decided by the SAME verified DFA router the protocol
//! already uses.
//!
//! ## Non-degrading: the SAME caveats the FactoryDescriptor bakes
//!
//! The service installs the IDENTICAL [`tad_born_cell_program`](crate::tad_born_cell_program)
//! — the [`tad_state_constraints`](crate::tad_state_constraints) the
//! [`tad_factory_descriptor`](crate::tad_factory_descriptor) bakes into every factory-born
//! mandate cell (an `Always` program, so it re-enforces method-agnostically on every
//! invoke()-desugared turn exactly as on a factory-born cell's turns):
//!
//! | Slot         | Caveat                       | Bites on |
//! |--------------|------------------------------|----------|
//! | `tool_id`    | `WriteOnce`                  | `grant` (admit-from-zero), then the SCOPE is frozen |
//! | `rate_limit` | `WriteOnce`                  | `grant` (admit-from-zero), then the ceiling is frozen |
//! | `deadline`   | `WriteOnce`                  | `grant` (admit-from-zero), then the EXPIRY is frozen |
//! | `calls_made` | `Monotonic` + `FieldLteField`| every `exercise` (`c → c+1`, and `c+1 <= rate_limit`) |
//!
//! ## The published interface (the delegation lifecycle as typed methods)
//!
//! | method     | semantics                | auth        | args                   | desugars to |
//! |------------|--------------------------|-------------|------------------------|-------------|
//! | `grant`    | [`Semantics::Replayable`]| `Signature` | `(tool, rate, deadline)`| `SetField(TOOL_ID, RATE_LIMIT, DEADLINE, CALLS_MADE=0)` |
//! | `exercise` | [`Semantics::Replayable`]| `Signature` | `(payload)`            | `SetField(CALLS_MADE := c+1)` |
//! | `delegate` | [`Semantics::Replayable`]| `Signature` | `(worker)`             | `GrantCapability(invoke cap → worker, NARROWED)` |
//! | `revoke`   | [`Semantics::Replayable`]| `Signature` | `(worker)`             | `RevokeDelegation(worker)` |
//! | `view`     | [`Semantics::Serviced`]  | `None`      | `()`                   | — (the named OFE seam: a pure read, no turn) |
//!
//! ## The ATTENUATION story this face surfaces
//!
//! `delegate` is the object-capability core: the grantor hands the mandate's *invoke*
//! capability FORWARD to a worker NARROWED — at the same `Signature` permissions, never
//! widened (the `derive_no_amplify` shape, the cap-graph half of attenuated delegation).
//! And the attenuation is unforgeable downstream: a delegated mandate **cannot be
//! amplified**. The granted RATE is the consumption budget — `exercise` advances the meter
//! and the executor's `FieldLteField(calls_made <= rate_limit)` refuses the call that would
//! overrun it, and `WriteOnce(rate_limit)` refuses any attempt to raise the ceiling. A
//! holder of an N-call mandate gets exactly N calls; it can neither widen the grant nor
//! exceed it. Those are EXECUTOR refusals on the invoke()-desugared turn, not userspace
//! checks.

use dregg_app_framework::{
    AppCipherclerk, Effect, EmbeddedExecutor, FieldElement, InterfaceRegistry, InvokeAuthority,
    InvokeRefused, field_from_u64, invoke_with_descriptor,
};
use dregg_cell::interface::{ArgsSchema, InterfaceDescriptor, MethodSig, Semantics, method_symbol};
use dregg_cell::permissions::AuthRequired;
use dregg_turn::Turn;
use dregg_types::CellId;

use crate::{
    CALLS_MADE_SLOT, DEADLINE_SLOT, RATE_LIMIT_SLOT, TOOL_ID_SLOT, grant_invoke_effect,
    tad_born_cell_program, tool_id_field,
};

// =============================================================================
// Method names — the card's button vocabulary, the delegation lifecycle.
// =============================================================================

/// The `grant` method — a [`Semantics::Replayable`], `Signature`-gated mutator: the
/// grantor mints the mandate (`TOOL_ID` / `RATE_LIMIT` / `DEADLINE` `WriteOnce`,
/// `CALLS_MADE → 0`).
pub const METHOD_GRANT: &str = "grant";
/// The `exercise` method — a [`Semantics::Replayable`], `Signature`-gated mutator: the
/// worker meters one tool call (`CALLS_MADE := c+1`, re-enforced `c+1 <= rate_limit`).
pub const METHOD_EXERCISE: &str = "exercise";
/// The `delegate` method — a [`Semantics::Replayable`], `Signature`-gated mutator: the
/// grantor hands the invoke capability FORWARD to a worker NARROWED (the ATTENUATION:
/// `GrantCapability` at the same `Signature` permissions, never widened).
pub const METHOD_DELEGATE: &str = "delegate";
/// The `revoke` method — a [`Semantics::Replayable`], `Signature`-gated mutator: the
/// grantor revokes a delegated worker (`RevokeDelegation`, immediate single-machine
/// revocation).
pub const METHOD_REVOKE: &str = "revoke";
/// The `view` method — a [`Semantics::Serviced`] read (the named OFE seam): read the
/// mandate's committed terms (scope / rate / deadline / meter). Never desugared.
pub const METHOD_VIEW: &str = "view";

// =============================================================================
// The published, typed interface
// =============================================================================

/// **The mandate's first-class typed interface** — the five methods it publishes, with
/// their auth and replayable-vs-serviced semantics.
///
/// This is the richer-than-derived descriptor: `derive_replayable` would make every method
/// `Replayable`/`None`, but the mandate wants its four mutators `Signature`-gated and `view`
/// marked `Serviced`. An app registers THIS in an [`InterfaceRegistry`] so the Service
/// Explorer resolves the real auth + seam shape, not the permissive derived default.
pub fn interface_descriptor() -> InterfaceDescriptor {
    let mutator = |name: &str, args: u8| MethodSig {
        args_schema: ArgsSchema::Fixed(args),
        auth_required: AuthRequired::Signature,
        ..MethodSig::replayable(method_symbol(name))
    };
    InterfaceDescriptor::new(vec![
        // grant(tool, rate, deadline): mint the mandate.
        mutator(METHOD_GRANT, 3),
        // exercise(payload): meter one tool call (rate-bounded).
        mutator(METHOD_EXERCISE, 1),
        // delegate(worker): hand the invoke cap forward NARROWED (attenuation).
        mutator(METHOD_DELEGATE, 1),
        // revoke(worker): revoke a delegated worker.
        mutator(METHOD_REVOKE, 1),
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
/// falling back to derive-from-program. After this, the explorer resolves the mandate's
/// real `Signature`/`Serviced` shape.
pub fn register_interface(registry: &mut InterfaceRegistry, cell: CellId) {
    registry.register(cell, interface_descriptor());
}

// =============================================================================
// Seeding — install the SAME program the factory bakes + a granted baseline.
// =============================================================================

/// **Seed a granted mandate cell** so the service's `exercise` has live state + the caveats
/// bite: install the [`tad_born_cell_program`] (the SAME flat caveats the
/// [`tad_factory_descriptor`](crate::tad_factory_descriptor) bakes) on the executor's agent
/// cell, then bind the grant terms directly into the embedded ledger — `RATE_LIMIT` /
/// `TOOL_ID` / `DEADLINE` (`WriteOnce`, frozen after) and `CALLS_MADE = 0`.
///
/// After seeding, the mandate is granted with the meter at 0 — a real `(old, new)` baseline
/// against which `exercise` advances the counter up to `rate_limit`.
pub fn seed_granted_mandate(
    executor: &EmbeddedExecutor,
    tool: &str,
    rate_limit: u64,
    deadline: u64,
) {
    let mandate = executor.cell_id();
    executor.install_program(mandate, tad_born_cell_program());
    executor.with_ledger_mut(|ledger| {
        if let Some(cell) = ledger.get_mut(&mandate) {
            cell.state
                .set_field(RATE_LIMIT_SLOT as usize, field_from_u64(rate_limit));
            cell.state
                .set_field(TOOL_ID_SLOT as usize, tool_id_field(tool));
            cell.state
                .set_field(DEADLINE_SLOT as usize, field_from_u64(deadline));
            cell.state
                .set_field(CALLS_MADE_SLOT as usize, field_from_u64(0));
        }
    });
}

/// **Install just the mandate program** on the executor's agent cell — a born-empty mandate
/// the service drives `grant` against (the `WriteOnce` scope/rate/deadline admit-from-zero on
/// the grant turn). For tests that exercise `grant` through the front door.
pub fn seed_empty_mandate(executor: &EmbeddedExecutor) {
    executor.install_program(executor.cell_id(), tad_born_cell_program());
}

// =============================================================================
// The service handle — building invocations through invoke()
// =============================================================================

/// **A handle to a deployed mandate cell** — bundles the mandate cell with its published
/// interface, and builds method invocations through the `invoke()` front door.
///
/// Each builder returns a fully-signed [`Turn`] (the build half); submit it through an
/// executor ([`dregg_app_framework::EmbeddedExecutor::submit_turn`], a node `/turns/submit`,
/// …) to actually commit. A refusal at the front door (unknown method, insufficient
/// authority, a serviced seam) is surfaced as an [`InvokeRefused`] before any turn is
/// built — fail-closed.
#[derive(Clone, Debug)]
pub struct MandateService {
    /// The mandate cell this handle drives.
    pub cell: CellId,
    /// The mandate's published typed interface (the richer-than-derived one).
    pub descriptor: InterfaceDescriptor,
}

impl MandateService {
    /// A handle to the mandate cell `cell`, carrying the mandate's published
    /// [`interface_descriptor`].
    pub fn new(cell: CellId) -> Self {
        MandateService {
            cell,
            descriptor: interface_descriptor(),
        }
    }

    /// **Invoke `grant(tool, rate, deadline)`** — the grantor mints the mandate: write
    /// `TOOL_ID`, `RATE_LIMIT`, `DEADLINE` (all `WriteOnce`, admitted from zero on this
    /// first turn) and the meter `CALLS_MADE → 0`. Routes through the verified DFA, cap-gates
    /// on `Signature`, and desugars to the underlying `SetField`s.
    pub fn grant(
        &self,
        cipherclerk: &AppCipherclerk,
        tool: &str,
        rate_limit: u64,
        deadline: u64,
        authority: InvokeAuthority,
    ) -> Result<Turn, MandateServiceError> {
        if tool.is_empty() {
            return Err(MandateServiceError::EmptyField);
        }
        let tool_h = tool_id_field(tool);
        let rate_f = field_from_u64(rate_limit);
        let deadline_f = field_from_u64(deadline);
        let effects = vec![
            self.set(TOOL_ID_SLOT, tool_h),
            self.set(RATE_LIMIT_SLOT, rate_f),
            self.set(DEADLINE_SLOT, deadline_f),
            self.set(CALLS_MADE_SLOT, field_from_u64(0)),
        ];
        self.invoke(
            cipherclerk,
            METHOD_GRANT,
            vec![tool_h, rate_f, deadline_f],
            effects,
            authority,
        )
    }

    /// **Invoke `exercise(payload)`** — the worker meters one tool call: advance `CALLS_MADE`
    /// from `prev_calls_made` to `prev_calls_made + 1`. The executor's
    /// `FieldLteField(calls_made <= rate_limit)` refuses the call that would overrun the
    /// granted budget, and `Monotonic(calls_made)` refuses a meter rollback — the attenuation
    /// that cannot be amplified.
    pub fn exercise(
        &self,
        cipherclerk: &AppCipherclerk,
        prev_calls_made: u64,
        invocation_payload: FieldElement,
        authority: InvokeAuthority,
    ) -> Result<Turn, MandateServiceError> {
        let new_count = prev_calls_made + 1;
        let effects = vec![self.set(CALLS_MADE_SLOT, field_from_u64(new_count))];
        self.invoke(
            cipherclerk,
            METHOD_EXERCISE,
            vec![invocation_payload],
            effects,
            authority,
        )
    }

    /// **Invoke `delegate(worker)`** — the ATTENUATION: the grantor hands the mandate's
    /// invoke capability FORWARD to `worker` NARROWED (the same `Signature` permissions the
    /// factory's `allowed_cap_templates` ceiling allows, never widened — the
    /// `derive_no_amplify` cap-graph shape, the same [`grant_invoke_effect`] the deos `grant`
    /// affordance carries). Desugars to a real [`Effect::GrantCapability`].
    pub fn delegate(
        &self,
        cipherclerk: &AppCipherclerk,
        worker: CellId,
        authority: InvokeAuthority,
    ) -> Result<Turn, MandateServiceError> {
        let effects = vec![grant_invoke_effect(self.cell, worker)];
        self.invoke(
            cipherclerk,
            METHOD_DELEGATE,
            vec![*worker.as_bytes()],
            effects,
            authority,
        )
    }

    /// **Invoke `revoke(worker)`** — the grantor revokes a delegated worker (immediate
    /// single-machine revocation): desugars to a real [`Effect::RevokeDelegation`]. Thereafter
    /// the worker's delegated invoke capability is dead.
    pub fn revoke(
        &self,
        cipherclerk: &AppCipherclerk,
        worker: CellId,
        authority: InvokeAuthority,
    ) -> Result<Turn, MandateServiceError> {
        let effects = vec![Effect::RevokeDelegation { child: worker }];
        self.invoke(
            cipherclerk,
            METHOD_REVOKE,
            vec![*worker.as_bytes()],
            effects,
            authority,
        )
    }

    /// **Attempt to invoke `view()`** — which ALWAYS refuses with
    /// [`InvokeRefused::ServicedSeam`]: `view` is a [`Semantics::Serviced`] read, answered by
    /// the OFE cross-cell-read (the mandate's committed terms), not a replay desugar. This
    /// method exists to make the seam legible (and testable): a serviced read is not a turn,
    /// and `invoke()` will not pretend otherwise. To actually READ the mandate, read the
    /// committed state at its slots ([`RATE_LIMIT_SLOT`](crate::RATE_LIMIT_SLOT), …).
    pub fn view(&self, cipherclerk: &AppCipherclerk) -> Result<Turn, MandateServiceError> {
        self.invoke(
            cipherclerk,
            METHOD_VIEW,
            vec![],
            vec![],
            InvokeAuthority::None,
        )
    }

    /// A `SetField` effect on this mandate cell.
    fn set(&self, index: u8, value: FieldElement) -> Effect {
        Effect::SetField {
            cell: self.cell,
            index: index as u64,
            value,
        }
    }

    /// Route → cap-gate → desugar → sign, through the `invoke()` front door against this
    /// mandate's published descriptor.
    fn invoke(
        &self,
        cipherclerk: &AppCipherclerk,
        method: &str,
        args: Vec<FieldElement>,
        effects: Vec<Effect>,
        authority: InvokeAuthority,
    ) -> Result<Turn, MandateServiceError> {
        invoke_with_descriptor(
            cipherclerk,
            self.cell,
            &self.descriptor,
            method,
            args,
            effects,
            authority,
        )
        .map_err(MandateServiceError::Refused)
    }
}

/// Why a [`MandateService`] invocation could not be built.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MandateServiceError {
    /// A required text field (the tool id) was empty.
    EmptyField,
    /// The `invoke()` front door refused (unknown method, insufficient authority, or a
    /// serviced seam) — fail-closed, no turn built.
    Refused(InvokeRefused),
}

impl std::fmt::Display for MandateServiceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MandateServiceError::EmptyField => write!(f, "a required text field must be non-empty"),
            MandateServiceError::Refused(r) => write!(f, "invoke refused: {r}"),
        }
    }
}

impl std::error::Error for MandateServiceError {}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::AgentCipherclerk;

    fn test_cipherclerk() -> AppCipherclerk {
        AppCipherclerk::new(AgentCipherclerk::new(), [0x11; 32])
    }

    #[test]
    fn interface_publishes_five_typed_methods() {
        let iface = interface_descriptor();
        assert_eq!(iface.methods.len(), 5);
        assert!(iface.verify_id());

        for m in [
            METHOD_GRANT,
            METHOD_EXERCISE,
            METHOD_DELEGATE,
            METHOD_REVOKE,
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
    fn the_interface_names_the_delegation_vocabulary() {
        let iface = interface_descriptor();
        for m in [
            METHOD_GRANT,
            METHOD_EXERCISE,
            METHOD_DELEGATE,
            METHOD_REVOKE,
            METHOD_VIEW,
        ] {
            assert!(iface.method(&method_symbol(m)).is_some(), "{m} published");
        }
    }

    #[test]
    fn empty_tool_rejected_before_any_turn() {
        let cclerk = test_cipherclerk();
        let svc = MandateService::new(cclerk.cell_id());
        assert!(matches!(
            svc.grant(&cclerk, "", 3, 100, InvokeAuthority::Signature),
            Err(MandateServiceError::EmptyField)
        ));
    }

    #[test]
    fn unauthorized_exercise_refused_at_the_front_door() {
        let cclerk = test_cipherclerk();
        let svc = MandateService::new(cclerk.cell_id());
        // `exercise` needs `Signature`; a `None` holder is refused before any turn.
        assert!(matches!(
            svc.exercise(&cclerk, 0, field_from_u64(1), InvokeAuthority::None),
            Err(MandateServiceError::Refused(
                InvokeRefused::Unauthorized { .. }
            ))
        ));
    }

    #[test]
    fn unauthorized_delegate_refused_at_the_front_door() {
        let cclerk = test_cipherclerk();
        let svc = MandateService::new(cclerk.cell_id());
        let worker = CellId::from_bytes([0xAA; 32]);
        // `delegate` (the attenuation handoff) needs `Signature` — fail-closed for `None`.
        assert!(matches!(
            svc.delegate(&cclerk, worker, InvokeAuthority::None),
            Err(MandateServiceError::Refused(
                InvokeRefused::Unauthorized { .. }
            ))
        ));
    }

    #[test]
    fn view_is_a_serviced_seam_never_desugared() {
        let cclerk = test_cipherclerk();
        let svc = MandateService::new(cclerk.cell_id());
        assert!(matches!(
            svc.view(&cclerk),
            Err(MandateServiceError::Refused(
                InvokeRefused::ServicedSeam { .. }
            ))
        ));
    }

    #[test]
    fn unknown_method_does_not_route() {
        let iface = interface_descriptor();
        assert!(
            iface.method(&method_symbol("exfiltrate")).is_none(),
            "an unknown method is not a member of the interface"
        );
    }
}
