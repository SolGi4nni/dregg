//! # compute-exchange — the job lifecycle as a SERVICE CELL on the `invoke()` front door.
//!
//! The canonical three-state compute job re-expressed as a
//! CELLS-AS-SERVICE-OBJECTS citizen (after the `starbridge-bounty-board`,
//! `starbridge-kvstore`, and `starbridge-escrow-market` exemplars). A `service`
//! module on the existing crate: it publishes a first-class, typed
//! [`InterfaceDescriptor`] and drives the job lifecycle through the
//! [`dregg_app_framework::invoke`] front door — the userspace method-dispatch
//! layer that sits *slightly above* the effect-VM and desugars a method call to
//! the ordinary verified effects it names. There is **no `Effect::Invoke`**, no
//! kernel change, no new circuit rung: the kernel and the light client keep
//! seeing only the [`SetField`](dregg_app_framework::Effect::SetField) /
//! [`EmitEvent`](dregg_app_framework::Effect::EmitEvent) effects they already
//! enforce and witness. The one extra fact — that an invoked method is a member
//! of the cell's interface — is decided by the SAME verified DFA router
//! ([`InterfaceDescriptor::route_method`]) the protocol already uses.
//!
//! ## Non-degrading: the SAME canonical lifecycle program
//!
//! The service face drives the IDENTICAL canonical
//! [`job_program`](crate::job_program) installed on every job cell. So the
//! organ-composition teeth re-enforce on every invoke()-desugared turn exactly
//! as they do on a factory-born job cell's turns:
//!
//! | Organ     | Caveat                                       | Bites on |
//! |-----------|----------------------------------------------|----------|
//! | BUDGET    | `FieldLteField { BID <= BUDGET }`            | `bid` (over-budget refused) |
//! | ACCEPTED  | `WriteOnce(BID)`                             | `bid` (then frozen) |
//! | FLASHWELL | `AffineEq { PAID + REFUNDED == BUDGET }` + `AffineLe` | `settle` (no mint/burn) |
//! | LIFECYCLE | `StrictMonotonic(STATE)`                     | every turn (POSTED→BID→SETTLED) |
//!
//! ## The published interface (the lifecycle as typed methods)
//!
//! | method   | semantics                | auth        | desugars to |
//! |----------|--------------------------|-------------|-------------|
//! | `post`   | [`Semantics::Replayable`]| `Signature` | `SetField(REQUESTER, BUDGET, SPEC, STATE=POSTED)` + `EmitEvent(job-posted)` |
//! | `bid`    | [`Semantics::Replayable`]| `Signature` | `SetField(PROVIDER, BID, STATE=BID)` + `EmitEvent(job-bid)` |
//! | `settle` | [`Semantics::Replayable`]| `Signature` | `Transfer(payer → provider)` + `SetField(PAID, REFUNDED, STATE=SETTLED)` + `EmitEvent(job-settled)` |
//! | `view`   | [`Semantics::Serviced`]  | `None`      | — (the named OFE seam: a pure read, no turn) |
//!
//! ⚑ `settle` MOVES VALUE. It desugars to the conserving kernel `Effect::Transfer`
//! ([`crate::settlement_effects`], via the shared `Payable` desugar) in the SAME
//! action as the `STATE = SETTLED` advance, so there is no accepted turn in which
//! the job reads SETTLED and the provider was not paid. This face drives a job cell
//! that IS the paying agent's own cell, so both legs fit one action; the budget is
//! a PROMISE rather than an escrow (see the crate docs for the three measured
//! executor refusals that make a self-escrowing job cell inexpressible).
//!
//! `post`/`bid`/`settle` are **replayable**: they desugar (via `invoke()`) to a
//! verified turn whose post-state the executor checks against the job
//! [`CellProgram`](dregg_cell::program::CellProgram). `view` is **serviced**: the
//! job's committed lifecycle state IS the answer (it rides the OFE
//! cross-cell-read, not a replay), so `invoke()` refuses to desugar it and names
//! the seam honestly rather than faking a write.

use dregg_app_framework::{
    AppCipherclerk, CellId, Effect, Event, FieldElement, InterfaceRegistry, InvokeAuthority,
    InvokeRefused, Turn, field_from_bytes, field_from_u64, invoke_with_descriptor, symbol,
};
use dregg_cell::interface::{ArgsSchema, InterfaceDescriptor, MethodSig, Semantics, method_symbol};
use dregg_cell::permissions::AuthRequired;

use crate::{
    BUDGET_SLOT, REQUESTER_HASH_SLOT, SPEC_HASH_SLOT, STATE_POSTED, STATE_SLOT, bid_effects,
    settlement_effects, state_field,
};

// =============================================================================
// Method names
// =============================================================================

/// The `post` method — a [`Semantics::Replayable`], `Signature`-gated mutator:
/// open a job (`REQUESTER_HASH`, `BUDGET`, `SPEC_HASH` `WriteOnce`, `STATE →
/// POSTED`).
pub const METHOD_POST: &str = "post";
/// The `bid` method — a [`Semantics::Replayable`], `Signature`-gated mutator: a
/// provider bids `price <= BUDGET` (`BID` `WriteOnce`, `STATE → BID`).
pub const METHOD_BID: &str = "bid";
/// The `settle` method — a [`Semantics::Replayable`], `Signature`-gated mutator:
/// PAY the provider (`Effect::Transfer`) and record the split (`PAID + REFUNDED ==
/// BUDGET`, `STATE → SETTLED`, terminal) in one action.
pub const METHOD_SETTLE: &str = "settle";
/// The `view` method — a [`Semantics::Serviced`] read (the named OFE seam): read
/// the job's committed lifecycle state. Never desugared.
pub const METHOD_VIEW: &str = "view";

// =============================================================================
// The published, typed interface
// =============================================================================

/// **The job's first-class typed interface** — the four methods it publishes,
/// with their auth and replayable-vs-serviced semantics.
///
/// This is the richer-than-derived descriptor: `derive_replayable` would make
/// every method `Replayable`/`None`, but the job wants its three mutators
/// `Signature`-gated and `view` marked `Serviced`. An app registers THIS in an
/// [`InterfaceRegistry`] so the Service Explorer resolves the real auth + seam
/// shape, not the permissive derived default.
pub fn interface_descriptor() -> InterfaceDescriptor {
    let mutator = |name: &str, args: u8| MethodSig {
        args_schema: ArgsSchema::Fixed(args),
        auth_required: AuthRequired::Signature,
        ..MethodSig::replayable(method_symbol(name))
    };
    InterfaceDescriptor::new(vec![
        // post(requester, budget, spec): open the job.
        mutator(METHOD_POST, 3),
        // bid(provider, price): a provider bids <= budget.
        mutator(METHOD_BID, 2),
        // settle(paid, refunded, provider): PAY the provider and record the
        // split, terminal.
        mutator(METHOD_SETTLE, 3),
        // view(): a pure read — the named OFE seam, never desugared.
        MethodSig {
            args_schema: ArgsSchema::Fixed(0),
            auth_required: AuthRequired::None,
            semantics: Semantics::Serviced,
            ..MethodSig::replayable(method_symbol(METHOD_VIEW))
        },
    ])
}

/// Register the job's [`interface_descriptor`] for `cell` in a userspace
/// [`InterfaceRegistry`] — the resolution path the Service Explorer consults
/// before falling back to derive-from-program. After this, the explorer resolves
/// the job's real `Signature`/`Serviced` shape.
pub fn register_interface(registry: &mut InterfaceRegistry, cell: CellId) {
    registry.register(cell, interface_descriptor());
}

// =============================================================================
// The service handle — building invocations through invoke()
// =============================================================================

/// **A handle to a deployed job cell** — bundles the job cell with its published
/// interface, and builds method invocations through the `invoke()` front door.
///
/// Each builder returns a fully-signed [`Turn`] (the build half); submit it
/// through an executor
/// ([`dregg_app_framework::EmbeddedExecutor::submit_turn`], a node
/// `/turns/submit`, …) to actually commit. A refusal at the front door (unknown
/// method, insufficient authority, a serviced seam) is surfaced as an
/// [`InvokeRefused`] before any turn is built — fail-closed.
#[derive(Clone, Debug)]
pub struct JobService {
    /// The job cell this handle drives.
    pub cell: CellId,
    /// The job's published typed interface (the richer-than-derived one).
    pub descriptor: InterfaceDescriptor,
}

impl JobService {
    /// A handle to the job cell `cell`, carrying the job's published
    /// [`interface_descriptor`].
    pub fn new(cell: CellId) -> Self {
        JobService {
            cell,
            descriptor: interface_descriptor(),
        }
    }

    /// **Invoke `post(requester, budget, spec)`** — open the job: write
    /// `REQUESTER_HASH`, `BUDGET`, `SPEC_HASH` (all `WriteOnce`, admitted from
    /// zero on this first turn), advance `STATE → POSTED`, emit `job-posted`.
    /// Routes through the verified DFA, cap-gates on `Signature`, and desugars to
    /// the underlying `SetField`/`EmitEvent` effects targeting the `post` method
    /// symbol.
    pub fn post(
        &self,
        cipherclerk: &AppCipherclerk,
        requester: &str,
        budget: u64,
        spec: &FieldElement,
        authority: InvokeAuthority,
    ) -> Result<Turn, JobServiceError> {
        let requester_h = field_from_bytes(requester.as_bytes());
        let budget_f = field_from_u64(budget);
        // Mirrors `crate::build_post_action`: the post body, here desugared
        // through the invoke() front door rather than `make_action`.
        let effects = vec![
            Effect::SetField {
                cell: self.cell,
                index: REQUESTER_HASH_SLOT as u64,
                value: requester_h,
            },
            Effect::SetField {
                cell: self.cell,
                index: BUDGET_SLOT as u64,
                value: budget_f,
            },
            Effect::SetField {
                cell: self.cell,
                index: SPEC_HASH_SLOT as u64,
                value: *spec,
            },
            Effect::SetField {
                cell: self.cell,
                index: STATE_SLOT as u64,
                value: state_field(STATE_POSTED),
            },
            Effect::EmitEvent {
                cell: self.cell,
                event: Event::new(symbol("job-posted"), vec![requester_h, budget_f]),
            },
        ];
        self.invoke(
            cipherclerk,
            METHOD_POST,
            vec![requester_h, budget_f, *spec],
            effects,
            authority,
        )
    }

    /// **Invoke `bid(provider, price)`** — a provider bids `price` (`<= BUDGET`,
    /// the budget gate), binds `PROVIDER_HASH`, advances `STATE → BID`. An
    /// over-budget bid is an executor refusal (`FieldLteField(BID <= BUDGET)`); a
    /// re-bid is refused by `WriteOnce(BID)` / `StrictMonotonic(STATE)`.
    pub fn bid(
        &self,
        cipherclerk: &AppCipherclerk,
        provider: &str,
        price: u64,
        authority: InvokeAuthority,
    ) -> Result<Turn, JobServiceError> {
        let provider_h = field_from_bytes(provider.as_bytes());
        let price_f = field_from_u64(price);
        let effects = bid_effects(self.cell, provider, price);
        self.invoke(
            cipherclerk,
            METHOD_BID,
            vec![provider_h, price_f],
            effects,
            authority,
        )
    }

    /// **Invoke `settle(paid, refunded, provider)`** — close the deal: **PAY
    /// `paid` to `provider`** (the conserving kernel `Effect::Transfer`) and record
    /// the split — write `PAID`, `REFUNDED`, advance `STATE → SETTLED` (terminal)
    /// — in ONE action, so neither leg can land without the other.
    ///
    /// The FLASHWELL `AffineEq(PAID + REFUNDED == BUDGET)` requires the recorded
    /// split to conserve the budget; a value-conjuring or value-burning split is an
    /// executor refusal, and so is a settlement this cell cannot fund
    /// (`InsufficientBalance`). A `paid` of zero is the CANCELLATION case: no
    /// transfer is emitted, because nothing is owed.
    pub fn settle(
        &self,
        cipherclerk: &AppCipherclerk,
        provider: CellId,
        paid: u64,
        refunded: u64,
        authority: InvokeAuthority,
    ) -> Result<Turn, JobServiceError> {
        let paid_f = field_from_u64(paid);
        let refunded_f = field_from_u64(refunded);
        let mut payee = [0u8; 32];
        payee.copy_from_slice(provider.as_bytes());
        let effects = settlement_effects(self.cell, provider, paid, refunded);
        self.invoke(
            cipherclerk,
            METHOD_SETTLE,
            vec![paid_f, refunded_f, payee],
            effects,
            authority,
        )
    }

    /// **Attempt to invoke `view()`** — which ALWAYS refuses with
    /// [`InvokeRefused::ServicedSeam`]: `view` is a [`Semantics::Serviced`] read,
    /// answered by the OFE cross-cell-read (the job's committed lifecycle state),
    /// not a replay desugar. This method exists to make the seam legible (and
    /// testable): a serviced read is not a turn, and `invoke()` will not pretend
    /// otherwise. To actually READ the job, read the committed state at the job's
    /// slots ([`STATE_SLOT`](crate::STATE_SLOT), …).
    pub fn view(&self, cipherclerk: &AppCipherclerk) -> Result<Turn, JobServiceError> {
        self.invoke(
            cipherclerk,
            METHOD_VIEW,
            vec![],
            vec![],
            InvokeAuthority::None,
        )
    }

    /// Route → cap-gate → desugar → sign, through the `invoke()` front door
    /// against this job's published descriptor.
    fn invoke(
        &self,
        cipherclerk: &AppCipherclerk,
        method: &str,
        args: Vec<FieldElement>,
        effects: Vec<Effect>,
        authority: InvokeAuthority,
    ) -> Result<Turn, JobServiceError> {
        invoke_with_descriptor(
            cipherclerk,
            self.cell,
            &self.descriptor,
            method,
            args,
            effects,
            authority,
        )
        .map_err(JobServiceError::Refused)
    }
}

/// Why a [`JobService`] invocation could not be built.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum JobServiceError {
    /// The `invoke()` front door refused (unknown method, insufficient authority,
    /// or a serviced seam) — fail-closed, no turn built.
    Refused(InvokeRefused),
}

impl std::fmt::Display for JobServiceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            JobServiceError::Refused(r) => write!(f, "invoke refused: {r}"),
        }
    }
}

impl std::error::Error for JobServiceError {}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::AgentCipherclerk;

    #[test]
    fn interface_publishes_four_typed_methods() {
        let iface = interface_descriptor();
        assert_eq!(iface.methods.len(), 4);
        assert!(iface.verify_id());

        for m in [METHOD_POST, METHOD_BID, METHOD_SETTLE] {
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
    fn the_published_interface_names_the_lifecycle_vocabulary() {
        let iface = interface_descriptor();
        for m in [METHOD_POST, METHOD_BID, METHOD_SETTLE, METHOD_VIEW] {
            assert!(iface.method(&method_symbol(m)).is_some(), "{m} published");
        }
    }

    #[test]
    fn unauthorized_mutator_refused_at_the_front_door() {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x11; 32]);
        let svc = JobService::new(cclerk.cell_id());
        let spec = crate::spec_digest(b"render-frame-batch");
        // `post` needs `Signature`; a `None` holder is refused before any turn.
        assert!(matches!(
            svc.post(
                &cclerk,
                "requester-corp",
                1000,
                &spec,
                InvokeAuthority::None
            ),
            Err(JobServiceError::Refused(InvokeRefused::Unauthorized { .. }))
        ));
        // Likewise `bid`.
        assert!(matches!(
            svc.bid(&cclerk, "provider-pat", 800, InvokeAuthority::None),
            Err(JobServiceError::Refused(InvokeRefused::Unauthorized { .. }))
        ));
    }

    #[test]
    fn view_is_a_serviced_seam_never_desugared() {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x11; 32]);
        let svc = JobService::new(cclerk.cell_id());
        assert!(matches!(
            svc.view(&cclerk),
            Err(JobServiceError::Refused(InvokeRefused::ServicedSeam { .. }))
        ));
    }
}
