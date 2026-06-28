//! # execution-lease — the lease as a SERVICE CELL on the `invoke()` front door.
//!
//! The third axis of a modern starbridge-app: the durable-execution lease
//! re-expressed as a CELLS-AS-SERVICE-OBJECTS citizen. A `service` module
//! publishes a first-class, typed [`InterfaceDescriptor`] and drives the lease
//! operations through the [`dregg_app_framework::invoke`] front door — the
//! userspace method-dispatch layer that desugars a method call to the ordinary
//! verified effects it names. There is **no `Effect::Invoke`**, no kernel change,
//! no new circuit rung: the kernel and the light client keep seeing only the
//! [`SetField`](dregg_app_framework::Effect::SetField) /
//! [`Transfer`](dregg_app_framework::Effect::Transfer) /
//! [`EmitEvent`](dregg_app_framework::Effect::EmitEvent) effects they already
//! enforce and witness.
//!
//! ## The published interface (the lease as typed methods)
//!
//! | method    | semantics    | auth        | args                      | desugars to |
//! |-----------|--------------|-------------|---------------------------|-------------|
//! | `pay`     | `Replayable` | `Signature` | `(asset, amount, to)`     | one conserving [`Effect::Transfer`] (rent → provider) |
//! | `advance` | `Replayable` | `Signature` | `(new_step, new_digest)`  | the cursor-advancing [`crate::advance_effects`] (durable delivery) |
//! | `open`    | `Replayable` | `Signature` | `(rent, period, provider)`| the seal [`crate::build_open_lease_action`] effects |
//! | `status`  | `Serviced`   | `None`      | `()`                      | — (the OFE read seam: read the lease state, never desugared) |
//!
//! `pay`/`advance`/`open` are **replayable**: they desugar to a verified turn whose
//! post-state the executor checks against the lease
//! [`CellProgram`](crate::lease_cell_program) (the `Monotonic(STEP)` durable-cursor
//! tooth + the `WriteOnce` economics bite). `status` is **serviced**: a state read
//! rides the OFE cross-cell-read, so `invoke()` refuses to desugar it and names the
//! seam honestly rather than faking a turn.

use dregg_app_framework::{
    AppCipherclerk, Effect, FieldElement, InvokeAuthority, InvokeRefused, Turn, field_from_u64,
    invoke_with_descriptor,
};
use dregg_cell::interface::{ArgsSchema, InterfaceDescriptor, MethodSig, Semantics, method_symbol};
use dregg_cell::permissions::AuthRequired;
use dregg_types::CellId;

use crate::{LeaseTerms, advance_effects, cell_tag};

/// The `pay` method — a `Replayable`, `Signature`-gated rent payment (a conserving
/// `Transfer` of one period's rent to the provider).
pub const METHOD_PAY: &str = "pay";
/// The `advance` method — a `Replayable`, `Signature`-gated durable-checkpoint
/// delivery (advance the cursor + re-bind the state digest).
pub const METHOD_ADVANCE: &str = "advance";
/// The `open` method — a `Replayable`, `Signature`-gated lease open (seal the
/// economics + genesis checkpoint).
pub const METHOD_OPEN: &str = "open";
/// The `status` method — a `Serviced` read of the lease state (the OFE seam).
pub const METHOD_STATUS: &str = "status";

/// **The lease's first-class typed interface** — the four methods it publishes,
/// with their auth and replayable-vs-serviced semantics.
pub fn interface_descriptor() -> InterfaceDescriptor {
    let mutator = |name: &str, args: u8| MethodSig {
        args_schema: ArgsSchema::Fixed(args),
        auth_required: AuthRequired::Signature,
        ..MethodSig::replayable(method_symbol(name))
    };
    InterfaceDescriptor::new(vec![
        // pay(asset, amount, to): a conserving rent Transfer.
        mutator(METHOD_PAY, 3),
        // advance(new_step, new_digest): a durable checkpoint delivery.
        mutator(METHOD_ADVANCE, 2),
        // open(rent, period, provider): seal the lease.
        mutator(METHOD_OPEN, 3),
        // status(): a pure read — the named OFE seam, never desugared.
        MethodSig {
            args_schema: ArgsSchema::Fixed(0),
            auth_required: AuthRequired::None,
            semantics: Semantics::Serviced,
            ..MethodSig::replayable(method_symbol(METHOD_STATUS))
        },
    ])
}

/// **A handle to a deployed lease cell** — bundles the lease cell with its
/// published interface, and builds method invocations through the `invoke()` front
/// door. Each builder returns a fully-signed [`Turn`]; a refusal (unknown method,
/// insufficient authority, a serviced seam) is surfaced as [`InvokeRefused`] before
/// any turn is built — fail-closed.
#[derive(Clone, Debug)]
pub struct LeaseService {
    /// The lease cell this handle drives.
    pub cell: CellId,
    /// The lease's published typed interface.
    pub descriptor: InterfaceDescriptor,
}

impl LeaseService {
    /// A handle to lease cell `cell`, carrying the published [`interface_descriptor`].
    pub fn new(cell: CellId) -> Self {
        LeaseService {
            cell,
            descriptor: interface_descriptor(),
        }
    }

    /// **Invoke `pay`** — pay one period's rent to the provider, a conserving
    /// `Transfer` desugar. Re-enforced by the kernel's per-asset Σδ=0.
    pub fn pay(
        &self,
        cipherclerk: &AppCipherclerk,
        terms: &LeaseTerms,
        authority: InvokeAuthority,
    ) -> Result<Turn, LeaseServiceError> {
        let mut asset = [0u8; 32];
        asset.copy_from_slice(terms.asset.as_bytes());
        let effects = vec![Effect::Transfer {
            from: self.cell,
            to: terms.provider,
            amount: terms.rent_per_period,
        }];
        self.invoke(
            cipherclerk,
            METHOD_PAY,
            vec![
                asset,
                field_from_u64(terms.rent_per_period),
                cell_tag(terms.provider),
            ],
            effects,
            authority,
        )
    }

    /// **Invoke `advance`** — deliver a durable checkpoint: advance the cursor to
    /// `new_step` and re-bind `new_digest`. The executor re-enforces
    /// `Monotonic(STEP_SLOT)`, so a rewound cursor is a REAL refusal on the
    /// desugared turn.
    pub fn advance(
        &self,
        cipherclerk: &AppCipherclerk,
        new_step: u64,
        new_digest: FieldElement,
        authority: InvokeAuthority,
    ) -> Result<Turn, LeaseServiceError> {
        let effects = advance_effects(self.cell, new_step, new_digest);
        self.invoke(
            cipherclerk,
            METHOD_ADVANCE,
            vec![field_from_u64(new_step), new_digest],
            effects,
            authority,
        )
    }

    /// **Attempt to invoke `status`** — which ALWAYS refuses with
    /// [`InvokeRefused::ServicedSeam`]: a state read is answered by the OFE
    /// cross-cell read, not a replay desugar. This makes the seam legible.
    pub fn status(&self, cipherclerk: &AppCipherclerk) -> Result<Turn, LeaseServiceError> {
        self.invoke(
            cipherclerk,
            METHOD_STATUS,
            vec![],
            vec![],
            InvokeAuthority::None,
        )
    }

    fn invoke(
        &self,
        cipherclerk: &AppCipherclerk,
        method: &str,
        args: Vec<FieldElement>,
        effects: Vec<Effect>,
        authority: InvokeAuthority,
    ) -> Result<Turn, LeaseServiceError> {
        invoke_with_descriptor(
            cipherclerk,
            self.cell,
            &self.descriptor,
            method,
            args,
            effects,
            authority,
        )
        .map_err(LeaseServiceError::Refused)
    }
}

/// Why a [`LeaseService`] invocation could not be built.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LeaseServiceError {
    /// The `invoke()` front door refused (unknown method, insufficient authority,
    /// or a serviced seam) — fail-closed, no turn built.
    Refused(InvokeRefused),
}

impl std::fmt::Display for LeaseServiceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LeaseServiceError::Refused(r) => write!(f, "invoke refused: {r}"),
        }
    }
}

impl std::error::Error for LeaseServiceError {}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::AgentCipherclerk;

    fn cid(b: u8) -> CellId {
        CellId::from_bytes([b; 32])
    }

    #[test]
    fn interface_publishes_four_typed_methods() {
        let iface = interface_descriptor();
        assert_eq!(iface.methods.len(), 4);
        assert!(iface.verify_id());
        for m in [METHOD_PAY, METHOD_ADVANCE, METHOD_OPEN] {
            let sig = iface.method(&method_symbol(m)).unwrap();
            assert_eq!(sig.semantics, Semantics::Replayable, "{m} is replayable");
            assert_eq!(
                sig.auth_required,
                AuthRequired::Signature,
                "{m} is sig-gated"
            );
        }
        let status = iface.method(&method_symbol(METHOD_STATUS)).unwrap();
        assert_eq!(status.semantics, Semantics::Serviced);
    }

    #[test]
    fn pay_desugars_to_one_conserving_transfer() {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x11; 32]);
        let svc = LeaseService::new(cclerk.cell_id());
        let terms = LeaseTerms::new(cid(2), cclerk.cell_id(), cid(9), 100, 50, 1000, 0);
        let turn = svc
            .pay(&cclerk, &terms, InvokeAuthority::Signature)
            .expect("pay routes through the interface");
        let action = &turn.call_forest.roots[0].action;
        assert_eq!(action.method, method_symbol(METHOD_PAY));
        assert_eq!(action.effects.len(), 1);
        assert!(matches!(action.effects[0], Effect::Transfer { amount, .. } if amount == 100));
    }

    #[test]
    fn unauthorized_advance_refused_at_the_front_door() {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x11; 32]);
        let svc = LeaseService::new(cclerk.cell_id());
        assert!(matches!(
            svc.advance(&cclerk, 1, FieldElement::default(), InvokeAuthority::None),
            Err(LeaseServiceError::Refused(
                InvokeRefused::Unauthorized { .. }
            ))
        ));
    }

    #[test]
    fn status_is_a_serviced_seam_never_desugared() {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x11; 32]);
        let svc = LeaseService::new(cclerk.cell_id());
        assert!(matches!(
            svc.status(&cclerk),
            Err(LeaseServiceError::Refused(
                InvokeRefused::ServicedSeam { .. }
            ))
        ));
    }
}
