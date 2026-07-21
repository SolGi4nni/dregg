//! # tool-access-delegation — the AUDIT reactor (the reactive twin of `invoke()`, AX5).
//!
//! The fifth axis (AX5) of a modern starbridge-app. Where the [`crate::service`] face is the
//! **command** front-door (a `grant` / `exercise` / `delegate` / `revoke` turn comes *in*,
//! caller-driven), this is the **reaction** front-door: a service that WATCHES the mandate
//! cell and, when a worker `exercise`s the delegated tool, REACTS by emitting an on-chain
//! audit-log turn — event-driven, the grantor's tamper-evident record of how the delegated
//! capability was used.
//!
//! [`MandateAuditReactor`] reads the new meter value off the observed `exercise`'s committed
//! `SetField` and emits a `tool-invocation-logged` event linking the audit record back to the
//! exercising turn's receipt. This is a genuine event→reaction in the delegation lifecycle: a
//! delegated cap should leave a witnessed trail, and the audit is produced REACTIVELY from the
//! committed exercise, not by trusting the worker to self-report.
//!
//! Both front-doors are **userspace**: there is NO kernel `Effect::React` (just as there is no
//! `Effect::Invoke`). The reaction desugars to an ordinary [`Effect::EmitEvent`] the kernel
//! already enforces and the circuit already witnesses, re-enforced by the installed
//! [`tad_born_cell_program`](crate::tad_born_cell_program) (the audit turn writes no slot, so
//! the `WriteOnce` / `Monotonic` / `FieldLteField` caveats hold vacuously — an audit can never
//! perturb the meter it records).

use dregg_app_framework::{
    AuthRequired, Effect, Event, FieldElement, ObservedReceipt, ReactionPlan, Reactor,
    ReceiptFilter, symbol,
};
use dregg_types::CellId;

use crate::CALLS_MADE_SLOT;

/// The reaction op the audit reactor emits (not a member of the command interface — it is the
/// reactor's own downstream op): a `tool-invocation-logged` audit receipt.
pub const REACTION_AUDIT: &str = "audit_exercise";

/// **An audit reactor** — watches a mandate cell for committed `exercise` ops and reacts by
/// emitting an on-chain `tool-invocation-logged` audit event recording the new meter value and
/// linking back to the exercising turn.
///
/// The reactive analogue of a [`crate::service::MandateService`] consumer: it DECLARES its
/// watch ([`ReceiptFilter`] over the mandate's `exercise` method) and how it reacts
/// ([`Reactor::react`] → an audit [`ReactionPlan`]); the framework wires the match → cap-gate
/// → build → sign.
#[derive(Clone, Debug)]
pub struct MandateAuditReactor {
    /// The mandate cell this reactor watches (and writes the audit receipt to).
    pub mandate: CellId,
}

impl MandateAuditReactor {
    /// An audit reactor watching the mandate cell `mandate`.
    pub fn new(mandate: CellId) -> Self {
        MandateAuditReactor { mandate }
    }
}

impl Reactor for MandateAuditReactor {
    fn filter(&self) -> ReceiptFilter {
        // What it watches: the mandate cell, for the `exercise` op. The reactive analogue of
        // the service cell's interface descriptor.
        ReceiptFilter::cell_methods(self.mandate, &[crate::service::METHOD_EXERCISE])
    }

    fn react(&self, observed: &ObservedReceipt) -> Option<ReactionPlan> {
        // Decode the new meter value off the observed exercise's committed effect — the
        // `SetField` on CALLS_MADE is the metered counter the worker just advanced.
        let mut new_calls: Option<FieldElement> = None;
        for effect in &observed.effects {
            if let Effect::SetField { index, value, .. } = effect
                && *index == CALLS_MADE_SLOT as u64
            {
                new_calls = Some(*value);
            }
        }
        // No metered advance in the observed op → nothing to audit.
        let calls = new_calls?;
        Some(ReactionPlan {
            target: self.mandate,
            method: REACTION_AUDIT.into(),
            args: vec![],
            // The reaction desugars to an ordinary EmitEvent — the kernel / circuit see only
            // what they already know. It writes no slot, so the mandate program re-enforces it
            // vacuously (the audit cannot perturb the meter it records). The event links the
            // new meter value to the exercising turn's receipt (provenance).
            effects: vec![Effect::EmitEvent {
                cell: self.mandate,
                event: Event::new(
                    symbol("tool-invocation-logged"),
                    vec![calls, observed.turn_hash],
                ),
            }],
            auth_required: AuthRequired::Signature,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::{
        AgentCipherclerk, AppCipherclerk, EmbeddedExecutor, InvokeAuthority, ReactRefused,
        field_from_u64, react_build,
    };

    use crate::service::{MandateService, seed_granted_mandate};

    fn deploy(seed: u8) -> (AppCipherclerk, EmbeddedExecutor, MandateService) {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32]);
        let executor = EmbeddedExecutor::new(&cclerk, "default");
        // Installs `tad_born_cell_program()` (the SAME caveats the factory bakes) + a granted
        // baseline (tool search-mcp, rate 4, no expiry at the embedded height).
        seed_granted_mandate(&executor, "search-mcp", 4, 0);
        let service = MandateService::new(cclerk.cell_id());
        (cclerk, executor, service)
    }

    #[test]
    fn an_on_chain_exercise_drives_the_reactor_to_audit_log() {
        // THE END-TO-END event-driven loop: a committed `exercise` → the reactor sees it via
        // the observed receipt → its audit reaction emits a `tool-invocation-logged` turn,
        // committed through the real executor.
        let (cclerk, executor, service) = deploy(0x01);

        // 1) A worker exercises the mandate: meter 0 → 1, through the invoke() front door.
        let turn = service
            .exercise(
                &cclerk,
                0,
                field_from_u64(0xabc),
                InvokeAuthority::Signature,
            )
            .expect("a Signature holder may exercise");
        let receipt = executor
            .submit_turn(&turn)
            .expect("the exercise commits (meter advances under the ceiling)");
        assert_eq!(
            executor.cell_state(service.cell).unwrap().fields[CALLS_MADE_SLOT as usize],
            field_from_u64(1),
            "the exercise advanced the meter to 1"
        );

        // 2) The reactor OBSERVES the exercise and reacts with an audit log.
        let observed = ObservedReceipt {
            cell: service.cell,
            method: symbol(crate::service::METHOD_EXERCISE),
            effects: vec![Effect::SetField {
                cell: service.cell,
                index: CALLS_MADE_SLOT as u64,
                value: field_from_u64(1),
            }],
            turn_hash: receipt.turn_hash,
            signer: cclerk.public_key().0,
        };
        let reactor = MandateAuditReactor::new(service.cell);
        let audit = react_build(&cclerk, &reactor, &observed, InvokeAuthority::Signature)
            .expect("a Signature-holding reactor is authorized")
            .expect("a watched exercise reacts");

        // 3) The audit reaction IS a genuine turn — submit it; it commits without perturbing
        //    the meter it records.
        executor
            .submit_turn(&audit)
            .expect("the audit-log reaction turn commits (writes no slot)");
        assert_eq!(
            executor.cell_state(service.cell).unwrap().fields[CALLS_MADE_SLOT as usize],
            field_from_u64(1),
            "the audit did not perturb the meter it recorded"
        );
    }

    #[test]
    fn the_reactor_only_watches_exercise() {
        let (cclerk, executor, service) = deploy(0x02);
        let reactor = MandateAuditReactor::new(service.cell);
        let _ = &executor;

        // An observed `grant` (not the watched `exercise`) → no reaction.
        let off = ObservedReceipt {
            cell: service.cell,
            method: symbol(crate::service::METHOD_GRANT),
            effects: vec![],
            turn_hash: [0u8; 32],
            signer: cclerk.public_key().0,
        };
        assert!(matches!(
            react_build(&cclerk, &reactor, &off, InvokeAuthority::Signature),
            Ok(None)
        ));
    }

    #[test]
    fn the_reaction_is_cap_gated_fail_closed() {
        let (cclerk, _executor, service) = deploy(0x03);
        let reactor = MandateAuditReactor::new(service.cell);

        let observed = ObservedReceipt {
            cell: service.cell,
            method: symbol(crate::service::METHOD_EXERCISE),
            effects: vec![Effect::SetField {
                cell: service.cell,
                index: CALLS_MADE_SLOT as u64,
                value: field_from_u64(1),
            }],
            turn_hash: [7u8; 32],
            signer: cclerk.public_key().0,
        };

        // A None-authority reactor cannot satisfy the Signature-required audit reaction.
        let refused = react_build(&cclerk, &reactor, &observed, InvokeAuthority::None)
            .expect_err("None authority cannot satisfy a Signature reaction");
        assert!(matches!(refused, ReactRefused::Unauthorized { .. }));
    }
}
