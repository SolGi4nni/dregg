//! # compartment-workflow-mandate — the OFFICER auto-driver as a `Reactor` (the
//! reactive twin of `invoke()`).
//!
//! The fifth axis (AX5) of a modern starbridge-app. Where the [`crate::service`]
//! face is the **command** front-door (an `advance_step` turn comes *in*,
//! caller-driven), this is the **reaction** front-door: a service that WATCHES the
//! mandate cell and, when an `advance_step` commits, REACTS by advancing the charter
//! to the NEXT step — event-driven, the on-chain officer-loop. The workflow becomes
//! self-driving: one committed step wakes the next.
//!
//! [`WorkflowAdvanceReactor`] is an **auto-advancing officer**: it watches the
//! mandate for committed [`advance_step`](crate::service::METHOD_ADVANCE_STEP) ops
//! and reacts by advancing one more step — reading the new charter cursor straight
//! off the observed turn's committed [`SetField`](Effect::SetField) on
//! [`STEP_CURSOR_SLOT`](crate::STEP_CURSOR_SLOT), then driving the cursor up by one
//! more, entering the next step's compartment under the officer's clearance.
//!
//! Both front-doors are **userspace**: there is NO kernel `Effect::React` (just as
//! there is no `Effect::Invoke`). The reaction desugars to the SAME
//! [`crate::advance_effects`] body a service `advance_step` desugars to — the kernel
//! / circuit see only effects they already know. The reaction's `advance_step` turn
//! is re-enforced by the installed [`crate::cwm_cell_program`]: a non-`+1` cursor
//! (`MonotonicSequence(STEP_CURSOR)`), a past-terminal advance
//! (`FieldLteField(STEP_CURSOR <= CHARTER_TERMINAL)`), and a clearance miss (the
//! root-bound `ClearanceDominates`) all bite as REAL executor refusals — so a
//! reaction can never overrun the charter.

use dregg_app_framework::{
    AuthRequired, Effect, FieldElement, ObservedReceipt, ReactionPlan, Reactor, ReceiptFilter,
};
use dregg_types::CellId;

use crate::{STEP_CURSOR_SLOT, WorkflowPhase, advance_effects, officer_label, service};

/// **An auto-advancing OFFICER reactor** — watches a mandate cell for committed
/// `advance_step` ops and reacts by advancing the charter cursor one more step.
///
/// The reactive analogue of a [`crate::service::WorkflowService`]: it DECLARES its
/// watch ([`ReceiptFilter`] over the mandate's `advance_step` method) and how it
/// reacts ([`Reactor::react`] → an `advance_step` [`ReactionPlan`]); the framework
/// wires the match → cap-gate → build → sign. The officer's clearance
/// ([`officer_label`]) dominates every step compartment, so each reaction passes the
/// executor's root-bound `ClearanceDominates` tooth.
#[derive(Clone, Debug)]
pub struct WorkflowAdvanceReactor {
    /// The mandate cell this reactor watches (and drives).
    pub cell: CellId,
}

impl WorkflowAdvanceReactor {
    /// An officer auto-driver watching the mandate cell `cell`.
    pub fn new(cell: CellId) -> Self {
        WorkflowAdvanceReactor { cell }
    }
}

impl Reactor for WorkflowAdvanceReactor {
    fn filter(&self) -> ReceiptFilter {
        // What it watches: the mandate cell, for the `advance_step` op. The reactive
        // analogue of the service cell's interface descriptor.
        ReceiptFilter::cell_methods(self.cell, &[service::METHOD_ADVANCE_STEP])
    }

    fn react(&self, observed: &ObservedReceipt) -> Option<ReactionPlan> {
        // Decode the cursor the observed advance committed (the `SetField` on
        // STEP_CURSOR) — this is where the charter now sits, and the step the
        // reaction advances FROM.
        let mut new_cursor: Option<u64> = None;
        for effect in &observed.effects {
            if let Effect::SetField { index, value, .. } = effect {
                if *index == STEP_CURSOR_SLOT as usize {
                    new_cursor = Some(field_to_u64(value));
                }
            }
        }
        // No cursor advance in the observed step → nothing to react to.
        let next = new_cursor?;
        // The charter is complete (the cursor has reached the terminal) — nothing
        // left to drive. Matched against the canonical demo charter length the seed
        // pins ([`crate::DEFAULT_CHARTER_STEPS`]).
        if next >= crate::DEFAULT_CHARTER_STEPS {
            return None;
        }
        Some(ReactionPlan {
            target: self.cell,
            method: service::METHOD_ADVANCE_STEP.into(),
            args: vec![],
            // The reaction desugars to the ordinary advance body — the kernel /
            // circuit see only what they already know. The executor re-enforces
            // `MonotonicSequence(STEP_CURSOR)` + `FieldLteField(STEP_CURSOR <=
            // CHARTER_TERMINAL)` + the root-bound `ClearanceDominates` on it. The
            // officer's clearance dominates the entered compartment.
            effects: advance_effects(self.cell, next + 1, officer_label(), phase_for(next)),
            auth_required: AuthRequired::Signature,
        })
    }
}

/// The compartment label of the step ENTERED when advancing FROM cursor `step` to
/// `step + 1` (the step at index `step` in the canonical charter). A zero label past
/// the charter (the executor refuses such an advance anyway).
fn phase_for(step: u64) -> FieldElement {
    WorkflowPhase::CHARTER
        .get(step as usize)
        .map(|p| p.compartment_label())
        .unwrap_or([0u8; 32])
}

/// Read a `u64` from the last 8 big-endian bytes of a field element (the inverse of
/// `field_from_u64` for the `STEP_CURSOR` the mandate stores).
pub fn field_to_u64(f: &FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&f[24..32]);
    u64::from_be_bytes(b)
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::{
        AgentCipherclerk, AppCipherclerk, EmbeddedExecutor, InvokeAuthority, ReactRefused,
        field_from_u64, react_build, symbol,
    };

    use crate::{
        DEFAULT_CHARTER_STEPS, DEFAULT_COMMITMENT_ANCHOR, DEFAULT_STEP_SPEND_POLICY,
        build_advance_step_action, charter_clearance_root, seed_workflow,
    };

    fn deploy(seed: u8) -> (AppCipherclerk, EmbeddedExecutor, CellId) {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32]);
        let executor = EmbeddedExecutor::new(&cclerk, "default");
        // Installs `cwm_cell_program()` + the charter config (terminal 3, the REAL
        // clearance-graph root), cursor 0.
        seed_workflow(
            &executor,
            DEFAULT_COMMITMENT_ANCHOR,
            DEFAULT_CHARTER_STEPS,
            charter_clearance_root(),
            DEFAULT_STEP_SPEND_POLICY,
        );
        let cell = cclerk.cell_id();
        (cclerk, executor, cell)
    }

    #[test]
    fn an_on_chain_advance_drives_the_reactor_to_auto_advance_the_next_step() {
        // THE END-TO-END event-driven loop: a committed `advance_step` (0 -> 1) →
        // the reactor sees it via the observed receipt → its `advance_step` reaction
        // drives the cursor one more (1 -> 2), committed through the real executor.
        let (cclerk, executor, cell) = deploy(0x01);

        // 1) An officer advances step 0 (review): cursor 0 -> 1, presenting officer
        //    clearance so the executor's root-bound ClearanceDominates admits.
        let action =
            build_advance_step_action(&cclerk, cell, 0, officer_label(), WorkflowPhase::Review);
        let receipt = executor
            .submit_action(&cclerk, action.clone())
            .expect("the officer's review advance commits (0 -> 1)");
        assert_eq!(
            executor.cell_state(cell).unwrap().fields[STEP_CURSOR_SLOT as usize],
            field_from_u64(1),
            "the first advance moved the cursor to 1"
        );

        // 2) The reactor OBSERVES the advance (off its committed effects) and reacts.
        let observed =
            ObservedReceipt::from_action(&action, receipt.turn_hash, cclerk.public_key().0);
        let reactor = WorkflowAdvanceReactor::new(cell);
        let turn = react_build(&cclerk, &reactor, &observed, InvokeAuthority::Signature)
            .expect("a Signature-holding reactor is authorized")
            .expect("a watched advance reacts");

        // 3) The reaction IS the genuine next advance turn — submit it; the cursor
        //    advances 1 -> 2 (the reactor enters the next step under officer clearance).
        executor
            .submit_turn(&turn)
            .expect("the reaction advance_step turn commits (1 -> 2)");
        assert_eq!(
            executor.cell_state(cell).unwrap().fields[STEP_CURSOR_SLOT as usize],
            field_from_u64(2),
            "the reactor auto-advanced the charter cursor to 2"
        );
    }

    #[test]
    fn the_reactor_only_watches_advance_step() {
        let (cclerk, executor, cell) = deploy(0x02);
        let reactor = WorkflowAdvanceReactor::new(cell);

        // An observed `init_mandate` (not the watched `advance_step`) → no reaction.
        let off = ObservedReceipt {
            cell,
            method: symbol("init_mandate"),
            effects: vec![],
            turn_hash: [0u8; 32],
            signer: cclerk.public_key().0,
        };
        let _ = &executor;
        assert!(matches!(
            react_build(&cclerk, &reactor, &off, InvokeAuthority::Signature),
            Ok(None)
        ));
    }

    #[test]
    fn the_reaction_is_cap_gated_fail_closed() {
        let (cclerk, executor, cell) = deploy(0x03);

        let action =
            build_advance_step_action(&cclerk, cell, 0, officer_label(), WorkflowPhase::Review);
        let receipt = executor
            .submit_action(&cclerk, action.clone())
            .expect("the review advance commits");
        let observed =
            ObservedReceipt::from_action(&action, receipt.turn_hash, cclerk.public_key().0);
        let reactor = WorkflowAdvanceReactor::new(cell);

        // A None-authority reactor cannot satisfy the Signature-required reaction.
        let refused = react_build(&cclerk, &reactor, &observed, InvokeAuthority::None)
            .expect_err("None authority cannot satisfy a Signature reaction");
        assert!(matches!(refused, ReactRefused::Unauthorized { .. }));
    }
}
