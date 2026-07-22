//! # swarm-orchestration — the COORDINATOR agent-loop as a `Reactor` (the reactive
//! twin of `invoke()`).
//!
//! The fifth axis (AX5) of a modern starbridge-app, and the PRIME agentic
//! [`dregg_app_framework::Reactor`] exemplar in the starbridge-apps tree. Where the
//! [`crate::service`] face is the **command** front-door (an `open_board`/`dispatch`
//! turn comes *in*, operator-driven), this is the **reaction** front-door: a
//! coordinator agent that WATCHES the board cell and, when a swarm mandate is opened,
//! REACTS by dispatching the first sub-task to a worker — event-driven, the on-chain
//! agent-loop made first-class.
//!
//! An agent loop (perceive / plan / act / reflect) lives ABOVE dregg and is the
//! integrator's game; dregg owns the ONE seam that matters — the tool-call / turn
//! boundary. [`CoordinatorReactor`] makes that seam the agent's *autonomy*: the
//! reactor PERCEIVES a committed [`open_board`](crate::service::METHOD_OPEN_BOARD)
//! (a posted mandate, read straight off the observed turn's committed effects),
//! PLANS the next move (size a sub-task against the conserved budget), and ACTS by
//! emitting its own [`dispatch`](crate::service::METHOD_DISPATCH) turn — advancing a
//! worker's spend meter, strictly advancing the epoch, and waking the worker. The
//! same loop a human operator would drive by hand, run on-chain and receipted, where
//! every step is a verified turn the executor re-enforces the swarm policy on.
//!
//! Both front-doors are **userspace**: there is NO kernel `Effect::React` (just as
//! there is no `Effect::Invoke`). The reaction desugars to ordinary [`Effect`]s the
//! kernel already enforces and the circuit already witnesses — here, the SAME
//! [`crate::dispatch_effects`] body a service `dispatch` desugars to. The reaction's
//! `dispatch` turn is re-enforced by the installed [`crate::coordinator_program`]
//! (the SAME swarm policy the deos surface (AX2) and the service face (AX3) assume):
//! the atomic budget gate `AffineLe(spent_a + spent_b <= budget)`, the
//! `StrictMonotonic(EPOCH)` no-replay caveat, and the `Monotonic(SPENT_*)` meters all
//! bite as REAL executor refusals — so an autonomous coordinator can NEVER auto-dispatch
//! past the swarm's mandate. The narration-vs-truth property holds for the agent loop
//! too: what the reactor DID is the on-ledger receipt, not what it claims.

use dregg_app_framework::{
    AuthRequired, Effect, FieldElement, ObservedReceipt, ReactionPlan, Reactor, ReceiptFilter,
};
use dregg_types::CellId;

use crate::{EPOCH_SLOT, Worker, dispatch_effects};

/// **An auto-dispatching coordinator reactor** — watches a dispatch-board cell for a
/// committed `open_board` (a swarm mandate posted) and reacts by `dispatch`-ing the
/// first sub-task to a worker.
///
/// The reactive analogue of a [`crate::service::BoardService`] coordinator: it
/// DECLARES its watch ([`ReceiptFilter`] over the board's `open_board` method) and how
/// it reacts ([`Reactor::react`] → a `dispatch` [`ReactionPlan`]); the framework wires
/// the match → cap-gate → build → sign. The autonomous coordinator's loop, made
/// first-class.
#[derive(Clone, Debug)]
pub struct CoordinatorReactor {
    /// The dispatch-board cell this reactor watches (and dispatches against).
    pub board: CellId,
    /// Which worker the coordinator auto-dispatches the first sub-task to.
    pub worker: Worker,
    /// The worker agent cell the dispatch's async-notify wake targets.
    pub worker_cell: CellId,
    /// The cost the coordinator assigns the auto-dispatched sub-task (summed against
    /// the conserved budget by the executor's `AffineLe` gate).
    pub cost: u64,
    /// The sub-task topic the wake carries.
    pub topic: String,
}

impl CoordinatorReactor {
    /// A coordinator reactor watching `board`, auto-dispatching a `cost`-sized
    /// sub-task on the `topic` to `worker` (agent cell `worker_cell`) the moment the
    /// board is opened.
    pub fn new(board: CellId, worker: Worker, worker_cell: CellId, cost: u64, topic: &str) -> Self {
        CoordinatorReactor {
            board,
            worker,
            worker_cell,
            cost,
            topic: topic.to_string(),
        }
    }
}

impl Reactor for CoordinatorReactor {
    fn filter(&self) -> ReceiptFilter {
        // What it watches: the board cell, for the `open_board` op. The reactive
        // analogue of the service cell's interface descriptor.
        ReceiptFilter::cell_methods(self.board, &[crate::service::METHOD_OPEN_BOARD])
    }

    fn react(&self, observed: &ObservedReceipt) -> Option<ReactionPlan> {
        // PERCEIVE — decode the opened board off the observed turn's committed effects:
        //   - the `SetField` on EPOCH is the board's current dispatch counter (1 at
        //     open) — the next dispatch strictly advances it;
        //   - the `SetField` on the target worker's meter is its current spend (0 at
        //     open) — the dispatch accumulates `cost` onto it.
        let mut cur_epoch: Option<u64> = None;
        let mut prev_spent: u64 = 0;
        for effect in &observed.effects {
            if let Effect::SetField { index, value, .. } = effect {
                if *index == EPOCH_SLOT as u64 {
                    cur_epoch = Some(field_to_u64(value));
                } else if *index == self.worker.spend_slot() as u64 {
                    prev_spent = field_to_u64(value);
                }
            }
        }
        // No epoch in the observed open → nothing to dispatch against (fail-closed).
        let epoch = cur_epoch?;

        // PLAN — size the sub-task: accumulate `cost` onto the worker's meter and
        // strictly advance the epoch.
        let new_spent = prev_spent.saturating_add(self.cost);
        let new_epoch = epoch.saturating_add(1);

        // ACT — emit the dispatch. The reaction desugars to the ordinary dispatch body
        // (meter + epoch + async wake) — the kernel / circuit see only what they already
        // know. The executor re-enforces `AffineLe(spent_a + spent_b <= budget)` +
        // `StrictMonotonic(EPOCH)` + `Monotonic(SPENT_*)` on it.
        Some(ReactionPlan {
            target: self.board,
            method: crate::service::METHOD_DISPATCH.into(),
            args: vec![field_to_field(self.cost), field_to_field(new_epoch)],
            effects: dispatch_effects(
                self.board,
                self.worker,
                self.worker_cell,
                new_spent,
                new_epoch,
                self.cost,
                &self.topic,
            ),
            auth_required: AuthRequired::Signature,
        })
    }
}

/// Read a `u64` from the last 8 big-endian bytes of a field element (the inverse of
/// `field_from_u64` for the epoch/meter counters the board stores).
fn field_to_u64(f: &FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&f[24..32]);
    u64::from_be_bytes(b)
}

/// A `u64` as a big-endian-padded field element (the args the dispatch records).
fn field_to_field(v: u64) -> FieldElement {
    let mut f = [0u8; 32];
    f[24..32].copy_from_slice(&v.to_be_bytes());
    f
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::{
        AgentCipherclerk, AppCipherclerk, EmbeddedExecutor, InvokeAuthority, ReactRefused,
        field_from_u64, react_build, symbol,
    };

    use crate::{SPENT_A_SLOT, build_open_board_action, coordinator_program};

    fn agent(seed: u8) -> (AppCipherclerk, EmbeddedExecutor) {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32]);
        let executor = EmbeddedExecutor::new(&cclerk, "default");
        (cclerk, executor)
    }

    /// Birth a worker agent cell into the embedded ledger so the dispatch's
    /// async-notify wake (an `EmitEvent` targeting the worker) lands on a real cell —
    /// mirror `tests/deos_seam.rs::birth_worker`. Without it the wake's target is
    /// absent and `apply_emit_event` returns `CellNotFound` before the swarm caveats
    /// are evaluated.
    fn birth_worker(executor: &EmbeddedExecutor, cclerk: &AppCipherclerk, tag: &[u8]) -> CellId {
        let pk = cclerk.public_key().0;
        let token: [u8; 32] = *blake3::hash(tag).as_bytes();
        let mut cell = dregg_cell::Cell::new(pk, token);
        cell.state.set_balance(5_000);
        executor.ensure_cell(cell).expect("worker cell inserts");
        let id = CellId::derive_raw(&pk, &token);
        let agent = cclerk.cell_id();
        executor.with_ledger_mut(|ledger| {
            if let Some(a) = ledger.get_mut(&agent) {
                a.capabilities.grant(id, AuthRequired::Signature);
            }
        });
        id
    }

    /// Install the swarm program on the (fresh, not-yet-open) board cell so the
    /// executor re-enforces it, and birth the worker the dispatch wakes.
    fn deploy(seed: u8) -> (AppCipherclerk, EmbeddedExecutor, CellId, CellId) {
        let (cclerk, executor) = agent(seed);
        let board = cclerk.cell_id();
        // Install the FULL swarm program but do NOT seed the open state — `open_board`
        // is the trigger that binds it (epoch 0 -> 1).
        executor.install_program(board, coordinator_program());
        let worker_cell = birth_worker(&executor, &cclerk, b"worker-a");
        (cclerk, executor, board, worker_cell)
    }

    #[test]
    fn an_on_chain_open_board_drives_the_coordinator_to_auto_dispatch() {
        // THE END-TO-END agent loop: a committed `open_board` (a mandate posted) → the
        // reactor sees it via the observed receipt → its `dispatch` reaction advances a
        // worker meter + the epoch + wakes the worker, committed through the real
        // executor and re-enforced by the swarm program.
        let (cclerk, executor, board, worker_cell) = deploy(0x01);

        // 1) The operator opens the board: lead pinned, budget 1000, epoch 0 -> 1.
        let action = build_open_board_action(&cclerk, board, "lead", 1000);
        let receipt = executor
            .submit_action(&cclerk, action.clone())
            .expect("the open_board commits (epoch advances 0 -> 1 under StrictMonotonic)");
        assert_eq!(
            executor.cell_state(board).unwrap().fields[EPOCH_SLOT as usize],
            field_from_u64(1),
            "the open advanced the dispatch counter to 1"
        );

        // 2) The coordinator OBSERVES the open (off its committed effects) and reacts.
        let observed =
            ObservedReceipt::from_action(&action, receipt.turn_hash, cclerk.public_key().0);
        let reactor = CoordinatorReactor::new(board, Worker::A, worker_cell, 300, "index");
        let turn = react_build(&cclerk, &reactor, &observed, InvokeAuthority::Signature)
            .expect("a Signature-holding reactor is authorized")
            .expect("a watched open_board reacts");

        // 3) The reaction IS the genuine dispatch turn — submit it; the swarm advances.
        executor
            .submit_turn(&turn)
            .expect("the reaction dispatch turn commits (within budget, epoch advances)");
        let state = executor.cell_state(board).unwrap();
        assert_eq!(
            state.fields[SPENT_A_SLOT as usize],
            field_from_u64(300),
            "the coordinator auto-dispatched a 300-cost sub-task to worker A"
        );
        assert_eq!(
            state.fields[EPOCH_SLOT as usize],
            field_from_u64(2),
            "the dispatch strictly advanced the epoch 1 -> 2"
        );
    }

    #[test]
    fn an_over_budget_auto_dispatch_is_refused_by_the_executor() {
        // The agent loop cannot outrun the mandate: a reaction sized past the budget is
        // a REAL executor refusal on the `AffineLe(spent_a + spent_b <= budget)` gate,
        // not a userspace check — the narration-vs-truth tooth on the autonomous loop.
        let (cclerk, executor, board, worker_cell) = deploy(0x02);
        let action = build_open_board_action(&cclerk, board, "lead", 1000);
        let receipt = executor
            .submit_action(&cclerk, action.clone())
            .expect("open_board commits");
        let observed =
            ObservedReceipt::from_action(&action, receipt.turn_hash, cclerk.public_key().0);
        // cost 1001 > budget 1000.
        let reactor = CoordinatorReactor::new(board, Worker::A, worker_cell, 1001, "runaway");
        let turn = react_build(&cclerk, &reactor, &observed, InvokeAuthority::Signature)
            .expect("authorized")
            .expect("the open reacts (the front door passes — the budget gate is the executor's)");
        let rejected = executor.submit_turn(&turn);
        assert!(
            rejected.is_err(),
            "the executor must refuse an over-budget auto-dispatch"
        );
    }

    #[test]
    fn the_reactor_only_watches_open_board() {
        let (cclerk, _executor, board, worker_cell) = deploy(0x03);
        let reactor = CoordinatorReactor::new(board, Worker::A, worker_cell, 1, "t");

        // An observed `dispatch` (not the watched `open_board`) → no reaction.
        let off = ObservedReceipt {
            cell: board,
            method: symbol(crate::service::METHOD_DISPATCH),
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
        let (cclerk, executor, board, worker_cell) = deploy(0x04);
        let action = build_open_board_action(&cclerk, board, "lead", 1000);
        let receipt = executor
            .submit_action(&cclerk, action.clone())
            .expect("open_board commits");
        let observed =
            ObservedReceipt::from_action(&action, receipt.turn_hash, cclerk.public_key().0);
        let reactor = CoordinatorReactor::new(board, Worker::A, worker_cell, 1, "t");

        // A None-authority reactor cannot satisfy the Signature-required reaction.
        let refused = react_build(&cclerk, &reactor, &observed, InvokeAuthority::None)
            .expect_err("None authority cannot satisfy a Signature reaction");
        assert!(matches!(refused, ReactRefused::Unauthorized { .. }));
    }
}
