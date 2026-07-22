//! # privacy-voting — the vote-forwarding feed as a `Reactor` (the reactive twin of
//! `invoke()`).
//!
//! The fifth axis (AX5) of a modern starbridge-app. Where the [`crate::service`] face
//! is the **command** front-door (a `cast_vote`/`record_tally` turn comes *in*,
//! caller-driven), this is the **reaction** front-door: a service that WATCHES the
//! BALLOT cell and, when a `cast_vote` commits, REACTS by emitting a `record_tally`
//! turn on the POLL cell — event-driven, the on-chain agent-loop.
//!
//! Both front-doors are **userspace**: there is NO kernel `Effect::React` (just as
//! there is no `Effect::Invoke`). The reaction desugars to an ordinary [`Effect`] the
//! kernel already enforces and the circuit already witnesses — here, an `EmitEvent`
//! `vote-cast` on the poll, re-enforced by the poll's installed `always(...)` program.
//!
//! ## What the reactor does — and the honest seam
//!
//! [`VotingTallyReactor`] watches the BALLOT for committed
//! [`cast_vote`](crate::service::METHOD_CAST_VOTE) ops. On a match it reads the CHOICE
//! straight off the observed turn's committed `SetField` on
//! [`VOTE_SLOT`](crate::VOTE_SLOT) and reacts with a `record_tally` turn on the POLL
//! whose effect is an `EmitEvent` `vote-cast` carrying that choice — the poll-side
//! public audit/tally FEED.
//!
//! The reaction is **emit-only by design**, not by omission. [`Reactor::react`]
//! receives ONLY the observed receipt — there is NO live-state access — so the
//! running `Monotonic` tally COUNTER bump (which needs `old + 1`) is NOT directly
//! expressible: a single observed vote carries no running count, and a
//! fire-and-forget reactor cannot read the poll's live tally to compute the next
//! value. So the COUNT bump stays on the COMMAND path
//! ([`record_tally`](crate::service::VotingService::record_tally) /
//! [`crate::fire_record_tally`], which DO read live state); the reactor records each
//! observed vote into the poll's public `vote-cast` FEED. This needs no live read, no
//! schema change, and commits cleanly: the poll's `always(...)` program admits an
//! `EmitEvent`-only turn (the three `Monotonic` tallies and the two `WriteOnce` slots
//! are all unchanged, which every caveat permits).

use dregg_app_framework::{
    AuthRequired, Effect, Event, FieldElement, ObservedReceipt, ReactionPlan, Reactor,
    ReceiptFilter, symbol,
};
use dregg_types::CellId;

use crate::VOTE_SLOT;

/// **A vote-forwarding tally reactor** — watches the BALLOT cell for committed
/// `cast_vote` ops and reacts by recording the vote into the POLL cell's public
/// `vote-cast` feed.
///
/// The reactive analogue of a [`crate::service::VotingService`] mutator: it DECLARES
/// its watch ([`ReceiptFilter`] over the ballot's `cast_vote` method) and how it
/// reacts ([`Reactor::react`] → a `record_tally` [`ReactionPlan`] on the poll); the
/// framework wires the match → cap-gate → build → sign.
#[derive(Clone, Debug)]
pub struct VotingTallyReactor {
    /// The BALLOT cell this reactor watches.
    pub ballot: CellId,
    /// The POLL cell this reactor records observed votes into.
    pub poll: CellId,
}

impl VotingTallyReactor {
    /// A tally reactor watching `ballot` and recording into `poll`.
    pub fn new(ballot: CellId, poll: CellId) -> Self {
        VotingTallyReactor { ballot, poll }
    }
}

impl Reactor for VotingTallyReactor {
    fn filter(&self) -> ReceiptFilter {
        // What it watches: the BALLOT cell, for the `cast_vote` op. The reactive
        // analogue of the service cell's interface descriptor.
        ReceiptFilter::cell_methods(self.ballot, &[crate::service::METHOD_CAST_VOTE])
    }

    fn react(&self, observed: &ObservedReceipt) -> Option<ReactionPlan> {
        // Decode the CHOICE off the observed turn's committed effects: the `SetField`
        // on VOTE_SLOT is the voter's choice code.
        let mut choice: Option<FieldElement> = None;
        for effect in &observed.effects {
            if let Effect::SetField { index, value, .. } = effect
                && *index == VOTE_SLOT as u64
            {
                choice = Some(*value);
            }
        }
        // No vote write in the observed turn → nothing to forward.
        let choice = choice?;
        Some(ReactionPlan {
            target: self.poll,
            method: crate::service::METHOD_RECORD_TALLY.into(),
            args: vec![choice],
            // The reaction records the observed vote into the poll's public feed: an
            // EmitEvent-only turn the poll's `always(...)` program admits (every slot
            // unchanged). The running COUNT bump stays on the command path (it needs
            // a live read the fire-and-forget reactor does not have).
            effects: vec![Effect::EmitEvent {
                cell: self.poll,
                event: Event::new(symbol("vote-cast"), vec![choice]),
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
        react_build, symbol,
    };

    use crate::{VOTE_YES, build_cast_vote_action, seed_ballot, seed_poll};

    fn deploy(seed: u8) -> (AppCipherclerk, EmbeddedExecutor, CellId, CellId) {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32]);
        let executor = EmbeddedExecutor::new(&cclerk, "default");
        // Installs the poll program + genesis state and the ballot companion cell.
        seed_poll(&executor, "ship it?");
        let poll = cclerk.cell_id();
        let ballot = seed_ballot(&executor, &cclerk, poll);
        (cclerk, executor, ballot, poll)
    }

    #[test]
    fn an_on_chain_cast_vote_drives_the_reactor_to_record_into_the_poll_feed() {
        // THE END-TO-END event-driven loop: a committed `cast_vote` on the ballot →
        // the reactor sees it via the observed receipt → its `record_tally` reaction
        // records the vote into the poll's public feed, committed through the real
        // executor.
        let (cclerk, executor, ballot, poll) = deploy(0x01);

        // 1) A voter casts YES on their ballot (binds POLL_REF + VOTE).
        let action = build_cast_vote_action(&cclerk, ballot, poll, VOTE_YES);
        let receipt = executor
            .submit_action(&cclerk, action.clone())
            .expect("the cast_vote commits (one vote per ballot)");
        assert_eq!(
            executor.cell_state(ballot).unwrap().fields[VOTE_SLOT],
            crate::field_from_u64(VOTE_YES),
            "the ballot recorded the YES choice"
        );

        // 2) The reactor OBSERVES the cast_vote (off its committed effects) and reacts.
        let observed =
            ObservedReceipt::from_action(&action, receipt.turn_hash, cclerk.public_key().0);
        let reactor = VotingTallyReactor::new(ballot, poll);
        let turn = react_build(&cclerk, &reactor, &observed, InvokeAuthority::Signature)
            .expect("a Signature-holding reactor is authorized")
            .expect("a watched cast_vote reacts");

        // 3) The reaction IS the genuine record_tally turn — submit it; it commits on
        //    the poll (an EmitEvent-only feed entry the `always(...)` program admits).
        executor
            .submit_turn(&turn)
            .expect("the reaction record_tally turn commits on the poll");
    }

    #[test]
    fn the_reactor_only_watches_cast_vote() {
        let (cclerk, executor, ballot, poll) = deploy(0x02);
        let reactor = VotingTallyReactor::new(ballot, poll);

        // An observed `close_poll` (not the watched `cast_vote`) → no reaction.
        let off = ObservedReceipt {
            cell: ballot,
            method: symbol(crate::service::METHOD_CLOSE_POLL),
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
        let (cclerk, executor, ballot, poll) = deploy(0x03);

        let action = build_cast_vote_action(&cclerk, ballot, poll, VOTE_YES);
        let receipt = executor
            .submit_action(&cclerk, action.clone())
            .expect("cast_vote commits");
        let observed =
            ObservedReceipt::from_action(&action, receipt.turn_hash, cclerk.public_key().0);
        let reactor = VotingTallyReactor::new(ballot, poll);

        // A None-authority reactor cannot satisfy the Signature-required reaction.
        let refused = react_build(&cclerk, &reactor, &observed, InvokeAuthority::None)
            .expect_err("None authority cannot satisfy a Signature reaction");
        assert!(matches!(refused, ReactRefused::Unauthorized { .. }));
    }
}
