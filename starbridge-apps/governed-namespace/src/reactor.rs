//! # governed-namespace — the quorum auto-committer as a `Reactor` (the reactive
//! twin of `invoke()`).
//!
//! The fifth axis (AX5) of a modern starbridge-app. Where the [`crate::service`]
//! face is the **command** front-door (a `propose` / `vote` / `commit` turn comes
//! *in*, caller-driven), this is the **reaction** front-door: a service that WATCHES
//! the namespace cell and, when a `vote_on_proposal` commits that crosses the
//! committee threshold, REACTS by emitting its own `commit_table_update` turn —
//! event-driven, the on-chain governance loop.
//!
//! [`GovernanceCommitReactor`] is the vote→commit step made reactive: the
//! propose → vote → commit lifecycle's final step is EVENT-DRIVEN (a quorum of votes
//! triggers the swap), which is exactly what a [`Reactor`] models. It watches the
//! namespace for committed [`vote_on_proposal`](crate::service::METHOD_VOTE) ops and
//! reacts by [`commit_table_update`](crate::service::METHOD_COMMIT)-ing the proposal
//! — reading the running tally off the observed turn's `PENDING_PROPOSAL_ROOT`
//! slot, and the proposed root + target version off the `vote-cast` event the same
//! turn emits.
//!
//! Both front-doors are **userspace**: there is NO kernel `Effect::React` (just as
//! there is no `Effect::Invoke`). The reaction desugars to an ordinary [`Effect`]
//! the kernel already enforces and the circuit already witnesses — here, the SAME
//! [`crate::service::commit_effects`] body a service `commit` desugars to. The
//! reaction's `commit` turn is re-enforced by the installed
//! [`crate::service::governance_service_program`] (the descriptor's own flat
//! invariants): `Monotonic(VERSION)` bites as a real executor refusal, so a reaction
//! can never roll the route-table generation backward.

use dregg_app_framework::{
    AuthRequired, Effect, FieldElement, ObservedReceipt, ReactionPlan, Reactor, ReceiptFilter,
    symbol,
};
use dregg_types::CellId;

use crate::PENDING_PROPOSAL_ROOT_SLOT;
use crate::service::commit_effects;

/// **A quorum auto-committer reactor** — watches a governed-namespace cell for
/// committed `vote_on_proposal` ops and reacts by `commit_table_update`-ing once the
/// running tally crosses the committee `threshold`.
///
/// The reactive analogue of a [`crate::service::GovernanceService`] commit: it
/// DECLARES its watch ([`ReceiptFilter`] over the namespace's `vote_on_proposal`
/// method) and how it reacts ([`Reactor::react`] → a `commit` [`ReactionPlan`]); the
/// framework wires the match → cap-gate → build → sign. A vote below quorum produces
/// no reaction.
#[derive(Clone, Debug)]
pub struct GovernanceCommitReactor {
    /// The namespace cell this reactor watches (and commits against).
    pub namespace: CellId,
    /// The committee threshold — the running tally must REACH this for the swap to
    /// fire. Carried as reactor config (the same `threshold` the cell's
    /// `THRESHOLD_SLOT` pins); a vote whose observed tally is below it does not
    /// react.
    pub threshold: u64,
}

impl GovernanceCommitReactor {
    /// A commit reactor watching `namespace`, firing the swap at `threshold`
    /// distinct approving votes.
    pub fn new(namespace: CellId, threshold: u64) -> Self {
        GovernanceCommitReactor {
            namespace,
            threshold,
        }
    }
}

impl Reactor for GovernanceCommitReactor {
    fn filter(&self) -> ReceiptFilter {
        // What it watches: the namespace cell, for the `vote_on_proposal` op. The
        // reactive analogue of the service cell's interface descriptor.
        ReceiptFilter::cell_methods(self.namespace, &[crate::service::METHOD_VOTE])
    }

    fn react(&self, observed: &ObservedReceipt) -> Option<ReactionPlan> {
        // Decode the running tally + the proposal payload off the observed turn's
        // committed effects:
        //   - the `SetField` on PENDING_PROPOSAL_ROOT is the running vote count;
        //   - the `vote-cast` event carries [tally, proposed_root, new_version].
        let mut tally: Option<u64> = None;
        let mut proposed_root: Option<FieldElement> = None;
        let mut new_version: Option<u64> = None;
        for effect in &observed.effects {
            match effect {
                Effect::SetField { index, value, .. }
                    if *index == PENDING_PROPOSAL_ROOT_SLOT as usize =>
                {
                    tally = Some(field_to_u64(value));
                }
                Effect::EmitEvent { event, .. } if event.topic == symbol("vote-cast") => {
                    if event.data.len() >= 3 {
                        proposed_root = Some(event.data[1]);
                        new_version = Some(field_to_u64(&event.data[2]));
                    }
                }
                _ => {}
            }
        }
        // The swap only fires once the running tally REACHES the committee threshold
        // — a vote below quorum produces no reaction (fail-closed on missing data).
        let tally = tally?;
        if tally < self.threshold {
            return None;
        }
        let new_root = proposed_root?;
        let new_version = new_version?;
        Some(ReactionPlan {
            target: self.namespace,
            method: crate::service::METHOD_COMMIT.into(),
            args: vec![],
            // The reaction desugars to the ordinary commit body — the kernel /
            // circuit see only what they already know. The executor re-enforces
            // `Monotonic(VERSION)` on it.
            effects: commit_effects(self.namespace, new_root, new_version),
            auth_required: AuthRequired::Signature,
        })
    }
}

/// Read a `u64` from the last 8 big-endian bytes of a field element (the inverse of
/// `field_from_u64` for the tally + version the namespace stores).
fn field_to_u64(f: &FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&f[24..32]);
    u64::from_be_bytes(b)
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::{
        AgentCipherclerk, AppCipherclerk, EmbeddedExecutor, InvokeAuthority, ReactRefused,
        field_from_bytes, field_from_u64, react_build,
    };

    use crate::VERSION_SLOT;
    use crate::service::{GovernanceService, seed_namespace};

    const THRESHOLD: u64 = 3;

    /// A cipherclerk + an embedded executor whose agent cell IS the namespace cell,
    /// seeded with the service program (the descriptor's flat invariants), a quorum
    /// threshold, and version 1 with a genesis route table.
    fn deploy(seed: u8) -> (AppCipherclerk, EmbeddedExecutor, GovernanceService) {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32]);
        let executor = EmbeddedExecutor::new(&cclerk, "default");
        seed_namespace(
            &executor,
            THRESHOLD,
            1,
            field_from_bytes(b"genesis-route-table-root"),
        );
        let service = GovernanceService::new(cclerk.cell_id());
        (cclerk, executor, service)
    }

    #[test]
    fn an_on_chain_quorum_vote_drives_the_reactor_to_auto_commit_the_swap() {
        // THE END-TO-END event-driven loop: a committed quorum-crossing `vote` → the
        // reactor sees it via the observed receipt → its `commit` reaction swaps the
        // route table + bumps the version, committed through the real executor.
        let (cclerk, executor, service) = deploy(0x01);
        let namespace = service.cell;
        let proposed_root = field_from_bytes(b"proposed-route-table-v2");

        // 1) A committee member casts the quorum-crossing vote (tally == THRESHOLD),
        //    carrying the proposed root + target version 2.
        let vote = service
            .vote(
                &cclerk,
                THRESHOLD,
                proposed_root,
                2,
                InvokeAuthority::Signature,
            )
            .expect("a Signature holder may build a vote invocation");
        let receipt = executor
            .submit_turn(&vote)
            .expect("the vote commits (PENDING slot unconstrained under flat invariants)");

        // 2) The reactor OBSERVES the vote (off its committed effects) and reacts.
        //    The observed receipt carries the SAME effects the vote turn committed.
        let observed = ObservedReceipt {
            cell: namespace,
            method: symbol(crate::service::METHOD_VOTE),
            effects: crate::service::vote_effects(namespace, THRESHOLD, proposed_root, 2),
            turn_hash: receipt.turn_hash,
            signer: cclerk.public_key().0,
        };
        let reactor = GovernanceCommitReactor::new(namespace, THRESHOLD);
        let turn = react_build(&cclerk, &reactor, &observed, InvokeAuthority::Signature)
            .expect("a Signature-holding reactor is authorized")
            .expect("a quorum-crossing vote reacts");

        // 3) The reaction IS the genuine commit turn — submit it; the swap lands.
        executor
            .submit_turn(&turn)
            .expect("the reaction commit turn commits (version advances under Monotonic)");
        let state = executor.cell_state(namespace).unwrap();
        assert_eq!(
            state.fields[crate::ROUTE_TABLE_ROOT_SLOT as usize],
            proposed_root,
            "the reactor swapped the route table to the proposed root"
        );
        assert_eq!(
            state.fields[VERSION_SLOT as usize],
            field_from_u64(2),
            "the reactor bumped the route-table generation to 2"
        );
    }

    #[test]
    fn a_below_quorum_vote_produces_no_reaction() {
        let (cclerk, _executor, service) = deploy(0x02);
        let namespace = service.cell;
        let proposed_root = field_from_bytes(b"proposed-route-table-v2");
        let reactor = GovernanceCommitReactor::new(namespace, THRESHOLD);

        // A vote with tally below threshold → no reaction (the swap stays unarmed).
        let observed = ObservedReceipt {
            cell: namespace,
            method: symbol(crate::service::METHOD_VOTE),
            effects: crate::service::vote_effects(namespace, THRESHOLD - 1, proposed_root, 2),
            turn_hash: [0u8; 32],
            signer: cclerk.public_key().0,
        };
        assert!(matches!(
            react_build(&cclerk, &reactor, &observed, InvokeAuthority::Signature),
            Ok(None)
        ));
    }

    #[test]
    fn the_reactor_only_watches_votes() {
        let (cclerk, _executor, service) = deploy(0x03);
        let namespace = service.cell;
        let reactor = GovernanceCommitReactor::new(namespace, THRESHOLD);

        // An observed `commit` (not the watched `vote`) → no reaction.
        let off = ObservedReceipt {
            cell: namespace,
            method: symbol(crate::service::METHOD_COMMIT),
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
        let (cclerk, _executor, service) = deploy(0x04);
        let namespace = service.cell;
        let proposed_root = field_from_bytes(b"proposed-route-table-v2");
        let reactor = GovernanceCommitReactor::new(namespace, THRESHOLD);

        let observed = ObservedReceipt {
            cell: namespace,
            method: symbol(crate::service::METHOD_VOTE),
            effects: crate::service::vote_effects(namespace, THRESHOLD, proposed_root, 2),
            turn_hash: [0u8; 32],
            signer: cclerk.public_key().0,
        };

        // A None-authority reactor cannot satisfy the Signature-required reaction.
        let refused = react_build(&cclerk, &reactor, &observed, InvokeAuthority::None)
            .expect_err("None authority cannot satisfy a Signature reaction");
        assert!(matches!(refused, ReactRefused::Unauthorized { .. }));
    }
}
