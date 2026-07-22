//! # subscription — the auto-drain CONSUMER as a `Reactor` (the reactive twin of
//! `invoke()`).
//!
//! The fifth axis (AX5) of a modern starbridge-app, and the FIRST concrete
//! [`dregg_app_framework::Reactor`] exemplar in the starbridge-apps tree. Where the
//! [`crate::service`] face is the **command** front-door (a `publish`/`consume` turn
//! comes *in*, caller-driven), this is the **reaction** front-door: a service that
//! WATCHES the feed cell and, when a `publish` commits, REACTS by emitting its own
//! `consume` turn — event-driven, the on-chain agent-loop.
//!
//! [`SubscriptionConsumerReactor`] is an **auto-draining consumer**: it watches the
//! feed for committed [`publish`](crate::service::METHOD_PUBLISH) ops and reacts by
//! [`consume`](crate::service::METHOD_CONSUME)-ing the just-published item — reading
//! the new producer cursor and the published payload straight off the observed
//! turn's committed effects, then drawing the consumer cursor up to it.
//!
//! Both front-doors are **userspace**: there is NO kernel `Effect::React` (just as
//! there is no `Effect::Invoke`). The reaction desugars to an ordinary [`Effect`]
//! the kernel already enforces and the circuit already witnesses — here, the SAME
//! [`crate::consume_effects`] body a service `consume` desugars to. The reaction's
//! `consume` turn is re-enforced by the installed [`crate::feed_invariants_program`]
//! (the SAME flat invariants the deos surface (AX2) and the service face (AX3)
//! assume): `Monotonic(SEQ_TAIL)` + `FieldLteField(tail <= head)` bite as real
//! executor refusals, so a reaction can never over-draw the feed.

use dregg_app_framework::{
    AuthRequired, Effect, FieldElement, ObservedReceipt, ReactionPlan, Reactor, ReceiptFilter,
};
use dregg_types::CellId;

use crate::{LATEST_PAYLOAD_SLOT, SEQ_HEAD_SLOT, consume_effects};

/// **An auto-draining consumer reactor** — watches a subscription feed cell for
/// committed `publish` ops and reacts by `consume`-ing the just-published item.
///
/// The reactive analogue of a [`crate::service::SubscriptionService`] consumer: it
/// DECLARES its watch ([`ReceiptFilter`] over the feed's `publish` method) and how
/// it reacts ([`Reactor::react`] → a `consume` [`ReactionPlan`]); the framework
/// wires the match → cap-gate → build → sign.
#[derive(Clone, Debug)]
pub struct SubscriptionConsumerReactor {
    /// The feed cell this reactor watches (and draws against).
    pub feed: CellId,
}

impl SubscriptionConsumerReactor {
    /// A consumer reactor watching the feed cell `feed`.
    pub fn new(feed: CellId) -> Self {
        SubscriptionConsumerReactor { feed }
    }
}

impl Reactor for SubscriptionConsumerReactor {
    fn filter(&self) -> ReceiptFilter {
        // What it watches: the feed cell, for the `publish` op. The reactive
        // analogue of the service cell's interface descriptor.
        ReceiptFilter::cell_methods(self.feed, &[crate::service::METHOD_PUBLISH])
    }

    fn react(&self, observed: &ObservedReceipt) -> Option<ReactionPlan> {
        // Decode the published cursor + payload off the observed turn's committed
        // effects (what the reactor reads off the cell's state):
        //   - the `SetField` on SEQ_HEAD is the new producer cursor — drain to it;
        //   - the `SetField` on LATEST_PAYLOAD is the delivered payload.
        let mut new_head: Option<u64> = None;
        let mut consumed: FieldElement = [0u8; 32];
        for effect in &observed.effects {
            if let Effect::SetField { index, value, .. } = effect {
                if *index == SEQ_HEAD_SLOT as u64 {
                    new_head = Some(field_to_u64(value));
                } else if *index == LATEST_PAYLOAD_SLOT as u64 {
                    consumed = *value;
                }
            }
        }
        // No producer-cursor advance in the observed publish → nothing to drain.
        let new_tail = new_head?;
        Some(ReactionPlan {
            target: self.feed,
            method: crate::service::METHOD_CONSUME.into(),
            args: vec![],
            // The reaction desugars to the ordinary consume body — the kernel /
            // circuit see only what they already know. The executor re-enforces
            // `Monotonic(SEQ_TAIL)` + `FieldLteField(tail <= head)` on it.
            effects: consume_effects(self.feed, new_tail, consumed),
            auth_required: AuthRequired::Signature,
        })
    }
}

/// Read a `u64` from the last 8 big-endian bytes of a field element (the inverse of
/// `field_from_u64` for the head/tail cursors the feed stores).
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
        field_from_u64, react_build, symbol,
    };

    use crate::{SEQ_TAIL_SLOT, build_publish_action, fold_message_root};

    fn field_from_bytes(bytes: &[u8]) -> FieldElement {
        crate::field_from_bytes(bytes)
    }

    fn deploy(seed: u8) -> (AppCipherclerk, EmbeddedExecutor, CellId) {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32]);
        let executor = EmbeddedExecutor::new(&cclerk, "default");
        // Installs `feed_invariants_program()` + seeds capacity/owner, head=1, tail=0.
        crate::seed_feed(&executor, 16, "owner");
        let feed = cclerk.cell_id();
        (cclerk, executor, feed)
    }

    #[test]
    fn an_on_chain_publish_drives_the_reactor_to_auto_drain_the_feed() {
        // THE END-TO-END event-driven loop: a committed `publish` → the reactor sees
        // it via the observed receipt → its `consume` reaction draws the tail up to
        // the just-published head, committed through the real executor.
        let (cclerk, executor, feed) = deploy(0x01);

        // 1) A publisher delivers: head 1 → 2, with a folded root + payload.
        let payload = field_from_bytes(b"item-2");
        let root = fold_message_root(&[0u8; 32], 2, &payload);
        let action = build_publish_action(&cclerk, feed, field_from_u64(2), root, payload);
        let receipt = executor
            .submit_action(&cclerk, action.clone())
            .expect("the publish commits (head advances under Monotonic)");
        assert_eq!(
            executor.cell_state(feed).unwrap().fields[SEQ_HEAD_SLOT as usize],
            field_from_u64(2),
            "the publish advanced the producer cursor to 2"
        );

        // 2) The reactor OBSERVES the publish (off its committed effects) and reacts.
        let observed =
            ObservedReceipt::from_action(&action, receipt.turn_hash, cclerk.public_key().0);
        let reactor = SubscriptionConsumerReactor::new(feed);
        let turn = react_build(&cclerk, &reactor, &observed, InvokeAuthority::Signature)
            .expect("a Signature-holding reactor is authorized")
            .expect("a watched publish reacts");

        // 3) The reaction IS the genuine consume turn — submit it; the feed drains.
        executor
            .submit_turn(&turn)
            .expect("the reaction consume turn commits (tail <= head)");
        assert_eq!(
            executor.cell_state(feed).unwrap().fields[SEQ_TAIL_SLOT as usize],
            field_from_u64(2),
            "the reactor drained the consumer cursor up to the published head"
        );
    }

    #[test]
    fn the_reactor_only_watches_publish() {
        let (cclerk, executor, feed) = deploy(0x02);
        let reactor = SubscriptionConsumerReactor::new(feed);

        // An observed `consume` (not the watched `publish`) → no reaction.
        let off = ObservedReceipt {
            cell: feed,
            method: symbol(crate::service::METHOD_CONSUME),
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
        let (cclerk, executor, feed) = deploy(0x03);

        let payload = field_from_bytes(b"item-2");
        let root = fold_message_root(&[0u8; 32], 2, &payload);
        let action = build_publish_action(&cclerk, feed, field_from_u64(2), root, payload);
        let receipt = executor
            .submit_action(&cclerk, action.clone())
            .expect("publish commits");
        let observed =
            ObservedReceipt::from_action(&action, receipt.turn_hash, cclerk.public_key().0);
        let reactor = SubscriptionConsumerReactor::new(feed);

        // A None-authority reactor cannot satisfy the Signature-required reaction.
        let refused = react_build(&cclerk, &reactor, &observed, InvokeAuthority::None)
            .expect_err("None authority cannot satisfy a Signature reaction");
        assert!(matches!(refused, ReactRefused::Unauthorized { .. }));
    }
}
