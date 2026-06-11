//! Adversarial tests against cross-federation promise pipelining (Lean
//! `CapTPPipeline` / B5). The Lean `pipelining_preserves_seam` proves the
//! pipelined `authorization` SURVIVES resolution (resolution delivers, it does
//! not discharge). But the proof said NOTHING about the bridge's sender-binding:
//! the cross-fed bridge used a `local_federation_placeholder() = [0;32]`, so a
//! pipelined send's `authorization` was bound to an ANONYMOUS originator — a
//! relay/bridge could replay a pipelined call under an unset sender (F-10).
//!
//! Adversary model: a malicious relay / bridge operator who wants to forward a
//! pipelined call WITHOUT a verifiable sender binding, so a receiver cannot pin
//! the `authorization` to a concrete originator.

use dregg_captp::{CrossFedPipelineBridge, PipelineWireMessage, PipelinedAction};
use dregg_types::FederationId;
use dregg_wire::prelude::CapTpState;

use dregg_redteam::AttackOutcome;

fn action(method: &str) -> PipelinedAction {
    PipelinedAction {
        method: method.to_string(),
        args: vec![1, 2, 3],
        authorization: vec![0xAB, 0xCD], // the sender's claimed authority
    }
}

fn peer() -> FederationId {
    FederationId([0xBB; 32])
}

// ===========================================================================
// ATTACK — DEFENDED (F-10 CLOSED): the PRODUCTION CapTP state binds a REAL
// sender on every outbound pipelined message.
//
// Previously `CapTpState` constructed its `CrossFedPipelineBridge` via the
// placeholder-default `new()`, so the bridge stamped `[0;32]` as the sender —
// the pipelined `authorization` was unbound. The fix makes
// `CapTpState::new(local_federation)` MANDATORY and constructs the bridge via
// `with_local_federation`, so production NEVER ships an unbound sender.
// ===========================================================================

#[test]
fn finding_pipeline_bridge_ships_unbound_sender() {
    // The node's real federation identity.
    let node_fed_bytes = [0x42u8; 32];
    let me = FederationId(node_fed_bytes);

    // Construct CapTP state the way production does: bound to the node's id.
    let mut captp = CapTpState::new(node_fed_bytes);

    // Send a pipelined action to a peer's promise. A relay observes the outbound
    // wire message and tries to learn / forge the sender.
    let _local = captp
        .pipeline_bridge
        .pipeline_to_remote(peer(), 7, action("drain_treasury"));

    let outbox = captp.pipeline_bridge.drain_outbox();
    assert_eq!(outbox.len(), 1, "exactly one outbound pipelined message");

    match &outbox[0].1 {
        PipelineWireMessage::PipelineToPromise {
            sender_federation,
            action,
            ..
        } => {
            // DEFENDED: the sender is the node's REAL federation id, NOT the
            // anonymous [0;32] placeholder. The pipelined authorization is now
            // bound to a concrete, verifiable originator — a receiver can check
            // it against the named sender; a relay cannot replay it under an
            // unset sender.
            assert_eq!(
                *sender_federation, me,
                "production bridge must stamp the node's real federation as sender"
            );
            assert_ne!(
                *sender_federation,
                FederationId([0u8; 32]),
                "sender must NOT be the unbound [0;32] placeholder (F-10)"
            );
            // The authorization rides along, bound to that concrete sender.
            assert_eq!(action.authorization, vec![0xAB, 0xCD]);
        }
        _ => panic!("expected PipelineToPromise"),
    }
    eprintln!(
        "[PIPELINE ATTACK / DEFENDED] production bridge binds real sender, no [0;32] placeholder (F-10 closed): {}",
        AttackOutcome::Defended
    );
}

// ===========================================================================
// ATTACK — DEFENDED: even constructing a bridge directly, the explicit
// `with_local_federation` path is what binds the sender; the unbound `new()` is
// retained ONLY as a test/back-compat convenience and is never how production
// state is built (there is no `Default for CapTpState`). This asserts the
// `with_local_federation` binding is faithful end-to-end through a chain.
// ===========================================================================

#[test]
fn configured_bridge_binds_sender_through_chain() {
    let me = FederationId([0x11; 32]);
    let mut bridge = CrossFedPipelineBridge::with_local_federation(me);
    assert_eq!(bridge.local_federation(), Some(me));

    // A 2-step chain to a remote: both legs must carry the real sender.
    let steps = vec![action("step_1"), action("step_2")];
    let _final = bridge
        .pipeline_chain_to_remote(peer(), 99, steps)
        .expect("chain must build");

    let outbox = bridge.drain_outbox();
    assert_eq!(outbox.len(), 2, "two pipelined legs");
    for (_, wire) in &outbox {
        match wire {
            PipelineWireMessage::PipelineToPromise {
                sender_federation, ..
            } => {
                assert_eq!(
                    *sender_federation, me,
                    "every chain leg binds the real sender"
                );
                assert_ne!(*sender_federation, FederationId([0u8; 32]));
            }
            _ => panic!("expected PipelineToPromise"),
        }
    }
    eprintln!(
        "[PIPELINE ATTACK 2 / DEFENDED] every chain leg binds the real sender (no unbound default): {}",
        AttackOutcome::Defended
    );
}
