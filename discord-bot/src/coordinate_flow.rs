//! Two channel-agents coordinate over the promise-pipeline — the surfaced flow.
//!
//! This module is **Discord-independent** (like [`crate::intent_flow`]): it runs a
//! real agent-coordination round through
//! [`dregg_app_framework::agent_coordination::coordinate`] and returns the receipt
//! the command layer renders. The community watching the channel sees two agents
//! cooperate: a PRODUCER agent computes a result off-chain, a CONSUMER agent
//! PIPELINES its payment against the producer's promised result, and the whole
//! cooperation settles ATOMICALLY as one verified conserving fold on the
//! light-client rail. If either leg's work fails the promise breaks and the round
//! rolls back whole — nothing settles.
//!
//! # What is REAL vs. demo (honest)
//!
//! REAL — and proven offline by the tests in this module:
//! * the promise HANDOFF — the producer's output is a canonical `EventualRef` the
//!   consumer pipelines against (its fill recorded in the receipt);
//! * the ATOMIC verified conserving settle — the round folds through
//!   `settle_ring_wide_verified`, the SAME verified executor (per-asset Σδ=0, Lean
//!   FFI cross-checked leg by leg) the ring trade and the service-promise escrow
//!   trust;
//! * the ROLLBACK — a broken promise refuses the round before any settle, so the
//!   ledger is byte-identical (atomicity).
//!
//! DEMO — the off-chain WORK each agent does is a small deterministic computation
//! (the producer "prices" the task at a fixed amount; the consumer pays exactly
//! that) and the round settles over a SEEDED ledger funded for the demonstration,
//! not the agents' live custodial balances. The coordination MECHANISM around that
//! work — the promise pipeline, the atomic verified settle, the conservation, the
//! rollback — is the real, proven part. Swapping the deterministic work for a live
//! agent's (a Hermes tool-call producing the result, a real funded ledger) changes
//! only the work producer, exactly as `crate::hermes_channel`'s classifier seam
//! changes only the tool-call producer.

use dregg_app_framework::agent_coordination::{
    CoordinationError, CoordinationLeg, CoordinationReceipt, LegOutput, coordinate,
};
use dregg_app_framework::ring_trade::{CommitmentId, WideLedger, WideLeg};

/// The asset the demonstration round settles in (a fixed demo asset tag).
const COORD_ASSET: [u8; 32] = {
    let mut a = [0u8; 32];
    a[0] = 0xC0;
    a[1] = 0x0D;
    a
};

/// The outcome of a surfaced two-agent coordination round.
#[derive(Clone, Debug)]
pub struct CoordinationOutcome {
    /// The producer agent (computes the result the consumer needs).
    pub producer: CommitmentId,
    /// The consumer agent (pipelines its payment against the producer's promise).
    pub consumer: CommitmentId,
    /// The price the producer quoted off-chain (the consumer paid exactly this).
    pub price: u64,
    /// The full coordination receipt (promise fills, parallel layers, the verified
    /// conserving post-ledger, the round hash).
    pub receipt: CoordinationReceipt,
}

impl CoordinationOutcome {
    /// The consumer's settled balance after the round.
    pub fn consumer_balance(&self) -> i128 {
        self.receipt
            .verified_post
            .get(self.consumer.0, &COORD_ASSET)
    }
    /// The producer's settled balance after the round.
    pub fn producer_balance(&self) -> i128 {
        self.receipt
            .verified_post
            .get(self.producer.0, &COORD_ASSET)
    }
    /// The conserved total supply across the round (unchanged by a conserving round).
    pub fn conserved_total(&self) -> i128 {
        self.receipt.verified_post.total_asset(&COORD_ASSET)
    }
    /// The round hash, hex-encoded.
    pub fn round_hash_hex(&self) -> String {
        hex32(&self.receipt.round_hash)
    }
}

/// Derive a round id binding the two agents + the task so the same pair coordinating
/// on the same task is reproducible while distinct tasks get distinct rounds.
fn round_id_for(producer: &CommitmentId, consumer: &CommitmentId, task: &str) -> [u8; 32] {
    let mut h = blake3::Hasher::new_derive_key("dregg.discord.coordinate-round.v1");
    h.update(&producer.0);
    h.update(&consumer.0);
    h.update(task.as_bytes());
    *h.finalize().as_bytes()
}

/// **Run a real two-agent coordination round** between `producer` and `consumer`
/// over the promise-pipeline.
///
/// The producer's off-chain work quotes a `price` for `task` (a deterministic
/// demonstration of "agent A produces a result agent B needs"). The consumer
/// PIPELINES against that promise: it reads the quoted price and contributes a
/// payment of exactly that amount. The round settles ATOMICALLY through the
/// verified executor over a ledger seeded with `consumer_balance` for the consumer.
///
/// Returns the outcome (the verified conserving post-ledger + the promise audit
/// trail), or a [`CoordinationError`] if the round refuses (e.g. the consumer
/// cannot afford the quote — the verified gate rejects the non-conserving fold).
pub fn run_pair_round(
    producer: CommitmentId,
    consumer: CommitmentId,
    task: &str,
    price: u64,
    consumer_balance: u64,
) -> Result<CoordinationOutcome, CoordinationError> {
    let round_id = round_id_for(&producer, &consumer, task);

    // Seed the demonstration ledger: the consumer is funded, the producer live.
    let mut ledger = WideLedger::new();
    ledger.add_account(producer.0);
    ledger.add_account(consumer.0);
    ledger.set(consumer.0, &COORD_ASSET, consumer_balance as i128);

    let legs = vec![
        // The PRODUCER agent: compute the result the consumer needs (the price),
        // off-chain. Its output is the promise the consumer pipelines against.
        CoordinationLeg::new(producer, "produce", move |_inputs| {
            Ok(LegOutput::compute(price.to_le_bytes().to_vec()))
        }),
        // The CONSUMER agent: pipeline against the producer's promise — read the
        // quoted price and settle a payment of exactly that amount.
        CoordinationLeg::new(consumer, "consume", move |inputs| {
            let raw = inputs.get("produce").cloned().unwrap_or_default();
            let quoted = u64::from_le_bytes(
                raw.try_into()
                    .map_err(|_| "producer promise was not a price".to_string())?,
            );
            Ok(LegOutput::with_moves(
                b"paid",
                vec![WideLeg {
                    from: consumer.0,
                    to: producer.0,
                    asset: COORD_ASSET,
                    amount: quoted as i128,
                }],
            ))
        })
        .after("produce"),
    ];

    let receipt = coordinate(round_id, legs, &ledger)?;
    Ok(CoordinationOutcome {
        producer,
        consumer,
        price,
        receipt,
    })
}

/// Hex-encode a 32-byte hash.
fn hex32(bytes: &[u8; 32]) -> String {
    let mut s = String::with_capacity(64);
    for b in bytes {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cid(b: u8) -> CommitmentId {
        CommitmentId([b; 32])
    }

    #[test]
    fn a_pair_round_settles_atomically_and_conserves() {
        // GENUINE ✓ — producer A quotes 30, consumer B (funded 100) pipelines a
        // payment of exactly 30 against A's promise; the round settles atomically
        // and conserves: B 70, A 30, supply unchanged.
        let out = run_pair_round(cid(1), cid(2), "render-report", 30, 100)
            .expect("an affordable round settles");
        assert_eq!(out.consumer_balance(), 70);
        assert_eq!(out.producer_balance(), 30);
        assert_eq!(out.conserved_total(), 100, "value conserved end-to-end");
        // The promise handoff is recorded: produce → consume.
        assert_eq!(out.receipt.fills.len(), 2);
        assert_eq!(out.receipt.fills[0].leg, "produce");
        assert_eq!(out.receipt.fills[1].leg, "consume");
        // The round hash is a real 64-hex digest.
        assert_eq!(out.round_hash_hex().len(), 64);
    }

    #[test]
    fn an_unaffordable_round_is_refused_whole() {
        // The consumer cannot afford the quote — the verified gate rejects the
        // non-conserving fold and nothing settles (atomic).
        let err = run_pair_round(cid(1), cid(2), "expensive", 999, 100)
            .expect_err("an unaffordable round cannot conserve");
        assert!(matches!(err, CoordinationError::NotConserving(_)));
    }

    #[test]
    fn the_round_is_reproducible_for_the_same_pair_and_task() {
        let a = run_pair_round(cid(1), cid(2), "task-x", 10, 100).unwrap();
        let b = run_pair_round(cid(1), cid(2), "task-x", 10, 100).unwrap();
        assert_eq!(a.round_hash_hex(), b.round_hash_hex());
        // A different task gives a different round.
        let c = run_pair_round(cid(1), cid(2), "task-y", 10, 100).unwrap();
        assert_ne!(a.round_hash_hex(), c.round_hash_hex());
    }
}
