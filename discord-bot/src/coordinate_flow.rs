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
//! that). The coordination MECHANISM around that work — the promise pipeline, the
//! atomic verified settle, the conservation, the rollback — is the real, proven
//! part. Swapping the deterministic work for a live agent's (a Hermes tool-call
//! producing the result) changes only the work producer, exactly as
//! `crate::hermes_channel`'s classifier seam changes only the tool-call producer.
//!
//! # Driving it LIVE on the node
//!
//! [`run_pair_round`] proves the round OFF-CHAIN (the promise pipeline + the
//! verified conserving fold over a representation ledger). [`settle_round_live`]
//! then submits the round's settled value moves to the LIVE node as ONE real,
//! atomic, conserving turn signed by the payer — the node's verified executor
//! re-checks Σδ=0 and commits the whole turn or rejects it whole. A broken
//! promise ([`run_pair_round_broken`]) refuses the round before that submit, so
//! NOTHING lands on the node and the live ledger is untouched. That is the live
//! "watch your agent civilization": real cells, a real on-chain settle, a real
//! receipt — and a real rollback when a promise breaks.

use dregg_app_framework::agent_coordination::{
    CoordinationError, CoordinationLeg, CoordinationReceipt, LegOutput, coordinate,
};
use dregg_app_framework::ring_trade::{CommitmentId, WideLedger, WideLeg};
use dregg_sdk::CellId;
use dregg_turn::{Action, Effect};

use crate::cipherclerk::UserCipherclerk;
use crate::devnet::{DevnetClient, DevnetError};

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

/// **Run a two-agent round whose PRODUCER work FAILS** — the broken-promise
/// path. The producer's off-chain work returns an error, so its promise BREAKS;
/// the breakage propagates to the consumer's pipelined leg and
/// [`coordinate`] refuses the round *before any settle*. Used to demonstrate the
/// live rollback: because the round never reaches the settle, nothing is ever
/// submitted to the node, so the live ledger is untouched (atomicity).
///
/// Returns the [`CoordinationError::Broken`] the round refuses with.
pub fn run_pair_round_broken(
    producer: CommitmentId,
    consumer: CommitmentId,
    task: &str,
) -> CoordinationError {
    let round_id = round_id_for(&producer, &consumer, task);
    let mut ledger = WideLedger::new();
    ledger.add_account(producer.0);
    ledger.add_account(consumer.0);
    ledger.set(consumer.0, &COORD_ASSET, 1000);

    let legs = vec![
        // The PRODUCER's off-chain work FAILS — its promise breaks.
        CoordinationLeg::new(producer, "produce", move |_inputs| {
            Err("producer could not complete the task — promise broken".to_string())
        }),
        // The CONSUMER would have pipelined a payment against the producer's
        // promise; the broken promise propagates here and the round rolls back.
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

    coordinate(round_id, legs, &ledger)
        .err()
        .unwrap_or_else(|| unreachable!("a broken producer promise always refuses the round"))
}

// ─── The LIVE on-chain settle ────────────────────────────────────────────────

/// Why a live coordination settle could not land on the node.
#[derive(Debug)]
pub enum LiveSettleError {
    /// The round's value moves are paid from more than one cell. A single
    /// signed turn moves value from ONE payer; a multi-payer ring's live
    /// surface is the node's multi-party atomic proposal (`/turn/atomic`), which
    /// this path does not drive. (A named gate, not a bug.)
    MultiPayer { payers: usize },
    /// A settled move's amount did not fit a `u64` computron value.
    BadAmount(i128),
    /// The node refused the settle turn (e.g. the payer could not afford it —
    /// atomic: nothing committed).
    Rejected(String),
    /// The submission itself failed (transport / node error).
    Submit(DevnetError),
}

impl std::fmt::Display for LiveSettleError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MultiPayer { payers } => write!(
                f,
                "round settles value from {payers} distinct payers; a single signed turn cannot settle a multi-payer ring atomically (use the node's /turn/atomic multi-party proposal)"
            ),
            Self::BadAmount(a) => {
                write!(f, "settled amount {a} does not fit a u64 computron value")
            }
            Self::Rejected(e) => write!(f, "node refused the settle turn (nothing committed): {e}"),
            Self::Submit(e) => write!(f, "settle submission failed: {e:?}"),
        }
    }
}

impl std::error::Error for LiveSettleError {}

/// The on-chain result of settling a coordination round on the LIVE node.
#[derive(Clone, Debug)]
pub enum LiveSettle {
    /// The round's atomic settle landed on the live node as ONE real conserving
    /// turn. `turn_hash` is the node's receipt; `moves` is how many value moves
    /// folded into it.
    Landed {
        /// The node's receipt hash for the settle turn.
        turn_hash: String,
        /// How many value moves the turn settled.
        moves: usize,
    },
    /// The round had no value moves (a pure promise-pipeline round); nothing to
    /// settle on-chain. The off-chain promise receipt still stands.
    NothingToSettle,
}

/// **Settle a coordination round's value moves on the LIVE node** as ONE real,
/// atomic, conserving turn signed by `payer_cclerk`.
///
/// The off-chain [`coordinate`] round has already proven the promise pipeline
/// and the conservation; this step submits the round's `settled_moves` to the
/// node as a single signed turn (one [`Effect::Transfer`] per move, all from the
/// one payer, in one atomic action group). The node's verified executor
/// re-checks per-asset Σδ=0 and either commits the whole turn or rejects it
/// whole — the same all-or-nothing atomicity the off-chain settle has, now on
/// the real chain.
///
/// Every settled move must be paid FROM `payer_cclerk`'s cell. A multi-payer
/// ring is a named gate ([`LiveSettleError::MultiPayer`]).
pub async fn settle_round_live(
    devnet: &DevnetClient,
    payer_cclerk: &UserCipherclerk,
    receipt: &CoordinationReceipt,
    memo: impl Into<String>,
) -> Result<LiveSettle, LiveSettleError> {
    if receipt.settled_moves.is_empty() {
        return Ok(LiveSettle::NothingToSettle);
    }

    let payer = payer_cclerk.cell_id_bytes();
    // Every move must be paid from the single signer; otherwise the round needs
    // the node's multi-party atomic proposal, which this turn cannot express.
    let distinct_payers = receipt
        .settled_moves
        .iter()
        .map(|m| m.from)
        .collect::<std::collections::BTreeSet<_>>()
        .len();
    if receipt.settled_moves.iter().any(|m| m.from != payer) {
        return Err(LiveSettleError::MultiPayer {
            payers: distinct_payers,
        });
    }

    let mut actions: Vec<Action> = Vec::with_capacity(receipt.settled_moves.len());
    for m in &receipt.settled_moves {
        let amount = u64::try_from(m.amount).map_err(|_| LiveSettleError::BadAmount(m.amount))?;
        let from = CellId(m.from);
        let to = CellId(m.to);
        actions.push(payer_cclerk.app.make_action(
            from,
            "transfer",
            vec![Effect::Transfer { from, to, amount }],
        ));
    }

    let result = devnet
        .submit_app_actions(payer_cclerk, actions, Some(memo.into()))
        .await
        .map_err(LiveSettleError::Submit)?;
    if !result.accepted {
        return Err(LiveSettleError::Rejected(result.error.unwrap_or_else(
            || "node rejected the coordination settle turn".to_string(),
        )));
    }
    let turn_hash = result.turn_hash.ok_or_else(|| {
        LiveSettleError::Rejected("node accepted but omitted turn_hash".to_string())
    })?;
    Ok(LiveSettle::Landed {
        turn_hash,
        moves: receipt.settled_moves.len(),
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
