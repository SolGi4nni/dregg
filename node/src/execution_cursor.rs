//! Identity-tracking execution cursor over the tau-finalized block order.
//!
//! # Why this exists (the TauPrefixMonotone soundness finding, and what became of it)
//!
//! `blocklace_sync::poll_finalized_blocks` used to keep a bare INDEX
//! (`executed_up_to`) into the finalized order computed by `ordering::tau` and
//! slice `ordered[executed_up_to..]` each poll. That is sound **iff** the
//! already-executed prefix of the order is bit-identical across polls — and at the
//! time, `metatheory/Dregg2/Consensus/TauPrefixMonotone.lean` REFUTED that
//! unconditionally: an honest lagging validator that caught up could emit a
//! wave-end block ratifying an ALREADY-FINAL leader, growing that wave's
//! coverage, and the late blocks sorted into the MIDDLE of the already-executed
//! region. ⚠ HISTORY, as of `d182d10fc`: that refutation was a fact about a τ that
//! had DEVIATED from CM Def. 6 (segments were live-lace ratifier coverage, which
//! grows with arrivals). The deviation is FIXED — a segment is now the anchor's
//! OWN closure, fixed by its signed pointers — and on the same lag trace the old
//! order IS a prefix of the new; the counterexample is retained in the Lean
//! INVERTED, as the positive exhibit.
//!
//! # Why the identity cursor STAYS (the closure, on the corrected theorem)
//!
//! The corrected theorem (`tau_finalized_prefix_monotone`) makes prefix stability
//! CONDITIONAL on `ClosedExtension` + `ChainExtends` (CM Prop. 3 leader-safety —
//! imported from the paper, owed a Lean proof), and the node cannot discharge
//! `ChainExtends` locally: `finalLeaderAt` is non-monotone where CM's
//! `final_leader` is, so a live equivocating leader can still RETRACT an anchored
//! wave and shorten τ. So the cursor must not depend on it: this module tracks executed
//! blocks **by identity** (`BlockId` = blake3 of signed content; one id per
//! `(creator, seq)` by the verified insert's equivocation exclusion) and each
//! poll executes exactly the finalized blocks **not yet executed, in the CURRENT
//! tau order** — execution is a set difference, order is the current tau. A
//! mid-prefix insertion then simply shows up as a new pending block: it executes
//! late, exactly once, and nothing already executed is re-served. This matches
//! the corrected theorem's shape instead of assuming its hypothesis.
//!
//! The prefix-shift event itself is surfaced as OBSERVABILITY (not correctness):
//! [`ExecutionCursor::observe_order`] diffs the previously computed order
//! against the new one so operators see reorgs happen (loud log +
//! `dregg_tau_prefix_shifts_total`). (The Lean-side runtime mirror this once
//! cited, `stableCheck`, was deleted as never-called; the observability signal
//! is this module's own.)
//!
//! # Memory & durability (honest accounting)
//!
//! The executed set grows with history — but the node already holds the ENTIRE
//! lace in RAM (`BlocklaceHandle::lace` keeps every block), so the cursor adds
//! 32 bytes per block to an already-O(history) resident structure; it is
//! strictly dominated. Durably, the set rides the EXISTING machinery: the
//! turn-carrying half is recovered exactly from the durable commit log (each
//! [`dregg_persist::CommitRecord`] carries its `block_id`, written atomically
//! with the applied turn — no lost turn, no double-apply), and the non-turn half
//! (membership/checkpoint/ack — idempotent on re-process, per the commit-log
//! contract) is persisted at the existing batch cadence alongside
//! `BlocklaceMeta` (`PersistentStore::persist_executed_block_ids`).

use std::collections::HashSet;

use dregg_blocklace::finality::BlockId;

/// Typed result of applying one consensus-finalized actionable block.
///
/// Only the first two variants carry durable terminal authority and may move
/// [`ExecutionCursor`].  Operational failure and integrity failure deliberately
/// retain the identity as pending; the finality executor stops the current tau
/// prefix at that identity instead of applying a successor through a hole.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FinalizedExecutionOutcome {
    Committed {
        block_id: BlockId,
        durable_ordinal: u64,
        /// The `receipt_stream_root` of the attested root this commit wrote —
        /// `merkle_root_of_receipt_hashes` over the receipts this block's turn
        /// produced.
        ///
        /// ⚑ It rides on the OUTCOME rather than being re-read from the store at
        /// the vote site, because the finalization vote must bind exactly the
        /// value THIS commit attested. A store re-read is a second derivation of
        /// the same quantity, and two derivations of a value a committee must
        /// agree on byte-for-byte is how a quorum silently stops forming.
        receipt_stream_root: Option<[u8; 32]>,
    },
    DeterministicallyRejected {
        block_id: BlockId,
        reason_code: String,
    },
    RetryableOperational {
        block_id: BlockId,
        error: String,
    },
    FatalIntegrity {
        block_id: BlockId,
        error: String,
    },
}

impl FinalizedExecutionOutcome {
    pub const fn block_id(&self) -> BlockId {
        match self {
            Self::Committed { block_id, .. }
            | Self::DeterministicallyRejected { block_id, .. }
            | Self::RetryableOperational { block_id, .. }
            | Self::FatalIntegrity { block_id, .. } => *block_id,
        }
    }

    pub const fn is_durable_terminal(&self) -> bool {
        matches!(
            self,
            Self::Committed { .. } | Self::DeterministicallyRejected { .. }
        )
    }
}

/// Identity-tracking cursor: which finalized blocks has this node already
/// served to the executor, by block id (NOT by position in the tau order).
#[derive(Debug, Default)]
pub struct ExecutionCursor {
    /// Identity set of served blocks.
    executed: HashSet<BlockId>,
    /// The same ids in first-served order (for persistence/diagnostics).
    served: Vec<BlockId>,
    /// The finalized order computed at the previous poll — the baseline for the
    /// prefix-shift observability signal (`observe_order`).
    last_order: Vec<BlockId>,
    /// How many times the computed order failed to extend the previous one
    /// (each is a live occurrence of the TauPrefixMonotone counterexample shape).
    prefix_shifts: u64,
}

impl ExecutionCursor {
    pub fn new() -> Self {
        Self::default()
    }

    /// Rebuild a cursor from a restored identity set (recovery path: durable
    /// commit-log block ids ∪ batch-cadence persisted ids).
    pub fn restore(ids: Vec<BlockId>) -> Self {
        let mut cur = Self::default();
        for id in ids {
            cur.mark_executed(id);
        }
        cur
    }

    /// Number of distinct finalized blocks served so far. (Feeds the checkpoint
    /// cadence and the legacy `executed_up_to` diagnostic count.)
    pub fn executed_count(&self) -> usize {
        self.served.len()
    }

    /// The served ids in first-served order (persisted at batch cadence).
    pub fn executed_ids(&self) -> &[BlockId] {
        &self.served
    }

    pub fn is_executed(&self, id: &BlockId) -> bool {
        self.executed.contains(id)
    }

    /// Mark a block as served. Returns `false` if it was already marked.
    pub fn mark_executed(&mut self, id: BlockId) -> bool {
        if self.executed.insert(id) {
            self.served.push(id);
            true
        } else {
            false
        }
    }

    /// Acknowledge an actionable identity only after its executor returned a
    /// durable terminal fact.  Returning `false` for retry/fatal outcomes makes
    /// premature acknowledgement structurally explicit at the caller.
    pub fn acknowledge_terminal(&mut self, outcome: &FinalizedExecutionOutcome) -> bool {
        if outcome.is_durable_terminal() {
            self.mark_executed(outcome.block_id())
        } else {
            false
        }
    }

    /// The finalized blocks not yet executed, **in the current tau order**.
    ///
    /// This is the load-bearing mechanism: a set difference walked in the
    /// CURRENT order, immune to mid-prefix insertion (TauPrefixMonotone).
    pub fn pending(&self, ordered: &[BlockId]) -> Vec<BlockId> {
        // Identity tracking (the load-bearing fix this module exists for): the
        // finalized blocks not yet executed, walked in the CURRENT tau order.
        // A bare `ordered[served.len()..]` index slice is UNSOUND under the
        // TauPrefixMonotone counterexample (a mid-prefix insertion shifts the
        // already-executed region, causing re-execution of a block past the
        // cursor AND skipping a finalized block that fell behind it). Walking a
        // set difference by id is immune: a late mid-prefix block surfaces as a
        // fresh pending entry (executes once, late), and nothing in `executed`
        // is ever re-served.
        ordered
            .iter()
            .filter(|id| !self.executed.contains(id))
            .copied()
            .collect()
    }

    /// Observability (the prefix-shift signal, conclusion-level): record the
    /// newly computed finalized order and report whether the previously
    /// computed one is still a prefix of it. `false` = the finalized region
    /// shifted under us — e.g. an equivocating leader retracting an anchored
    /// wave (the `ChainExtends` failure mode still live post-`d182d10fc`). The identity
    /// cursor ABSORBS the shift correctly; this only makes it visible.
    pub fn observe_order(&mut self, ordered: &[BlockId]) -> bool {
        let stable = ordered.len() >= self.last_order.len()
            && ordered[..self.last_order.len()] == self.last_order[..];
        if !stable {
            self.prefix_shifts += 1;
        }
        self.last_order = ordered.to_vec();
        stable
    }

    /// How many prefix shifts this cursor has observed since boot.
    pub fn prefix_shifts(&self) -> u64 {
        self.prefix_shifts
    }
}

// ─────────────────────────────────────────────────────────────────────────────
#[cfg(test)]
mod tests {
    use super::*;
    use dregg_blocklace::ordering::tau;
    use dregg_blocklace::{Block as OBlock, Blocklace as OBlocklace};

    fn key(i: u8) -> [u8; 32] {
        [i; 32]
    }

    /// ⚠ STALE FIXTURE — encodes the PRE-`d182d10fc` coverage-τ, which no longer
    /// exists. This was the TauPrefixMonotone §4 counterexample (`lagBase →
    /// lagGrown`) ported block-for-block to the then-deployed `ordering::tau`:
    /// validator 4 lags, catches up, and its late ratifier GREW the wave's
    /// coverage so late blocks sorted into the executed region. Against the
    /// landed CM Def. 6 τ (segments = the anchor's OWN closure) the same trace
    /// is PREFIX-STABLE — the Lean retains it inverted as the positive exhibit —
    /// and this helper's mid-prefix search cannot succeed (a 3-round lace now
    /// emits exactly the anchor), so the five tests consuming it need a RE-ARM
    /// against the new rule (e.g. the still-real `ChainExtends` failure: an
    /// equivocating leader's late leader-slot block retracting an anchored wave).
    ///
    /// Returns `(base_order, grown_order, id41, id42)` as finality-layer ids
    /// (the coordinate `poll_finalized_blocks` cursors over).
    ///
    /// OPEN-CM-XSORT note: the Lean model tie-breaks concurrent blocks by
    /// abstract id; Rust `xsort` tie-breaks by blake3 block id. The mid-prefix
    /// landing is a property of the tie-break CLASS (the late round-2 block
    /// sorts with/before round-3 blocks), realized here by searching for a
    /// payload byte whose hash exhibits it — the damage is payload-independent,
    /// the search only de-correlates the test from blake3's arbitrary order.
    fn lag_trace_orders() -> (Vec<BlockId>, Vec<BlockId>, BlockId, BlockId) {
        let participants: Vec<[u8; 32]> = (1..=4).map(key).collect();

        // lagBase: rounds 1–3 without validator 4's rounds 2–3.
        let genesis: Vec<OBlock> = (1..=4)
            .map(|i| OBlock::new(key(i), 0, vec![], vec![1, i]))
            .collect();
        let gids: Vec<[u8; 32]> = genesis.iter().map(|b| b.id()).collect();
        let r2: Vec<OBlock> = (1..=3)
            .map(|i| OBlock::new(key(i), 1, gids.clone(), vec![2, i]))
            .collect();
        let r2ids: Vec<[u8; 32]> = r2.iter().map(|b| b.id()).collect();
        let r3: Vec<OBlock> = (1..=3)
            .map(|i| OBlock::new(key(i), 2, r2ids.clone(), vec![3, i]))
            .collect();

        let mut base = OBlocklace::new();
        for b in genesis.iter().chain(&r2).chain(&r3) {
            base.insert_unverified(b.clone()).expect("causal order");
        }
        let base_order: Vec<[u8; 32]> = tau(&base, &participants);

        // lagGrown: validator 4 catches up — 41 (round 2) + 42 (round 3,
        // ratifying leader 10 via preds [11,21,31,41]). Search the payload byte
        // so 41's blake3 id lands MID-PREFIX under xsort's id tie-break (the
        // Lean counterexample's shape; see OPEN-CM-XSORT note above).
        for payload_byte in 0..=255u8 {
            let b41 = OBlock::new(key(4), 1, gids.clone(), vec![2, 4, payload_byte]);
            let id41 = b41.id();
            let mut preds42 = r2ids.clone();
            preds42.push(id41);
            let b42 = OBlock::new(key(4), 2, preds42, vec![3, 4]);
            let id42 = b42.id();

            let mut grown = OBlocklace::new();
            for b in genesis.iter().chain(&r2).chain(&r3) {
                grown.insert_unverified(b.clone()).expect("causal order");
            }
            grown.insert_unverified(b41).expect("causal order");
            grown.insert_unverified(b42).expect("causal order");
            let grown_order: Vec<[u8; 32]> = tau(&grown, &participants);

            let pos41 = grown_order.iter().position(|id| *id == id41);
            if let Some(pos41) = pos41 {
                if pos41 < base_order.len() {
                    // Mid-prefix landing realized — the counterexample trace.
                    let wrap = |v: Vec<[u8; 32]>| v.into_iter().map(BlockId).collect();
                    return (
                        wrap(base_order),
                        wrap(grown_order),
                        BlockId(id41),
                        BlockId(id42),
                    );
                }
            }
        }
        panic!("no payload byte realized the mid-prefix landing (xsort tie-break changed?)");
    }

    /// PIN — the Lean counterexample reproduces against the REAL Rust `tau`:
    /// both laces finalize wave 0, the old order is NOT a prefix of the new,
    /// and index slicing would (a) re-serve an already-executed block and
    /// (b) drop the finalized honest catch-up block forever. Mirrors the
    /// `#guard` teeth of `TauPrefixMonotone.lean` §4 at the node's coordinate.
    #[test]
    fn lean_lag_counterexample_reproduces_in_rust_tau() {
        let (base, grown, id41, _id42) = lag_trace_orders();

        // Same finalization shape as the Lean trace: 10 then 12 blocks.
        assert_eq!(base.len(), 10, "lagBase finalizes all 10 blocks");
        assert_eq!(grown.len(), 12, "lagGrown finalizes all 12 blocks");
        // Growth is conservative on membership: nothing finalized is lost…
        assert!(base.iter().all(|id| grown.contains(id)));
        // …but the old order is NOT a prefix of the new (T5 unconditional REFUTED).
        assert!(
            !grown.starts_with(&base),
            "old finalized order must not be a prefix (the counterexample)"
        );
        // The catch-up block landed inside the already-executed region.
        let pos41 = grown.iter().position(|id| *id == id41).unwrap();
        assert!(pos41 < base.len(), "41 lands mid-prefix (got {pos41})");

        // NODE DAMAGE under index slicing (the deployed pre-fix logic):
        // slice = ordered[executed_up_to..] with executed_up_to = base.len().
        let slice = &grown[base.len()..];
        assert!(
            slice.iter().any(|id| base.contains(id)),
            "index slice RE-SERVES an already-executed block"
        );
        assert!(
            !slice.contains(&id41),
            "index slice NEVER serves the finalized honest catch-up block 41"
        );
    }

    /// THE FIX — identity tracking executes every finalized block exactly once,
    /// in the current tau order, across the catch-up reorg. (This test FAILS
    /// against the index-slicing cursor: it re-executes one block and skips 41.)
    #[test]
    fn identity_cursor_executes_each_finalized_block_exactly_once_across_catchup_reorg() {
        let (base, grown, id41, id42) = lag_trace_orders();

        let mut cursor = ExecutionCursor::new();

        // Poll 1: wave 0 finalized without validator 4's rounds 2–3.
        let batch1 = cursor.pending(&base);
        assert_eq!(
            batch1, base,
            "fresh cursor serves the whole finalized order"
        );
        for id in &batch1 {
            cursor.mark_executed(*id);
        }

        // Poll 2: validator 4 caught up; the finalized order grew MID-PREFIX.
        let batch2 = cursor.pending(&grown);

        // (a) NO RE-EXECUTION: nothing already executed is served again.
        for id in &batch2 {
            assert!(
                !batch1.contains(id),
                "block {id:?} re-served after the catch-up reorg (re-execution)"
            );
        }
        // (b) NO SKIP: across both polls, every finalized block executes
        // exactly once — in particular the mid-prefix catch-up block 41.
        let mut all: Vec<BlockId> = batch1.iter().chain(&batch2).copied().collect();
        all.sort();
        let mut want = grown.clone();
        want.sort();
        assert_eq!(
            all, want,
            "the two polls together must execute EXACTLY the finalized set, once each"
        );
        assert!(
            batch2.contains(&id41),
            "the skipped-forever block 41 executes"
        );
        assert!(
            batch2.contains(&id42),
            "the late wave-end ratifier 42 executes"
        );
        // (c) ORDER: the batch is served in the CURRENT tau order.
        let positions: Vec<usize> = batch2
            .iter()
            .map(|id| grown.iter().position(|x| x == id).unwrap())
            .collect();
        assert!(
            positions.windows(2).all(|w| w[0] < w[1]),
            "pending batch follows the current tau order"
        );
    }

    /// ⚑ **TWO HONEST NODES APPLY THE SAME FINALIZED SET IN DIFFERENT ORDERS.**
    ///
    /// The test above pins what the identity cursor DOES guarantee across a
    /// catch-up reorg — every finalized block executes exactly once — and it
    /// compares the union of the two batches as a SORTED SET. That is the
    /// blindness this test removes.
    ///
    /// `pending` serves "the finalized blocks not yet executed, in the CURRENT
    /// tau order". Which blocks are "not yet executed" is a function of WHEN
    /// this node polled, which is local wall-clock, not consensus. So on the
    /// counterexample growth two honest nodes running identical code over the
    /// identical final lace produce different APPLICATION SEQUENCES:
    ///
    /// * the node that polled BEFORE validator 4 caught up executes the base
    ///   order, then the late blocks — so `41` lands at the END;
    /// * the node that first polled AFTER the catch-up executes `grown` in one
    ///   batch — so `41` lands MID-PREFIX, where tau puts it.
    ///
    /// Both are "correct" by exactly-once. They are not the same sequence, and
    /// `blocklace_sync`'s post-finalization predicates are order-sensitive: the
    /// agent-scoped receipt-continuity check compares a turn's
    /// `previous_receipt_hash` against `cclerk.agent_receipt_head_hash(agent)`,
    /// a value that is a pure function of the order in which that agent's turns
    /// were applied. Two same-agent turns straddling the shift therefore get
    /// OPPOSITE `receipt-chain-mismatch` verdicts on the two nodes — a
    /// consensus-level disagreement about what the ledger contains, reached
    /// without any equivocation, any Byzantine validator, or any un-verified
    /// ordering twin. `ordering::tau` is a pure function of the lace here; both
    /// nodes ran the SAME order function on the SAME lace.
    ///
    /// This is the boundary `TauPrefixMonotone.lean` names. Its
    /// `tau_executed_prefix_fixed` — "the executed region is bit-identical" —
    /// holds under `ClosedExtension` + `ChainExtends`, and the trace below WAS a
    /// witness that the (pre-`d182d10fc`) hypothesis failed. The identity
    /// cursor's answer to that failure preserves LIVENESS (exactly-once) and
    /// abandons the ORDER AGREEMENT the theorem was supplying. The node cannot
    /// discharge `ChainExtends` locally; `observe_order` only counts a shift
    /// and logs it.
    #[test]
    fn two_honest_nodes_that_polled_at_different_times_apply_a_different_sequence() {
        let (base, grown, id41, _id42) = lag_trace_orders();

        // NODE L (lagged behind validator 4's catch-up): polled at `base`, then
        // again at `grown`.
        let mut lagged = ExecutionCursor::new();
        let mut seq_lagged: Vec<BlockId> = Vec::new();
        for id in lagged.pending(&base) {
            lagged.mark_executed(id);
            seq_lagged.push(id);
        }
        for id in lagged.pending(&grown) {
            lagged.mark_executed(id);
            seq_lagged.push(id);
        }

        // NODE P (its first poll already saw the catch-up): one batch at `grown`.
        let mut prompt = ExecutionCursor::new();
        let mut seq_prompt: Vec<BlockId> = Vec::new();
        for id in prompt.pending(&grown) {
            prompt.mark_executed(id);
            seq_prompt.push(id);
        }

        // ANTI-VACUITY 1: both nodes really did execute the whole finalized set.
        let mut set_l = seq_lagged.clone();
        let mut set_p = seq_prompt.clone();
        set_l.sort();
        set_p.sort();
        let mut want = grown.clone();
        want.sort();
        assert_eq!(set_l, want, "node L executed exactly the finalized set");
        assert_eq!(set_p, want, "node P executed exactly the finalized set");
        assert!(!want.is_empty(), "the finalized set must be non-empty");

        // ANTI-VACUITY 2: node P's sequence IS the current tau order, so the
        // disagreement below is not two arbitrary permutations — one of them is
        // the order the verified rule actually names.
        assert_eq!(
            seq_prompt, grown,
            "node P applies the current tau order verbatim"
        );

        // THE DIVERGENCE: same set, same code, same lace — different sequence.
        assert_ne!(
            seq_lagged, seq_prompt,
            "the two honest nodes must be shown to APPLY A DIFFERENT SEQUENCE; if this \
             passes, the order-agreement hazard has been closed and this test should be \
             re-read, not deleted"
        );

        // Name the inversion concretely, so a future reader sees the mechanism
        // and not just an inequality: there is a pair whose relative order flips.
        let pos = |seq: &[BlockId], id: &BlockId| seq.iter().position(|x| x == id).unwrap();
        let inverted: Vec<(BlockId, BlockId)> = grown
            .iter()
            .flat_map(|a| grown.iter().map(move |b| (*a, *b)))
            .filter(|(a, b)| a != b)
            .filter(|(a, b)| {
                (pos(&seq_lagged, a) < pos(&seq_lagged, b))
                    != (pos(&seq_prompt, a) < pos(&seq_prompt, b))
            })
            .collect();
        assert!(
            !inverted.is_empty(),
            "a sequence difference must exhibit at least one inverted pair"
        );
        // The catch-up block is in one of them: node P applies it mid-prefix,
        // node L applies it after everything the base order already covered.
        assert!(
            inverted.iter().any(|(a, b)| *a == id41 || *b == id41),
            "the catch-up block 41 must be one side of an inverted pair"
        );
        assert!(
            pos(&seq_lagged, &id41) >= base.len(),
            "node L applies 41 AFTER the whole base order"
        );
        assert!(
            pos(&seq_prompt, &id41) < base.len(),
            "node P applies 41 INSIDE the region node L had already executed"
        );
    }

    /// The prefix-shift observability signal: a pure extension is stable; the
    /// catch-up reorg trips the signal exactly once and is absorbed.
    #[test]
    fn prefix_shift_signal_fires_on_catchup_reorg_only() {
        let (base, grown, _id41, id42) = lag_trace_orders();

        // Stable growth: extending the order at the END does not trip it.
        let mut cursor = ExecutionCursor::new();
        assert!(cursor.observe_order(&base), "first observation is stable");
        let mut extended = base.clone();
        extended.push(id42);
        assert!(
            cursor.observe_order(&extended),
            "append-only growth is stable"
        );
        assert_eq!(cursor.prefix_shifts(), 0);

        // The counterexample growth: NOT a prefix → the signal fires.
        let mut cursor = ExecutionCursor::new();
        assert!(cursor.observe_order(&base));
        assert!(
            !cursor.observe_order(&grown),
            "catch-up reorg must trip the prefix-shift signal"
        );
        assert_eq!(cursor.prefix_shifts(), 1);
        // …and is absorbed: the new order is the baseline thereafter.
        assert!(cursor.observe_order(&grown));
        assert_eq!(cursor.prefix_shifts(), 1);
    }

    /// Recovery: a cursor rebuilt from its persisted identity set resumes with
    /// exactly the not-yet-executed blocks pending — across the reorg.
    #[test]
    fn restored_cursor_resumes_by_identity() {
        let (base, grown, id41, id42) = lag_trace_orders();

        let mut cursor = ExecutionCursor::new();
        for id in &base {
            cursor.mark_executed(*id);
        }
        let restored = ExecutionCursor::restore(cursor.executed_ids().to_vec());
        assert_eq!(restored.executed_count(), base.len());

        let pending = restored.pending(&grown);
        let in_order = |a: &BlockId, b: &BlockId| {
            grown.iter().position(|x| x == a).unwrap() < grown.iter().position(|x| x == b).unwrap()
        };
        assert_eq!(pending.len(), 2);
        assert!(pending.contains(&id41) && pending.contains(&id42));
        assert!(in_order(&pending[0], &pending[1]));
    }

    /// `mark_executed` is idempotent by identity; the count is of DISTINCT blocks.
    #[test]
    fn mark_executed_is_idempotent() {
        let id = BlockId([7u8; 32]);
        let mut cursor = ExecutionCursor::new();
        assert!(cursor.mark_executed(id));
        assert!(!cursor.mark_executed(id));
        assert_eq!(cursor.executed_count(), 1);
        assert_eq!(cursor.executed_ids(), &[id]);
        assert!(cursor.is_executed(&id));
    }

    #[test]
    fn only_durable_terminal_outcomes_advance_the_cursor() {
        let committed = FinalizedExecutionOutcome::Committed {
            block_id: BlockId([1; 32]),
            durable_ordinal: 7,
            receipt_stream_root: Some([0x3D; 32]),
        };
        let rejected = FinalizedExecutionOutcome::DeterministicallyRejected {
            block_id: BlockId([2; 32]),
            reason_code: "bad-signature".into(),
        };
        let retry = FinalizedExecutionOutcome::RetryableOperational {
            block_id: BlockId([3; 32]),
            error: "store unavailable".into(),
        };
        let fatal = FinalizedExecutionOutcome::FatalIntegrity {
            block_id: BlockId([4; 32]),
            error: "conflicting durable row".into(),
        };

        let mut cursor = ExecutionCursor::new();
        assert!(cursor.acknowledge_terminal(&committed));
        assert!(cursor.acknowledge_terminal(&rejected));
        assert!(!cursor.acknowledge_terminal(&retry));
        assert!(!cursor.acknowledge_terminal(&fatal));
        assert_eq!(cursor.executed_ids(), &[BlockId([1; 32]), BlockId([2; 32])]);
        assert_eq!(
            cursor.pending(&[
                BlockId([1; 32]),
                BlockId([2; 32]),
                BlockId([3; 32]),
                BlockId([4; 32])
            ]),
            vec![BlockId([3; 32]), BlockId([4; 32])]
        );
    }
}
