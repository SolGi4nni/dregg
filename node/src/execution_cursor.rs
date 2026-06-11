//! Identity-tracking execution cursor over the tau-finalized block order.
//!
//! # Why this exists (the TauPrefixMonotone soundness finding)
//!
//! `blocklace_sync::poll_finalized_blocks` used to keep a bare INDEX
//! (`executed_up_to`) into the finalized order computed by `ordering::tau` and
//! slice `ordered[executed_up_to..]` each poll. That is sound **iff** the
//! already-executed prefix of the order is bit-identical across polls — and the
//! machine-checked theorem `metatheory/Dregg2/Consensus/TauPrefixMonotone.lean`
//! REFUTES that unconditionally: an honest lagging validator that catches up can
//! emit a wave-end block ratifying an ALREADY-FINAL leader, growing that wave's
//! coverage, and the late blocks sort into the MIDDLE of the already-executed
//! region (`lagBase → lagGrown`, `#guard`-pinned: insert-valid, equivocation-free,
//! yet the old order is not a prefix of the new). Under index slicing the node
//! then (a) RE-EXECUTES a block past the cursor and (b) NEVER executes a
//! finalized honest block that fell behind the cursor. No Byzantine step needed;
//! any n>1 deployment can hit it.
//!
//! # The closure (this module)
//!
//! The corrected theorem (`tau_finalized_prefix_monotone`) shows prefix stability
//! is a CONDITIONAL property (`FinalizedRegionStable`) the node cannot discharge
//! locally. So the cursor must not depend on it: this module tracks executed
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
//! against the new one — the executable conclusion-level mirror of the Lean
//! `stableCheck` (the theorem header names "diffed the recomputed prefix against
//! the executed one" as exactly this check) — so operators see
//! reorgs-by-catchup happen (loud log + `dregg_tau_prefix_shifts_total`).
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

    /// Observability (the `stableCheck` signal, conclusion-level): record the
    /// newly computed finalized order and report whether the previously
    /// computed one is still a prefix of it. `false` = the finalized region
    /// shifted under us — the Lean counterexample happening live. The identity
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

    /// The TauPrefixMonotone §4 counterexample (`lagBase → lagGrown`), ported
    /// block-for-block to the REAL Rust `ordering::tau` (default wavelength 3):
    /// 4 validators (supermajority 3); validator 4 publishes genesis then LAGS;
    /// validators 1–3 complete rounds 2–3 and wave 0 finalizes all 10 blocks;
    /// THEN validator 4 catches up with its round-2 block ("41") and a round-3
    /// block ("42") that RATIFIES the already-final wave-0 leader — growing the
    /// wave's coverage so the late blocks sort into the executed region.
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

    /// The stableCheck observability signal: a pure extension is stable; the
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
}
