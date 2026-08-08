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

    /// The honest-laggard trace, at the depth CM's τ actually reaches.
    ///
    /// This WAS the exhibit for the pre-`d182d10fc` coverage-τ: validator 4
    /// lagged, caught up, and its late wave-end ratifier GREW an already-final
    /// wave's coverage so the catch-up blocks sorted into the already-executed
    /// region. That τ is gone. Under CM Def. 6 a segment is the anchor's OWN
    /// closure — fixed by the anchor's signed pointers — so the same trace is
    /// prefix-stable, and the fixture is kept INVERTED as the invariant's
    /// witness rather than deleted.
    ///
    /// Three orders, because prefix-stability over a one-block order proves
    /// nothing:
    ///
    /// * `base`  — rounds 1–6. Validator 4 publishes genesis, then LAGS through
    ///   rounds 2–3. Wave 0 anchors on validator 1's genesis; wave 1 anchors on
    ///   validator 2's round-4 block, whose closure is the whole of rounds 1–3.
    /// * `grown` — `base` plus validator 4's catch-up blocks `41` (round 2) and
    ///   `42` (round 3, ratifying wave 0's leader). They arrive AFTER wave 1 was
    ///   sealed, so no anchor observes them yet.
    /// * `later` — `grown` plus rounds 7–9, whose wave-2 leader DOES observe the
    ///   catch-up. This is where `41`/`42` get ordered: at the END, after
    ///   everything already emitted, which is exactly CM's claim.
    ///
    /// No search over payload bytes. The old fixture brute-forced a byte until
    /// `41`'s blake3 id landed mid-prefix under `xsort`'s id tie-break; that
    /// landing is now unreachable by construction, so a search for it would
    /// panic. Nothing here depends on the tie-break.
    fn lag_trace_orders() -> (Vec<BlockId>, Vec<BlockId>, Vec<BlockId>, BlockId, BlockId) {
        let participants: Vec<[u8; 32]> = (1..=4).map(key).collect();
        let ids = |v: &[OBlock]| -> Vec<[u8; 32]> { v.iter().map(|b| b.id()).collect() };

        // Rounds 1–3: validator 4 publishes genesis, then lags.
        let genesis: Vec<OBlock> = (1..=4)
            .map(|i| OBlock::new(key(i), 0, vec![], vec![1, i]))
            .collect();
        let gids = ids(&genesis);
        let r2: Vec<OBlock> = (1..=3)
            .map(|i| OBlock::new(key(i), 1, gids.clone(), vec![2, i]))
            .collect();
        let r2ids = ids(&r2);
        let r3: Vec<OBlock> = (1..=3)
            .map(|i| OBlock::new(key(i), 2, r2ids.clone(), vec![3, i]))
            .collect();
        let r3ids = ids(&r3);
        // Rounds 4–6 complete wave 1, whose leader anchors rounds 1–3.
        let r4: Vec<OBlock> = (1..=3)
            .map(|i| OBlock::new(key(i), 3, r3ids.clone(), vec![4, i]))
            .collect();
        let r4ids = ids(&r4);
        let r5: Vec<OBlock> = (1..=3)
            .map(|i| OBlock::new(key(i), 4, r4ids.clone(), vec![5, i]))
            .collect();
        let r5ids = ids(&r5);
        let r6: Vec<OBlock> = (1..=3)
            .map(|i| OBlock::new(key(i), 5, r5ids.clone(), vec![6, i]))
            .collect();
        let r6ids = ids(&r6);

        let seed = |lace: &mut OBlocklace| {
            for b in genesis
                .iter()
                .chain(&r2)
                .chain(&r3)
                .chain(&r4)
                .chain(&r5)
                .chain(&r6)
            {
                lace.insert_unverified(b.clone()).expect("causal order");
            }
        };

        let mut base_lace = OBlocklace::new();
        seed(&mut base_lace);
        let base_order: Vec<[u8; 32]> = tau(&base_lace, &participants);

        // Validator 4 catches up. `42` sits at wave 0's END round and ratifies
        // wave 0's leader — the premise of the OLD refutation is still true; it
        // simply no longer decides what any anchor orders.
        let b41 = OBlock::new(key(4), 1, gids.clone(), vec![2, 4]);
        let id41 = b41.id();
        let mut preds42 = r2ids.clone();
        preds42.push(id41);
        let b42 = OBlock::new(key(4), 2, preds42, vec![3, 4]);
        let id42 = b42.id();

        let mut grown_lace = OBlocklace::new();
        seed(&mut grown_lace);
        grown_lace
            .insert_unverified(b41.clone())
            .expect("causal order");
        grown_lace
            .insert_unverified(b42.clone())
            .expect("causal order");
        let grown_order: Vec<[u8; 32]> = tau(&grown_lace, &participants);

        // Rounds 7–9: wave 2, whose leader observes the catch-up (round 7 acks
        // round 6 AND `42`).
        let mut r7preds = r6ids.clone();
        r7preds.push(id42);
        let r7: Vec<OBlock> = (1..=3)
            .map(|i| OBlock::new(key(i), 6, r7preds.clone(), vec![7, i]))
            .collect();
        let r7ids = ids(&r7);
        let r8: Vec<OBlock> = (1..=3)
            .map(|i| OBlock::new(key(i), 7, r7ids.clone(), vec![8, i]))
            .collect();
        let r8ids = ids(&r8);
        let r9: Vec<OBlock> = (1..=3)
            .map(|i| OBlock::new(key(i), 8, r8ids.clone(), vec![9, i]))
            .collect();

        let mut later_lace = OBlocklace::new();
        seed(&mut later_lace);
        later_lace.insert_unverified(b41).expect("causal order");
        later_lace.insert_unverified(b42).expect("causal order");
        for b in r7.iter().chain(&r8).chain(&r9) {
            later_lace
                .insert_unverified(b.clone())
                .expect("causal order");
        }
        let later_order: Vec<[u8; 32]> = tau(&later_lace, &participants);

        let wrap = |v: Vec<[u8; 32]>| -> Vec<BlockId> { v.into_iter().map(BlockId).collect() };
        (
            wrap(base_order),
            wrap(grown_order),
            wrap(later_order),
            BlockId(id41),
            BlockId(id42),
        )
    }

    /// THE INVARIANT (was the counterexample). Against the real Rust `tau`, the
    /// honest catch-up changes NOTHING already emitted, and the catch-up blocks
    /// are ordered later, at the END — never inside the executed region.
    ///
    /// The mechanism is pinned, not just the conclusion: `grown == base`
    /// EXACTLY (not merely a prefix), because the wave-1 anchor's closure is a
    /// function of its own signed pointers and the late blocks are not in it.
    /// That is the node-side mirror of `TauPrefixMonotone.lean` §8's
    /// `causalPastIncl lagBase 10 == causalPastIncl lagGrown 10`.
    #[test]
    fn lean_lag_trace_is_prefix_stable_in_rust_tau() {
        let (base, grown, later, id41, id42) = lag_trace_orders();

        // NON-VACUITY FIRST: a prefix claim over an empty or one-block order is
        // worth nothing. Wave 0 emits its anchor; wave 1 emits rounds 1–3.
        assert!(
            base.len() >= 10,
            "base order must be substantial, got {}",
            base.len()
        );
        assert!(later.len() > grown.len(), "the third poll must order more");

        // THE MECHANISM: the anchor's closure did not move, so the order is not
        // merely prefix-stable — it is IDENTICAL.
        assert_eq!(
            grown, base,
            "the honest catch-up must change nothing already emitted"
        );
        // The catch-up blocks are not ordered YET…
        assert!(!grown.contains(&id41) && !grown.contains(&id42));
        // …and they are not lost: a later anchor that OBSERVES them orders them.
        assert!(later.starts_with(&grown), "history must only extend");
        assert!(later.contains(&id41) && later.contains(&id42));
        let pos41 = later.iter().position(|id| *id == id41).unwrap();
        let pos42 = later.iter().position(|id| *id == id42).unwrap();
        assert!(
            pos41 >= grown.len() && pos42 >= grown.len(),
            "catch-up blocks land AFTER the already-emitted region (41 at {pos41}, 42 at {pos42})"
        );

        // …so index slicing would now be sound at this trace: the tail contains
        // nothing already executed. (The cursor stays identity-based anyway —
        // `ChainExtends` is unproved; see the module header.)
        let tail = &later[grown.len()..];
        assert!(
            !tail.iter().any(|id| grown.contains(id)),
            "the tail must re-serve nothing"
        );
    }

    /// Identity tracking executes every finalized block exactly once across the
    /// catch-up, and the catch-up poll is a no-op because nothing changed.
    #[test]
    fn identity_cursor_executes_each_finalized_block_exactly_once_across_catchup() {
        let (base, grown, later, id41, id42) = lag_trace_orders();

        let mut cursor = ExecutionCursor::new();
        let mut applied: Vec<BlockId> = Vec::new();

        for id in cursor.pending(&base) {
            cursor.mark_executed(id);
            applied.push(id);
        }
        assert_eq!(applied, base, "fresh cursor serves the whole order");

        // Poll 2: validator 4 caught up — and there is nothing new to do.
        assert!(
            cursor.pending(&grown).is_empty(),
            "the catch-up poll must serve nothing: the order did not change"
        );

        // Poll 3: a later anchor observes the catch-up; the tail is served.
        for id in cursor.pending(&later) {
            cursor.mark_executed(id);
            applied.push(id);
        }
        assert_eq!(applied, later, "the applied sequence IS the tau order");
        assert!(applied.contains(&id41) && applied.contains(&id42));

        // Exactly once, by identity.
        let mut seen = std::collections::HashSet::new();
        assert!(
            applied.iter().all(|id| seen.insert(*id)),
            "no block executed twice"
        );
        assert_eq!(cursor.executed_count(), later.len());
    }

    /// THE ORDER-AGREEMENT INVARIANT (was
    /// `..._apply_a_different_sequence`). Two honest nodes that polled at
    /// different times apply the SAME sequence.
    ///
    /// The old test asserted the opposite and was correct about the old τ: with
    /// segments drawn from live-lace ratifier coverage, `pending` is a set
    /// difference, so WHICH blocks are outstanding depended on local poll
    /// timing and the two nodes applied the same set in different orders — a
    /// consensus-level disagreement reached with no Byzantine validator. Under
    /// CM Def. 6 the order is append-only across these polls, so "not yet
    /// executed" is a SUFFIX regardless of when you polled, and the set-difference
    /// cursor and an index cursor coincide.
    ///
    /// ⚠ This does NOT say the node is now safe in general. It is a statement
    /// about growth that is a CLOSED EXTENSION with a non-retracting head.
    /// `ChainExtends` (CM Prop. 3) is still unproved, and `finalLeaderAt` can
    /// still retract an anchored wave when a leader equivocates — that case is
    /// NOT exhibited here and is owed a test.
    #[test]
    fn two_honest_nodes_that_polled_at_different_times_apply_the_same_sequence() {
        let (base, grown, later, id41, _id42) = lag_trace_orders();

        // NODE L: polled early, then across the catch-up, then again.
        let mut lagged = ExecutionCursor::new();
        let mut seq_lagged: Vec<BlockId> = Vec::new();
        for order in [&base, &grown, &later] {
            for id in lagged.pending(order) {
                lagged.mark_executed(id);
                seq_lagged.push(id);
            }
        }

        // NODE P: its first poll already saw everything.
        let mut prompt = ExecutionCursor::new();
        let mut seq_prompt: Vec<BlockId> = Vec::new();
        for id in prompt.pending(&later) {
            prompt.mark_executed(id);
            seq_prompt.push(id);
        }

        // Non-vacuity: both sequences are substantial and contain the block the
        // old fork turned on.
        assert!(seq_prompt.len() >= 10, "sequence must be substantial");
        assert!(seq_lagged.contains(&id41) && seq_prompt.contains(&id41));

        assert_eq!(
            seq_lagged, seq_prompt,
            "two honest nodes must apply the SAME sequence"
        );

        // …and stated the way the old test stated its refutation, so the two are
        // directly comparable: there is NO inverted pair.
        let pos = |seq: &[BlockId], id: &BlockId| seq.iter().position(|x| x == id).unwrap();
        let inverted: Vec<(BlockId, BlockId)> = later
            .iter()
            .flat_map(|a| later.iter().map(move |b| (*a, *b)))
            .filter(|(a, b)| a != b)
            .filter(|(a, b)| {
                (pos(&seq_lagged, a) < pos(&seq_lagged, b))
                    != (pos(&seq_prompt, a) < pos(&seq_prompt, b))
            })
            .collect();
        assert!(
            inverted.is_empty(),
            "no pair may flip between the two nodes, found {}",
            inverted.len()
        );
    }

    /// The prefix-shift observability signal. The catch-up no longer trips it —
    /// but the signal must still be capable of firing, so the red half is kept
    /// on a SYNTHETIC non-prefix order rather than deleted.
    #[test]
    fn prefix_shift_signal_is_quiet_on_catchup_and_still_able_to_fire() {
        let (base, grown, later, _id41, _id42) = lag_trace_orders();

        // The real trace: three polls, no shift.
        let mut cursor = ExecutionCursor::new();
        assert!(cursor.observe_order(&base), "first observation is stable");
        assert!(
            cursor.observe_order(&grown),
            "the catch-up no longer reorders finalized history"
        );
        assert!(cursor.observe_order(&later), "append-only growth is stable");
        assert_eq!(cursor.prefix_shifts(), 0);

        // THE RED HALF. `observe_order` is a pure function of two id vectors, so
        // a hand-built permutation proves the detector still detects — WITHOUT
        // claiming tau can produce it. A signal that cannot go red is not a
        // signal; a signal whose red case is asserted of tau would be a lie.
        let mut swapped = later.clone();
        assert!(swapped.len() >= 2);
        swapped.swap(0, 1);
        let mut cursor = ExecutionCursor::new();
        assert!(cursor.observe_order(&later));
        assert!(
            !cursor.observe_order(&swapped),
            "a genuine reorder must trip the signal"
        );
        assert_eq!(cursor.prefix_shifts(), 1);
        // …and is absorbed: the new order is the baseline thereafter.
        assert!(cursor.observe_order(&swapped));
        assert_eq!(cursor.prefix_shifts(), 1);
    }

    /// Recovery: a cursor rebuilt from its persisted identity set resumes with
    /// exactly the not-yet-executed blocks pending, in tau order.
    #[test]
    fn restored_cursor_resumes_by_identity() {
        let (base, _grown, later, id41, id42) = lag_trace_orders();

        let mut cursor = ExecutionCursor::new();
        for id in &base {
            cursor.mark_executed(*id);
        }
        let restored = ExecutionCursor::restore(cursor.executed_ids().to_vec());
        assert_eq!(restored.executed_count(), base.len());

        let pending = restored.pending(&later);
        assert_eq!(
            pending.len(),
            later.len() - base.len(),
            "pending is exactly the un-executed tail"
        );
        assert!(!pending.is_empty(), "non-vacuity: there IS a tail");
        assert!(pending.contains(&id41) && pending.contains(&id42));
        // …and it is served in tau order.
        let posn = |id: &BlockId| later.iter().position(|x| x == id).unwrap();
        assert!(
            pending.windows(2).all(|w| posn(&w[0]) < posn(&w[1])),
            "pending must be served in tau order"
        );
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
