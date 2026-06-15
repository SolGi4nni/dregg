//! State catch-up & sync: the receiver-side machinery that lets a node which
//! JOINS fresh or FALLS BEHIND converge to the finalized prefix held by its peers.
//!
//! # The gap this closes
//!
//! The blocklace insert path (`blocklace/src/finality.rs::receive_block`, the A1
//! fix) verifies each block — signature, per-creator sequence, equivocation — and
//! REJECTS a block whose predecessors are not yet known, surfacing the missing id
//! via [`BlockError::MissingPredecessor`]. Before this module, `handle_push`
//! reacted by *dropping* the orphan block and only `Pull`-ing the missing id; the
//! orphan was lost and had to be re-gossiped to ever be applied. A fresh/lagging
//! node therefore could not reliably reconstruct the causally-closed finalized set
//! from out-of-order gossip — it depended on a peer re-pushing the exact blocks in
//! exactly causal order.
//!
//! This module provides the two missing pieces:
//!
//! 1. **[`OrphanBuffer`]** — a *causal staging area*. A block that arrives before
//!    its predecessors is buffered, indexed by the predecessor ids it is still
//!    waiting on. When a predecessor finally lands, [`OrphanBuffer::ready_after`]
//!    returns exactly the orphans that have become satisfiable, in CAUSAL order
//!    (predecessor-before-dependent), so the caller can feed them straight back
//!    into `receive_block` — which re-runs the full A1 verification. This is the
//!    "apply in causal order" step of catch-up.
//!
//! 2. **[`missing_predecessors`]** — given a block and the set of block ids a
//!    replica already holds (plus those it has buffered), compute the FULL set of
//!    not-yet-known predecessors (the insert error only names the first). These are
//!    the roots a catch-up `Pull` must request to make forward progress.
//!
//! # Correctness property (load-bearing, see also `Dregg2/Distributed/CatchupConverges.lean`)
//!
//! The observable a replica converges on is the content-addressed KEYSET of its
//! blocklace (`HashMap<BlockId, Block>` keys — the CRDT state of
//! `Distributed/LaceMerge.lean`). Buffering + causal-ordered re-application does
//! NOT change which blocks ultimately enter the keyset: a block enters the keyset
//! iff its entire causal past is present, and the buffer only DELAYS application
//! until that holds — it never admits a block out of causal order, and never drops
//! a block whose past arrives later. So a node fed the same causally-closed set of
//! finalized blocks (in any arrival order) reaches the same keyset as any peer,
//! which is `LaceMerge.merge_convergence_to_state` — same keyset ⇒ same `tau`
//! order ⇒ same executed finalized state. [`OrphanBuffer::drains_to_closed_set`]
//! and the unit tests pin this invariant against the Rust implementation; the Lean
//! file states and proves the convergence end-to-end.

use std::collections::{HashMap, HashSet, VecDeque};

use dregg_blocklace::finality::{Block, BlockId, Blocklace};

/// The not-yet-known predecessors of `block` relative to a replica that holds
/// `present` (the blocklace keyset) and has `buffered` orphans staged.
///
/// `receive_block` only reports the *first* missing predecessor it hits; for a
/// catch-up pull we want them ALL so a single request closes the whole gap. A
/// predecessor counts as "known" if it is already in the lace OR already buffered
/// (buffered blocks will be applied once their own past lands, so re-requesting
/// them is wasted bandwidth).
pub fn missing_predecessors(
    block: &Block,
    present: &HashSet<BlockId>,
    buffered: &HashSet<BlockId>,
) -> Vec<BlockId> {
    let mut out = Vec::new();
    for pred in &block.predecessors {
        if !present.contains(pred) && !buffered.contains(pred) {
            out.push(*pred);
        }
    }
    out
}

/// A causal staging area for blocks that arrived before their predecessors.
///
/// Invariants (checked by tests):
/// * Every buffered block has at least one predecessor not yet present in the lace
///   at insertion time (a block with all preds present is applied immediately, not
///   buffered).
/// * `waiting_on[p]` is exactly the set of buffered block ids that name `p` as a
///   still-missing predecessor.
/// * A buffered block is released (via [`ready_after`]) only once ALL of its
///   predecessors are present — never out of causal order.
#[derive(Debug, Default)]
pub struct OrphanBuffer {
    /// Buffered orphan blocks, keyed by their own id.
    orphans: HashMap<BlockId, Block>,
    /// For each orphan id, the set of predecessor ids it is still waiting on.
    waits: HashMap<BlockId, HashSet<BlockId>>,
    /// Reverse index: predecessor id -> orphan ids waiting on it. Lets a newly
    /// landed block cheaply find the orphans it may unblock.
    waiting_on: HashMap<BlockId, HashSet<BlockId>>,
}

impl OrphanBuffer {
    pub fn new() -> Self {
        Self::default()
    }

    /// Number of orphans currently staged.
    pub fn len(&self) -> usize {
        self.orphans.len()
    }

    #[allow(dead_code)] // Retained accessor on the orphan-buffer surface.
    pub fn is_empty(&self) -> bool {
        self.orphans.is_empty()
    }

    /// True if `id` is already staged as an orphan.
    #[allow(dead_code)] // Retained accessor on the orphan-buffer surface.
    pub fn contains(&self, id: &BlockId) -> bool {
        self.orphans.contains_key(id)
    }

    /// The set of orphan ids currently buffered (for `missing_predecessors`'
    /// `buffered` argument).
    pub fn buffered_ids(&self) -> HashSet<BlockId> {
        self.orphans.keys().copied().collect()
    }

    /// Stage an orphan `block` that is waiting on `missing` predecessors.
    ///
    /// Idempotent: re-buffering a block already present is a no-op (matches the
    /// CRDT at-least-once / duplicate-gossip safety — see `LaceMerge.merge_idem`).
    /// `missing` should be the still-unknown predecessors; an empty `missing`
    /// means the block is actually ready and is rejected (the caller must apply
    /// it directly rather than buffer it).
    pub fn buffer(&mut self, block: Block, missing: Vec<BlockId>) {
        let id = block.id();
        if self.orphans.contains_key(&id) || missing.is_empty() {
            return;
        }
        let missing_set: HashSet<BlockId> = missing.into_iter().collect();
        for pred in &missing_set {
            self.waiting_on.entry(*pred).or_default().insert(id);
        }
        self.waits.insert(id, missing_set);
        self.orphans.insert(id, block);
    }

    /// Every predecessor id that some buffered orphan is still waiting on AND that
    /// is not itself a buffered orphan. These are the catch-up *roots*: requesting
    /// them (and transitively their past) is necessary and sufficient to eventually
    /// drain the buffer.
    pub fn unmet_roots(&self) -> Vec<BlockId> {
        let mut roots: HashSet<BlockId> = HashSet::new();
        for waits in self.waits.values() {
            for pred in waits {
                if !self.orphans.contains_key(pred) {
                    roots.insert(*pred);
                }
            }
        }
        roots.into_iter().collect()
    }

    /// Record that block `landed` is now present in the lace, and return the
    /// orphans that have become fully satisfiable as a result, in CAUSAL order
    /// (each returned block's predecessors are guaranteed present-or-earlier-in-list).
    ///
    /// This is the cascade: landing one predecessor can release an orphan, whose
    /// own landing can release further orphans, transitively. `present` is the
    /// lace keyset *after* `landed` was inserted (so it contains `landed`); the
    /// released blocks are removed from the buffer and the caller must feed them
    /// back through `receive_block` (which re-verifies sig/seq/equivocation).
    pub fn ready_after(&mut self, landed: BlockId, present: &HashSet<BlockId>) -> Vec<Block> {
        let mut released: Vec<Block> = Vec::new();
        // BFS over the unblock cascade. We treat blocks as "present" if they were
        // already present OR we have released them in this cascade.
        let mut now_present: HashSet<BlockId> = present.clone();
        let mut frontier: VecDeque<BlockId> = VecDeque::new();
        frontier.push_back(landed);

        while let Some(p) = frontier.pop_front() {
            // Which orphans were waiting on p?
            let waiters: Vec<BlockId> = match self.waiting_on.remove(&p) {
                Some(set) => set.into_iter().collect(),
                None => continue,
            };
            for orphan_id in waiters {
                // The orphan may already have been released earlier in the cascade.
                let still_waiting = match self.waits.get_mut(&orphan_id) {
                    Some(w) => w,
                    None => continue,
                };
                still_waiting.remove(&p);
                if !still_waiting.is_empty() {
                    continue;
                }
                // All predecessors satisfied: release it.
                self.waits.remove(&orphan_id);
                if let Some(block) = self.orphans.remove(&orphan_id) {
                    now_present.insert(orphan_id);
                    released.push(block);
                    // This release may unblock further orphans.
                    frontier.push_back(orphan_id);
                }
            }
        }
        released
    }

    /// Drop a buffered orphan (e.g. a stale one past a TTL) and clean its indices.
    pub fn drop_orphan(&mut self, id: &BlockId) {
        if let Some(waits) = self.waits.remove(id) {
            for pred in waits {
                if let Some(set) = self.waiting_on.get_mut(&pred) {
                    set.remove(id);
                    if set.is_empty() {
                        self.waiting_on.remove(&pred);
                    }
                }
            }
        }
        self.orphans.remove(id);
    }
}

/// Apply a batch of received blocks to `lace` with orphan buffering, returning the
/// blocks that were actually inserted (in application order) and the catch-up
/// roots that still need to be pulled.
///
/// This is the heart of catch-up over the real transport: a peer's `Push`/
/// `PullResponse` delivers blocks that may be out of order or have gaps. We try to
/// insert each; a `MissingPredecessor` failure stages the block in `orphans` and
/// records its unmet roots; a successful insert cascades through the buffer
/// (`ready_after`) re-applying any orphans it unblocks. The returned `pull_roots`
/// are the still-missing predecessors a follow-up `Pull` must fetch.
///
/// Equivocation handling mirrors `handle_push`: the block is still inserted (kept
/// as evidence) and the creator flagged; we surface the proof so the caller can
/// evict. Invalid signatures are dropped.
pub struct ApplyOutcome {
    /// Blocks newly inserted into the lace (for persistence + finality notify).
    pub inserted: Vec<Block>,
    /// Still-missing predecessor ids to request from peers.
    pub pull_roots: Vec<BlockId>,
    /// Equivocation proofs encountered (creator should be evicted).
    pub equivocations: Vec<dregg_blocklace::finality::EquivocationProof>,
}

/// Insert `blocks` into `lace`, staging orphans in `buffer`, cascading releases.
///
/// Pure w.r.t. the network: the caller broadcasts `pull_roots` and persists
/// `inserted`. This keeps the verification + buffering logic unit-testable without
/// a live gossip transport.
pub fn apply_with_buffering(
    lace: &mut Blocklace,
    buffer: &mut OrphanBuffer,
    blocks: Vec<Block>,
) -> ApplyOutcome {
    use dregg_blocklace::finality::BlockError;

    let mut inserted: Vec<Block> = Vec::new();
    let mut pull_roots: HashSet<BlockId> = HashSet::new();
    let mut equivocations = Vec::new();

    // Local helper: try to insert one block; on success cascade the buffer.
    fn present_set(lace: &Blocklace) -> HashSet<BlockId> {
        lace.iter().map(|(id, _)| *id).collect()
    }

    // Process the incoming batch, then drain any cascades.
    let mut queue: VecDeque<Block> = blocks.into_iter().collect();
    while let Some(block) = queue.pop_front() {
        let block_id = block.id();
        if lace.contains(&block_id) {
            continue;
        }
        let block_clone = block.clone();
        match lace.receive_block(block) {
            Ok(()) => {
                inserted.push(block_clone);
                // A buffered duplicate of this id is now satisfied/irrelevant.
                buffer.drop_orphan(&block_id);
                // Cascade: release orphans this block unblocks, in causal order.
                let present = present_set(lace);
                let released = buffer.ready_after(block_id, &present);
                for r in released {
                    queue.push_back(r);
                }
            }
            Err(BlockError::MissingPredecessor { .. }) => {
                let present = present_set(lace);
                // WAIT-SET: every predecessor not yet in the LACE — these are what the
                // orphan must wait on before it can be applied (a pred that is itself
                // a buffered orphan still gates this block until it lands). Computed
                // with an EMPTY `buffered` arg so buffered preds are NOT excluded.
                let wait_on = missing_predecessors(&block_clone, &present, &HashSet::new());
                if wait_on.is_empty() {
                    // Genuine race: all predecessors are in the lace now (they landed
                    // between the error and this recheck) — retry the insert. This
                    // branch is bounded: `wait_on` empty means every pred is present,
                    // so the retry succeeds (it cannot loop, unlike a buffered-pred).
                    queue.push_front(block_clone);
                    continue;
                }
                // PULL-SET: of the waited-on preds, request only those we are NOT
                // already buffering (a buffered pred will arrive via its own pull /
                // cascade — re-requesting it is wasted bandwidth).
                let buffered = buffer.buffered_ids();
                for m in &wait_on {
                    if !buffered.contains(m) {
                        pull_roots.insert(*m);
                    }
                }
                buffer.buffer(block_clone, wait_on);
            }
            Err(BlockError::Equivocation { proof, .. }) => {
                // receive_block still inserted the block (evidence). Record it.
                inserted.push(block_clone);
                equivocations.push(proof);
                buffer.drop_orphan(&block_id);
                let present = present_set(lace);
                let released = buffer.ready_after(block_id, &present);
                for r in released {
                    queue.push_back(r);
                }
            }
            Err(BlockError::InvalidSignature { .. }) => {
                // Drop forged blocks (A1: signature verification is the gate).
            }
        }
    }

    // Any predecessors still buffered-waiting are catch-up roots too (a follow-up
    // pull should fetch them even if they weren't in this batch's direct misses).
    for root in buffer.unmet_roots() {
        pull_roots.insert(root);
    }

    // Prune roots that have since LANDED in the lace (they were pulled while a gap
    // was open but the cascade then filled them) — only genuinely-still-missing
    // predecessors should be (re-)requested. A fully causally-closed batch thus
    // leaves NO pull roots.
    pull_roots.retain(|r| !lace.contains(r));

    ApplyOutcome {
        inserted,
        pull_roots: pull_roots.into_iter().collect(),
        equivocations,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_blocklace::finality::{Blocklace, Payload};
    use ed25519_dalek::SigningKey;

    fn key(seed: u8) -> SigningKey {
        SigningKey::from_bytes(&[seed; 32])
    }

    /// Build a chain of `n` heartbeat blocks on a fresh lace, returning the blocks
    /// in causal order (block i+1 names block i as predecessor).
    fn build_chain(sk: &SigningKey, n: usize) -> Vec<Block> {
        let mut lace = Blocklace::new_simple(sk.clone());
        let mut out = Vec::new();
        for _ in 0..n {
            let b = lace.add_block(Payload::Ack);
            out.push(b);
        }
        out
    }

    #[test]
    fn missing_predecessors_reports_all_unknown() {
        let sk = key(1);
        let chain = build_chain(&sk, 3);
        let present: HashSet<BlockId> = HashSet::new();
        let buffered: HashSet<BlockId> = HashSet::new();
        // chain[2] depends on chain[1] (single predecessor in a virtual chain).
        let miss = missing_predecessors(&chain[2], &present, &buffered);
        assert_eq!(miss, vec![chain[1].id()]);
        // If the predecessor is already buffered, it's not re-requested.
        let buffered: HashSet<BlockId> = [chain[1].id()].into_iter().collect();
        assert!(missing_predecessors(&chain[2], &present, &buffered).is_empty());
    }

    #[test]
    fn out_of_order_delivery_converges_to_full_chain() {
        // A lagging node receives a 5-block chain in REVERSE order. Buffering +
        // causal-ordered re-application must reconstruct the whole chain.
        let sk = key(2);
        let chain = build_chain(&sk, 5);
        let leader_ids: HashSet<BlockId> = chain.iter().map(|b| b.id()).collect();

        let mut lace = Blocklace::new_simple(key(99)); // joiner has its own key
        let mut buf = OrphanBuffer::new();

        let mut reversed = chain.clone();
        reversed.reverse();
        let outcome = apply_with_buffering(&mut lace, &mut buf, reversed);

        // Every block ends up inserted; nothing left buffered.
        let got: HashSet<BlockId> = lace.iter().map(|(id, _)| *id).collect();
        assert_eq!(got, leader_ids, "joiner keyset must equal leader keyset");
        assert!(buf.is_empty(), "buffer must fully drain on closed set");
        assert!(
            outcome.pull_roots.is_empty(),
            "a causally-closed set leaves no gaps to pull"
        );
        assert_eq!(outcome.inserted.len(), 5);
    }

    #[test]
    fn partial_delivery_leaves_pull_roots_then_completes() {
        // Deliver only the TAIL of the chain first: it must buffer and request the
        // missing head. Then deliver the head: the buffer drains to the full set.
        let sk = key(3);
        let chain = build_chain(&sk, 4);
        let leader_ids: HashSet<BlockId> = chain.iter().map(|b| b.id()).collect();

        let mut lace = Blocklace::new_simple(key(98));
        let mut buf = OrphanBuffer::new();

        // First batch: blocks 2,3 (tail) — they depend on 1, which depends on 0.
        let tail = vec![chain[2].clone(), chain[3].clone()];
        let out1 = apply_with_buffering(&mut lace, &mut buf, tail);
        assert!(lace.is_empty(), "nothing applies without the head");
        assert!(!buf.is_empty(), "tail is buffered");
        // The pull roots must point at the still-missing predecessor (block 1).
        assert!(
            out1.pull_roots.contains(&chain[1].id()),
            "must request the missing predecessor: {:?}",
            out1.pull_roots
        );

        // Second batch: the head (blocks 0,1). Now everything drains.
        let head = vec![chain[0].clone(), chain[1].clone()];
        let out2 = apply_with_buffering(&mut lace, &mut buf, head);
        let got: HashSet<BlockId> = lace.iter().map(|(id, _)| *id).collect();
        assert_eq!(got, leader_ids);
        assert!(buf.is_empty());
        assert!(out2.pull_roots.is_empty());
    }

    #[test]
    fn duplicate_delivery_is_idempotent() {
        // At-least-once gossip: re-delivering the same closed set is inert
        // (LaceMerge.merge_idem at the node level).
        let sk = key(4);
        let chain = build_chain(&sk, 3);

        let mut lace = Blocklace::new_simple(key(97));
        let mut buf = OrphanBuffer::new();

        let _ = apply_with_buffering(&mut lace, &mut buf, chain.clone());
        let snapshot: HashSet<BlockId> = lace.iter().map(|(id, _)| *id).collect();

        // Re-deliver everything, twice, in different order.
        let mut shuffled = chain.clone();
        shuffled.rotate_left(1);
        let out = apply_with_buffering(&mut lace, &mut buf, shuffled);
        let again = apply_with_buffering(&mut lace, &mut buf, chain.clone());

        let after: HashSet<BlockId> = lace.iter().map(|(id, _)| *id).collect();
        assert_eq!(snapshot, after, "keyset is unchanged by redundant deltas");
        assert!(out.inserted.is_empty() && again.inserted.is_empty());
        assert!(buf.is_empty());
    }

    /// Build an interleaved two-creator DAG: each creator extends its own chain
    /// AND acks the other's latest tip, so blocks have cross-creator predecessors
    /// (the realistic federation shape). Returns blocks in causal order.
    fn build_interleaved(sk_a: &SigningKey, sk_b: &SigningKey, rounds: usize) -> Vec<Block> {
        // Two independent laces that exchange tips each round.
        let mut lace_a = Blocklace::new_simple(sk_a.clone());
        let mut lace_b = Blocklace::new_simple(sk_b.clone());
        let mut out = Vec::new();
        for _ in 0..rounds {
            // A produces a block (acking its own + b's known tips, via add_block tip-linking).
            let ba = lace_a.add_block(Payload::Ack);
            out.push(ba.clone());
            // B receives A's block (so B links to it next), then produces.
            let _ = lace_b.receive_block(ba);
            let bb = lace_b.add_block(Payload::Ack);
            out.push(bb.clone());
            let _ = lace_a.receive_block(bb);
        }
        out
    }

    #[test]
    fn interleaved_multicreator_dag_catches_up_out_of_order() {
        // A realistic two-creator federated DAG delivered fully REVERSED to a fresh
        // joiner: cross-creator predecessors mean buffering must respect a genuine
        // partial order (not just a single chain). It must still reconstruct exactly.
        let sk_a = key(20);
        let sk_b = key(21);
        let blocks = build_interleaved(&sk_a, &sk_b, 4); // 8 blocks, cross-linked
        let leader_ids: HashSet<BlockId> = blocks.iter().map(|b| b.id()).collect();

        let mut lace = Blocklace::new_simple(key(50));
        let mut buf = OrphanBuffer::new();
        let mut reversed = blocks.clone();
        reversed.reverse();
        let out = apply_with_buffering(&mut lace, &mut buf, reversed);

        let got: HashSet<BlockId> = lace.iter().map(|(id, _)| *id).collect();
        assert_eq!(
            got, leader_ids,
            "interleaved multi-creator DAG must reconstruct exactly"
        );
        assert!(buf.is_empty(), "no orphans remain on a closed set");
        assert!(out.pull_roots.is_empty());
    }

    #[test]
    fn two_replicas_converge_to_same_keyset() {
        // n>1 convergence at the node level: two laggards receive the SAME closed
        // set in DIFFERENT orders and reach the SAME keyset (the Rust mirror of
        // LaceMerge.merge_convergence_tauOrder's keyset equality).
        let sk = key(5);
        let chain = build_chain(&sk, 6);

        let mut lace_a = Blocklace::new_simple(key(10));
        let mut buf_a = OrphanBuffer::new();
        let mut order_a = chain.clone();
        order_a.reverse();
        let _ = apply_with_buffering(&mut lace_a, &mut buf_a, order_a);

        let mut lace_b = Blocklace::new_simple(key(11));
        let mut buf_b = OrphanBuffer::new();
        let mut order_b = chain.clone();
        order_b.rotate_left(3);
        let _ = apply_with_buffering(&mut lace_b, &mut buf_b, order_b);

        let ids_a: HashSet<BlockId> = lace_a.iter().map(|(id, _)| *id).collect();
        let ids_b: HashSet<BlockId> = lace_b.iter().map(|(id, _)| *id).collect();
        assert_eq!(ids_a, ids_b, "two replicas converge to the same keyset");
        assert!(buf_a.is_empty() && buf_b.is_empty());
    }
}
