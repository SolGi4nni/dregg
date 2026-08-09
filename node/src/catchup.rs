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
//!    into `receive_block_pinned` — which re-runs the full A1 verification plus
//!    the hybrid PQ pin. This is the "apply in causal order" step of catch-up.
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

use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
use std::time::{Duration, Instant};

use dregg_blocklace::finality::{Block, BlockId, Blocklace};

/// THEME-2 #4 RESOURCE BOUND — maximum orphans a node will stage at once.
///
/// A Byzantine committee member can sign blocks citing arbitrarily many
/// never-landing predecessors; without a cap the [`OrphanBuffer`] grows without
/// bound (and each staged orphan feeds the catch-up Pull fan-out). This cap is
/// deliberately GENEROUS: honest out-of-order gossip during a real catch-up
/// stages far fewer than this (the buffer is a transient causal-reorder window,
/// not a backlog), so the cap only ever bites under an adversarial flood. When
/// the buffer is full a NEW orphan evicts the OLDEST one (drop-oldest), and a
/// dropped orphan is not lost to the system: it is re-pullable (its id reappears
/// as a peer frontier tip / is re-gossiped at-least-once), so a legit block whose
/// predecessor is merely slow still finalizes once its past lands — the cap only
/// discards the STALEST staged block, which under load is the one least likely to
/// still be resolvable.
pub const MAX_ORPHANS: usize = 4096;

/// THEME-2 #4 — how long a staged orphan may wait for its predecessors before it
/// is swept as stale. A legit predecessor that is merely slow arrives well within
/// this window; past it, the orphan is almost certainly citing a predecessor that
/// will never land (an attack, or a block whose producer is gone), and a genuine
/// straggler is re-pullable. Swept opportunistically on each apply batch.
pub const ORPHAN_TTL: Duration = Duration::from_secs(120);

/// THEME-2 #4 — hard cap on the number of catch-up Pull roots a single apply
/// batch will emit, bounding the network amplification an orphan flood can
/// trigger. A causally-closed batch emits ZERO roots and a genuine gap needs only
/// a handful (bounded by the honest DAG width), so this generous cap never bites a
/// legit catch-up; it only truncates an adversarial fan-out. Truncation is
/// liveness-safe: any root not requested this batch is re-derived from the still
/// buffered orphans on the next batch ([`OrphanBuffer::unmet_roots`]).
pub const MAX_PULL_ROOTS: usize = 8192;

/// Cap on blocks held awaiting acknowledgment (the BC §5.3 buffer — see
/// [`OrphanBuffer::hold_for_ack`]). Same drop-oldest discipline as [`MAX_ORPHANS`]:
/// a dropped held block is re-pullable and will be re-evaluated on re-arrival, so
/// the cap bounds an adversarial flood without ever permanently losing an honest
/// block. This cap is also the per-batch factor of the finite-harm bound: an
/// admitted batch is `⌊head⌋ ∩ D`, so no single license can admit more than the
/// buffer holds.
pub const MAX_ACK_HELD: usize = 4096;

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
    /// THEME-2 #4 age bookkeeping. `order` maps a strictly-increasing insertion
    /// sequence to the orphan staged at that moment (ascending seq == ascending
    /// insertion time), so the OLDEST staged orphan is `order.first_key_value()`
    /// — the drop-oldest eviction and TTL sweep victim. `inserted_at` is the
    /// reverse index: orphan id -> (its seq, the wall-clock instant it was
    /// staged). Both are maintained in lockstep with `orphans` (an orphan enters
    /// and leaves all three together), so neither can outgrow the buffer.
    order: BTreeMap<u64, BlockId>,
    inserted_at: HashMap<BlockId, (u64, Instant)>,
    /// Monotonic insertion counter feeding `order` keys.
    next_seq: u64,
    /// THE ACKNOWLEDGE-BEFORE-ADMIT HOLD (blocklace paper §5.3; the verified rule
    /// is `Dregg2.Distributed.AckBeforeAdmit`, consulted via `dregg_ack_admit`).
    /// Blocks whose predecessors are present (or satisfiable in-box) but which the
    /// verified gate refuses to admit — a known equivocator's continued stream, or
    /// a peer's blocks that do not yet acknowledge a known fork. Distinct from
    /// `orphans`: an orphan waits on MISSING HISTORY and is drained by arrivals; an
    /// ack-held block waits on an ACKNOWLEDGING HEAD and is drained by a license.
    /// Same cap/TTL discipline (`MAX_ACK_HELD` / [`Self::sweep_expired_ack`]).
    ack_held: HashMap<BlockId, Block>,
    /// Age bookkeeping for `ack_held`, mirroring `order`/`inserted_at`.
    ack_age: BTreeMap<u64, BlockId>,
    ack_at: HashMap<BlockId, (u64, Instant)>,
}

impl OrphanBuffer {
    pub fn new() -> Self {
        Self::default()
    }

    /// Number of orphans currently staged.
    pub fn len(&self) -> usize {
        self.orphans.len()
    }

    pub fn is_empty(&self) -> bool {
        self.orphans.is_empty()
    }

    /// True if `id` is already staged as an orphan.
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
        // THEME-2 #4: drop-OLDEST when at capacity, so a Byzantine flood of
        // orphans citing never-landing predecessors stays bounded at
        // `MAX_ORPHANS`. The victim is the STALEST staged orphan (smallest
        // insertion seq); a legit-but-slow child is the FRESHEST and is never the
        // victim, and any dropped orphan is re-pullable, so this preserves
        // liveness for honest late blocks while capping the adversary.
        while self.orphans.len() >= MAX_ORPHANS {
            let Some((_, oldest)) = self.order.iter().next().map(|(s, id)| (*s, *id)) else {
                break;
            };
            self.drop_orphan(&oldest);
        }
        let missing_set: HashSet<BlockId> = missing.into_iter().collect();
        for pred in &missing_set {
            self.waiting_on.entry(*pred).or_default().insert(id);
        }
        self.waits.insert(id, missing_set);
        self.orphans.insert(id, block);
        let seq = self.next_seq;
        self.next_seq += 1;
        self.order.insert(seq, id);
        self.inserted_at.insert(id, (seq, Instant::now()));
    }

    /// Remove an orphan's age bookkeeping (`order` + `inserted_at`). Called from
    /// every path that removes an orphan so the two age indices never outgrow
    /// `orphans`.
    fn forget_age(&mut self, id: &BlockId) {
        if let Some((seq, _)) = self.inserted_at.remove(id) {
            self.order.remove(&seq);
        }
    }

    /// THEME-2 #4 — sweep orphans that have waited longer than `ttl` for their
    /// predecessors. Returns the ids dropped (for metrics/logging). Because
    /// `order` is ascending by insertion time, the sweep stops at the first
    /// not-yet-expired orphan. A swept orphan is re-pullable, so this never
    /// permanently loses a block whose past simply arrives late.
    pub fn sweep_expired(&mut self, ttl: Duration) -> Vec<BlockId> {
        let now = Instant::now();
        let mut expired: Vec<BlockId> = Vec::new();
        for (_, id) in self.order.iter() {
            match self.inserted_at.get(id) {
                Some((_, at)) if now.duration_since(*at) >= ttl => expired.push(*id),
                // `order` is time-ordered: the first fresh orphan ends the sweep.
                _ => break,
            }
        }
        for id in &expired {
            self.drop_orphan(id);
        }
        expired
    }

    /// Every predecessor id that some buffered orphan is still waiting on AND that
    /// is not itself a buffered orphan. These are the catch-up *roots*: requesting
    /// them (and transitively their past) is necessary and sufficient to eventually
    /// drain the buffer.
    pub fn unmet_roots(&self) -> Vec<BlockId> {
        let mut roots: HashSet<BlockId> = HashSet::new();
        for waits in self.waits.values() {
            for pred in waits {
                // An ack-HELD pred is on-box (waiting on a license, not on the
                // network) — pulling it again is pure waste.
                if !self.orphans.contains_key(pred) && !self.ack_held.contains_key(pred) {
                    roots.insert(*pred);
                }
            }
        }
        roots.into_iter().collect()
    }

    /// Stage `block` in the acknowledge-before-admit hold (BC §5.3): its
    /// predecessors are satisfiable but the verified gate refused admission (no
    /// first-evidence license, no acknowledging head yet). Idempotent. Drop-oldest
    /// at [`MAX_ACK_HELD`]; a dropped block is re-pullable and re-evaluated on
    /// re-arrival.
    pub fn hold_for_ack(&mut self, block: Block) {
        let id = block.id();
        if self.ack_held.contains_key(&id) {
            return;
        }
        while self.ack_held.len() >= MAX_ACK_HELD {
            let Some((_, oldest)) = self.ack_age.iter().next().map(|(s, id)| (*s, *id)) else {
                break;
            };
            self.drop_ack_held(&oldest);
        }
        let seq = self.next_seq;
        self.next_seq += 1;
        self.ack_age.insert(seq, id);
        self.ack_at.insert(id, (seq, Instant::now()));
        self.ack_held.insert(id, block);
    }

    /// True if `id` is currently held awaiting acknowledgment.
    pub fn is_ack_held(&self, id: &BlockId) -> bool {
        self.ack_held.contains_key(id)
    }

    pub fn ack_held_is_empty(&self) -> bool {
        self.ack_held.is_empty()
    }

    /// Number of blocks currently held awaiting acknowledgment.
    pub fn ack_held_len(&self) -> usize {
        self.ack_held.len()
    }

    /// Clones of the ack-held blocks (the `D` the verified gate evaluates over,
    /// together with the orphans and the arriving candidate).
    pub fn ack_held_blocks(&self) -> Vec<Block> {
        self.ack_held.values().cloned().collect()
    }

    /// Clones of the orphan-buffered blocks (they complete `D`: a licensing head
    /// may sit in the orphan buffer waiting on an ack-held predecessor).
    pub fn orphan_blocks(&self) -> Vec<Block> {
        self.orphans.values().cloned().collect()
    }

    /// Remove a block from the ack hold (admitted under a license, or landed via
    /// another path).
    pub fn drop_ack_held(&mut self, id: &BlockId) {
        if let Some((seq, _)) = self.ack_at.remove(id) {
            self.ack_age.remove(&seq);
        }
        self.ack_held.remove(id);
    }

    /// Drain the whole ack hold (the retry epoch: fresh inserts may have changed
    /// the evidence, so every held block gets re-offered to the gate once).
    pub fn take_all_ack_held(&mut self) -> Vec<Block> {
        let out: Vec<Block> = self.ack_held.values().cloned().collect();
        self.ack_held.clear();
        self.ack_age.clear();
        self.ack_at.clear();
        out
    }

    /// Orphans whose ENTIRE wait-set is in-box (ack-held or itself orphaned, per
    /// `in_box`): these are gate HEAD candidates — their batch closure is
    /// satisfiable from the buffers, so only a license separates them from the
    /// lace. The retry epoch re-offers them (a licensing head that arrived BEFORE
    /// its backlog sits here, and nothing else would ever re-consult it).
    pub fn closable_orphan_ids(&self, in_box: &HashSet<BlockId>) -> Vec<BlockId> {
        self.waits
            .iter()
            .filter(|(_, waits)| waits.iter().all(|w| in_box.contains(w)))
            .map(|(id, _)| *id)
            .collect()
    }

    /// TTL sweep for the ack hold, mirroring [`Self::sweep_expired`]. A swept
    /// block is re-pullable; a colluder-fed stream therefore occupies at most
    /// `MAX_ACK_HELD` slots for at most `ttl` each — memory stays bounded no
    /// matter how long the colluder feeds.
    pub fn sweep_expired_ack(&mut self, ttl: Duration) -> Vec<BlockId> {
        let now = Instant::now();
        let mut expired: Vec<BlockId> = Vec::new();
        for (_, id) in self.ack_age.iter() {
            match self.ack_at.get(id) {
                Some((_, at)) if now.duration_since(*at) >= ttl => expired.push(*id),
                _ => break,
            }
        }
        for id in &expired {
            self.drop_ack_held(id);
        }
        expired
    }

    /// Record that block `landed` is now present in the lace, and return the
    /// orphans that have become fully satisfiable as a result, in CAUSAL order
    /// (each returned block's predecessors are guaranteed present-or-earlier-in-list).
    ///
    /// This is the cascade: landing one predecessor can release an orphan, whose
    /// own landing can release further orphans, transitively. The released blocks
    /// are removed from the buffer and the caller must feed them back through
    /// `receive_block_pinned` (which re-verifies sig/seq/equivocation + the
    /// hybrid PQ pin). The cascade is
    /// driven purely by the wait-set bookkeeping (`waits` / `waiting_on`), so it
    /// needs no snapshot of the lace keyset.
    pub fn ready_after(&mut self, landed: BlockId) -> Vec<Block> {
        let mut released: Vec<Block> = Vec::new();
        // BFS over the unblock cascade.
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
                    self.forget_age(&orphan_id);
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
        self.forget_age(id);
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
    /// Blocks HELD by the verified acknowledge-before-admit gate (BC §5.3): their
    /// predecessors were satisfiable but no license (first evidence / acknowledging
    /// head) admitted them. They stay in [`OrphanBuffer`]'s ack hold and are
    /// re-offered when new evidence lands; a colluder-fed stream sits here forever
    /// (bounded by `MAX_ACK_HELD` + TTL) — which IS the finite-harm bound working.
    pub held_for_ack: Vec<BlockId>,
    /// Blocks REFUSED on a deterministic policy/signature ground and dropped
    /// permanently — `(block_id, reason)`. These are neither inserted nor buffered
    /// nor re-pulled, which at `supermajority_threshold(n) == n` (n ≤ 3) halts the
    /// committee forever, so the caller MUST surface them rather than let them
    /// vanish. Empty on a healthy ingest.
    pub refused: Vec<(BlockId, String)>,
}

/// First four bytes of a 32-byte id, hex — enough to correlate a refusal with the
/// producing node's own log line without dumping the whole hash.
fn hex4(bytes: &[u8; 32]) -> String {
    bytes[..4].iter().map(|b| format!("{b:02x}")).collect()
}

// =============================================================================
// The acknowledge-before-admit gate (BC §5.3) — Lean decides, Rust marshals.
// =============================================================================
//
// THE SUBSTRATE, SAID OUT LOUD: the admission RULE is authored in Lean
// (`metatheory/Dregg2/Distributed/AckBeforeAdmit.lean`, `@[export] dregg_ack_admit`,
// verdict proved equal to the verified `admitBatch` by `ack_admit_eq_gate`). This
// Rust code only (a) encodes the query wire, (b) calls the exported artifact, and
// (c) applies the verdict. Nothing here evaluates an admission clause.
//
// ⚠ ENCODER NOTE. This encoder interns `(lace ∪ D)` — the finality gate's
// `build_wire` cannot be reused as-is because (1) it interns lace blocks only (the
// gate needs the buffered set `D` and the head on the wire) and (2) it FILTERS
// absent predecessors, which would vacuously satisfy the Lean closure check; here
// an unresolved pred id is interned WITHOUT a block so the Lean `batchClosed`
// genuinely fails on it. Grammar and BLOCKW encoding are byte-compatible with
// `FinalityGate`'s (`AckBeforeAdmit.encodeAckWire` mirrors this). When
// `finality_gate.rs` is free of live lanes, fold this into `build_wire` behind an
// extra-blocks parameter so there is one lace encoder again.

/// The verified gate's verdict on a head candidate.
enum AckVerdict {
    /// Admit exactly these blocks (the head's licensed batch), in insertion order.
    Admit(Vec<Block>),
    /// Hold: no license. Fail-closed.
    Hold,
    /// The gate could not answer (archive without the export, wire error). The
    /// caller FAILS CLOSED — absence never admits.
    Unavailable(String),
}

/// Encode the `(head, D, lace)` query for `dregg_ack_admit` and consult the
/// verified rule. `d_blocks` must contain the head.
fn consult_ack_gate(lace: &Blocklace, d_blocks: &[Block], head: &BlockId) -> AckVerdict {
    if !dregg_lean_ffi::ack_admit_available() {
        return AckVerdict::Unavailable(
            "dregg_ack_admit not exported by the linked archive".into(),
        );
    }

    // ── Intern ids and creators over lace ∪ D (+ unresolved preds), deterministically.
    let mut lace_blocks: Vec<(&BlockId, &Block)> = lace.iter().collect();
    lace_blocks.sort_by(|(_, a), (_, b)| a.seq.cmp(&b.seq).then_with(|| a.creator.cmp(&b.creator)));
    let mut d_sorted: Vec<&Block> = d_blocks.iter().collect();
    d_sorted.sort_by(|a, b| a.seq.cmp(&b.seq).then_with(|| a.creator.cmp(&b.creator)));

    let mut id_of: HashMap<BlockId, u64> = HashMap::new();
    let mut block_of: HashMap<u64, BlockId> = HashMap::new();
    let mut next_id: u64 = 0;
    let mut intern = |id: BlockId,
                      id_of: &mut HashMap<BlockId, u64>,
                      block_of: &mut HashMap<u64, BlockId>,
                      next_id: &mut u64|
     -> u64 {
        *id_of.entry(id).or_insert_with(|| {
            let v = *next_id;
            *next_id += 1;
            block_of.insert(v, id);
            v
        })
    };
    for (id, _) in &lace_blocks {
        intern(**id, &mut id_of, &mut block_of, &mut next_id);
    }
    for b in &d_sorted {
        intern(b.id(), &mut id_of, &mut block_of, &mut next_id);
    }
    // Unresolved predecessor ids get interned WITHOUT a block: the Lean closure
    // check must be able to fail on them (never encode a vacuously-closed graph).
    let all_pred_ids: Vec<BlockId> = lace_blocks
        .iter()
        .flat_map(|(_, b)| b.predecessors.iter().copied())
        .chain(d_sorted.iter().flat_map(|b| b.predecessors.iter().copied()))
        .collect();
    for p in all_pred_ids {
        intern(p, &mut id_of, &mut block_of, &mut next_id);
    }

    let mut creator_of: HashMap<[u8; 32], u64> = HashMap::new();
    let mut next_creator: u64 = 0;
    let mut creator =
        |c: [u8; 32], creator_of: &mut HashMap<[u8; 32], u64>, next_creator: &mut u64| -> u64 {
            *creator_of.entry(c).or_insert_with(|| {
                let v = *next_creator;
                *next_creator += 1;
                v
            })
        };

    let encode_block = |b: &Block,
                        id_of: &HashMap<BlockId, u64>,
                        creator_of: &mut HashMap<[u8; 32], u64>,
                        next_creator: &mut u64|
     -> String {
        let preds: Vec<String> = b
            .predecessors
            .iter()
            .map(|p| id_of.get(p).expect("interned above").to_string())
            .collect();
        format!(
            "{}:{}:{}:{}",
            id_of.get(&b.id()).expect("interned above"),
            creator(b.creator, creator_of, next_creator),
            b.seq,
            preds.join(".")
        )
    };

    let d_wire: Vec<String> = d_sorted
        .iter()
        .map(|b| encode_block(b, &id_of, &mut creator_of, &mut next_creator))
        .collect();
    let b_wire: Vec<String> = lace_blocks
        .iter()
        .map(|(_, b)| encode_block(b, &id_of, &mut creator_of, &mut next_creator))
        .collect();
    let Some(head_id) = id_of.get(head) else {
        return AckVerdict::Unavailable("head not interned (not in D?)".into());
    };
    let wire = format!(
        "h={};D={};w=0;P=;B={}",
        head_id,
        d_wire.join("|"),
        b_wire.join("|")
    );

    // ── The verified rule decides.
    let reply = match dregg_lean_ffi::shadow_ack_admit(&wire) {
        Ok(r) => r,
        Err(e) => return AckVerdict::Unavailable(e),
    };
    if reply == "0" {
        return AckVerdict::Hold;
    }
    let Some(ids) = reply.strip_prefix("1:") else {
        // "ERR" or anything unexpected: fail closed.
        return AckVerdict::Unavailable(format!("gate replied {reply:?}"));
    };
    let mut batch: Vec<Block> = Vec::new();
    let by_id: HashMap<BlockId, &Block> = d_blocks.iter().map(|b| (b.id(), b)).collect();
    for tok in ids.split(',').filter(|t| !t.is_empty()) {
        let Ok(n) = tok.parse::<u64>() else {
            return AckVerdict::Unavailable(format!("unparseable batch id {tok:?}"));
        };
        let Some(real) = block_of.get(&n) else {
            return AckVerdict::Unavailable(format!("batch id {n} never interned"));
        };
        // The verified batch is `⌊head⌋ ∩ D` — every member is a D block.
        if let Some(b) = by_id.get(real) {
            batch.push((*b).clone());
        }
    }
    if batch.is_empty() {
        return AckVerdict::Unavailable("gate admitted an empty batch".into());
    }
    AckVerdict::Admit(batch)
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

    // THEME-2 #4: opportunistically sweep stale orphans (predecessors that never
    // landed within the TTL) on every apply batch. Cheap — stops at the first
    // still-fresh orphan — and needs no separate timer task; orphans only matter
    // while blocks are flowing, which is exactly when this runs. The ack hold is
    // swept on the same cadence.
    let _swept = buffer.sweep_expired(ORPHAN_TTL);
    let _swept_ack = buffer.sweep_expired_ack(ORPHAN_TTL);

    let mut inserted: Vec<Block> = Vec::new();
    let mut pull_roots: HashSet<BlockId> = HashSet::new();
    let mut equivocations = Vec::new();
    let mut refused: Vec<(BlockId, String)> = Vec::new();
    let mut held_for_ack: Vec<BlockId> = Vec::new();

    // The lace keyset, seeded ONCE and maintained incrementally: every accepted
    // block (Ok or Equivocation-evidence) is inserted below, so `present` always
    // equals the current lace keyset at each use — without an O(N) rescan per
    // block on the sync path.
    let mut present: HashSet<BlockId> = lace.iter().map(|(id, _)| *id).collect();

    // Blocks the verified gate has already licensed this call: they bypass the
    // gate consult (their admission IS the gate's verdict) and go straight to the
    // signature/pin arms below.
    let mut licensed: HashSet<BlockId> = HashSet::new();
    // Epoch machinery. A drained queue re-offers the gate candidates (ack-held
    // blocks + orphans whose closure is satisfiable in-box) whenever the call
    // state CHANGED since the last epoch: an insert (fresh evidence can license
    // what was refused) or a FIRST-TIME hold (a newly held block can complete the
    // in-box closure of a licensing head that arrived before its backlog — that
    // head sits in the orphan buffer and nothing else re-consults it). Re-holds of
    // already-seen ids do not set the flag, so an epoch that makes no progress is
    // the last: the loop terminates after at most (inserts + distinct holds)
    // epochs.
    //
    // ⚠ THE PARAGRAPH ABOVE DESCRIBES A MACHINE THAT IS NOT BUILT YET. `0eccd772d`
    // landed its DECLARATIONS (`epoch_dirty`, `seen_holds`) without its body: the
    // loop below still sets only the insert flag and still re-offers only the ack
    // hold, so `epoch_dirty` had no assignments and the four `retry_ack` uses had
    // no binding — `dregg-node` did not compile at that commit, for every lane in
    // the tree. This restores the name the BODY uses; it does not implement the
    // redesign. What is still missing, exactly: a FIRST-TIME hold must dirty the
    // epoch (that is what `seen_holds` is for), and an epoch must re-offer orphans
    // whose closure is satisfiable in-box, not just ack-held blocks.
    //
    // `seen_holds` is deliberately left in place, unused: its warning is the only
    // live marker that the second half is outstanding. Delete it when you build
    // the machine, not to quiet the build.
    let mut retry_ack = false;
    let mut seen_holds: HashSet<BlockId> = HashSet::new();

    // Process the incoming batch, then drain any cascades, then retry epochs.
    let mut queue: VecDeque<Block> = blocks.into_iter().collect();
    loop {
        while let Some(block) = queue.pop_front() {
            let block_id = block.id();
            if lace.contains(&block_id) {
                buffer.drop_ack_held(&block_id);
                continue;
            }

            // ── THE ACKNOWLEDGE-BEFORE-ADMIT GATE (BC §5.3; the verified rule is
            // `Dregg2.Distributed.AckBeforeAdmit.admitBatch`, called through the
            // `dregg_ack_admit` export). Consulted only in FORK CONTEXT — a known
            // equivocator or a non-empty ack hold. The fork-free fast path below
            // is the gate's own verdict by the named Lean theorems: with
            // `byzOf B = []` and a singleton batch, `no_byz_no_hold` admits every
            // clean block and `firstEvidence` admits the fork-completing one (the
            // `Equivocation` arm) — so skipping the FFI here decides nothing.
            let fork_context = !lace.equivocators().is_empty() || !buffer.ack_held_is_empty();
            if fork_context && !licensed.contains(&block_id) {
                let wait_on = missing_predecessors(&block, &present, &HashSet::new());
                let satisfiable_in_box = wait_on
                    .iter()
                    .all(|m| buffer.contains(m) || buffer.is_ack_held(m));
                if !wait_on.is_empty() && !satisfiable_in_box {
                    // Genuinely missing history: the CLOSURE gate (orphan + pull),
                    // exactly as ever — the ack gate never relaxes it.
                    let buffered = buffer.buffered_ids();
                    for m in &wait_on {
                        if !buffered.contains(m) && !buffer.is_ack_held(m) {
                            pull_roots.insert(*m);
                        }
                    }
                    buffer.buffer(block, wait_on);
                    continue;
                }
                // Closed (or closable from the buffers): the verified rule decides.
                // D = ack-held ∪ orphans ∪ {candidate}: orphans complete D because a
                // licensing head may be orphan-buffered waiting on an ack-held pred.
                let mut d_blocks: Vec<Block> = buffer.ack_held_blocks();
                d_blocks.extend(buffer.orphan_blocks());
                d_blocks.push(block.clone());
                match consult_ack_gate(lace, &d_blocks, &block_id) {
                    AckVerdict::Admit(batch) => {
                        // Feed the licensed batch through the signature/pin arms in
                        // the verified insertion order. The license does NOT bypass
                        // the pin: a forged batch member is still refused below and
                        // its dependents re-orphan.
                        for b in &batch {
                            let id = b.id();
                            licensed.insert(id);
                            buffer.drop_ack_held(&id);
                            buffer.drop_orphan(&id);
                        }
                        for b in batch.into_iter().rev() {
                            queue.push_front(b);
                        }
                        continue;
                    }
                    AckVerdict::Hold => {
                        if wait_on.is_empty() {
                            buffer.hold_for_ack(block);
                            held_for_ack.push(block_id);
                        } else {
                            // Waits on in-box (held/orphaned) preds; the cascade
                            // re-offers it if they ever land.
                            buffer.buffer(block, wait_on);
                        }
                        continue;
                    }
                    AckVerdict::Unavailable(why) => {
                        // ⚑ FAIL CLOSED, LOUDLY. Without the verified gate there is
                        // no finite-harm bound at all (READING-BLOCKLACE §0.4), so
                        // absence HOLDS the block — it never admits. Fork-free
                        // ingest (the deployed n=1 path) is unaffected.
                        tracing::warn!(
                            block = %hex4(&block_id.0),
                            creator = %hex4(&block.creator),
                            why = %why,
                            "ack-before-admit gate UNAVAILABLE in fork context — \
                             HOLDING block (fail-closed; rebuild the Lean archive \
                             to restore verified admission)"
                        );
                        if wait_on.is_empty() {
                            buffer.hold_for_ack(block);
                            held_for_ack.push(block_id);
                        } else {
                            buffer.buffer(block, wait_on);
                        }
                        continue;
                    }
                }
            }

            let block_clone = block.clone();
            // LIVE WIRE INGEST (GAP #1b): PIN each incoming consensus block's
            // post-quantum half to its creator's ENROLLED ML-DSA-65 key
            // (`receive_block_pinned`), NOT the ed25519-only `receive_block`. Fails
            // closed (`BlockError::UnenrolledCreator`) on a creator absent from the
            // roster, so a quantum adversary who forges only the classical half
            // cannot inject a block under an enrolled member's identity. The roster
            // is enrolled from the committee in `blocklace_sync::run_blocklace_sync`
            // (and re-enrolled on every committee rotation) before any ingest runs.
            match lace.receive_block_pinned(block) {
                Ok(()) => {
                    inserted.push(block_clone);
                    present.insert(block_id);
                    retry_ack = true;
                    // A buffered duplicate of this id is now satisfied/irrelevant.
                    buffer.drop_orphan(&block_id);
                    buffer.drop_ack_held(&block_id);
                    // Cascade: release orphans this block unblocks, in causal order.
                    let released = buffer.ready_after(block_id);
                    for r in released {
                        queue.push_back(r);
                    }
                }
                Err(BlockError::MissingPredecessor { .. }) => {
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
                        if !buffered.contains(m) && !buffer.is_ack_held(m) {
                            pull_roots.insert(*m);
                        }
                    }
                    buffer.buffer(block_clone, wait_on);
                }
                Err(BlockError::Equivocation { proof, .. }) => {
                    // receive_block still inserted the block (evidence — FIRST
                    // evidence on the fast path; in fork context the gate's
                    // clause-1 license got it here). Record it.
                    inserted.push(block_clone);
                    present.insert(block_id);
                    retry_ack = true;
                    equivocations.push(proof);
                    buffer.drop_orphan(&block_id);
                    buffer.drop_ack_held(&block_id);
                    let released = buffer.ready_after(block_id);
                    for r in released {
                        queue.push_back(r);
                    }
                }
                Err(other) => {
                    // Drop forged / unpinnable blocks (A1 + GAP #1b: BOTH signature
                    // halves are the gate). A bad ed25519 half, a missing/forged
                    // post-quantum half, or a creator with no enrolled ML-DSA key
                    // fails CLOSED here — never inserted, never buffered, never
                    // pulled. A quantum adversary who forges only the classical half
                    // cannot inject a block under an enrolled member's identity.
                    // Consensus-time failures are likewise deterministic invalid
                    // payload/policy observations, never missing-history retries;
                    // buffering or pulling them would turn a stable refusal into a
                    // hot operational loop.
                    //
                    // ⚑ SAY IT OUT LOUD. This arm used to be a bare `{}` — a silent,
                    // permanent, unlogged drop of a consensus block, and it is the one
                    // place on the ingest path where a block can vanish with no trace.
                    // It cost a full day of the n=3 committee-wedge investigation: with
                    // nothing emitted here, "the peer never sent it", "the wire dropped
                    // it" and "we refused it" are indistinguishable from the outside.
                    // `warn!`, not `debug!`: at n=3 a single refused block halts the
                    // committee forever, because `supermajority_threshold(3) == 3` means
                    // the round cohort can never complete without it.
                    tracing::warn!(
                        creator = %hex4(&block_clone.creator),
                        seq = block_clone.seq,
                        block = %hex4(&block_id.0),
                        error = %other,
                        "consensus block REFUSED on ingest and dropped permanently \
                         (deterministic policy/signature refusal — never buffered, never re-pulled)"
                    );
                    refused.push((block_id, other.to_string()));
                }
            }
        }

        // Queue drained. One ack-RETRY EPOCH: if anything was inserted since the
        // last epoch and blocks are still held, re-offer them to the gate — fresh
        // evidence (a fork-completing insert, an acknowledging head) may license
        // what was refused a moment ago. Held-again blocks simply return to the
        // hold; no insert since the last epoch means no verdict can have changed,
        // so the loop exits.
        if retry_ack && !buffer.ack_held_is_empty() {
            retry_ack = false;
            for b in buffer.take_all_ack_held() {
                queue.push_back(b);
            }
            continue;
        }
        break;
    }

    // A block can be held, retried, and held again within one call; report each id
    // once.
    held_for_ack.sort();
    held_for_ack.dedup();
    // Only blocks still actually in the hold at exit count as held (a later epoch
    // may have admitted them).
    held_for_ack.retain(|id| buffer.is_ack_held(id));

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

    // THEME-2 #4: bound the catch-up Pull fan-out this batch emits (network
    // amplification cap). Truncation is liveness-safe — any root dropped here is
    // re-derived from the still-buffered orphans on the next batch.
    let mut pull_roots: Vec<BlockId> = pull_roots.into_iter().collect();
    if pull_roots.len() > MAX_PULL_ROOTS {
        pull_roots.truncate(MAX_PULL_ROOTS);
    }

    ApplyOutcome {
        inserted,
        pull_roots,
        equivocations,
        refused,
        held_for_ack,
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

    /// Enroll a creator's ML-DSA-65 public key into `lace`'s PQ roster so the
    /// pinned live ingest (`receive_block_pinned`, exercised by
    /// `apply_with_buffering`) accepts that creator's hybrid-signed blocks. The
    /// enrolled key is the SAME one `Block::new` signs the PQ half with (both
    /// derive from the ed25519 seed via `ml_dsa_65::keygen_from_seed`).
    fn enroll(lace: &mut Blocklace, sk: &SigningKey) {
        // The roster is keyed by the HYBRID id (== `Block::creator`).
        lace.enroll_pq(Block::hybrid_id(sk), Block::pq_public_key(sk));
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
        enroll(&mut lace, &sk);
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
        enroll(&mut lace, &sk);
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
        enroll(&mut lace, &sk);
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
        enroll(&mut lace, &sk_a);
        enroll(&mut lace, &sk_b);
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
        enroll(&mut lace_a, &sk);
        let mut buf_a = OrphanBuffer::new();
        let mut order_a = chain.clone();
        order_a.reverse();
        let _ = apply_with_buffering(&mut lace_a, &mut buf_a, order_a);

        let mut lace_b = Blocklace::new_simple(key(11));
        enroll(&mut lace_b, &sk);
        let mut buf_b = OrphanBuffer::new();
        let mut order_b = chain.clone();
        order_b.rotate_left(3);
        let _ = apply_with_buffering(&mut lace_b, &mut buf_b, order_b);

        let ids_a: HashSet<BlockId> = lace_a.iter().map(|(id, _)| *id).collect();
        let ids_b: HashSet<BlockId> = lace_b.iter().map(|(id, _)| *id).collect();
        assert_eq!(ids_a, ids_b, "two replicas converge to the same keyset");
        assert!(buf_a.is_empty() && buf_b.is_empty());
    }

    #[test]
    fn pinned_ingest_finalizes_honest_and_refuses_forged_pq() {
        // GAP #1b live path: the wire ingest (`apply_with_buffering` →
        // `receive_block_pinned`) accepts an ENROLLED creator's hybrid-signed
        // chain and REFUSES a block whose post-quantum half is forged.

        // Honest hybrid-signed chain from an enrolled creator → finalizes.
        let sk = key(30);
        let honest = build_chain(&sk, 3);
        let honest_ids: HashSet<BlockId> = honest.iter().map(|b| b.id()).collect();

        let mut lace = Blocklace::new_simple(key(60));
        enroll(&mut lace, &sk);
        let mut buf = OrphanBuffer::new();
        let out = apply_with_buffering(&mut lace, &mut buf, honest);
        let got: HashSet<BlockId> = lace.iter().map(|(id, _)| *id).collect();
        assert_eq!(
            got, honest_ids,
            "an enrolled creator's hybrid chain finalizes through the pinned ingest"
        );
        assert_eq!(out.inserted.len(), 3);
        assert!(buf.is_empty());

        // Forged PQ half: a genuinely ed25519-signed block (empty predecessors,
        // so no gap) whose ML-DSA half is corrupted. The classical half still
        // verifies, but the PQ pin against the enrolled key FAILS — the block is
        // refused (never inserted, never buffered).
        let mut forged = {
            let mut producer = Blocklace::new_simple(sk.clone());
            producer.add_block(Payload::Ack)
        };
        assert!(
            !forged.pq_signature.is_empty(),
            "Block::new must carry a PQ half to forge"
        );
        forged.pq_signature[0] ^= 0xff; // tamper the post-quantum signature

        let mut lace_f = Blocklace::new_simple(key(61));
        enroll(&mut lace_f, &sk); // creator IS enrolled — only the PQ half is bad
        let mut buf_f = OrphanBuffer::new();
        let out_f = apply_with_buffering(&mut lace_f, &mut buf_f, vec![forged.clone()]);
        assert!(
            !lace_f.contains(&forged.id()),
            "a forged post-quantum half is refused by the pinned ingest"
        );
        assert!(
            out_f.inserted.is_empty(),
            "nothing inserts from a forged block"
        );
        assert!(
            buf_f.is_empty(),
            "a forged block fails closed — it is dropped, not buffered/pulled"
        );

        // Unenrolled creator (valid hybrid block, but its key is not in the
        // roster) is also refused — fail-closed on an unknown identity.
        let stranger = key(31);
        let stranger_block = {
            let mut producer = Blocklace::new_simple(stranger.clone());
            producer.add_block(Payload::Ack)
        };
        let mut lace_u = Blocklace::new_simple(key(62)); // stranger NOT enrolled
        let mut buf_u = OrphanBuffer::new();
        let out_u = apply_with_buffering(&mut lace_u, &mut buf_u, vec![stranger_block.clone()]);
        assert!(
            !lace_u.contains(&stranger_block.id()),
            "a block from an unenrolled creator is refused fail-closed"
        );
        assert!(out_u.inserted.is_empty());
    }

    #[test]
    fn flag_day_catchup_drops_legacy_turn_without_buffering_then_accepts_timed_v1() {
        let anchor = 1_700_000_000;
        let producer = key(32);
        let legacy = Block::new(
            &producer,
            1,
            Payload::Turn(b"timestamp-less".to_vec()),
            Vec::new(),
        );

        let mut lace = Blocklace::new_simple(key(63));
        lace.enable_consensus_time_v1(dregg_blocklace::finality::ConsensusTimePolicyV1::new(
            anchor,
        ))
        .unwrap();
        enroll(&mut lace, &producer);
        let mut buffer = OrphanBuffer::new();
        let refused = apply_with_buffering(&mut lace, &mut buffer, vec![legacy.clone()]);
        assert!(!lace.contains(&legacy.id()));
        assert!(refused.inserted.is_empty());
        assert!(refused.pull_roots.is_empty());
        assert!(
            buffer.is_empty(),
            "deterministic flag-day refusal must not become an orphan retry loop"
        );

        let timed = Block::new(
            &producer,
            1,
            Payload::ConsensusTimedTurnV1(
                dregg_blocklace::finality::ConsensusTimedTurnPayloadV1::new(
                    anchor,
                    b"signed-turn".to_vec(),
                ),
            ),
            Vec::new(),
        );
        let accepted = apply_with_buffering(&mut lace, &mut buffer, vec![timed.clone()]);
        assert!(lace.contains(&timed.id()));
        assert_eq!(accepted.inserted.len(), 1);
        assert!(buffer.is_empty());
    }

    /// A fake predecessor id that will never land (distinct per `n`).
    fn fake_pred(n: u64) -> BlockId {
        let mut bytes = [0xEEu8; 32];
        bytes[..8].copy_from_slice(&n.to_le_bytes());
        BlockId(bytes)
    }

    /// A distinct-id orphan, cheaply: clone a real signed block and vary its
    /// payload so `id()` (a content hash) differs. `OrphanBuffer::buffer` keys
    /// only on `id()` + the supplied `missing` set, so this exercises the buffer's
    /// capacity/eviction bookkeeping without thousands of expensive hybrid signs.
    fn distinct_orphan(base: &Block, tag: u64) -> Block {
        let mut b = base.clone();
        b.payload = Payload::Data(tag.to_le_bytes().to_vec());
        b
    }

    /// THEME-2 #4 FALSIFIER — both directions. A Byzantine flood of orphans citing
    /// never-landing predecessors stays BOUNDED at `MAX_ORPHANS`; AND a legit
    /// late-arriving parent still releases its child (liveness preserved for
    /// honest late blocks under the cap).
    #[test]
    fn orphan_flood_stays_bounded_and_legit_late_parent_still_finalizes() {
        let sk = key(70);
        let base = Block::new(&sk, 1, Payload::Ack, Vec::new());

        let mut buf = OrphanBuffer::new();
        // Flood: MAX_ORPHANS + 500 orphans, each waiting on its own fake pred.
        let flood = MAX_ORPHANS + 500;
        for i in 0..flood as u64 {
            let orphan = distinct_orphan(&base, i);
            buf.buffer(orphan, vec![fake_pred(i)]);
        }
        assert_eq!(
            buf.len(),
            MAX_ORPHANS,
            "an orphan flood must stay bounded at MAX_ORPHANS (drop-oldest evicts the stalest)"
        );
        // The age indices never outgrow the buffer.
        assert_eq!(buf.order.len(), MAX_ORPHANS);
        assert_eq!(buf.inserted_at.len(), MAX_ORPHANS);

        // LIVENESS DIRECTION: a legit parent P and its child C. C is staged LAST
        // (freshest), so the flood's drop-oldest never evicts it; when P lands, C
        // is released even though the buffer is at capacity.
        let parent = distinct_orphan(&base, 9_000_001);
        let child = distinct_orphan(&base, 9_000_002);
        buf.buffer(child.clone(), vec![parent.id()]);
        assert_eq!(
            buf.len(),
            MAX_ORPHANS,
            "buffering C evicted the oldest fake"
        );
        assert!(
            buf.contains(&child.id()),
            "the fresh legit child is retained"
        );

        let released = buf.ready_after(parent.id());
        assert_eq!(
            released.len(),
            1,
            "the legit child is released when its late parent lands"
        );
        assert_eq!(released[0].id(), child.id());
        assert!(
            !buf.contains(&child.id()),
            "released child leaves the buffer"
        );
    }

    /// THEME-2 #4 FALSIFIER — the TTL sweep drops orphans that have out-waited the
    /// window while leaving fresh ones staged (so a slow-but-present predecessor
    /// still resolves its child, and the sweep's age bookkeeping stays consistent).
    #[test]
    fn orphan_ttl_sweep_drops_stale_but_keeps_fresh() {
        let sk = key(71);
        let base = Block::new(&sk, 1, Payload::Ack, Vec::new());
        let mut buf = OrphanBuffer::new();
        for i in 0..10u64 {
            buf.buffer(distinct_orphan(&base, i), vec![fake_pred(i)]);
        }
        assert_eq!(buf.len(), 10);

        // A generous TTL sweeps nothing (all fresh).
        let dropped = buf.sweep_expired(Duration::from_secs(3600));
        assert!(
            dropped.is_empty(),
            "no orphan is stale within the TTL window"
        );
        assert_eq!(buf.len(), 10);

        // A zero TTL treats every staged orphan as expired: all swept, and the age
        // indices drain in lockstep (no leak).
        let dropped = buf.sweep_expired(Duration::ZERO);
        assert_eq!(dropped.len(), 10);
        assert!(buf.is_empty());
        assert!(buf.order.is_empty());
        assert!(buf.inserted_at.is_empty());
    }
}
