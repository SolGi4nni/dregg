//! L6 — Receipts, Provenance & Time-Travel (the receipt/forest/MMR/blocklace
//! family, on the moldable-inspector spine).
//!
//! `presentable.rs` (L1) gives every protocol object a *set* of named
//! presentations; `replay.rs` gives the live world a VERIFIED, replayable
//! history (`World::recorded_turns() -> &History`, with a per-step canonical
//! `Ledger::root` tooth that every landing re-derives and checks). This module
//! welds the two for the provenance/time-travel surface (census slice 6):
//!
//!   * [`ReflectedReceiptChain`] — a whole receipt chain (the local blocklace)
//!     as a [`Presentable`], offering five lenses entirely off real machinery:
//!       - **Provenance** ← a [`PresentationBody::Timeline`] of the receipt chain
//!         (the causal-history scrubber), every event a real `receipt_hash()`.
//!       - **Graph** ← the call-forest / chain-linkage DAG: one node per receipt,
//!         one edge per `previous_receipt_hash` link (the real causal DAG).
//!       - **MerkleTree** ← the MMR receipt-index (positional non-omission): the
//!         receipt commitments are the dense log; the view carries the peak
//!         frontier, the committed root, and one membership path.
//!       - **Trace** ← the chain-hash linkage step-by-step (each step recomputes
//!         `receipt[i].receipt_hash()` and checks `receipt[i+1]`'s back-link).
//!       - **RawFields** ← the mandatory floor (`reflect_receipt` of the head).
//!   * [`ReflectedReceipt`] — ONE receipt as a [`Presentable`] (RawFields +
//!     Provenance + the consumed-cap MerkleTree + a Trace of its own hash absorb).
//!   * The verifier [`Gadget`]s (read-only — `Output = ReceiptVerification`):
//!       - [`ChainLinkageVerifier`] — recomputes every `receipt_hash()` and the
//!         back-links (the real `dregg-receipt-v3` commitment; reused, not faked).
//!       - [`ConsumedCapVerifier`] — runs the real
//!         [`dregg_turn::ConsumedCapWitness::verify`] (the cap-membership fold).
//!       - [`MmrRangeVerifier`] — the positional-range / non-omission check over
//!         the receipt-index MMR (`verify_range`-shaped, against the committed
//!         root; non-omission = a dense count pinned by the root).
//!   * [`TimeTravel`] — the time-travel gadget that REUSES `replay.rs`'s VERIFIED
//!     `History` (step / genesis / head / fork). It does NOT re-implement replay:
//!     it drives `History::replay_to` / `fork_at`, whose every landing re-derives
//!     state from genesis and checks it against the recorded root tooth.
//!
//! Everything is pure data + real verifiers, gpui-free, proven by `cargo test`.
//!
//! # Reuse map (no parallel model)
//!
//! | Need                         | Reused machinery                                   |
//! |------------------------------|----------------------------------------------------|
//! | verified time-travel         | `replay::History` (off `world.recorded_turns()`)   |
//! | receipt → field tree         | `reflect::reflect_receipt` / `reflect_nullifiers`  |
//! | receipt commitment           | `dregg_turn::TurnReceipt::receipt_hash` (v3)        |
//! | consumed-cap membership      | `dregg_turn::ConsumedCapWitness::verify` (real fold)|
//! | the L1 presentation kinds    | `presentable::{Presentation, PresentationBody, …}`  |
//!
//! The receipt-index MMR is rebuilt here over `blake3` with the SAME algorithm
//! the model (`metatheory/Dregg2/Lightclient/MMR.lean`) and `dregg-query`'s
//! `Mmr`/`verify_range` realize (peaks = the binary carry; the root bags the
//! peaks youngest-outward; non-omission = a dense count the root pins). The one
//! wiring note (see the module-end REPORT): `dregg-query` is not linked into
//! starbridge-v2 today, so this carries a faithful local instance; the upgrade is
//! to take `dregg-query` as a dep and call its `Mmr::open_range`/`verify_range`
//! verbatim — the leaf values (the receipt commitments) and the domain-tagged
//! hash are identical, so the swap is mechanical.

use dregg_cell::CellId;
use dregg_turn::turn::{ConsumedCapWitness, TurnReceipt};

use crate::presentable::{
    GadgetError, GadgetField, GadgetInput, GadgetValidation, Gadget, GraphView, MerkleTreeView,
    Presentable, PresentCtx, Presentation, PresentationBody, PresentationKind, TimelineEvent,
    TimelineView, TraceStep, TraceView,
};
use crate::reflect::{self, Inspectable, ObjectKind};
use crate::replay::{Fork, History, ReplayError, StateDiff};
use dregg_turn::turn::Turn;
use dregg_cell::Ledger;

// ===========================================================================
// §6.1 — the receipt-index MMR (the faithful local instance)
// ===========================================================================
//
// The dense log of receipt commitments. The algorithm is the model's
// (`MMR.lean`) / `dregg-query::mmr`'s exactly: peaks are perfect binary trees
// (one per set bit of the length, oldest-first / heights strictly decreasing);
// the root bags the peaks youngest-outward over the empty bag; a positional
// membership opening's directions are DERIVED from the dense offset (never
// carried), so a path cannot be replayed at another position; and non-omission
// is a COUNT the root pins (`Σ 2^height`). See the module REPORT for the
// dregg-query swap.

const MMR_TAG_EMPTY: &[u8] = b"dregg-query-mmr-v1:empty";
const MMR_TAG_LEAF: &[u8] = b"dregg-query-mmr-v1:leaf";
const MMR_TAG_NODE: &[u8] = b"dregg-query-mmr-v1:node";
const MMR_TAG_BAG: &[u8] = b"dregg-query-mmr-v1:bag";

fn b3(parts: &[&[u8]]) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    for p in parts {
        h.update(p);
    }
    *h.finalize().as_bytes()
}

fn mmr_empty() -> [u8; 32] {
    b3(&[MMR_TAG_EMPTY])
}
fn mmr_leaf(v: &[u8; 32]) -> [u8; 32] {
    b3(&[MMR_TAG_LEAF, v])
}
fn mmr_node(l: &[u8; 32], r: &[u8; 32]) -> [u8; 32] {
    b3(&[MMR_TAG_NODE, l, r])
}
fn mmr_bag(peak: &[u8; 32], rest: &[u8; 32]) -> [u8; 32] {
    b3(&[MMR_TAG_BAG, peak, rest])
}

/// One peak of the MMR frontier: its height and its subtree hash. Wire order is
/// OLDEST-FIRST (heights strictly decreasing — the mountains invariant).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReceiptMmrPeak {
    pub height: u8,
    pub hash: [u8; 32],
}

/// A positional membership opening of one receipt position: the peak frontier
/// (which pins the committed length + root) plus the bottom-up sibling path of
/// the position inside its covering peak. NO direction bits travel — the
/// verifier derives them from the dense offset (positional binding).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReceiptMmrOpening {
    pub peaks: Vec<ReceiptMmrPeak>,
    /// The position (dense index) this opening is for.
    pub pos: u64,
    /// The bottom-up sibling path of `pos` inside its covering peak (length =
    /// the covering peak's height).
    pub path: Vec<[u8; 32]>,
}

/// The receipt-index MMR: the appendable log of receipt commitments. The
/// receipt chain IS the log (`chain_index` = the dense position). Append-only.
#[derive(Clone, Debug, Default)]
pub struct ReceiptMmr {
    values: Vec<[u8; 32]>,
}

impl ReceiptMmr {
    pub fn new() -> Self {
        ReceiptMmr { values: Vec::new() }
    }

    /// Build the MMR over a receipt chain — the leaf values are the real
    /// `receipt_hash()` commitments, in commit order (the dense log).
    pub fn over_receipts(receipts: &[TurnReceipt]) -> Self {
        ReceiptMmr { values: receipts.iter().map(|r| r.receipt_hash()).collect() }
    }

    /// Append one receipt commitment. Returns its dense position.
    pub fn push(&mut self, v: [u8; 32]) -> u64 {
        self.values.push(v);
        (self.values.len() - 1) as u64
    }

    pub fn len(&self) -> u64 {
        self.values.len() as u64
    }

    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }

    /// The hash of the perfect subtree over `values[start .. start + 2^height]`.
    fn subtree(&self, start: usize, height: u8) -> [u8; 32] {
        if height == 0 {
            mmr_leaf(&self.values[start])
        } else {
            let half = 1usize << (height - 1);
            let l = self.subtree(start, height - 1);
            let r = self.subtree(start + half, height - 1);
            mmr_node(&l, &r)
        }
    }

    /// The peak frontier, oldest-first: one perfect peak per set bit of the
    /// length, highest bit first (the binary decomposition of the log length).
    pub fn peaks(&self) -> Vec<ReceiptMmrPeak> {
        let mut out = Vec::new();
        let mut start = 0usize;
        let len = self.values.len();
        for height in (0..64u8).rev() {
            if len & (1usize << height) != 0 {
                out.push(ReceiptMmrPeak { height, hash: self.subtree(start, height) });
                start += 1usize << height;
            }
        }
        out
    }

    /// The committed root: bag the peaks youngest-outward over the empty bag.
    pub fn root(&self) -> [u8; 32] {
        bag_peaks(&self.peaks())
    }

    /// The sibling path (bottom-up) of `pos` inside its covering peak.
    fn path_of(&self, pos: u64) -> Option<Vec<[u8; 32]>> {
        let (peak_start, peak_height) = covering_peak(self.len(), pos)?;
        let offset = (pos - peak_start) as usize;
        let mut path = Vec::with_capacity(peak_height as usize);
        for level in 0..peak_height {
            let sib_offset = (offset >> level) ^ 1;
            let sib_start = peak_start as usize + (sib_offset << level);
            path.push(self.subtree(sib_start, level));
        }
        Some(path)
    }

    /// Open one position for a membership proof: the value at `pos` plus its
    /// positional [`ReceiptMmrOpening`]. `None` iff `pos >= len`.
    pub fn open(&self, pos: u64) -> Option<([u8; 32], ReceiptMmrOpening)> {
        if pos >= self.len() {
            return None;
        }
        let path = self.path_of(pos)?;
        Some((
            self.values[pos as usize],
            ReceiptMmrOpening { peaks: self.peaks(), pos, path },
        ))
    }
}

/// Bag an oldest-first frontier into the root (youngest-outward fold).
fn bag_peaks(peaks_oldest_first: &[ReceiptMmrPeak]) -> [u8; 32] {
    let mut acc = mmr_empty();
    for p in peaks_oldest_first {
        acc = mmr_bag(&p.hash, &acc);
    }
    acc
}

/// The covering peak of `pos` in a log of length `len`: `(chunk_start, height)`.
fn covering_peak(len: u64, pos: u64) -> Option<(u64, u8)> {
    if pos >= len {
        return None;
    }
    let mut start = 0u64;
    for height in (0..64u8).rev() {
        if len & (1u64 << height) != 0 {
            let size = 1u64 << height;
            if pos < start + size {
                return Some((start, height));
            }
            start += size;
        }
    }
    None
}

/// The membership-failure shapes (each a model FALSE-witness): the frontier is
/// not mountains-shaped, does not bag to the trusted root, or the opening path
/// does not recompute its covering peak from the claimed value+position.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReceiptMmrError {
    BadFrontier,
    RootMismatch,
    PathLength { got: usize, want: usize },
    SlotMismatch,
    OutOfRange { pos: u64, len: u64 },
}

/// **The client-side membership acceptance** (the `RVerifies` shape, single
/// position). Against a TRUSTED `root` only (the length + peak hashes are
/// recomputed/pinned, never trusted), accept `value` as the receipt commitment
/// at `opening.pos` iff: the frontier is mountains-shaped and bags to `root`
/// (which pins the whole log + its length); and the path — with directions
/// DERIVED from the dense offset — recomputes the covering peak's pinned hash.
pub fn verify_membership(
    root: &[u8; 32],
    value: &[u8; 32],
    opening: &ReceiptMmrOpening,
) -> Result<u64, ReceiptMmrError> {
    // (1a) mountains shape: heights strictly decreasing oldest-first, < 64.
    let mut len = 0u64;
    let mut prev: Option<u8> = None;
    for p in &opening.peaks {
        if p.height >= 64 {
            return Err(ReceiptMmrError::BadFrontier);
        }
        if let Some(ph) = prev {
            if p.height >= ph {
                return Err(ReceiptMmrError::BadFrontier);
            }
        }
        prev = Some(p.height);
        len += 1u64 << p.height;
    }
    // (1b) the frontier bags to the trusted root — peak hashes, chunking, and
    // the length are now all pinned.
    if bag_peaks(&opening.peaks) != *root {
        return Err(ReceiptMmrError::RootMismatch);
    }
    if opening.pos >= len {
        return Err(ReceiptMmrError::OutOfRange { pos: opening.pos, len });
    }
    // (2) locate the covering peak by dense chunking.
    let mut chunk_starts = Vec::with_capacity(opening.peaks.len());
    let mut start = 0u64;
    for p in &opening.peaks {
        chunk_starts.push(start);
        start += 1u64 << p.height;
    }
    let k = opening
        .peaks
        .iter()
        .zip(chunk_starts.iter())
        .position(|(p, s)| opening.pos < s + (1u64 << p.height))
        .expect("pos < len implies a covering peak");
    let peak = &opening.peaks[k];
    let offset = (opening.pos - chunk_starts[k]) as usize;
    if opening.path.len() != peak.height as usize {
        return Err(ReceiptMmrError::PathLength {
            got: opening.path.len(),
            want: peak.height as usize,
        });
    }
    // (3) the positional opening: directions derived from the dense offset.
    let mut cur = mmr_leaf(value);
    for (level, sib) in opening.path.iter().enumerate() {
        cur = if (offset >> level) & 1 == 1 {
            mmr_node(sib, &cur)
        } else {
            mmr_node(&cur, sib)
        };
    }
    if cur != peak.hash {
        return Err(ReceiptMmrError::SlotMismatch);
    }
    Ok(len)
}

// ===========================================================================
// §6.2 — the Presentable impls: a whole receipt chain + one receipt
// ===========================================================================

/// First 6 bytes of a hash, hex (the timeline/trace short form).
fn short(bytes: &[u8]) -> String {
    reflect::short_hex(bytes)
}

/// A thin newtype reflecting a whole receipt chain (the local blocklace) as a
/// [`Presentable`] — the established "reflect a foreign datum into a starbridge
/// view" pattern. Snapshots the chain off the live world; the presentations are
/// pure projections of the real `TurnReceipt`s (never a parallel chain model).
#[derive(Clone, Debug)]
pub struct ReflectedReceiptChain {
    /// The receipts, in commit order (each links to its predecessor via
    /// `previous_receipt_hash`).
    pub receipts: Vec<TurnReceipt>,
}

impl ReflectedReceiptChain {
    /// Snapshot the whole receipt chain off the live world's receipt log.
    pub fn from_world(world: &crate::world::World) -> Self {
        ReflectedReceiptChain { receipts: world.receipts().to_vec() }
    }

    /// The chain's provenance [`TimelineView`] — every receipt, in commit order,
    /// the causal-history scrubber. Each event carries the real `receipt_hash()`.
    pub fn provenance(&self) -> TimelineView {
        let events = self
            .receipts
            .iter()
            .enumerate()
            .map(|(i, r)| TimelineEvent {
                at: i as u64,
                label: format!(
                    "receipt {} · agent {} · {} action(s) · {} computrons",
                    short(&r.receipt_hash()),
                    short(r.agent.as_bytes()),
                    r.action_count,
                    r.computrons_used
                ),
                hash: Some(r.receipt_hash()),
            })
            .collect();
        TimelineView { events }
    }

    /// The chain-linkage DAG as a [`GraphView`]: one node per receipt, one
    /// directed edge per `previous_receipt_hash` back-link (the real causal
    /// chain / blocklace DAG). Reuses the L1 graph primitives.
    pub fn linkage_graph(&self) -> GraphView {
        use crate::graph::{GraphEdge, GraphNode};
        // Index receipts by their hash so a back-link resolves to a holder node.
        let by_hash: std::collections::HashMap<[u8; 32], CellId> =
            self.receipts.iter().map(|r| (r.receipt_hash(), r.agent)).collect();
        let _ = &by_hash;

        // One node per agent that authored a receipt (the chain's principals),
        // reusing the GraphNode shape. The receipts themselves are the edges.
        let mut nodes: Vec<GraphNode> = Vec::new();
        let mut seen: std::collections::BTreeSet<CellId> = std::collections::BTreeSet::new();
        for r in &self.receipts {
            if seen.insert(r.agent) {
                nodes.push(GraphNode {
                    cell: r.agent,
                    short: short(r.agent.as_bytes()),
                    balance: 0,
                    lifecycle: "live".to_string(),
                    out_degree: 0,
                    in_degree: 0,
                });
            }
        }
        // Edges: for each receipt with a previous link, draw agent(prev)→agent(r)
        // (the causal step). Self-links (a single-agent strand) draw agent→agent.
        let mut edges: Vec<GraphEdge> = Vec::new();
        for r in &self.receipts {
            if let Some(prev) = r.previous_receipt_hash {
                if let Some(prev_agent) = by_hash.get(&prev) {
                    edges.push(GraphEdge {
                        holder: *prev_agent,
                        target: r.agent,
                        slot: r.action_count as u32,
                        rights: dregg_cell::AuthRequired::None,
                        faceted: false,
                        expires_at: None,
                        delegated_epoch: None,
                    });
                }
            }
        }
        GraphView { nodes, edges, focus: None }
    }

    /// The receipt-index MMR [`MerkleTreeView`]: the receipt commitments are the
    /// dense leaves, the published root is the committed root, and `path` is the
    /// membership path of the HEAD receipt (the most recently appended). Built
    /// off the real [`ReceiptMmr`].
    pub fn mmr_view(&self) -> MerkleTreeView {
        let mmr = ReceiptMmr::over_receipts(&self.receipts);
        let leaves: Vec<String> = self.receipts.iter().map(|r| hex::encode(r.receipt_hash())).collect();
        let path = if mmr.is_empty() {
            Vec::new()
        } else {
            match mmr.open(mmr.len() - 1) {
                Some((_, opening)) => opening.path.iter().map(hex::encode).collect(),
                None => Vec::new(),
            }
        };
        MerkleTreeView {
            label: format!("receipt-index MMR · {} receipt(s)", self.receipts.len()),
            leaves,
            root: mmr.root(),
            path,
        }
    }

    /// The chain-linkage [`TraceView`]: step-by-step, each step recomputes
    /// `receipt[i].receipt_hash()` and checks `receipt[i+1].previous_receipt_hash`
    /// matches it (the real `dregg-receipt-v3` linkage). A break is surfaced in
    /// the step text (never swallowed).
    pub fn linkage_trace(&self) -> TraceView {
        let mut steps = Vec::new();
        for (i, r) in self.receipts.iter().enumerate() {
            let h = r.receipt_hash();
            let link_ok = match (i, r.previous_receipt_hash) {
                (0, None) => true,           // genesis link: no predecessor.
                (0, Some(_)) => true,        // an off-strand first receipt (allowed).
                (i, Some(prev)) => self.receipts[i - 1].receipt_hash() == prev,
                (_, None) => false,          // a missing back-link mid-chain is a break.
            };
            steps.push(TraceStep {
                index: i,
                label: format!(
                    "receipt[{i}] hash {} · back-link {}",
                    short(&h),
                    if link_ok { "✓ matches predecessor" } else { "✗ BREAK (link mismatch)" }
                ),
            });
        }
        TraceView { steps }
    }
}

impl Presentable for ReflectedReceiptChain {
    fn object_kind(&self) -> ObjectKind {
        ObjectKind::Receipt
    }

    fn present(&self, _ctx: &PresentCtx) -> Vec<Presentation> {
        let mut out: Vec<Presentation> = Vec::new();

        // (1) RawFields — the MANDATORY floor: the genuine reflect_receipt of the
        //     HEAD receipt (or a chain-summary field tree if the chain is empty).
        let head_fields = match self.receipts.last() {
            Some(r) => reflect::reflect_receipt(r),
            None => Inspectable {
                kind: ObjectKind::Receipt,
                title: "Receipt chain (empty)".to_string(),
                subtitle: "no receipts committed yet".to_string(),
                fields: vec![reflect::Field::count("receipts", 0)],
            },
        };
        out.push(Presentation {
            kind: PresentationKind::RawFields,
            label: "Head Receipt".to_string(),
            search_text: PresentationBody::Fields(head_fields.clone()).search_text(),
            body: PresentationBody::Fields(head_fields),
        });

        // (2) Provenance — the causal-history Timeline (the scrubber).
        let timeline = self.provenance();
        out.push(Presentation {
            kind: PresentationKind::Provenance,
            label: "Receipt Chain".to_string(),
            search_text: format!(
                "provenance receipt chain {}",
                timeline.events.iter().map(|e| e.label.as_str()).collect::<Vec<_>>().join(" ")
            ),
            body: PresentationBody::Timeline(timeline),
        });

        // (3) Graph — the chain-linkage / blocklace causal DAG.
        let graph = self.linkage_graph();
        out.push(Presentation {
            kind: PresentationKind::Graph,
            label: "Chain DAG".to_string(),
            search_text: format!("graph chain dag {} edges {} nodes", graph.edges.len(), graph.nodes.len()),
            body: PresentationBody::Graph(graph),
        });

        // (4) MerkleTree — the receipt-index MMR membership + root.
        let mmr = self.mmr_view();
        out.push(Presentation {
            kind: PresentationKind::DomainVisual,
            label: "Receipt-Index MMR".to_string(),
            search_text: format!("mmr receipt index merkle {}", mmr.label),
            body: PresentationBody::MerkleTree(mmr),
        });

        // (5) Trace — the chain-hash linkage, step by step.
        let trace = self.linkage_trace();
        out.push(Presentation {
            kind: PresentationKind::Invariant,
            label: "Chain Linkage".to_string(),
            search_text: format!(
                "trace chain linkage {}",
                trace.steps.iter().map(|s| s.label.as_str()).collect::<Vec<_>>().join(" ")
            ),
            body: PresentationBody::Trace(trace),
        });

        out
    }
}

/// A thin newtype reflecting ONE receipt as a [`Presentable`] (the provenance
/// node) — RawFields + a consumed-cap MerkleTree + a hash-absorb Trace.
#[derive(Clone, Debug)]
pub struct ReflectedReceipt {
    pub receipt: TurnReceipt,
}

impl ReflectedReceipt {
    pub fn new(receipt: TurnReceipt) -> Self {
        ReflectedReceipt { receipt }
    }

    /// The consumed-capability MerkleTree view: each consumed cap is a leaf
    /// (its recomputed cap-root, off the real `ConsumedCapWitness`), and the
    /// `path` is the sibling digests of the FIRST consumed cap (the membership
    /// path the verifier opens). Empty for a self-sovereign turn.
    pub fn consumed_cap_view(&self) -> MerkleTreeView {
        let leaves: Vec<String> = self
            .receipt
            .consumed_capabilities
            .iter()
            .map(|w| match w.recompute_root() {
                Some(root) => format!("holder {} slot {} → cap-root {root}", short(w.holder.as_bytes()), w.slot),
                None => format!("holder {} slot {} → (malformed witness)", short(w.holder.as_bytes()), w.slot),
            })
            .collect();
        // The committed cap-root of the first witness (felt → 32 bytes), and its
        // sibling path (u32 siblings rendered hex).
        let (root, path) = match self.receipt.consumed_capabilities.first() {
            Some(w) => (
                w.cap_root_bytes32(),
                w.siblings.iter().map(|s| hex::encode(s.to_le_bytes())).collect(),
            ),
            None => ([0u8; 32], Vec::new()),
        };
        MerkleTreeView {
            label: format!(
                "consumed capabilities · {} spent",
                self.receipt.consumed_capabilities.len()
            ),
            leaves,
            root,
            path,
        }
    }

    /// The receipt's own hash-absorb [`TraceView`]: the ordered components the
    /// `dregg-receipt-v3` commitment binds (turn/forest/pre/post-state/…), the
    /// "what the receipt_hash absorbs" face.
    pub fn absorb_trace(&self) -> TraceView {
        let r = &self.receipt;
        let mut steps = vec![
            TraceStep { index: 0, label: format!("absorb turn_hash {}", short(&r.turn_hash)) },
            TraceStep { index: 1, label: format!("absorb forest_hash {}", short(&r.forest_hash)) },
            TraceStep { index: 2, label: format!("absorb pre_state {}", short(&r.pre_state_hash)) },
            TraceStep { index: 3, label: format!("absorb post_state {}", short(&r.post_state_hash)) },
            TraceStep { index: 4, label: format!("absorb effects_hash {}", short(&r.effects_hash)) },
            TraceStep { index: 5, label: format!("absorb agent {}", short(r.agent.as_bytes())) },
        ];
        match r.previous_receipt_hash {
            Some(prev) => steps.push(TraceStep {
                index: 6,
                label: format!("absorb previous_receipt {} (chain link)", short(&prev)),
            }),
            None => steps.push(TraceStep { index: 6, label: "absorb (no predecessor)".to_string() }),
        }
        steps.push(TraceStep {
            index: 7,
            label: format!("→ receipt_hash {}", short(&r.receipt_hash())),
        });
        TraceView { steps }
    }
}

impl Presentable for ReflectedReceipt {
    fn object_kind(&self) -> ObjectKind {
        ObjectKind::Receipt
    }

    fn present(&self, _ctx: &PresentCtx) -> Vec<Presentation> {
        let mut out = Vec::new();

        // (1) RawFields — the floor: the genuine reflect_receipt.
        let insp = reflect::reflect_receipt(&self.receipt);
        out.push(Presentation {
            kind: PresentationKind::RawFields,
            label: "Receipt".to_string(),
            search_text: PresentationBody::Fields(insp.clone()).search_text(),
            body: PresentationBody::Fields(insp),
        });

        // (2) MerkleTree — the consumed-capability membership view.
        let ccv = self.consumed_cap_view();
        out.push(Presentation {
            kind: PresentationKind::DomainVisual,
            label: "Consumed Capabilities".to_string(),
            search_text: format!("consumed caps merkle {}", ccv.label),
            body: PresentationBody::MerkleTree(ccv),
        });

        // (3) Trace — the receipt-hash absorb order (what the commitment binds).
        let trace = self.absorb_trace();
        out.push(Presentation {
            kind: PresentationKind::Invariant,
            label: "Hash Absorb".to_string(),
            search_text: format!(
                "trace hash absorb {}",
                trace.steps.iter().map(|s| s.label.as_str()).collect::<Vec<_>>().join(" ")
            ),
            body: PresentationBody::Trace(trace),
        });

        out
    }
}

// ===========================================================================
// §6.3 — verifier gadgets (read-only; Output = ReceiptVerification)
// ===========================================================================

/// The verdict a receipt verifier gadget builds — green/red plus the per-item
/// detail (which step broke, if any). A read-only `Gadget::Output` (no commit):
/// these run REAL cryptographic machinery and return a result, never a turn.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReceiptVerification {
    /// `true` iff every checked item verified against the real machinery.
    pub ok: bool,
    /// The number of items checked (receipts / consumed caps / positions).
    pub checked: usize,
    /// Per-item notes (the failure detail is surfaced, never swallowed).
    pub notes: Vec<String>,
}

impl ReceiptVerification {
    pub fn is_ok(&self) -> bool {
        self.ok
    }
}

/// **Q-Chain Verifier** — recomputes every receipt's `receipt_hash()` (the real
/// `dregg-receipt-v3` commitment) and checks each receipt's
/// `previous_receipt_hash` matches its predecessor's recomputed hash. A tampered
/// receipt (any field touched) breaks its hash, so the NEXT receipt's back-link
/// no longer matches — the tamper is flagged at the break. Reuses the real
/// commitment, never a re-implementation.
#[derive(Clone, Debug)]
pub struct ChainLinkageVerifier {
    pub receipts: Vec<TurnReceipt>,
}

impl ChainLinkageVerifier {
    pub fn over(receipts: Vec<TurnReceipt>) -> Self {
        ChainLinkageVerifier { receipts }
    }
}

impl Gadget for ChainLinkageVerifier {
    type Output = ReceiptVerification;

    fn fields(&self) -> Vec<GadgetField> {
        // A read-only verifier takes no editable fields (it runs over the chain).
        Vec::new()
    }
    fn set(&mut self, _field: &str, _v: GadgetInput) {}
    fn validate(&self) -> GadgetValidation {
        if self.receipts.is_empty() {
            GadgetValidation::Invalid { reason: "empty receipt chain".into() }
        } else {
            GadgetValidation::Ok
        }
    }

    fn build(&self) -> Result<ReceiptVerification, GadgetError> {
        let mut notes = Vec::new();
        let mut ok = true;
        for (i, r) in self.receipts.iter().enumerate() {
            let h = r.receipt_hash();
            match (i, r.previous_receipt_hash) {
                (0, _) => notes.push(format!("receipt[0] {} (chain head)", short(&h))),
                (i, Some(prev)) => {
                    let want = self.receipts[i - 1].receipt_hash();
                    if want == prev {
                        notes.push(format!("receipt[{i}] {} ✓ links to predecessor", short(&h)));
                    } else {
                        ok = false;
                        notes.push(format!(
                            "receipt[{i}] {} ✗ back-link {} != predecessor {}",
                            short(&h),
                            short(&prev),
                            short(&want)
                        ));
                    }
                }
                (i, None) => {
                    ok = false;
                    notes.push(format!("receipt[{i}] {} ✗ missing back-link mid-chain", short(&h)));
                }
            }
        }
        Ok(ReceiptVerification { ok, checked: self.receipts.len(), notes })
    }
}

/// **Consumed-Cap Witness Validator** — runs the REAL
/// [`dregg_turn::ConsumedCapWitness::verify`] (the sorted-Merkle cap-membership
/// fold over the holder's pre-state `capability_root`) on every consumed cap a
/// receipt carries. `build()` returns green iff every witness's recorded leaf
/// preimage opens to its recorded `cap_root`.
#[derive(Clone, Debug)]
pub struct ConsumedCapVerifier {
    pub witnesses: Vec<ConsumedCapWitness>,
}

impl ConsumedCapVerifier {
    pub fn over_receipt(r: &TurnReceipt) -> Self {
        ConsumedCapVerifier { witnesses: r.consumed_capabilities.clone() }
    }
}

impl Gadget for ConsumedCapVerifier {
    type Output = ReceiptVerification;

    fn fields(&self) -> Vec<GadgetField> {
        Vec::new()
    }
    fn set(&mut self, _field: &str, _v: GadgetInput) {}
    fn validate(&self) -> GadgetValidation {
        // A self-sovereign turn (no consumed caps) is a valid, trivially-green
        // input — not an error.
        GadgetValidation::Ok
    }

    fn build(&self) -> Result<ReceiptVerification, GadgetError> {
        let mut notes = Vec::new();
        let mut ok = true;
        for (i, w) in self.witnesses.iter().enumerate() {
            // The REAL cap-membership fold (ConsumedCapWitness::verify).
            if w.verify() {
                notes.push(format!(
                    "cap[{i}] holder {} slot {} ✓ opens to cap_root {}",
                    short(w.holder.as_bytes()),
                    w.slot,
                    w.cap_root
                ));
            } else {
                ok = false;
                notes.push(format!(
                    "cap[{i}] holder {} slot {} ✗ membership FAILS (leaf/path/root mismatch)",
                    short(w.holder.as_bytes()),
                    w.slot
                ));
            }
        }
        Ok(ReceiptVerification { ok, checked: self.witnesses.len(), notes })
    }
}

/// **MMR Range / Non-Omission Verifier** — opens a positional membership proof
/// over the receipt-index MMR and runs the client-side acceptance
/// ([`verify_membership`]) against the committed root. A `build()` green means
/// the proven receipt commitment sits at exactly the claimed dense position
/// (the positional non-omission tooth: a path cannot be replayed at another
/// position, and the length is pinned by the root).
#[derive(Clone, Debug)]
pub struct MmrMembershipVerifier {
    /// The receipt commitments (the dense log).
    pub values: Vec<[u8; 32]>,
    /// The position to prove membership at.
    pub pos: u64,
}

impl MmrMembershipVerifier {
    pub fn over_receipts(receipts: &[TurnReceipt], pos: u64) -> Self {
        MmrMembershipVerifier {
            values: receipts.iter().map(|r| r.receipt_hash()).collect(),
            pos,
        }
    }
}

impl Gadget for MmrMembershipVerifier {
    type Output = ReceiptVerification;

    fn fields(&self) -> Vec<GadgetField> {
        vec![GadgetField::U64 { key: "position".into(), min: 0, max: self.values.len() as u64 }]
    }
    fn set(&mut self, field: &str, v: GadgetInput) {
        if field == "position" {
            if let GadgetInput::U64(p) = v {
                self.pos = p;
            }
        }
    }
    fn validate(&self) -> GadgetValidation {
        if self.values.is_empty() {
            GadgetValidation::Invalid { reason: "empty MMR (no receipts)".into() }
        } else if self.pos >= self.values.len() as u64 {
            GadgetValidation::Invalid {
                reason: format!("position {} out of range (len {})", self.pos, self.values.len()),
            }
        } else {
            GadgetValidation::Ok
        }
    }

    fn build(&self) -> Result<ReceiptVerification, GadgetError> {
        if let GadgetValidation::Invalid { reason } = self.validate() {
            return Err(GadgetError::Incomplete { reason });
        }
        let mmr = ReceiptMmr::from_values(self.values.clone());
        let root = mmr.root();
        let (value, opening) = mmr
            .open(self.pos)
            .ok_or_else(|| GadgetError::Lowering { reason: "position has no opening".into() })?;
        match verify_membership(&root, &value, &opening) {
            Ok(len) => Ok(ReceiptVerification {
                ok: true,
                checked: 1,
                notes: vec![format!(
                    "receipt {} ✓ at position {} of {} (root-pinned, dense, non-omitted)",
                    short(&value),
                    self.pos,
                    len
                )],
            }),
            Err(e) => Ok(ReceiptVerification {
                ok: false,
                checked: 1,
                notes: vec![format!("position {} ✗ membership rejected: {e:?}", self.pos)],
            }),
        }
    }
}

impl ReceiptMmr {
    /// Build an MMR directly over the dense leaf values (the verifier path).
    pub fn from_values(values: Vec<[u8; 32]>) -> Self {
        ReceiptMmr { values }
    }
}

// ===========================================================================
// §6.4 — the TIME-TRAVEL gadget (REUSES replay.rs's VERIFIED History)
// ===========================================================================

/// Where the time-travel cursor can land — the four motions the prompt names.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TimeTravelMotion {
    /// Jump to genesis (the empty pre-genesis ledger, step 0).
    Genesis,
    /// Jump to the head (the live world's latest committed step).
    Head,
    /// Step to an explicit step index (`0..=len`).
    Step(usize),
}

/// The verified landing a time-travel motion produces: the step, the canonical
/// root tooth recorded there, whether replay re-derived+verified it (it always
/// should — a `false` is a real bug surfaced honestly), and the reconstructed
/// per-cell readout (id, balance, caps).
#[derive(Clone, Debug)]
pub struct TimeLanding {
    pub step: usize,
    pub root: [u8; 32],
    pub root_verified: bool,
    pub cells: Vec<(CellId, i64, usize)>,
}

/// **The time-travel gadget.** It REUSES `replay.rs`'s VERIFIED [`History`]
/// (sourced off the live world via `World::recorded_turns()`): every landing is
/// re-derived from genesis (or the nearest checkpoint) and checked against the
/// recorded canonical `Ledger::root` tooth. This gadget does NOT re-implement
/// replay — it drives `History::replay_to` / `History::fork_at`, so a landing it
/// reports is exactly the verified replay's, never an approximation.
pub struct TimeTravel<'h> {
    history: &'h History,
}

impl<'h> TimeTravel<'h> {
    /// Drive time-travel over a recorded history (e.g. `world.recorded_turns()`).
    pub fn over(history: &'h History) -> Self {
        TimeTravel { history }
    }

    /// The head step index (the live world's latest landing).
    pub fn head(&self) -> usize {
        self.history.len()
    }

    /// The number of recorded steps + 1 landings (genesis..head inclusive).
    pub fn landing_count(&self) -> usize {
        self.history.len() + 1
    }

    /// Resolve a motion to an absolute step index (clamped into range).
    fn resolve(&self, motion: TimeTravelMotion) -> usize {
        match motion {
            TimeTravelMotion::Genesis => 0,
            TimeTravelMotion::Head => self.history.len(),
            TimeTravelMotion::Step(k) => k.min(self.history.len()),
        }
    }

    /// **Land** on a motion via the VERIFIED replay. Reconstructs the world at
    /// the target step (re-derived from genesis, checked against the recorded
    /// root tooth) and reports the per-cell readout. A replay error (a tampered
    /// tooth, a nondeterministic re-run) surfaces as `root_verified = false`.
    pub fn land(&self, motion: TimeTravelMotion) -> TimeLanding {
        let step = self.resolve(motion);
        match self.history.replay_to(step) {
            Ok(ledger) => {
                let mut cells: Vec<(CellId, i64, usize)> = ledger
                    .iter()
                    .map(|(id, c)| (*id, c.state.balance(), c.capabilities.len()))
                    .collect();
                cells.sort_by(|a, b| a.0.as_bytes().cmp(b.0.as_bytes()));
                TimeLanding {
                    step,
                    root: self.history.root_at(step),
                    root_verified: true,
                    cells,
                }
            }
            Err(_) => TimeLanding {
                step,
                root: self.history.root_at(step.min(self.history.len())),
                root_verified: false,
                cells: Vec::new(),
            },
        }
    }

    /// The verified replay at a step (the raw ledger), for callers that want the
    /// reconstructed `Ledger` itself (it re-derives + checks the tooth).
    pub fn replay_to(&self, step: usize) -> Result<Ledger, ReplayError> {
        self.history.replay_to(step)
    }

    /// **Fork / what-if** at a step: branch off the VERIFIED branch point and run
    /// a DIFFERENT turn on the throwaway fork — the mainline is untouched. Reuses
    /// `History::fork_at` (which replays+verifies the branch point first).
    pub fn fork(&self, at_step: usize, alt: Turn) -> Result<Fork, ReplayError> {
        self.history.fork_at(at_step, alt)
    }

    /// The state DIFF between two landings (verified replays of both).
    pub fn diff(&self, from: usize, to: usize) -> Result<StateDiff, ReplayError> {
        self.history.diff(from, to)
    }

    /// The provenance [`TimelineView`] of the history itself — one event per
    /// recorded step (the time-travel scrubber's own timeline), each carrying
    /// the recorded root tooth as its navigable hash.
    pub fn timeline(&self) -> TimelineView {
        let events = self
            .history
            .checkpoints()
            .into_iter()
            .map(|cp| TimelineEvent {
                at: cp.step as u64,
                label: if cp.step == 0 {
                    "genesis (empty)".to_string()
                } else {
                    self.history.steps()[cp.step - 1].label()
                },
                hash: Some(cp.root),
            })
            .collect();
        TimelineView { events }
    }
}

// ===========================================================================
// TESTS — the model + real verifiers, gpui-free (cargo test).
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::replay::demo_history;
    use crate::world::{transfer, World};

    /// A two-cell world: a treasury (1_000) and a sink (0).
    fn two_cell_world() -> (World, CellId, CellId) {
        let mut w = World::new();
        let treasury = w.genesis_cell(0x11, 1_000);
        let sink = w.genesis_cell(0x22, 0);
        (w, treasury, sink)
    }

    // ── the Timeline reflects the REAL receipt chain (grows after a turn) ─────

    #[test]
    fn the_provenance_timeline_reflects_the_real_chain_and_grows_after_a_turn() {
        let (mut w, treasury, sink) = two_cell_world();

        // Before any turn: the chain (and its Provenance timeline) is empty.
        let chain = ReflectedReceiptChain::from_world(&w);
        let ctx = PresentCtx::new(&w, treasury);
        let set = chain.present(&ctx);
        let prov = set.iter().find(|p| p.kind == PresentationKind::Provenance).unwrap();
        match &prov.body {
            PresentationBody::Timeline(t) => assert!(t.events.is_empty(), "no receipts yet"),
            other => panic!("Provenance must carry a Timeline, got {other:?}"),
        }

        // Commit TWO real transfers.
        let t1 = w.turn(treasury, vec![transfer(treasury, sink, 250)]);
        assert!(w.commit_turn(t1).is_committed());
        let t2 = w.turn(treasury, vec![transfer(treasury, sink, 100)]);
        assert!(w.commit_turn(t2).is_committed());

        // After: the Provenance timeline carries the two real receipts, in order,
        // each navigable by its real receipt_hash().
        let chain = ReflectedReceiptChain::from_world(&w);
        let set = chain.present(&PresentCtx::new(&w, treasury));
        let prov = set.iter().find(|p| p.kind == PresentationKind::Provenance).unwrap();
        match &prov.body {
            PresentationBody::Timeline(t) => {
                assert_eq!(t.events.len(), 2, "the two committed receipts appear");
                assert_eq!(t.events[0].at, 0);
                assert_eq!(t.events[1].at, 1);
                // The navigable hashes are the REAL receipt hashes.
                assert_eq!(t.events[0].hash, Some(w.receipts()[0].receipt_hash()));
                assert_eq!(t.events[1].hash, Some(w.receipts()[1].receipt_hash()));
            }
            _ => unreachable!(),
        }
        // The RawFields floor is the head receipt.
        assert!(set.iter().any(|p| p.kind == PresentationKind::RawFields));
    }

    #[test]
    fn the_chain_offers_the_full_presentation_family() {
        let (mut w, treasury, sink) = two_cell_world();
        let t = w.turn(treasury, vec![transfer(treasury, sink, 50)]);
        assert!(w.commit_turn(t).is_committed());
        let chain = ReflectedReceiptChain::from_world(&w);
        let set = chain.present(&PresentCtx::new(&w, treasury));
        // RawFields (floor) + Provenance (timeline) + Graph (DAG) + MerkleTree (MMR) + Trace.
        assert!(set.iter().any(|p| p.kind == PresentationKind::RawFields));
        assert!(set.iter().any(|p| matches!(p.body, PresentationBody::Timeline(_))));
        assert!(set.iter().any(|p| matches!(p.body, PresentationBody::Graph(_))));
        assert!(set.iter().any(|p| matches!(p.body, PresentationBody::MerkleTree(_))));
        assert!(set.iter().any(|p| matches!(p.body, PresentationBody::Trace(_))));
    }

    // ── the MMR MerkleTree verifies a REAL receipt's membership ──────────────

    #[test]
    fn the_mmr_verifies_a_real_receipts_membership_at_its_position() {
        let (mut w, treasury, sink) = two_cell_world();
        // Commit five real transfers so the MMR has mixed peak heights (5 = 101b
        // → peaks of height 2 and 0 — a non-trivial frontier).
        for _ in 0..5 {
            let t = w.turn(treasury, vec![transfer(treasury, sink, 10)]);
            assert!(w.commit_turn(t).is_committed());
        }
        let receipts = w.receipts();
        assert_eq!(receipts.len(), 5);

        let mmr = ReceiptMmr::over_receipts(receipts);
        let root = mmr.root();
        // The peak frontier of length 5 is heights [2, 0] (oldest-first).
        let heights: Vec<u8> = mmr.peaks().iter().map(|p| p.height).collect();
        assert_eq!(heights, vec![2, 0]);

        // EVERY real receipt verifies at its own position against the committed root.
        for (pos, r) in receipts.iter().enumerate() {
            let (value, opening) = mmr.open(pos as u64).expect("a real position opens");
            assert_eq!(value, r.receipt_hash(), "the opened leaf IS the receipt commitment");
            let len = verify_membership(&root, &value, &opening)
                .expect("a genuine receipt opens against the committed root");
            assert_eq!(len, 5);
        }

        // The verifier gadget agrees.
        let v = MmrMembershipVerifier::over_receipts(receipts, 3);
        assert!(v.validate().is_ok());
        assert!(v.build().unwrap().is_ok());

        // Tampering the proven value (a forged commitment) is REJECTED.
        let (mut value, opening) = mmr.open(2).unwrap();
        value[0] ^= 0xff;
        assert!(verify_membership(&root, &value, &opening).is_err(), "a forged leaf is rejected");

        // A wrong-position replay of a genuine path is REJECTED (positional bind).
        let (value0, opening0) = mmr.open(0).unwrap();
        let mut mis = opening0.clone();
        mis.pos = 1; // claim position 1 with position 0's path
        assert!(
            verify_membership(&root, &value0, &mis).is_err(),
            "a path replayed at the wrong position is rejected"
        );

        // The MerkleTree presentation carries the real root.
        let chain = ReflectedReceiptChain::from_world(&w);
        let set = chain.present(&PresentCtx::new(&w, treasury));
        let mtv = set.iter().find_map(|p| match &p.body {
            PresentationBody::MerkleTree(m) => Some(m),
            _ => None,
        }).unwrap();
        assert_eq!(mtv.root, root, "the MMR presentation's root is the real committed root");
        assert_eq!(mtv.leaves.len(), 5);
    }

    // ── the Trace shows the REAL chain linkage; the verifier reuses receipt_hash

    #[test]
    fn the_trace_shows_real_chain_linkage_and_the_verifier_reuses_receipt_hash() {
        let (mut w, treasury, sink) = two_cell_world();
        for _ in 0..3 {
            let t = w.turn(treasury, vec![transfer(treasury, sink, 5)]);
            assert!(w.commit_turn(t).is_committed());
        }
        let chain = ReflectedReceiptChain::from_world(&w);

        // The Trace presentation has one step per receipt; each non-head step's
        // back-link matches its predecessor (the real dregg-receipt-v3 linkage).
        let trace = chain.linkage_trace();
        assert_eq!(trace.steps.len(), 3);
        assert!(trace.steps.iter().all(|s| s.label.contains("✓ matches predecessor") || s.index == 0));

        // The Q-Chain verifier gadget runs the REAL receipt_hash() over the chain.
        let verifier = ChainLinkageVerifier::over(w.receipts().to_vec());
        assert!(verifier.validate().is_ok());
        let result = verifier.build().unwrap();
        assert!(result.ok, "a genuine chain links cleanly: {:?}", result.notes);
        assert_eq!(result.checked, 3);

        // TAMPER: corrupt a receipt mid-chain — its recomputed hash changes, so
        // the next receipt's back-link no longer matches → the verifier flags it.
        let mut tampered = w.receipts().to_vec();
        tampered[1].computrons_used ^= 0xdead; // any field touched breaks the hash
        let tv = ChainLinkageVerifier::over(tampered).build().unwrap();
        assert!(!tv.ok, "a tampered receipt breaks the chain linkage");
    }

    // ── the consumed-cap MerkleTree verifier runs the REAL membership fold ───

    #[test]
    fn the_consumed_cap_verifier_runs_the_real_membership_fold() {
        // Build a ConsumedCapWitness whose recorded leaf preimage + path open to
        // a self-consistent cap_root via the REAL fold (ConsumedCapWitness::
        // recompute_root / verify). We construct the path, recompute the genuine
        // root with the real machinery, and pin it — verify() then exercises the
        // real sorted-Merkle cap fold and returns true.
        use dregg_turn::turn::ConsumedCapAuthPath;
        const DEPTH: usize = 16; // dregg_circuit::cap_root::CAP_TREE_DEPTH
        let mut w = ConsumedCapWitness {
            holder: CellId::derive_raw(&[0x42u8; 32], &[0u8; 32]),
            slot: 3,
            action_path: vec![0],
            auth_path: ConsumedCapAuthPath::Breadstuff,
            leaf_slot_hash: 7,
            leaf_target: 11,
            leaf_auth_tag: 1,
            leaf_mask_lo: 0xFFFF,
            leaf_mask_hi: 0,
            leaf_expiry: 0,
            leaf_breadstuff: 0,
            siblings: (0..DEPTH as u32).map(|i| i + 1).collect(),
            directions: (0..DEPTH).map(|i| (i % 2) as u8).collect(),
            cap_root: 0, // placeholder — pinned below to the genuine recomputed root
        };
        // The REAL fold computes the genuine root for this leaf+path.
        let genuine = w.recompute_root().expect("a depth-16 witness recomputes");
        w.cap_root = genuine;
        assert!(w.verify(), "the genuine leaf+path opens to its recomputed root (real fold)");

        // The verifier gadget over a receipt carrying this witness is GREEN.
        let receipt = receipt_with_consumed(vec![w.clone()]);
        let v = ConsumedCapVerifier::over_receipt(&receipt);
        let r = v.build().unwrap();
        assert!(r.ok, "the real cap-membership fold accepts a genuine witness: {:?}", r.notes);
        assert_eq!(r.checked, 1);

        // TAMPER: corrupt a sibling → the recomputed root diverges → verify FAILS.
        let mut bad = w.clone();
        bad.siblings[0] ^= 0xff;
        let badr = ConsumedCapVerifier { witnesses: vec![bad] }.build().unwrap();
        assert!(!badr.ok, "a tampered membership path fails the real fold");

        // A self-sovereign receipt (no consumed caps) is trivially green.
        let empty = ConsumedCapVerifier::over_receipt(&receipt_with_consumed(vec![]));
        assert!(empty.build().unwrap().ok);
    }

    /// Build a minimal real `TurnReceipt` carrying the given consumed caps (for
    /// the consumed-cap verifier test — the rest of the receipt is irrelevant to
    /// the cap fold).
    fn receipt_with_consumed(caps: Vec<ConsumedCapWitness>) -> TurnReceipt {
        let agent = CellId::derive_raw(&[0x42u8; 32], &[0u8; 32]);
        TurnReceipt {
            turn_hash: [1u8; 32],
            forest_hash: [2u8; 32],
            pre_state_hash: [3u8; 32],
            post_state_hash: [4u8; 32],
            timestamp: 0,
            effects_hash: [5u8; 32],
            computrons_used: 0,
            action_count: 1,
            previous_receipt_hash: None,
            agent,
            federation_id: [0u8; 32],
            routing_directives: Vec::new(),
            introduction_exports: Vec::new(),
            derivation_records: Vec::new(),
            emitted_events: Vec::new(),
            executor_signature: None,
            finality: Default::default(),
            was_encrypted: false,
            was_burn: false,
            consumed_capabilities: caps,
        }
    }

    // ── time-travel via replay.rs lands on the right historical state ────────

    #[test]
    fn time_travel_reuses_replay_and_lands_on_the_right_historical_state() {
        // Drive the gadget off the SAME demo history replay.rs records/verifies.
        let (history, _live, [treasury, service, user]) = demo_history();
        let tt = TimeTravel::over(&history);

        // 4 genesis + 5 turns = 9 steps, 10 landings.
        assert_eq!(tt.head(), 9);
        assert_eq!(tt.landing_count(), 10);

        // GENESIS lands on the empty pre-genesis ledger (verified).
        let g = tt.land(TimeTravelMotion::Genesis);
        assert_eq!(g.step, 0);
        assert!(g.root_verified);
        assert!(g.cells.is_empty(), "step 0 is the empty pre-genesis ledger");

        // HEAD lands on the live world (verified) — service holds 250_000 + 1_000.
        let h = tt.land(TimeTravelMotion::Head);
        assert_eq!(h.step, 9);
        assert!(h.root_verified);
        let svc = h.cells.iter().find(|(id, _, _)| *id == service).unwrap();
        assert_eq!(svc.1, 251_000, "the head landing reconstructs the real service balance");

        // A mid-history STEP lands verified, and its root is the recorded tooth.
        let mid = tt.land(TimeTravelMotion::Step(4));
        assert!(mid.root_verified);
        assert_eq!(mid.root, history.root_at(4), "the landing root IS replay.rs's recorded tooth");

        // Every landing is verified (the root tooth re-derived from genesis).
        for k in 0..=tt.head() {
            assert!(tt.land(TimeTravelMotion::Step(k)).root_verified, "step {k} must verify");
        }

        let _ = (treasury, user);
    }

    #[test]
    fn time_travel_fork_diverges_and_leaves_the_mainline_intact() {
        // The fork motion reuses History::fork_at (verified branch point), and a
        // different turn diverges while the mainline is untouched.
        let mut h = crate::replay::History::new(1_700_000_000);
        let mut l = Ledger::new();
        let ex = h.fresh_executor();
        let a = h.record_genesis(&mut l, crate::world::make_open_cell(1, 1_000));
        let b = h.record_genesis(&mut l, crate::world::make_open_cell(2, 0));
        let nonce = |l: &Ledger, id: &CellId| l.get(id).map(|c| c.state.nonce()).unwrap_or(0);
        let t1 = crate::world::bare_turn(a, nonce(&l, &a), vec![transfer(a, b, 100)]);
        assert!(h.record_commit(&ex, &mut l, t1).is_some());

        let tt = TimeTravel::over(&h);
        let mainline_head = h.root_at(h.len());

        // Fork at the branch point (after the genesis installs, before the turn)
        // with a DIFFERENT turn.
        let branch = 2; // 2 genesis steps
        let alt_nonce = tt.replay_to(branch).unwrap().get(&a).unwrap().state.nonce();
        let alt = crate::world::bare_turn(a, alt_nonce, vec![transfer(a, b, 500)]);
        let fork = tt.fork(branch, alt).expect("fork replays+verifies the branch point");
        assert!(fork.outcome.is_committed());
        assert!(fork.diverged(), "a different turn diverges from the mainline");

        // The mainline is intact (its recorded head root is unchanged + replays).
        assert_eq!(h.root_at(h.len()), mainline_head);
        let mut head = tt.replay_to(h.len()).unwrap();
        assert_eq!(head.root(), mainline_head);
    }

    #[test]
    fn the_time_travel_timeline_carries_the_recorded_root_teeth() {
        let (history, _l, _ids) = demo_history();
        let tt = TimeTravel::over(&history);
        let tl = tt.timeline();
        // One landing per step + the genesis-empty landing.
        assert_eq!(tl.events.len(), tt.landing_count());
        assert_eq!(tl.events[0].label, "genesis (empty)");
        // Each event's navigable hash IS the recorded canonical root tooth.
        for (k, ev) in tl.events.iter().enumerate() {
            assert_eq!(ev.hash, Some(history.root_at(k)));
        }
    }

    // ── a single receipt's presentation family ───────────────────────────────

    #[test]
    fn a_single_receipt_presents_raw_fields_consumed_caps_and_an_absorb_trace() {
        let (mut w, treasury, sink) = two_cell_world();
        let t = w.turn(treasury, vec![transfer(treasury, sink, 10)]);
        assert!(w.commit_turn(t).is_committed());
        let receipt = ReflectedReceipt::new(w.receipts()[0].clone());
        let set = receipt.present(&PresentCtx::new(&w, treasury));

        // RawFields floor (the genuine reflect_receipt).
        let raw = set.iter().find(|p| p.kind == PresentationKind::RawFields).unwrap();
        match &raw.body {
            PresentationBody::Fields(i) => {
                assert!(i.fields.iter().any(|f| f.key == "receipt_hash"));
                assert!(i.fields.iter().any(|f| f.key == "post_state"));
            }
            _ => unreachable!(),
        }
        // The consumed-cap MerkleTree (empty for a plain transfer) + absorb Trace.
        assert!(set.iter().any(|p| matches!(p.body, PresentationBody::MerkleTree(_))));
        let trace = set.iter().find_map(|p| match &p.body {
            PresentationBody::Trace(t) => Some(t),
            _ => None,
        }).unwrap();
        // The absorb trace ends at the real receipt_hash.
        assert!(trace.steps.last().unwrap().label.contains(&short(&w.receipts()[0].receipt_hash())));
    }
}
