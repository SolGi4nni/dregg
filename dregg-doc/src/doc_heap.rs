//! **The document rides the per-cell umem-heap.** A dreggverse document IS a
//! [`dregg_cell::Cell`], and its commitment IS that cell's committed `heap_root`
//! — the boundary of the cell's universal-memory heap (the per-cell umem of
//! `docs/deos/UMEM-PRIMITIVE.md` §2, §8).
//!
//! [`crate::commit`] names this target directly: *"The real substrate commitment
//! is sorted-Poseidon2 over the document cell's heap (the faithful 8-felt
//! commitment floor); this crate rides that later"* (`commit.rs:30`). This module
//! is that ride, onto the **umem-heap** specifically — the cell's
//! `heap_map`/`heap_root` umem collection that Stage A exposes
//! (`cell/src/state.rs`: `set_heap` / `reseal_heap_root` / `heap_root_membership`)
//! — distinct from the `fields_map`/`fields_root` ride
//! [`crate::executor_drive`] drives through the executor.
//!
//! ## The document IS a cell with a umem-heap
//!
//! The document's content — the atom graph, order-edges, and field assignments,
//! each binding provenance ([`crate::substrate::to_heap_map`]) — is projected
//! into the cell's heap as a `(collection_id, key) -> 32-byte value` umem
//! address space. The cell's `heap_root` (the sorted-Poseidon2 boundary over the
//! present cells) is the document's commitment. So:
//!
//! - **A sovereign document** is a cell whose whole content is bound by one
//!   committed umem boundary root ([`DocHeapCell::commitment`]).
//! - **Conflicts-as-objects** ride the boundary: a conflict state's *both* live
//!   alternatives (and their provenance) are heap leaves, so the umem boundary
//!   binds them — a light client cannot be shown a forged or dropped alternative
//!   (the [`crate::commit`] anti-forge tooth survives onto the real root).
//! - **`dregg://` transclusion** is a **composable umem** ([`DocHeapCell::transclude`]):
//!   an embed leaf whose VALUE is a child cell's `heap_root` — the parent's umem
//!   holds, at an embed key, another cell's boundary root. A `Pin::At` citation
//!   that does not break is exactly this content-addressed umem boundary: mutate
//!   the child and its root changes, so the parent boundary changes — the
//!   citation cannot be silently forged.
//!
//! - **The patch-history lives IN the cell** ([`COLL_HISTORY`]): the ordered
//!   patch chain — the [`History`] whose fold IS the content — is serialized
//!   into recoverable heap leaves alongside the text, so the committed boundary
//!   binds not just *what the document says* but *how it got there*. Reopening
//!   a document ([`DocHeapCell::reopen`]) replays the committed chain: blame
//!   answers from the reopened document identically to the never-closed one,
//!   and a tampered history leaf fails the heap-root check (the same anti-forge
//!   tooth the content leaves carry).
//!
//! This is an **app/integration-layer** ride: it projects into and reseals the
//! cell's existing umem-heap. It introduces **no new kernel effect** — the writes
//! are ordinary heap writes the substrate already commits.
//!
//! ## Named seams (honest, not built here)
//!
//! - **History compaction.** The committed history payload grows linearly with
//!   the edit count (every patch, verbatim, re-laid on each reseal). For long-
//!   lived documents a checkpoint scheme (fold a prefix into a committed graph
//!   snapshot + keep the suffix chain) is the obvious compaction; it is NOT
//!   built — building it changes what the boundary binds and deserves its own
//!   design pass.
//! - **Executor-journal cross-check.** [`crate::executor_drive`] journals each
//!   committed edit as a real turn receipt. A history entry here and the
//!   receipt chain there are two witnesses of the same edit that are not yet
//!   cross-checked against each other (patch-id ↔ receipt correspondence).

use crate::atom::{AtomId, Author};
use crate::graph::DocGraph;
use crate::history::History;
use crate::patch::{Op, Patch};
use crate::substrate::to_heap_map;
use dregg_cell::{Cell, CellId, FieldElement, compute_heap_root};
use std::collections::BTreeMap;

/// Heap collection holding `dregg://` transclusion edges. Each leaf VALUE is a
/// child cell's committed `heap_root` — a composable-umem boundary embedded by
/// reference. Disjoint from the document-content collections
/// ([`crate::COLL_ATOMS`]=0 / [`crate::COLL_EDGES`]=1 / [`crate::COLL_FIELDS`]=2),
/// so an embed can never be confused for document content (umem tag isolation).
pub const COLL_EMBED: u32 = 3;

/// Heap collection holding the document's **verbatim editor prose**, so a
/// reopened document re-seeds its text FROM the committed umem-heap. The
/// structured atom/edge/field projection ([`to_heap_map`]) hashes its leaf
/// preimages (one-way BLAKE3), so the *recoverable* prose is bound here too:
/// key `0` is the byte length (LE `u64` in the low 8 bytes), keys `1..` are
/// 32-byte verbatim UTF-8 chunks. Disjoint from the content collections
/// ([`crate::COLL_ATOMS`]=0 / [`crate::COLL_EDGES`]=1 / [`crate::COLL_FIELDS`]=2)
/// and [`COLL_EMBED`]=3 — umem tag isolation, so prose can never be confused for
/// content or an embed.
pub const COLL_TEXT: u32 = 4;

/// Heap collection holding the document's **patch-history** — the ordered patch
/// chain whose fold IS the content (`DOCUMENT-LANGUAGE.md` §0: "the document's
/// content is the result of applying its patch-history"). Same recoverable
/// chunk layout as [`COLL_TEXT`] (length leaf at key `0`, 32-byte payload
/// chunks at `1..`), carrying the canonical serialization of a [`History`]
/// ([`history_into_heap`] / [`history_from_heap`]). Disjoint from every other
/// collection — umem tag isolation, so a history leaf can never be confused for
/// content, an embed, or prose. Because these are ordinary heap leaves, the
/// committed `heap_root` binds the WHOLE chain: who edited, what, in which
/// order — a tampered or reordered history fails the same root check the
/// anti-forge content leaves do.
pub const COLL_HISTORY: u32 = 5;

/// Bytes of verbatim payload carried per heap leaf in the chunked collections
/// ([`COLL_TEXT`] prose, [`COLL_HISTORY`] patch chain).
const CHUNK_BYTES: usize = 32;

/// Lay `bytes` into `map` at collection `coll`: a length leaf at key `0` (LE
/// `u64` in the low 8 bytes), then one 32-byte payload chunk per key `1..`. Any
/// prior leaves of `coll` are cleared first so a shrunk payload leaves no stale
/// chunk bound by the boundary.
fn bytes_into_heap(map: &mut BTreeMap<(u32, u32), FieldElement>, coll: u32, bytes: &[u8]) {
    map.retain(|&(c, _), _| c != coll);
    let mut len_fe = [0u8; 32];
    len_fe[..8].copy_from_slice(&(bytes.len() as u64).to_le_bytes());
    map.insert((coll, 0), len_fe);
    for (i, chunk) in bytes.chunks(CHUNK_BYTES).enumerate() {
        let mut fe = [0u8; 32];
        fe[..chunk.len()].copy_from_slice(chunk);
        map.insert((coll, 1 + i as u32), fe);
    }
}

/// Recover a chunked payload from `map`'s `coll` leaves — the inverse of
/// [`bytes_into_heap`]. `None` when no length leaf is present, when a payload
/// chunk is missing, or when the length leaf claims more bytes than the present
/// chunks carry (a malformed/tampered heap is refused, never zero-filled).
fn bytes_from_heap(map: &BTreeMap<(u32, u32), FieldElement>, coll: u32) -> Option<Vec<u8>> {
    let len_fe = map.get(&(coll, 0))?;
    let byte_len = u64::from_le_bytes(len_fe[..8].try_into().ok()?) as usize;
    // Refuse a forged length that exceeds what the present chunk leaves carry
    // (also bounds the allocation below by the map's actual size).
    let chunks = map.range((coll, 1)..=(coll, u32::MAX)).count();
    if byte_len > chunks * CHUNK_BYTES {
        return None;
    }
    let mut bytes = Vec::with_capacity(byte_len);
    let mut i = 0u32;
    while bytes.len() < byte_len {
        let fe = map.get(&(coll, 1 + i))?;
        let take = (byte_len - bytes.len()).min(CHUNK_BYTES);
        bytes.extend_from_slice(&fe[..take]);
        i += 1;
    }
    Some(bytes)
}

/// Lay `text` into `map` at [`COLL_TEXT`]: a length leaf at key `0`, then one
/// 32-byte chunk per `1..`. Any prior [`COLL_TEXT`] leaves are cleared first so a
/// shrunk document leaves no stale chunk bound by the boundary.
pub fn text_into_heap(map: &mut BTreeMap<(u32, u32), FieldElement>, text: &str) {
    bytes_into_heap(map, COLL_TEXT, text.as_bytes());
}

/// Recover verbatim prose from a committed heap `map`'s [`COLL_TEXT`] leaves —
/// the inverse of [`text_into_heap`]. `None` when no length leaf is present (the
/// cell carries no umem-heap prose, so the caller can fall back) or when the
/// leaves are malformed (a missing chunk / forged length is refused, never
/// zero-filled). This is the reopen re-seed: a document's text is restored FROM
/// the umem boundary the light client trusts, not a sidecar.
pub fn text_from_heap(map: &BTreeMap<(u32, u32), FieldElement>) -> Option<String> {
    let bytes = bytes_from_heap(map, COLL_TEXT)?;
    Some(String::from_utf8_lossy(&bytes).into_owned())
}

// ─────────────────────────────────────────────────────────────────────────────
// The patch-history codec: a canonical, length-prefixed, domain-tagged byte
// serialization of a `History`, laid into COLL_HISTORY leaves. Canonical means
// the same history always encodes to the same bytes (BTree-free, order IS the
// data), so equal histories yield equal leaves and the boundary binds the chain
// verbatim. The decoder is strict: unknown op tags, truncation, or trailing
// garbage refuse (`None`) — and `DocHeapCell::reopen` additionally requires the
// decoded history to re-project to EXACTLY the given heap, so even a tampered
// byte that survives decoding is refused.
// ─────────────────────────────────────────────────────────────────────────────

/// Domain/version tag heading the serialized patch-history payload.
const HISTORY_DOMAIN: &[u8] = b"dregg-doc/history/v1";

/// Append a length-prefixed byte run.
fn enc_run(out: &mut Vec<u8>, b: &[u8]) {
    out.extend_from_slice(&(b.len() as u64).to_le_bytes());
    out.extend_from_slice(b);
}

/// Serialize one op: a tag byte, then its fields (fixed-width ids, length-
/// prefixed strings). The tags are part of the committed format (`v1`).
fn enc_op(out: &mut Vec<u8>, op: &Op) {
    match op {
        Op::Add { id, content, after } => {
            out.push(0);
            out.extend_from_slice(&id.0.to_le_bytes());
            enc_run(out, content.as_bytes());
            out.extend_from_slice(&after.0.to_le_bytes());
        }
        Op::Delete { id } => {
            out.push(1);
            out.extend_from_slice(&id.0.to_le_bytes());
        }
        Op::Connect { from, to } => {
            out.push(2);
            out.extend_from_slice(&from.0.to_le_bytes());
            out.extend_from_slice(&to.0.to_le_bytes());
        }
        Op::SetField {
            name,
            value,
            superseding,
        } => {
            out.push(3);
            enc_run(out, name.as_bytes());
            enc_run(out, value.as_bytes());
            out.push(u8::from(*superseding));
        }
        Op::Resurrect { id } => {
            out.push(4);
            out.extend_from_slice(&id.0.to_le_bytes());
        }
        Op::Disconnect { from, to } => {
            out.push(5);
            out.extend_from_slice(&from.0.to_le_bytes());
            out.extend_from_slice(&to.0.to_le_bytes());
        }
        Op::RetractField { name } => {
            out.push(6);
            enc_run(out, name.as_bytes());
        }
    }
}

/// The canonical byte serialization of a history: the domain tag, the patch
/// count, then each patch (author, op count, ops) in chain order.
fn history_to_bytes(h: &History) -> Vec<u8> {
    let mut out = Vec::new();
    enc_run(&mut out, HISTORY_DOMAIN);
    out.extend_from_slice(&(h.len() as u64).to_le_bytes());
    for p in h.patches() {
        out.extend_from_slice(&p.author.0.to_le_bytes());
        out.extend_from_slice(&(p.ops.len() as u64).to_le_bytes());
        for op in &p.ops {
            enc_op(&mut out, op);
        }
    }
    out
}

/// A strict little-endian cursor over untrusted bytes: every read is bounds-
/// checked and any shortfall is `None`.
struct Dec<'a> {
    bytes: &'a [u8],
    at: usize,
}

impl<'a> Dec<'a> {
    fn take(&mut self, n: usize) -> Option<&'a [u8]> {
        let end = self.at.checked_add(n)?;
        if end > self.bytes.len() {
            return None;
        }
        let s = &self.bytes[self.at..end];
        self.at = end;
        Some(s)
    }
    fn u8(&mut self) -> Option<u8> {
        Some(self.take(1)?[0])
    }
    fn u64(&mut self) -> Option<u64> {
        Some(u64::from_le_bytes(self.take(8)?.try_into().ok()?))
    }
    fn atom_id(&mut self) -> Option<AtomId> {
        Some(AtomId(u128::from_le_bytes(self.take(16)?.try_into().ok()?)))
    }
    fn run(&mut self) -> Option<&'a [u8]> {
        let n = self.u64()? as usize;
        self.take(n)
    }
    fn string(&mut self) -> Option<String> {
        String::from_utf8(self.run()?.to_vec()).ok()
    }
}

/// Decode a history from its canonical bytes — the strict inverse of
/// [`history_to_bytes`]. `None` on a wrong domain tag, an unknown op tag,
/// truncation, invalid UTF-8, or trailing garbage.
fn history_from_bytes(bytes: &[u8]) -> Option<History> {
    let mut d = Dec { bytes, at: 0 };
    if d.run()? != HISTORY_DOMAIN {
        return None;
    }
    let n_patches = d.u64()? as usize;
    let mut h = History::new();
    for _ in 0..n_patches {
        let author = Author(d.u64()?);
        let n_ops = d.u64()? as usize;
        let mut ops = Vec::new();
        for _ in 0..n_ops {
            ops.push(match d.u8()? {
                0 => Op::Add {
                    id: d.atom_id()?,
                    content: d.string()?,
                    after: d.atom_id()?,
                },
                1 => Op::Delete { id: d.atom_id()? },
                2 => Op::Connect {
                    from: d.atom_id()?,
                    to: d.atom_id()?,
                },
                3 => Op::SetField {
                    name: d.string()?,
                    value: d.string()?,
                    superseding: d.u8()? != 0,
                },
                4 => Op::Resurrect { id: d.atom_id()? },
                5 => Op::Disconnect {
                    from: d.atom_id()?,
                    to: d.atom_id()?,
                },
                6 => Op::RetractField { name: d.string()? },
                _ => return None,
            });
        }
        h.commit(Patch::by(author, ops));
    }
    if d.at != bytes.len() {
        return None; // trailing garbage is a malformed payload, refuse
    }
    Some(h)
}

/// Lay a document's patch-history into `map` at [`COLL_HISTORY`] (canonical
/// serialization, chunked like the prose). Any prior history leaves are cleared
/// first. After this, the heap root binds the whole chain.
pub fn history_into_heap(map: &mut BTreeMap<(u32, u32), FieldElement>, history: &History) {
    bytes_into_heap(map, COLL_HISTORY, &history_to_bytes(history));
}

/// Recover a document's patch-history from a committed heap `map`'s
/// [`COLL_HISTORY`] leaves — the inverse of [`history_into_heap`]. `None` when
/// the cell carries no committed history (e.g. a [`DocHeapCell::from_graph`]
/// snapshot document) or when the leaves are malformed. This is the reopen
/// re-seed for HISTORY: the chain is restored FROM the umem boundary the light
/// client trusts, so [`crate::blame`] on the replayed graph answers identically
/// to the never-closed document.
pub fn history_from_heap(map: &BTreeMap<(u32, u32), FieldElement>) -> Option<History> {
    history_from_bytes(&bytes_from_heap(map, COLL_HISTORY)?)
}

/// A document realized AS a cell riding the per-cell **umem-heap**.
///
/// Owns the [`Cell`] whose `heap_map` carries the document projection and whose
/// committed `heap_root` IS the document's commitment (the umem boundary), plus
/// the witness [`DocGraph`] the patch algebra reads (merge, content, blame). The
/// two are kept in lockstep: every edit re-projects the graph into the heap and
/// reseals the boundary root.
pub struct DocHeapCell {
    /// The document cell — its committed `heap_root` is the document commitment.
    cell: Cell,
    /// The witness graph the patch algebra reads; kept in lockstep with the
    /// cell's umem-heap projection.
    graph: DocGraph,
    /// The `dregg://` transclusion edges: embed key -> child cell `heap_root`.
    /// Re-laid into the heap on every reseal so the boundary binds every child
    /// boundary it cites.
    embeds: BTreeMap<u32, [u8; 32]>,
    /// The document's verbatim editor prose, bound into the heap at [`COLL_TEXT`]
    /// so a reopened document re-seeds its text from the committed boundary.
    /// `None` for the pure structured projection (the standalone commitment); the
    /// editor ride sets it via [`DocHeapCell::from_graph_with_text`] /
    /// [`DocHeapCell::set_text`].
    text: Option<String>,
    /// The document's patch-history, bound into the heap at [`COLL_HISTORY`] so
    /// a reopened document replays its chain from the committed boundary —
    /// blame answers identically across close/reopen. `Some` for history-
    /// carrying documents ([`DocHeapCell::new`] / [`DocHeapCell::from_history`]
    /// / [`DocHeapCell::reopen`]), where [`DocHeapCell::apply`] records every
    /// patch; `None` for graph-snapshot documents ([`DocHeapCell::from_graph`]),
    /// whose structured leaves are one-way digests and which therefore do NOT
    /// reopen with history.
    history: Option<History>,
}

impl DocHeapCell {
    /// Open a fresh document cell holding the empty document **with a committed
    /// (empty) patch-history**: every subsequent [`DocHeapCell::apply`] is
    /// recorded into the chain the boundary binds, so this document reopens
    /// with its full history ([`DocHeapCell::reopen`]).
    ///
    /// The cell's umem-heap is seeded with the empty-document projection (the
    /// `DocGraph::new()` ROOT-sentinel leaf) plus the empty-history leaves and
    /// resealed, so the commitment-equals-projection invariant holds from
    /// genesis.
    pub fn new(seed: u8) -> Self {
        Self::from_history(seed, History::new())
    }

    /// Open a document cell holding `graph`, projected into its umem-heap.
    ///
    /// This is the graph-SNAPSHOT ride: the boundary binds the projection (and
    /// its provenance, one-way), but no patch chain — the graph did not arrive
    /// as recorded patches, so there is honestly no history to commit, and the
    /// document does not [`DocHeapCell::reopen`]. Documents that should carry
    /// their history in the cell start from [`DocHeapCell::new`] /
    /// [`DocHeapCell::from_history`] instead.
    pub fn from_graph(seed: u8, graph: DocGraph) -> Self {
        Self::build(seed, graph, None)
    }

    /// Open a document cell holding a **patch-history** — the charter's
    /// "patch-history living IN the cell". The graph is the fold
    /// ([`History::replay`]) and the chain itself is serialized into
    /// [`COLL_HISTORY`] leaves, so the committed boundary binds content AND
    /// provenance chain, and [`DocHeapCell::reopen`] reconstructs both.
    pub fn from_history(seed: u8, history: History) -> Self {
        let graph = history.replay();
        Self::build(seed, graph, Some(history))
    }

    fn build(seed: u8, graph: DocGraph, history: Option<History>) -> Self {
        let mut pk = [0u8; 32];
        pk[0] = seed;
        pk[1] = 0xD0; // domain-tag the document cell's public key
        let cell = Cell::with_balance(pk, [0u8; 32], 0);
        let mut doc = DocHeapCell {
            cell,
            graph,
            embeds: BTreeMap::new(),
            text: None,
            history,
        };
        doc.reproject();
        doc
    }

    /// **Reopen a document FROM its committed umem-heap.** Recovers the patch-
    /// history ([`COLL_HISTORY`]), replays it into the witness graph, and
    /// recovers the prose ([`COLL_TEXT`]) and transclusion edges
    /// ([`COLL_EMBED`]) — then requires the reconstruction to re-project to
    /// EXACTLY the given heap. So a reopened document is the never-closed
    /// document: same commitment, same graph, same blame answers.
    ///
    /// `None` when the heap carries no committed history (a
    /// [`DocHeapCell::from_graph`] snapshot — its structured leaves are one-way
    /// digests, honestly not reopenable) or when ANY leaf is inconsistent with
    /// the replayed chain (a tampered history/content leaf is refused here, and
    /// independently fails the heap-root check against the trusted commitment).
    pub fn reopen(seed: u8, heap: &BTreeMap<(u32, u32), FieldElement>) -> Option<Self> {
        let history = history_from_heap(heap)?;
        let text = text_from_heap(heap);
        let embeds: BTreeMap<u32, [u8; 32]> = heap
            .iter()
            .filter(|&(&(coll, _), _)| coll == COLL_EMBED)
            .map(|(&(_, k), &v)| (k, v))
            .collect();
        let graph = history.replay();
        let mut doc = Self::build(seed, graph, Some(history));
        doc.embeds = embeds;
        doc.text = text;
        doc.reproject();
        // The tooth: the reconstruction must reproduce the given heap EXACTLY.
        // A tampered byte — even one that decodes cleanly (e.g. a forged
        // author inside the chain) — yields a projection that disagrees with
        // some leaf of the given heap, and is refused.
        if &doc.cell.state.heap_map != heap {
            return None;
        }
        Some(doc)
    }

    /// Open a document cell holding `graph` AND its verbatim editor `text`, both
    /// projected into the umem-heap. The boundary binds the structured projection
    /// (atoms/edges/fields, anti-forge) AND the recoverable prose ([`COLL_TEXT`]),
    /// so the document's commitment IS this `heap_root` and a reopen re-seeds the
    /// editor from it ([`text_from_heap`]).
    pub fn from_graph_with_text(seed: u8, graph: DocGraph, text: impl Into<String>) -> Self {
        let mut doc = Self::from_graph(seed, graph);
        doc.set_text(text);
        doc
    }

    /// Bind verbatim editor `text` into the umem-heap (collection [`COLL_TEXT`]),
    /// reseal the boundary, and return the new commitment. The prose becomes part
    /// of the committed `heap_root`, recoverable on reopen.
    pub fn set_text(&mut self, text: impl Into<String>) -> [u8; 32] {
        self.text = Some(text.into());
        self.reproject();
        self.commitment()
    }

    /// The document's verbatim editor prose, if this cell tracks it.
    pub fn text(&self) -> Option<&str> {
        self.text.as_deref()
    }

    /// The document cell id.
    pub fn cell_id(&self) -> CellId {
        self.cell.id()
    }

    /// The document cell (read-only) — the real substrate object whose committed
    /// `heap_root` is the commitment.
    pub fn cell(&self) -> &Cell {
        &self.cell
    }

    /// The witness graph the patch algebra reads.
    pub fn graph(&self) -> &DocGraph {
        &self.graph
    }

    /// The patch-history the committed boundary binds, if this document carries
    /// one (`None` for [`DocHeapCell::from_graph`] snapshots).
    pub fn history(&self) -> Option<&History> {
        self.history.as_ref()
    }

    /// **The document's commitment: the cell's committed umem-heap boundary
    /// `heap_root`.** This is the sorted-Poseidon2 root the light client trusts
    /// — the document as a sovereign, content-addressed umem (UMEM-PRIMITIVE §8).
    pub fn commitment(&self) -> [u8; 32] {
        self.cell.state.heap_root
    }

    /// Apply a patch — an edit. The patch is applied to the witness graph and —
    /// on a history-carrying document — **recorded as the new tip of the
    /// committed chain**; the graph, prose, and chain are re-projected into the
    /// cell's umem-heap and the boundary `heap_root` is resealed. The returned
    /// commitment is the document's new umem boundary, now binding this edit's
    /// place in the history.
    pub fn apply(&mut self, patch: Patch) -> [u8; 32] {
        patch.apply(&mut self.graph);
        if let Some(h) = &mut self.history {
            h.commit(patch);
        }
        self.reproject();
        self.commitment()
    }

    /// Transclude a child document by reference — a `dregg://` embed. Records a
    /// composable-umem edge: the child cell's `heap_root` becomes a leaf VALUE in
    /// this document's umem-heap (collection [`COLL_EMBED`], key `embed_key`), so
    /// the parent boundary binds the child boundary. Reseals and returns the new
    /// parent commitment.
    ///
    /// This is the witnessed `Pin::At` citation: the cited content is bound by
    /// its root under one CR floor, so a tampered child changes its root and the
    /// parent boundary changes — the citation cannot break or be forged silently.
    pub fn transclude(&mut self, embed_key: u32, child_root: [u8; 32]) -> [u8; 32] {
        self.embeds.insert(embed_key, child_root);
        self.reproject();
        self.commitment()
    }

    /// Membership witness for one document heap leaf against the committed
    /// boundary: returns the leaf value iff the current heap folds to the stored
    /// `heap_root` (so the value is genuinely bound by the boundary the light
    /// client trusts). Thin wrapper over [`dregg_cell`]'s `heap_root_membership`.
    pub fn heap_membership(&self, collection: u32, key: u32) -> Option<FieldElement> {
        self.cell.state.heap_root_membership(collection, key)
    }

    /// The invariant: the cell's committed umem boundary equals the canonical
    /// projection of the witness graph (plus its transclusion edges). When this
    /// holds, the document the algebra sees and the boundary the light client
    /// trusts are the same umem.
    pub fn boundary_matches_projection(&self) -> bool {
        self.cell.state.heap_root == compute_heap_root(&self.expected_heap())
            && self.cell.state.heap_map == self.expected_heap()
    }

    /// The canonical umem-heap this document projects to: the content projection
    /// (atoms/edges/fields, [`to_heap_map`]) plus the transclusion embed leaves,
    /// the recoverable prose, and — on a history-carrying document — the
    /// serialized patch chain ([`COLL_HISTORY`]).
    fn expected_heap(&self) -> BTreeMap<(u32, u32), FieldElement> {
        let mut map = to_heap_map(&self.graph);
        for (&k, &root) in &self.embeds {
            map.insert((COLL_EMBED, k), root);
        }
        if let Some(text) = &self.text {
            text_into_heap(&mut map, text);
        }
        if let Some(history) = &self.history {
            history_into_heap(&mut map, history);
        }
        map
    }

    /// Rebuild the cell's umem-heap from the witness graph + embeds and reseal the
    /// boundary `heap_root`. Rebuilding wholesale (rather than diffing) guarantees
    /// no stale leaf lingers: a dropped atom/edge/field/embed is simply absent from
    /// the fresh projection, so the boundary cannot bind content the document no
    /// longer carries.
    fn reproject(&mut self) {
        self.cell.state.heap_map = self.expected_heap();
        self.cell.state.reseal_heap_root();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::substrate::substrate_commit;
    use crate::{AtomId, Author, Op, blame, blame_summary, content, merge};
    use dregg_cell::empty_heap_root;

    /// A title-clash document: two authors set the canonical title differently =>
    /// a non-monotone field clash carrying both alternatives with provenance.
    fn title_clash() -> DocGraph {
        let base = DocGraph::new();
        let a = Patch::by(
            Author(1),
            [Op::SetField {
                name: "title".into(),
                value: "Cats".into(),
                superseding: false,
            }],
        )
        .apply_to(&base);
        let b = Patch::by(
            Author(2),
            [Op::SetField {
                name: "title".into(),
                value: "Dogs".into(),
                superseding: false,
            }],
        )
        .apply_to(&base);
        merge(&a, &b)
    }

    #[test]
    fn document_commits_as_a_umem_heap_boundary() {
        // A document realized as a cell: its commitment IS the cell's committed
        // umem `heap_root`, and that equals the canonical heap-root over the
        // document projection (the standalone `substrate_commit`). The document
        // is a sovereign umem.
        let doc = DocHeapCell::from_graph(7, title_clash());

        assert_eq!(
            doc.commitment(),
            doc.cell().state.heap_root,
            "the commitment IS the cell's committed umem boundary"
        );
        assert_eq!(
            doc.commitment(),
            substrate_commit(doc.graph()),
            "the boundary equals the canonical sorted-Poseidon2 heap root"
        );
        assert!(doc.boundary_matches_projection());

        // Non-vacuity: a populated document is not the empty-heap root.
        assert_ne!(
            doc.commitment(),
            empty_heap_root(),
            "a populated document is not the empty-heap boundary"
        );
        assert_ne!(
            doc.commitment(),
            DocHeapCell::new(7).commitment(),
            "the empty document has a distinct boundary"
        );
    }

    #[test]
    fn the_conflict_commitment_binds_both_alternatives_in_the_root() {
        // The conflict-as-state: BOTH live alternatives (and their provenance)
        // are bound in the umem boundary. Forging one alternative's author — even
        // while its rendered text is unchanged — changes the boundary root, and
        // dropping (hiding) an alternative changes it too. A light client cannot
        // be shown a forged or hidden conflict against the REAL umem boundary.
        let doc = DocHeapCell::from_graph(8, title_clash());
        let c0 = doc.commitment();

        // The two alternatives render as two values...
        let vals = |g: &DocGraph| -> Vec<String> {
            content(g)
                .field_conflicts()
                .flat_map(|c| c.alternatives.iter().map(|a| a.text.clone()))
                .collect()
        };
        let mut rendered = vals(doc.graph());
        rendered.sort();
        assert_eq!(rendered, vec!["Cats".to_string(), "Dogs".to_string()]);

        // ...both are heap leaves bound by the boundary (membership witness).
        assert!(
            doc.heap_membership(crate::COLL_FIELDS, 0).is_some()
                && doc.heap_membership(crate::COLL_FIELDS, 1).is_some(),
            "both clashing alternatives are leaves bound by the umem boundary"
        );

        // Forge one alternative's author: rendered text is identical, but the
        // umem boundary MUST change (provenance is inside the leaf preimage).
        let mut forged_graph = doc.graph().clone();
        forged_graph.forge_field_provenance("title", "Dogs", Author(7));
        let forged = DocHeapCell::from_graph(8, forged_graph);
        let mut forged_rendered = vals(forged.graph());
        forged_rendered.sort();
        assert_eq!(
            forged_rendered, rendered,
            "the forged conflict renders identically"
        );
        assert_ne!(
            forged.commitment(),
            c0,
            "forging an alternative's author changes the umem boundary"
        );

        // Drop one alternative: the boundary MUST change (a leaf vanished).
        let mut hidden_graph = doc.graph().clone();
        hidden_graph.drop_field_assignment("title", "Dogs");
        let hidden = DocHeapCell::from_graph(8, hidden_graph);
        assert_eq!(
            hidden.graph().field("title").len(),
            1,
            "one alternative hidden"
        );
        assert_ne!(
            hidden.commitment(),
            c0,
            "dropping an alternative changes the umem boundary"
        );
    }

    #[test]
    fn an_edit_moves_the_umem_boundary_and_a_leaf_is_bound() {
        // An edit (a patch) re-projects into the umem-heap and reseals: the
        // boundary moves, and the new content is a leaf genuinely bound by the
        // new boundary.
        let mut doc = DocHeapCell::new(9);
        let before = doc.commitment();

        let after = doc.apply(Patch::by(
            Author(1),
            [Patch::add(1, "Hello", AtomId::ROOT).1],
        ));
        assert_ne!(after, before, "the edit moved the umem boundary");
        assert!(doc.boundary_matches_projection());

        // The first atom is a leaf bound by the resealed boundary.
        assert!(
            doc.heap_membership(crate::COLL_ATOMS, 0).is_some(),
            "the edited content is a leaf bound by the umem boundary"
        );
        assert_eq!(content(doc.graph()).to_marked_string(), "Hello");
    }

    #[test]
    fn verbatim_prose_round_trips_through_the_umem_boundary() {
        // The editor ride: a document's verbatim prose is bound into the umem-heap
        // (COLL_TEXT) so the commitment IS the `heap_root` AND a reopen re-seeds the
        // text FROM the committed boundary. Setting text moves the boundary, and the
        // prose recovers byte-identically from the heap.
        let mut doc = DocHeapCell::from_graph(7, title_clash());
        let no_text = doc.commitment();
        assert_eq!(text_from_heap(&doc.cell().state.heap_map), None);

        let prose = "Cats vs Dogs — a clash with a long enough body to spill across several 32-byte umem chunks. ⊂( ◜◒◝ )⊃";
        let with_text = doc.set_text(prose);
        assert_ne!(with_text, no_text, "binding prose moved the umem boundary");
        assert_eq!(
            doc.commitment(),
            doc.cell().state.heap_root,
            "the commitment IS the cell's resealed umem boundary"
        );
        assert_eq!(
            text_from_heap(&doc.cell().state.heap_map).as_deref(),
            Some(prose),
            "prose recovers byte-identically from the committed boundary"
        );
        assert!(
            doc.boundary_matches_projection(),
            "the boundary still equals the canonical projection (graph + prose)"
        );

        // The structured projection survives: both clashing alternatives are still
        // bound (the anti-forge tooth) alongside the recoverable prose.
        assert!(
            doc.heap_membership(crate::COLL_FIELDS, 0).is_some()
                && doc.heap_membership(crate::COLL_FIELDS, 1).is_some(),
            "both clashing alternatives remain bound by the boundary"
        );

        // A shrunk document leaves no stale chunk: re-set to a short prose and the
        // recovered text is exactly the short one (trailing chunks cleared).
        let short = doc.set_text("hi");
        assert_ne!(short, with_text, "shrinking the prose moved the boundary");
        assert_eq!(
            text_from_heap(&doc.cell().state.heap_map).as_deref(),
            Some("hi"),
            "no stale chunk lingers after a shrink"
        );
    }

    #[test]
    fn from_graph_with_text_commits_graph_and_prose_together() {
        // The desktop's commit path: project graph + prose in one shot. The boundary
        // binds both, and equals re-deriving it via `set_text`.
        let a = DocHeapCell::from_graph_with_text(9, title_clash(), "the body");
        let mut b = DocHeapCell::from_graph(9, title_clash());
        b.set_text("the body");
        assert_eq!(a.commitment(), b.commitment());
        assert_eq!(
            text_from_heap(&a.cell().state.heap_map).as_deref(),
            Some("the body")
        );
        // Distinct prose over the same graph yields a distinct boundary.
        let c = DocHeapCell::from_graph_with_text(9, title_clash(), "a different body");
        assert_ne!(a.commitment(), c.commitment());
    }

    #[test]
    fn transclusion_rides_the_umem_heap_as_a_composable_boundary() {
        // `dregg://` transclusion is a composable umem: the parent's umem-heap
        // holds, at an embed key, a CHILD cell's boundary root. The parent
        // boundary binds the child boundary, so a tampered child (different root)
        // changes the parent boundary — a citation that cannot be forged.
        let mut parent = DocHeapCell::new(10);
        let no_embed = parent.commitment();

        // A child document with its own committed umem boundary.
        let child = DocHeapCell::from_graph(11, title_clash());
        let child_root = child.commitment();

        // Embed the child by reference: its boundary root becomes a leaf value.
        let with_child = parent.transclude(0, child_root);
        assert_ne!(
            with_child, no_embed,
            "embedding a child moves the parent boundary"
        );
        assert_eq!(
            parent.heap_membership(COLL_EMBED, 0),
            Some(child_root),
            "the embed leaf VALUE is the child cell's boundary root"
        );
        assert!(parent.boundary_matches_projection());

        // The witnessed-citation guarantee: a DIFFERENT child (a tampered or
        // evolved version, a different boundary root) changes the parent boundary
        // — the parent cannot silently cite a forged child.
        let mut tampered_child_graph = child.graph().clone();
        tampered_child_graph.forge_field_provenance("title", "Dogs", Author(99));
        let tampered_child = DocHeapCell::from_graph(11, tampered_child_graph);
        assert_ne!(
            tampered_child.commitment(),
            child_root,
            "the child boundary changed"
        );

        let mut parent2 = DocHeapCell::new(10);
        let with_tampered = parent2.transclude(0, tampered_child.commitment());
        assert_ne!(
            with_tampered, with_child,
            "citing a tampered child yields a different parent boundary"
        );
    }

    /// A history-carrying document with multi-author edits, prose, and an
    /// embed — the reopen fixture.
    fn edited_doc(seed: u8) -> DocHeapCell {
        let mut doc = DocHeapCell::new(seed);
        let (hello, add_hello) = Patch::add(1, "Hello, ", AtomId::ROOT);
        let (_world, add_world) = Patch::add(2, "world", hello);
        doc.apply(Patch::by(Author(1), [add_hello]));
        doc.apply(Patch::by(Author(2), [add_world]));
        doc.apply(Patch::by(
            Author(3),
            [Op::SetField {
                name: "title".into(),
                value: "Greeting".into(),
                superseding: false,
            }],
        ));
        doc.set_text("Hello, world");
        let child = DocHeapCell::from_graph(seed.wrapping_add(1), title_clash());
        doc.transclude(0, child.commitment());
        doc
    }

    #[test]
    fn reopening_a_doc_reconstructs_history_and_blame_answers_identically() {
        // THE PATCH-HISTORY LIVES IN THE CELL: close a document (keep only its
        // committed heap) and reopen it — the chain replays from the boundary,
        // so blame answers from the reopened document IDENTICALLY to the
        // never-closed one, and the commitment is the same root.
        let doc = edited_doc(20);
        let heap = doc.cell().state.heap_map.clone();

        let reopened = DocHeapCell::reopen(20, &heap).expect("a history-carrying doc reopens");

        // Same boundary, same projection invariant.
        assert_eq!(
            reopened.commitment(),
            doc.commitment(),
            "the reopened document IS the never-closed document (same root)"
        );
        assert!(reopened.boundary_matches_projection());

        // HISTORY reconstructed, not just text: the chain is equal patch-for-
        // patch, and blame over every range answers identically (per-atom
        // authorship — atom ids, contents, authors, patch ids — all equal).
        assert_eq!(reopened.history(), doc.history(), "the chain round-trips");
        assert_eq!(
            reopened.history().unwrap().len(),
            3,
            "non-vacuous: three recorded edits survive the close/reopen"
        );
        let (b_open, b_closed) = (blame(doc.graph()), blame(reopened.graph()));
        assert_eq!(b_open, b_closed, "blame answers identically after reopen");
        assert!(!b_open.is_empty(), "non-vacuous: blame has lines");
        assert_eq!(
            blame_summary(reopened.graph()),
            blame_summary(doc.graph()),
            "per-author tallies agree"
        );
        assert!(
            blame_summary(reopened.graph()).len() >= 2,
            "non-vacuous: multiple authors are attributed"
        );

        // Prose and embeds re-seed from the same boundary.
        assert_eq!(reopened.text(), doc.text());
        assert_eq!(
            reopened.heap_membership(COLL_EMBED, 0),
            doc.heap_membership(COLL_EMBED, 0)
        );

        // The reopened document keeps LIVING identically: the same further edit
        // moves both boundaries to the same place (and extends the same chain).
        let mut live = doc;
        let mut back = reopened;
        let more = Patch::by(Author(4), [Patch::add(9, "!", AtomId::ROOT).1]);
        assert_eq!(
            live.apply(more.clone()),
            back.apply(more),
            "the reopened doc evolves identically to the never-closed doc"
        );
        assert_eq!(live.history(), back.history());
    }

    #[test]
    fn a_fresh_doc_reopens_and_a_snapshot_doc_honestly_does_not() {
        // Genesis polarity: a brand-new document (empty chain) reopens.
        let fresh = DocHeapCell::new(30);
        let re = DocHeapCell::reopen(30, &fresh.cell().state.heap_map)
            .expect("a fresh history-carrying doc reopens");
        assert_eq!(re.commitment(), fresh.commitment());
        assert!(re.history().unwrap().is_empty());

        // A graph-SNAPSHOT document carries no chain: its structured leaves are
        // one-way digests, so it does not claim to reopen — and its commitment
        // is exactly the canonical projection (external `from_graph` users'
        // roots are unchanged by the history ride).
        let snap = DocHeapCell::from_graph(30, title_clash());
        assert!(snap.history().is_none());
        assert_eq!(snap.commitment(), substrate_commit(snap.graph()));
        assert!(
            DocHeapCell::reopen(30, &snap.cell().state.heap_map).is_none(),
            "no committed history leaf -> no history reopen (fall back to text re-seed)"
        );
    }

    #[test]
    fn a_tampered_history_leaf_fails_the_root_check_and_reopen_refuses() {
        // THE ANTI-FORGE TOOTH ON THE CHAIN, exhaustively: flip EVERY byte of
        // EVERY committed history leaf (the length leaf, its zero padding, the
        // payload chunks, the tail padding). Each flip must (a) change the heap
        // root — the tamper cannot hide under the trusted commitment — and (b)
        // be REFUSED by reopen, even when the flipped byte still decodes
        // cleanly: any surviving decode alters some patch's ops or author, so
        // its content-derived PatchId changes, and the provenance-bound
        // structured leaves (which commit that id) disagree with the replay.
        // Padding flips decode identically but re-encode canonically (zeros),
        // so the history leaves themselves disagree. Either way: refused.
        let doc = edited_doc(40);
        let c0 = doc.commitment();
        let heap = doc.cell().state.heap_map.clone();

        let history_keys: Vec<(u32, u32)> = heap
            .keys()
            .copied()
            .filter(|&(coll, _)| coll == COLL_HISTORY)
            .collect();
        assert!(
            history_keys.len() >= 2,
            "non-vacuous: the chain occupies a length leaf plus payload chunks"
        );

        for &key in &history_keys {
            for byte in 0..32 {
                let mut tampered = heap.clone();
                tampered.get_mut(&key).unwrap()[byte] ^= 0x01;
                assert_ne!(
                    compute_heap_root(&tampered),
                    c0,
                    "tampering history leaf {key:?} byte {byte} must fail the heap-root check"
                );
                assert!(
                    DocHeapCell::reopen(40, &tampered).is_none(),
                    "reopen must refuse the tampered history leaf {key:?} byte {byte}"
                );
            }
        }

        // Dropping the chain wholesale is also a visible tamper, not a silent
        // downgrade to a history-less document.
        let mut dropped = heap.clone();
        dropped.retain(|&(coll, _), _| coll != COLL_HISTORY);
        assert_ne!(compute_heap_root(&dropped), c0);
        assert!(DocHeapCell::reopen(40, &dropped).is_none());

        // And the untampered heap still reopens (the refusals above are teeth,
        // not a broken door).
        assert!(DocHeapCell::reopen(40, &heap).is_some());
    }

    #[test]
    fn the_boundary_binds_the_chain_order_not_just_the_fold() {
        // History is FIRST-CLASS state: two commuting edits applied in either
        // order fold to the SAME graph (same canonical content projection), but
        // the two documents carry DIFFERENT chains — and the umem boundary
        // distinguishes them. "How it got there" is committed, not just "what
        // it says".
        let p_add = Patch::by(Author(1), [Patch::add(1, "Hello", AtomId::ROOT).1]);
        let p_field = Patch::by(
            Author(2),
            [Op::SetField {
                name: "title".into(),
                value: "T".into(),
                superseding: false,
            }],
        );

        let mut ab = DocHeapCell::new(50);
        ab.apply(p_add.clone());
        ab.apply(p_field.clone());
        let mut ba = DocHeapCell::new(50);
        ba.apply(p_field);
        ba.apply(p_add);

        // Same fold: the canonical content projection is order-independent.
        assert_eq!(
            substrate_commit(ab.graph()),
            substrate_commit(ba.graph()),
            "commuting edits fold to the same canonical content projection"
        );
        assert_eq!(
            content(ab.graph()).to_marked_string(),
            content(ba.graph()).to_marked_string()
        );

        // Different chain: the boundary binds the order of the history.
        assert_ne!(
            ab.commitment(),
            ba.commitment(),
            "the umem boundary binds the CHAIN, so edit order is committed state"
        );

        // Determinism the other way: replaying the SAME chain reproduces the
        // SAME boundary (the serialization is canonical).
        let again = DocHeapCell::from_history(50, ab.history().unwrap().clone());
        assert_eq!(again.commitment(), ab.commitment());
    }
}
