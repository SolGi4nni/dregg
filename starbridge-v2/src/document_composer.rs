//! THE DOCUMENT COMPOSER — author a document *composed from cells*, by hand.
//!
//! `docs/deos/HYPERDREGGMEDIA-NOTES.md §6` (authoring surface #7): "add/reorder/role
//! embeds (`Op::Embed`/`Connect`/`Delete`) as turns on the document cell. (Compose a
//! doc from cells, by hand.)" This is the AUTHORING face to the embed algebra
//! [`crate::cell_transclusion`] / [`crate::desktop_doc`] already READ: there, a live
//! scene is *projected* into a composed document; HERE, a human composes one
//! deliberately — add an embed (a cell), reorder children, remove one, set a child's
//! role — each a real patch on the document cell's layout.
//!
//! ## It is the SAME machinery, pointed at authoring
//!
//! A composed document is a [`dregg_doc::composition::LayoutGraph`]: a graph of
//! embed-atoms (cell-pointers) plus order-edges. The composition grammar
//! ([`dregg_doc::composition::Op`]) is exactly four ops:
//!
//! | gesture | op | what it does |
//! |---|---|---|
//! | add an embed | [`Op::Embed`] | place a child cell as an embed-atom, ordered after a predecessor (a vertex + an order-edge — the additive insert) |
//! | reorder a child | [`Op::Order`] | add an order-edge `before -> child` (the layout resolution primitive; collapses a layout antichain into a chain — the `Connect` of the embed world) |
//! | remove a child | [`Op::Remove`] | tombstone the embed-atom (monotone `Alive -> Dead` — the child is gone from the render but RETAINED in the graph, provenanced + time-travellable: tombstoned-not-lost) |
//! | set a child's role | [`Op::Remove`] + [`Op::Embed`] | the role is part of the embed-atom's content ([`AtomContent::Embed(child, role)`]); changing it tombstones the old role-atom and embeds a fresh one for the SAME child at the SAME anchor — the citation (which cell) is preserved, the role reads back changed |
//!
//! Each gesture is committed by [`LayoutGraph::apply_patch`], which stamps every
//! written atom with the authoring [`Author`]'s [`Provenance`] (author + a
//! content-derived [`PatchId`]). That [`Provenance`] IS the receipt on the substrate:
//! a turn on the document cell whose effects write these embed-atoms, tombstones, and
//! order-edges, leaving a [`PatchId`] a light client can verify (the embed-atom carries
//! who placed it; a forged placement changes the document commitment — the anti-forge
//! tooth inherited from the document language, `docs/deos/DOC-CELL-COMPOSITION.md §3.3`).
//!
//! ## Roles
//!
//! [`Role`] mirrors [`dregg_doc::composition::EmbedRole`] exactly (`Section` / `Figure`
//! / `Inline` / `Citation`, plus `Block`), so a child placed as a Figure renders as a
//! figure, a Citation as a live cited cell. The role is layout metadata the algebra
//! commits to (which cell, in which order, in which role); *how* it paints is the
//! renderer's job (`docs/deos/DOC-CELL-COMPOSITION.md §7`).
//!
//! ## What this module IS and is NOT
//!
//! It is a gpui-free, `cargo test`-able **logic core** (like [`crate::desktop_doc`]'s
//! composed reading and [`crate::cell_transclusion`]): a [`DocumentComposer`] over a
//! [`LayoutGraph`], driving the REAL composition ops and reading the composed child
//! list back through the REAL membrane-gated fold ([`content_composed`]). No parallel
//! model — it reuses [`dregg_doc::composition`] verbatim.
//!
//! It is NOT a renderer (the role/order is committed; pixels are the servo pass), nor a
//! new op (every gesture is one of the four existing composition ops), nor a new
//! commitment (the receipt is the layout's stamped [`Provenance`] — the document
//! commitment binds it).

use dregg_doc::composition::{
    self, content_composed, AtomContent, ChildRef, EmbedRole, LayoutGraph, MapResolver, Op,
    Rendered, Viewer,
};
use dregg_doc::{AtomId, Author, PatchId, Provenance, Status};

pub use dregg_doc::composition::CellId as ChildCellId;

/// The seed domain for composer embed-atom ids — so a hand-authored embed never
/// collides with a desktop-window embed of the same cell ([`crate::desktop_doc`] uses
/// its own `DESKTOP_EMBED_SEED`). The embed-atom id keys on the CHILD CELL ONLY (not
/// the role), so the child's embed-atom identity is STABLE across a role change: a
/// `set_role` tombstones the old role-atom and embeds a fresh one, but both are
/// addressed from this same `(seed, cell)` derivation.
const COMPOSER_EMBED_SEED: u64 = 0xC0_4905_E1ED; // "composed"

/// The role an embedded child plays in the composed document — a thin, exhaustive
/// mirror of [`EmbedRole`] so the composer's public surface does not leak the
/// `dregg_doc` enum (and so a caller binds a role without depending on the crate).
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Role {
    /// A whole section.
    Section,
    /// A figure / illustration.
    Figure,
    /// An inline span.
    Inline,
    /// A block (e.g. the focused / active child).
    Block,
    /// A live cited cell (a citation that is itself a cell, not a value-quote).
    Citation,
}

impl Role {
    fn to_embed(self) -> EmbedRole {
        match self {
            Role::Section => EmbedRole::Section,
            Role::Figure => EmbedRole::Figure,
            Role::Inline => EmbedRole::Inline,
            Role::Block => EmbedRole::Block,
            Role::Citation => EmbedRole::Citation,
        }
    }

    fn from_embed(r: EmbedRole) -> Self {
        match r {
            EmbedRole::Section => Role::Section,
            EmbedRole::Figure => Role::Figure,
            EmbedRole::Inline => Role::Inline,
            EmbedRole::Block => Role::Block,
            EmbedRole::Citation => Role::Citation,
        }
    }
}

/// The receipt a composition gesture leaves — the [`Provenance`] the layout stamped
/// onto the atom(s) the gesture wrote (author + the content-derived [`PatchId`]). On
/// the substrate this IS the turn's receipt: a verifiable record that THIS author made
/// THIS edit to the document cell. Returned by every [`DocumentComposer`] gesture so an
/// edit is never silent — every gesture is a turn, every turn a receipt.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Receipt {
    /// Who authored the gesture.
    pub author: Author,
    /// The content-derived patch id (the turn's receipt id).
    pub patch: PatchId,
}

impl Receipt {
    fn from_prov(p: Provenance) -> Self {
        Receipt {
            author: p.author,
            patch: p.patch,
        }
    }
}

/// One composed child as the composer reads it back: which cell, at what role, who
/// placed it (the surviving provenance), and whether it is currently live in the
/// rendered document (a removed child is tombstoned — gone from the render but its
/// citation + provenance survive, so it is reported here too, marked not-live).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct ComposedChild {
    /// The embedded child cell (the citation — always present, even when removed).
    pub cell: ChildCellId,
    /// The embed-atom id (stable per child across a role change — the order target).
    pub atom: AtomId,
    /// The role the child currently plays.
    pub role: Role,
    /// Who placed this child (the surviving provenance — never forged).
    pub placed_by: Author,
    /// Whether the child is live in the rendered document (`false` => tombstoned: gone
    /// from the render but retained, provenanced, time-travellable).
    pub live: bool,
}

/// THE composer: a hand-authoring surface over a document cell's composition
/// [`LayoutGraph`]. You add embeds, reorder children, remove children, and set roles;
/// each gesture is a real composition patch on the layout, returning its [`Receipt`].
/// [`Self::children`] reads the composed list back through the REAL membrane-gated fold
/// (the document's own viewer); [`Self::roster`] reads the full roster including
/// tombstoned children (the time-travellable record).
#[derive(Clone, Debug)]
pub struct DocumentComposer {
    /// The document cell this composer authors (the host of the composition).
    host: ChildCellId,
    /// Who is authoring (binds into every gesture's provenance / receipt).
    author: Author,
    /// The composition layout graph — embed-atoms + order-edges (the REAL model).
    layout: LayoutGraph,
    /// The running predecessor for the NEXT add (the tail of the current chain), so a
    /// run of `add_embed`s appends in order without the caller threading anchors.
    tail: AtomId,
}

impl DocumentComposer {
    /// A fresh composer over an empty document cell `host`, authored by `author`.
    pub fn new(host: ChildCellId, author: Author) -> Self {
        DocumentComposer {
            host,
            author,
            layout: LayoutGraph::new(),
            tail: AtomId::ROOT,
        }
    }

    /// A composer that adopts an EXISTING composition layout (e.g. one a previous
    /// session authored, or a projected scene from [`crate::desktop_doc`]). Subsequent
    /// adds append after the current document tail.
    pub fn over(host: ChildCellId, author: Author, layout: LayoutGraph) -> Self {
        let tail = last_live_atom(&layout);
        DocumentComposer {
            host,
            author,
            layout,
            tail,
        }
    }

    /// The document cell this composer authors.
    pub fn host(&self) -> ChildCellId {
        self.host
    }

    /// The authoring identity.
    pub fn author(&self) -> Author {
        self.author
    }

    /// Read-only access to the underlying composition layout (for inspection, merge,
    /// time-travel, or projecting through a different viewer).
    pub fn layout(&self) -> &LayoutGraph {
        &self.layout
    }

    /// The embed-atom id a freshly-added `cell` is placed at (the initial-placement id,
    /// keyed on the cell). A later reorder / remove can target this directly — UNTIL a
    /// [`Self::set_role`] re-roles the cell, after which the live embed-atom is a fresh
    /// role-keyed atom (the old one is tombstoned). For a target that survives a re-role,
    /// use [`Self::live_atom`].
    pub fn embed_id(&self, cell: ChildCellId) -> AtomId {
        AtomId::derive(COMPOSER_EMBED_SEED, &format!("embed:{cell}"))
    }

    /// The CURRENT live embed-atom id for `cell` (the one a reorder / remove should
    /// target) — robust across a [`Self::set_role`] (which tombstones the old role-atom
    /// and mints a new live one). `None` if `cell` is not a live child.
    pub fn live_atom(&self, cell: ChildCellId) -> Option<AtomId> {
        embed_atoms(&self.layout)
            .into_iter()
            .find(|(id, _, c, _)| *c == cell && is_alive(&self.layout, *id))
            .map(|(id, _, _, _)| id)
    }

    /// **ADD AN EMBED** — place `cell` as a child of the document, in `role`, appended
    /// after the current tail (an [`Op::Embed`]: a fresh embed-atom + an order-edge).
    /// The child appears in [`Self::children`], provenanced with the composer's author.
    /// Returns the gesture's [`Receipt`] — a real patch on the document cell.
    pub fn add_embed(&mut self, cell: ChildCellId, role: Role) -> Receipt {
        let id = self.embed_id(cell);
        let after = self.tail;
        self.apply(&[Op::Embed {
            id,
            child: ChildRef::live(cell),
            after,
            role: role.to_embed(),
        }]);
        self.tail = id;
        self.receipt_of(id)
    }

    /// **ADD AN EMBED AT A FORK** — place `cell` as a child anchored after `after_cell`
    /// (or the HEAD if `None`), WITHOUT advancing the append tail. When two children are
    /// added at the SAME anchor this way, they form a layout FORK (an antichain — two
    /// children with no order between them), which [`Self::reorder`] resolves into a
    /// chain. This is how a hand-author lays out siblings whose order they want to set
    /// deliberately (vs. [`Self::add_embed`]'s straight append). Returns the [`Receipt`].
    pub fn add_embed_at(
        &mut self,
        cell: ChildCellId,
        after_cell: Option<ChildCellId>,
        role: Role,
    ) -> Receipt {
        let id = self.embed_id(cell);
        let after = match after_cell {
            Some(target) => self.live_atom(target).unwrap_or(AtomId::ROOT),
            None => AtomId::ROOT,
        };
        self.apply(&[Op::Embed {
            id,
            child: ChildRef::live(cell),
            after,
            role: role.to_embed(),
        }]);
        self.receipt_of(id)
    }

    /// **REORDER** — add the order constraint "`child` comes after `before`" (an
    /// [`Op::Order`]: the order-edge `before -> child`, the layout resolution primitive).
    ///
    /// The composition order is a PARTIAL order built additively, so reorder is a
    /// *constraint*, not a free move: ordering `before -> child` collapses a layout fork
    /// (two siblings added at the same anchor, an antichain) into a chain — the genuine
    /// authoring gesture for "I want THIS sibling before THAT one". It can never reverse
    /// an order already forced by a straight append-chain (that would be a contradiction
    /// the CRDT represents as a fork, never a silent overwrite). Pass [`AtomId::ROOT`] as
    /// `before` to constrain `child` to follow the head. Returns the [`Receipt`].
    pub fn reorder(&mut self, child: AtomId, before: AtomId) -> Receipt {
        self.apply(&[Op::Order {
            from: before,
            to: child,
        }]);
        self.receipt_of(child)
    }

    /// **REMOVE** — tombstone the embed-atom `child` (an [`Op::Remove`]: monotone
    /// `Alive -> Dead`). The child drops off [`Self::children`] (the live render) but is
    /// RETAINED in the graph — gone-but-provenanced, time-travellable, surfaced by
    /// [`Self::roster`] as not-live. Tombstoned, not lost. Returns the [`Receipt`].
    pub fn remove(&mut self, child: AtomId) -> Receipt {
        self.apply(&[Op::Remove { id: child }]);
        // If we removed the tail, re-derive the tail so the next add appends correctly.
        if self.tail == child {
            self.tail = last_live_atom(&self.layout);
        }
        self.receipt_of(child)
    }

    /// **SET A CHILD'S ROLE** — change the role `cell` plays (Section/Figure/Inline/
    /// Citation/Block). The role is part of the embed-atom's content
    /// ([`AtomContent::Embed(child, role)`]), so this tombstones the old role-atom and
    /// embeds a FRESH one for the SAME cell at the SAME anchor — the citation (which
    /// cell) and the order are preserved; only the role reads back changed. (The
    /// embed-atom id is keyed on the cell, not the role, so the child's identity is
    /// stable across the change.) Returns the [`Receipt`].
    ///
    /// Returns `None` if `cell` is not currently a live child of the document (nothing
    /// to re-role).
    pub fn set_role(&mut self, cell: ChildCellId, role: Role) -> Option<Receipt> {
        let id = self.embed_id(cell);
        // Find the live embed-atom's current anchor (its predecessor in the order), so
        // the re-embed lands in the SAME position.
        let atom = self.layout.atom(id)?;
        if !atom.is_alive() {
            return None;
        }
        let after = predecessor_of(&self.layout, id);
        // Tombstone the old role-atom, then re-embed the SAME cell+id with the new role
        // at the same anchor. `Op::Embed`'s apply is `entry().or_insert`, so the id must
        // be FREE for the new content to take — but the id is shared. We therefore mint
        // a role-distinct atom id for the new placement, keyed on cell+role, while the
        // OLD (cell-only) atom is tombstoned. The child's CITATION (cell) is preserved;
        // its order is re-threaded from the same predecessor.
        let new_id = AtomId::derive(
            COMPOSER_EMBED_SEED,
            &format!("embed:{}:role:{:?}", cell, role.to_embed()),
        );
        self.apply(&[
            Op::Remove { id },
            Op::Embed {
                id: new_id,
                child: ChildRef::live(cell),
                after,
                role: role.to_embed(),
            },
        ]);
        // The new atom becomes the canonical embed for this cell going forward; keep the
        // tail pointing at the document's true tail.
        if self.tail == id {
            self.tail = new_id;
        }
        Some(self.receipt_of(new_id))
    }

    /// **THE COMPOSED CHILD LIST** — the live children in document order, each with its
    /// cell, role, and who placed it. Read through the REAL membrane-gated fold
    /// ([`content_composed`]) over a `viewer` that clears every embedded cell (the
    /// owning author's own full-authority read). This is the composed reading the
    /// renderer paints.
    pub fn children(&self) -> Vec<ComposedChild> {
        let viewer = self.full_authority_viewer();
        let resolver = self.resolver();
        let rendered = content_composed(&self.layout, &viewer, &resolver);
        children_of(&rendered, &self.layout)
    }

    /// The full ROSTER — every embed-atom this composer ever placed, live OR tombstoned
    /// (the time-travellable record). A removed child appears here marked `live: false`,
    /// with its citation + provenance intact — the proof that remove is tombstone, not
    /// loss. In document order for the live ones; tombstoned ones follow.
    pub fn roster(&self) -> Vec<ComposedChild> {
        let live = self.children();
        let mut out = live.clone();
        let live_atoms: std::collections::BTreeSet<AtomId> = live.iter().map(|c| c.atom).collect();
        // Append the tombstoned embed-atoms (graph order by id — stable, deterministic).
        for (id, role, cell, prov) in embed_atoms(&self.layout) {
            if !live_atoms.contains(&id) {
                out.push(ComposedChild {
                    cell,
                    atom: id,
                    role: Role::from_embed(role),
                    placed_by: prov.author,
                    live: false,
                });
            }
        }
        out
    }

    /// The composed render for an arbitrary `viewer` (the per-viewer membrane: an
    /// out-of-cap child DARKENS — citation kept, content withheld — never forged). The
    /// author's own read is [`Self::children`]; this is the shareable reading.
    pub fn render_for(&self, viewer: &Viewer) -> Rendered {
        content_composed(&self.layout, viewer, &self.resolver())
    }

    // ── internals ────────────────────────────────────────────────────────────────

    /// Apply a gesture's ops to the layout under the composer's author (the REAL
    /// composition `apply_patch`, which stamps provenance = author + content-derived
    /// patch id).
    fn apply(&mut self, ops: &[Op]) {
        self.layout.apply_patch(self.author, ops);
    }

    /// The receipt an atom carries after a gesture — the provenance the layout stamped
    /// (author + the content-derived patch id). Reading it back off the atom is the
    /// honest move: the receipt IS what the document commitment binds.
    fn receipt_of(&self, id: AtomId) -> Receipt {
        match self.layout.atom(id) {
            Some(a) => Receipt::from_prov(a.provenance),
            // An order-only gesture (no atom written) still has a deterministic
            // provenance under the author; fall back to the host genesis-shaped author
            // stamp so a receipt is never absent.
            None => Receipt {
                author: self.author,
                patch: PatchId::GENESIS,
            },
        }
    }

    /// A viewer that clears every embedded cell (the owning author's full-authority
    /// read — no child darkens for them).
    fn full_authority_viewer(&self) -> Viewer {
        Viewer::able(
            embed_atoms(&self.layout)
                .into_iter()
                .map(|(_, _, cell, _)| cell),
        )
    }

    /// A resolver that renders each embedded cell as a one-atom leaf (the standalone
    /// shape — the substrate adapter plugs the real `dregg://` read + `Membrane::project`
    /// in, exactly as [`crate::cell_transclusion`] does for a single whole-cell embed).
    fn resolver(&self) -> MapResolver {
        let mut r = MapResolver::default();
        for (_, _, cell, _) in embed_atoms(&self.layout) {
            let mut g = LayoutGraph::new();
            let marker = AtomId::derive(0xC0_4EAF, &format!("content:{cell}"));
            g.insert_atom(composition::LayoutAtom {
                id: marker,
                content: AtomContent::Text(format!("cell {cell}")),
                status: Status::Alive,
                provenance: Provenance::GENESIS,
            });
            g.connect_pub(AtomId::ROOT, marker);
            r = r.with(cell, g);
        }
        r
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// THE LIVE COMPOSITION — the composer pointed at the real World
// ─────────────────────────────────────────────────────────────────────────────
//
// Everything above is the gpui-free logic core over `dregg_doc::composition`. What
// follows is the adapter that makes it an AUTHORING SURFACE OF THE LIVE WORLD, built
// to the same shape `crate::docuverse` gives the transclude gesture:
//
//   * a LEDGER GATE — an id the live World does not hold is never embedded
//     ([`LiveComposition::embed`] mirrors `Docuverse::publish_live`);
//   * a REFUSAL TYPE with a narration — nothing is written and the operator is told
//     ([`EmbedRefusal`] mirrors `docuverse::TranscludeRefusal`);
//   * a RENDERED BLOCK carrying full-width `dregg://` citations
//     ([`LiveComposition::block`] mirrors `docuverse::transclusion_line`), which is
//     what the desktop commits into the document cell's umem heap.
//
// THE CHILD POINTER IS THE CELL ID. `dregg_doc::composition::CellId` carries the same
// 32 bytes a substrate `dregg_types::CellId` does, so [`child_id`] is the identity
// injection and a `LiveComposition` holds no second copy of anything: the LayoutGraph
// alone names every child it embeds, at full width, and a reader with only the layout
// (a light client) recovers the same `dregg://` citation the desktop commits.
//
// ⚠ FLAG DAY (2026-08-01). `composition::CellId` was a `u128` and [`child_id`] NARROWED
// 256 bits onto 128 (BLAKE3 truncated to 16 bytes). Two containments existed solely to
// survive that and are now DELETED, not kept: a `LiveComposition::ids` side table that
// re-widened each pointer for rendering, and an `EmbedRefusal::ChildIdCollision` arm
// that refused a second cell landing on a bound pointer. Both are gone; the refusal
// variant is removed from the enum rather than retained as a no-op.
//
// What re-emits: nothing persisted — but every composition-layout commitment changes.
// `dregg_doc::substrate::leaf_for_embed` now binds 32 bytes where it bound 16, so every
// `layout_substrate_commit` root, and every document cell heap that carries a composed
// block, is a different value than it was. The devnet re-genesises; no reader holds an
// old layout root. Embed-atom ids move too (`AtomId::derive` now keys on the 64-hex id
// rather than the decimal `u128`), so a composition authored before this commit and a
// composition authored after do not share atom addresses.
//
// ⚠ STILL NARROW, and NOT this module's to widen: `dregg_doc::AtomId` is itself a
// `u128`, and an embed-atom's id is derived from the child id through it. The CHILD
// POINTER is now full width — it is what `Op::Embed` carries, what the commitment leaf
// binds, and what a citation renders — but the layout VERTEX addressing a child sits in
// a 128-bit space. That is a dregg-doc `AtomId` question (it addresses text atoms and
// order-edges too), measured and named here, not silently inherited.

use crate::world::World;

/// Why a composition gesture was REFUSED — the states in which the document's layout
/// must be left exactly as it was (no patch, no heap write, no revision turn).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EmbedRefusal {
    /// The id names no cell of the live World. **The anti-forge tooth**: a well-formed
    /// 32-byte id is not evidence of a cell, and `add_embed` would place any integer.
    NotALiveCell {
        /// The id that was dropped.
        cell: dregg_types::CellId,
    },
    /// The cell is not currently a live child of this document, so there is nothing to
    /// re-role / reorder / remove.
    NotAChild {
        /// The cell that was addressed.
        cell: dregg_types::CellId,
    },
}

impl EmbedRefusal {
    /// The line the desktop narrates — an honest "nothing was written and here is why",
    /// never a silent no-op. It never renders the refused id as a `dregg://` citation:
    /// a refusal must not mint an address.
    pub fn narration(&self) -> String {
        match self {
            EmbedRefusal::NotALiveCell { cell } => format!(
                "COMPOSE REFUSED: {} is not a cell of this World — there is nothing to \
                 embed. Nothing composed.",
                crate::reflect::short_hex(&cell.0)
            ),
            EmbedRefusal::NotAChild { cell } => format!(
                "COMPOSE REFUSED: {} is not a live child of this document — nothing to \
                 reorder, re-role or remove.",
                crate::reflect::short_hex(&cell.0)
            ),
        }
    }
}

/// One composed child at FULL substrate width — what the desktop paints and commits.
/// The `cell` here is the 32-byte id [`LiveComposition`] holds, not the layout's
/// narrowed pointer.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct LiveChild {
    /// The embedded child cell, full width.
    pub cell: dregg_types::CellId,
    /// The role it currently plays.
    pub role: Role,
    /// Who placed it (the surviving provenance — a fact off the layout).
    pub placed_by: Author,
    /// Live in the rendered document, or tombstoned (retained + provenanced).
    pub live: bool,
}

/// A substrate cell id AS the layout's child pointer — the identity injection, both
/// being the same 32 bytes. Lossless, so it needs no companion table and admits no
/// collision.
pub fn child_id(cell: &dregg_types::CellId) -> ChildCellId {
    ChildCellId(cell.0)
}

/// The layout child pointer's canonical bytes — **everything a reader holding only the
/// [`LayoutGraph`] knows about a child's identity**. The observation point for the
/// full-width gate: this must equal the substrate id's own 32 bytes, or the layout is
/// citing a cell it cannot name.
pub fn child_pointer_bytes(child: ChildCellId) -> Vec<u8> {
    child.0.to_vec()
}

/// **A composition of LIVE cells** — a [`DocumentComposer`] whose every embed passed
/// the live World's ledger gate, plus the full-width identity of each child.
#[derive(Clone, Debug)]
pub struct LiveComposition {
    composer: DocumentComposer,
}

impl LiveComposition {
    /// A fresh composition authored by `author` over the document cell `host`.
    pub fn new(host: dregg_types::CellId, author: Author) -> Self {
        LiveComposition {
            composer: DocumentComposer::new(child_id(&host), author),
        }
    }

    /// The underlying composer (read-only) — its layout, roster and receipts.
    pub fn composer(&self) -> &DocumentComposer {
        &self.composer
    }

    /// **THE LEDGER GATE** — `cell` must be a cell of the live World. Returns the
    /// pointer to place at.
    ///
    /// It used to also refuse a second cell narrowing onto a bound pointer; that arm
    /// existed only because the pointer was narrower than the id, and is deleted rather
    /// than kept as a check that can no longer fire.
    fn admit(&self, world: &World, cell: dregg_types::CellId) -> Result<ChildCellId, EmbedRefusal> {
        if world.ledger().get(&cell).is_none() {
            return Err(EmbedRefusal::NotALiveCell { cell });
        }
        Ok(child_id(&cell))
    }

    /// **ADD AN EMBED** of a LIVE cell, appended after the current tail. Refuses an id
    /// the World does not hold (nothing is placed).
    pub fn embed(
        &mut self,
        world: &World,
        cell: dregg_types::CellId,
        role: Role,
    ) -> Result<Receipt, EmbedRefusal> {
        let id = self.admit(world, cell)?;
        Ok(self.composer.add_embed(id, role))
    }

    /// **ADD AN EMBED AT A FORK** — anchored after `after` (or the head if `None`),
    /// without advancing the append tail. Two embeds at one anchor form a layout
    /// antichain that [`LiveComposition::reorder`] resolves.
    pub fn embed_at(
        &mut self,
        world: &World,
        cell: dregg_types::CellId,
        after: Option<dregg_types::CellId>,
        role: Role,
    ) -> Result<Receipt, EmbedRefusal> {
        let id = self.admit(world, cell)?;
        let anchor = match after {
            Some(a) => Some(self.child_of(a)?),
            None => None,
        };
        Ok(self.composer.add_embed_at(id, anchor, role))
    }

    /// The layout pointer of a cell that must currently be a LIVE child.
    fn child_of(&self, cell: dregg_types::CellId) -> Result<ChildCellId, EmbedRefusal> {
        let id = child_id(&cell);
        match self.composer.live_atom(id) {
            Some(_) => Ok(id),
            None => Err(EmbedRefusal::NotAChild { cell }),
        }
    }

    /// **REORDER** — constrain `child` to come after `before` (or after the head when
    /// `before` is `None`). Collapses a layout fork into the author's chosen chain.
    pub fn reorder(
        &mut self,
        child: dregg_types::CellId,
        before: Option<dregg_types::CellId>,
    ) -> Result<Receipt, EmbedRefusal> {
        let c = self.child_of(child)?;
        let child_atom = self
            .composer
            .live_atom(c)
            .ok_or(EmbedRefusal::NotAChild { cell: child })?;
        let before_atom = match before {
            Some(b) => {
                let bc = self.child_of(b)?;
                self.composer
                    .live_atom(bc)
                    .ok_or(EmbedRefusal::NotAChild { cell: b })?
            }
            None => AtomId::ROOT,
        };
        Ok(self.composer.reorder(child_atom, before_atom))
    }

    /// **REMOVE** — tombstone a live child (retained + provenanced, never deleted).
    pub fn remove(&mut self, cell: dregg_types::CellId) -> Result<Receipt, EmbedRefusal> {
        let c = self.child_of(cell)?;
        let atom = self
            .composer
            .live_atom(c)
            .ok_or(EmbedRefusal::NotAChild { cell })?;
        Ok(self.composer.remove(atom))
    }

    /// **SET A CHILD'S ROLE** — the citation is preserved, only the role reads back
    /// changed.
    pub fn set_role(
        &mut self,
        cell: dregg_types::CellId,
        role: Role,
    ) -> Result<Receipt, EmbedRefusal> {
        let c = self.child_of(cell)?;
        self.composer
            .set_role(c, role)
            .ok_or(EmbedRefusal::NotAChild { cell })
    }

    /// The LIVE children in document order, at full substrate width.
    pub fn children(&self) -> Vec<LiveChild> {
        self.composer
            .children()
            .into_iter()
            .map(live_child)
            .collect()
    }

    /// The full ROSTER — live children plus the tombstoned ones (retained, provenanced,
    /// time-travellable), at full substrate width.
    pub fn roster(&self) -> Vec<LiveChild> {
        self.composer.roster().into_iter().map(live_child).collect()
    }

    /// **THE COMPOSED BLOCK** — the composition rendered as document prose, carrying a
    /// FULL-WIDTH `dregg://<64-hex>` citation per child plus its role and the author
    /// who placed it. This is what the desktop splices into the document buffer and
    /// commits to the cell's umem heap, so the composition is a fact on the ledger
    /// rather than window state.
    ///
    /// Tombstoned children are rendered too, marked `tombstoned` — "retained, not
    /// deleted" is then a COMMITTED fact a reader can check, not an in-memory claim.
    pub fn block(&self) -> String {
        let roster = self.roster();
        let live = roster.iter().filter(|k| k.live).count();
        let dead = roster.len() - live;
        let mut out = format!("{BLOCK_OPEN} · {live} live · {dead} tombstoned}}\n");
        for k in roster.iter().filter(|k| k.live) {
            out.push_str(&format!(
                "{{compose dregg://{} · role: {:?} · placed by @{}}}\n",
                hex64(&k.cell),
                k.role,
                k.placed_by.0 & 0xffff
            ));
        }
        for k in roster.iter().filter(|k| !k.live) {
            out.push_str(&format!(
                "{{compose-removed dregg://{} · role: {:?} · placed by @{} · tombstoned}}\n",
                hex64(&k.cell),
                k.role,
                k.placed_by.0 & 0xffff
            ));
        }
        out.push_str(BLOCK_CLOSE);
        out.push('\n');
        out
    }
}

/// A composed child read at FULL substrate width — a total map, not a lookup. The
/// layout pointer IS the cell id, so there is nothing to restore and no case in which a
/// composed child cannot be named (the old `widen` consulted a side table and DROPPED a
/// child it had no entry for).
fn live_child(k: ComposedChild) -> LiveChild {
    LiveChild {
        cell: dregg_types::CellId(k.cell.0),
        role: k.role,
        placed_by: k.placed_by,
        live: k.live,
    }
}

/// The opening delimiter of the composed block inside a document's prose.
pub const BLOCK_OPEN: &str = "{composition";
/// The closing delimiter of the composed block.
pub const BLOCK_CLOSE: &str = "{/composition}";

/// A cell id at full 64-hex width — the citation anchor a composed embed carries.
fn hex64(cell: &dregg_types::CellId) -> String {
    cell.0.iter().map(|b| format!("{b:02x}")).collect()
}

/// **Splice a freshly-rendered composition `block` into `doc`'s prose**, replacing any
/// previous block. The composition is a projection of the layout, not an append log: a
/// reorder or a remove must REWRITE the region, never leave a stale reading beside the
/// live one. Returns the new document text.
pub fn splice_block(doc: &str, block: &str) -> String {
    let head = match doc.find(BLOCK_OPEN) {
        Some(i) => &doc[..i],
        None => doc,
    };
    let tail = match doc.find(BLOCK_OPEN) {
        Some(i) => match doc[i..].find(BLOCK_CLOSE) {
            Some(j) => {
                let end = i + j + BLOCK_CLOSE.len();
                doc[end..].strip_prefix('\n').unwrap_or(&doc[end..])
            }
            None => "",
        },
        None => "",
    };
    let mut out = String::with_capacity(head.len() + block.len() + tail.len());
    out.push_str(head);
    if !head.is_empty() && !head.ends_with('\n') {
        out.push('\n');
    }
    out.push_str(block);
    out.push_str(tail);
    out
}

/// The composed children read off a rendered fold, joined back to the layout for the
/// embed-atom id + provenance (the fold's `Segment::Embedded` carries role / placed_by /
/// resolved_cell; the atom id + the not-yet-needed live flag come from the graph).
fn children_of(rendered: &Rendered, layout: &LayoutGraph) -> Vec<ComposedChild> {
    let mut out = Vec::new();
    for seg in &rendered.segments {
        if let composition::Segment::Embedded {
            role,
            placed_by,
            resolved_cell: Some(cell),
            ..
        } = seg
        {
            // Recover the embed-atom id: the LIVE embed-atom whose ref resolves to this
            // cell (a composer keeps exactly one live embed per cell — a re-role
            // tombstones the old role-atom and the new one is the live one).
            let atom = embed_atoms(layout)
                .into_iter()
                .find(|(id, _, c, _)| *c == *cell && is_alive(layout, *id))
                .map(|(id, _, _, _)| id)
                .unwrap_or(AtomId::ROOT);
            out.push(ComposedChild {
                cell: *cell,
                atom,
                role: Role::from_embed(*role),
                placed_by: *placed_by,
                live: true,
            });
        }
    }
    out
}

/// All embed-atoms in the layout (live and tombstoned), as
/// `(atom_id, role, child_cell, provenance)`. Tombstoned ones included — the roster
/// reads them.
fn embed_atoms(layout: &LayoutGraph) -> Vec<(AtomId, EmbedRole, ChildCellId, Provenance)> {
    let mut out = Vec::new();
    // Walk every atom id we can reach by scanning the order graph from ROOT plus any
    // tombstoned ones (reachable via order-edges that conduct through tombstones). The
    // public surface gives us `atom(id)` + `successors(id)`; do a full graph crawl.
    let mut seen = std::collections::BTreeSet::new();
    let mut stack = vec![AtomId::ROOT];
    while let Some(id) = stack.pop() {
        if !seen.insert(id) {
            continue;
        }
        if let Some(a) = layout.atom(id) {
            if let AtomContent::Embed(ChildRef::Cell(cell, _), role) = &a.content {
                out.push((id, *role, *cell, a.provenance));
            } else if let AtomContent::Embed(ChildRef::Name(_, _), role) = &a.content {
                // A Name embed: report it with a sentinel cell id of 0 (the composer
                // places Cell embeds; Name is here for completeness so the crawl is total).
                let _ = role;
            }
        }
        for s in layout.successors(id) {
            stack.push(s);
        }
    }
    out.sort_by_key(|(id, _, _, _)| id.0);
    out.dedup_by_key(|(id, _, _, _)| *id);
    out
}

/// Is the embed-atom `id` alive in the layout?
fn is_alive(layout: &LayoutGraph, id: AtomId) -> bool {
    layout.atom(id).map(|a| a.is_alive()).unwrap_or(false)
}

/// The last live embed-atom in document order (the tail to append after). [`AtomId::ROOT`]
/// if the document is empty.
fn last_live_atom(layout: &LayoutGraph) -> AtomId {
    // Walk the order chain from ROOT, conducting through tombstones, taking the last
    // live atom reached.
    let mut cursor = AtomId::ROOT;
    let mut last = AtomId::ROOT;
    let mut seen = std::collections::BTreeSet::new();
    loop {
        // The live successor of the cursor (single-successor walk; a fork stops here —
        // appending after the clean prefix's tail is the right additive choice).
        let succ: Vec<AtomId> = layout.successors(cursor).collect();
        let next = match succ.first() {
            Some(n) => *n,
            None => return last,
        };
        if !seen.insert(next) {
            return last;
        }
        if is_alive(layout, next) {
            last = next;
        }
        cursor = next;
    }
}

/// The predecessor of `id` in the order graph (the atom whose order-edge points at it),
/// or [`AtomId::ROOT`] if it is anchored at the head / has no recorded predecessor.
fn predecessor_of(layout: &LayoutGraph, id: AtomId) -> AtomId {
    // Crawl the graph for the first atom that has `id` as an order-successor.
    let mut seen = std::collections::BTreeSet::new();
    let mut stack = vec![AtomId::ROOT];
    while let Some(cur) = stack.pop() {
        if !seen.insert(cur) {
            continue;
        }
        for s in layout.successors(cur) {
            if s == id {
                return cur;
            }
            stack.push(s);
        }
    }
    AtomId::ROOT
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cell(tag: u128) -> ChildCellId {
        ChildCellId::from_u128(tag)
    }

    fn doc() -> DocumentComposer {
        DocumentComposer::new(cell(0xD0C), Author(7))
    }

    // (1) ADD — two cell embeds list in order, each provenanced with the author.
    #[test]
    fn add_two_embeds_listed_in_order_with_provenance() {
        let mut c = doc();
        let intro = cell(0xA1);
        let figure = cell(0xB2);
        let r1 = c.add_embed(intro, Role::Section);
        let r2 = c.add_embed(figure, Role::Figure);

        // Each gesture left a real receipt (a patch on the document cell), authored by 7.
        assert_eq!(r1.author, Author(7));
        assert_eq!(r2.author, Author(7));
        assert_ne!(r1.patch, r2.patch, "distinct gestures => distinct receipts");

        let kids = c.children();
        assert_eq!(kids.len(), 2, "both embeds are live children");
        // IN ORDER: intro first, figure second (append order is document order).
        assert_eq!(kids[0].cell, intro);
        assert_eq!(kids[1].cell, figure);
        // The role each was placed in reads back.
        assert_eq!(kids[0].role, Role::Section);
        assert_eq!(kids[1].role, Role::Figure);
        // PROVENANCE: each child carries who placed it (Author 7 — never forged).
        assert!(kids.iter().all(|k| k.placed_by == Author(7)));
        assert!(kids.iter().all(|k| k.live));
    }

    // (2) REORDER — two siblings placed at the SAME anchor form a fork; the reorder
    //     constraint resolves them into a definite order (the layout resolution
    //     primitive doing real work).
    #[test]
    fn reorder_resolves_a_layout_fork_into_an_order() {
        let mut c = doc();
        let a = cell(0xA1);
        let b = cell(0xB2);
        // Place BOTH at the head (after ROOT) — a layout fork (an antichain, no order
        // between them). The clean prefix is empty, so neither leads yet.
        c.add_embed_at(a, None, Role::Section);
        c.add_embed_at(b, None, Role::Section);
        assert!(
            c.children().is_empty(),
            "two siblings at one anchor are a fork — the walk stops at the (empty) clean prefix"
        );
        // The layout records the fork (a first-class conflict state, not a loss).
        assert!(
            c.layout().layout_conflict_heads().is_some(),
            "the fork is surfaced as a layout antichain"
        );

        // REORDER: constrain a to come before b (order a -> b). The fork collapses into
        // a chain — a, then b.
        let a_atom = c.embed_id(a);
        let b_atom = c.embed_id(b);
        let receipt = c.reorder(b_atom, a_atom);
        assert_eq!(
            receipt.author,
            Author(7),
            "the reorder is a receipted gesture"
        );
        let order: Vec<ChildCellId> = c.children().iter().map(|k| k.cell).collect();
        assert_eq!(order, vec![a, b], "the reorder resolved the fork: a then b");

        // A DIFFERENT reorder choice yields the OTHER order — author's deliberate pick.
        let mut c2 = doc();
        c2.add_embed_at(a, None, Role::Section);
        c2.add_embed_at(b, None, Role::Section);
        c2.reorder(c2.embed_id(a), c2.embed_id(b)); // order b -> a
        assert_eq!(
            c2.children().iter().map(|k| k.cell).collect::<Vec<_>>(),
            vec![b, a],
            "ordering b before a yields b, a — the order is the author's choice"
        );
    }

    // (3) REMOVE — a removed child is gone from the live render but provenanced + retained.
    #[test]
    fn remove_tombstones_not_loses() {
        let mut c = doc();
        let a = cell(0xA1);
        let b = cell(0xB2);
        c.add_embed(a, Role::Section);
        c.add_embed(b, Role::Figure);

        let a_atom = c.embed_id(a);
        let receipt = c.remove(a_atom);
        assert_eq!(receipt.author, Author(7), "remove is a receipted gesture");

        // GONE from the live render: only b remains a child.
        let kids = c.children();
        assert_eq!(kids.len(), 1, "the removed child drops off the live render");
        assert_eq!(
            kids[0].cell, b,
            "b survives; the order conducts through the tombstone"
        );

        // BUT RETAINED — the roster still carries a, marked not-live, with its provenance.
        let roster = c.roster();
        let removed = roster
            .iter()
            .find(|k| k.cell == a)
            .expect("the removed child is RETAINED in the roster (tombstoned, not lost)");
        assert!(!removed.live, "the removed child is tombstoned (not live)");
        assert_eq!(
            removed.placed_by,
            Author(7),
            "the removed child keeps its provenance — gone-but-provenanced, never silently lost"
        );
    }

    // (4) SET_ROLE — a child's role reads back changed; the citation is preserved.
    #[test]
    fn set_role_reads_back_and_preserves_citation() {
        let mut c = doc();
        let fig = cell(0xF1);
        c.add_embed(fig, Role::Section); // placed as a Section first
        assert_eq!(c.children()[0].role, Role::Section);

        // Re-role it to a Figure.
        let receipt = c
            .set_role(fig, Role::Figure)
            .expect("re-roling a live child succeeds");
        assert_eq!(receipt.author, Author(7), "set_role is a receipted gesture");

        let kids = c.children();
        assert_eq!(
            kids.len(),
            1,
            "still exactly one live child (re-roled, not duplicated)"
        );
        // THE ROLE READS BACK CHANGED.
        assert_eq!(kids[0].role, Role::Figure, "the role reads back as Figure");
        // THE CITATION (which cell) IS PRESERVED.
        assert_eq!(kids[0].cell, fig, "the child cell is unchanged");
        assert_eq!(kids[0].placed_by, Author(7));

        // Re-roling a cell that is not a child returns None (nothing to re-role).
        assert!(
            c.set_role(cell(0xDEAD), Role::Citation).is_none(),
            "re-roling a non-child is a no-op (None)"
        );
    }

    // (5) EVERY GESTURE IS A RECEIPTED PATCH — the composition produces a real,
    //     attributed patch on the document cell at each step.
    #[test]
    fn every_gesture_is_a_receipted_patch() {
        let mut c = doc();
        let a = cell(0xA1);
        let b = cell(0xB2);

        let r_add_a = c.add_embed(a, Role::Section);
        let r_add_b = c.add_embed(b, Role::Section);
        let r_reorder = c.reorder(c.embed_id(b), AtomId::ROOT);
        let r_role = c.set_role(a, Role::Citation).expect("re-role a");
        let r_remove = c.remove(c.embed_id(b));

        // Every receipt is authored by the composer (each is a turn on the document cell).
        for r in [r_add_a, r_add_b, r_reorder, r_role, r_remove] {
            assert_eq!(
                r.author,
                Author(7),
                "every gesture is attributed to the author"
            );
        }
        // The adds are distinct turns (distinct content => distinct patch ids).
        assert_ne!(r_add_a.patch, r_add_b.patch);
    }

    // (6) A LONGER COMPOSITION — three children, a remove in the middle, a re-role: the
    //     composed list stays coherent and ordered throughout.
    #[test]
    fn a_three_child_composition_stays_coherent() {
        let mut c = doc();
        let (s, f, q) = (cell(1), cell(2), cell(3));
        c.add_embed(s, Role::Section);
        c.add_embed(f, Role::Figure);
        c.add_embed(q, Role::Citation);
        assert_eq!(
            c.children().iter().map(|k| k.cell).collect::<Vec<_>>(),
            vec![s, f, q],
            "three children in order"
        );

        // Remove the middle (the figure): the order conducts through it.
        c.remove(c.embed_id(f));
        assert_eq!(
            c.children().iter().map(|k| k.cell).collect::<Vec<_>>(),
            vec![s, q],
            "the middle child drops; s and q close up"
        );

        // Re-role the citation to a section: still two children, order preserved.
        c.set_role(q, Role::Section).expect("re-role q");
        let kids = c.children();
        assert_eq!(kids.iter().map(|k| k.cell).collect::<Vec<_>>(), vec![s, q]);
        assert_eq!(kids[1].role, Role::Section, "q is now a section");

        // The figure is still RETAINED (tombstoned) in the roster.
        assert!(
            c.roster().iter().any(|k| k.cell == f && !k.live),
            "the removed figure is retained, tombstoned"
        );
    }
}
