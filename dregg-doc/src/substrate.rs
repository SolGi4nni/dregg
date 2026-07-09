//! The REAL cell-substrate ride — a [`DocGraph`] committed via the production
//! sorted-Poseidon2 heap root of the dregg cell substrate (NOT the in-crate
//! `DefaultHasher` stand-in of [`crate::commit`]).
//!
//! `DOCUMENT-LANGUAGE.md` §4.1 (the weld): a dreggverse document rides the cell
//! substrate as a **content-addressed heap** — atoms, order-edges, and field
//! assignments become heap leaves, and the document's commitment is the cell's
//! `heap_root`: the sorted-Poseidon2 binary Merkle tree the light client
//! actually trusts (the faithful commitment floor). This module is that weld.
//!
//! ## The projection
//!
//! [`to_heap_map`] writes the *whole* document into a single `(collection_id,
//! key) -> 32-byte value` heap (`dregg_cell::FieldElement`), with one
//! collection per section so an atom can never be confused for a field:
//!
//! - **`COLL_ATOMS` (0)** — one leaf per atom (id-order), value binds
//!   `id ‖ content ‖ status ‖ provenance`;
//! - **`COLL_EDGES` (1)** — one leaf per order-edge `(from, to)` (canonical
//!   from-then-to order), value binds `from ‖ to`;
//! - **`COLL_FIELDS` (2)** — one leaf per field assignment (name-then-value
//!   order), value binds `name ‖ value ‖ provenance`.
//!
//! Within each collection the **key is the sequential canonical index**
//! (`0, 1, 2, …` in `DocGraph`'s `BTreeMap`/`BTreeSet` iteration order). That is
//! exactly injective — distinct entries get distinct heap addresses, so no leaf
//! can silently overwrite another in the `BTreeMap` — and canonical, so the same
//! document always projects to the same heap regardless of construction order.
//!
//! ## The anti-forge tooth survives the projection
//!
//! Each leaf VALUE is a BLAKE3 digest that **binds provenance**. Forging one
//! conflict alternative's author changes that alternative's leaf value; dropping
//! an alternative changes the field count and shifts every later field key.
//! Either way some leaf changes, so [`substrate_commit`] — the production
//! `compute_heap_root` over the projected map — changes. A light client cannot
//! be shown a conflict that hides or forges an alternative against the REAL root.

use crate::atom::{Atom, AtomId, Provenance, Status};
use crate::composition::{AtomContent as EmbedAtomContent, ChildRef, EmbedRole, LayoutGraph, Pin};
use crate::graph::{DocGraph, FieldAssign};
use dregg_cell::{FieldElement, compute_heap_root};
use std::collections::BTreeMap;

/// Heap collection holding the document's atoms (one leaf per atom).
pub const COLL_ATOMS: u32 = 0;
/// Heap collection holding the document's order-edges (one leaf per edge).
pub const COLL_EDGES: u32 = 1;
/// Heap collection holding the document's field assignments (one leaf each).
pub const COLL_FIELDS: u32 = 2;
/// Heap collection holding a **composition layout's embed POINTERS** (one leaf
/// per embed-atom of a [`LayoutGraph`], the `Op::Embed` prototype of
/// `docs/deos/DOC-CELL-COMPOSITION.md` §2.1b/§3.3). Disjoint from
/// [`COLL_ATOMS`]=0 / [`COLL_EDGES`]=1 / [`COLL_FIELDS`]=2 — an embed pointer can
/// never collide with a text atom, an order-edge, or a field leaf (collection-tag
/// isolation, on top of the per-section preimage tag). This is what closes §1.4
/// of `docs/DREGG-DOCUMENT-FOUNDATION.md` at the substrate: the parent's
/// commitment binds the embed pointer (and, for a `Name`, the indirection
/// itself), so a light client following the reference verifies the SAME thing the
/// author committed.
///
/// NOTE this is the composition-layout embed collection; it is distinct in
/// purpose from `doc_heap`'s `COLL_EMBED`=3 (a `dregg://` transclusion edge whose
/// leaf VALUE is a resolved child cell's `heap_root` — binding the RESOLUTION,
/// where this binds the POINTER/indirection). They live in independent
/// projections and never share one heap map.
pub const COLL_EMBEDS: u32 = 3;

/// Domain tag separating the substrate projection's leaf preimages from every
/// other hash in the system.
const LEAF_DOMAIN: &[u8] = b"dregg-doc/substrate/leaf/v1";

/// A canonical, length-prefixed leaf-preimage builder. Mirrors the discipline of
/// [`crate::commit`]'s `Encoder`: every variable-length run is length-prefixed so
/// sections cannot be confused (no concatenation-ambiguity collision), and a
/// per-section tag domain-separates atom / edge / field leaves.
struct Leaf {
    bytes: Vec<u8>,
}

impl Leaf {
    /// Start a leaf preimage with the global domain tag and a per-section tag.
    fn new(section: &[u8]) -> Self {
        let mut l = Leaf { bytes: Vec::new() };
        l.run(LEAF_DOMAIN);
        l.run(section);
        l
    }

    /// A length-prefixed byte run (content / name / value / tag).
    fn run(&mut self, b: &[u8]) {
        self.bytes
            .extend_from_slice(&(b.len() as u64).to_le_bytes());
        self.bytes.extend_from_slice(b);
    }

    /// A fixed-width u128 (atom ids, patch ids).
    fn u128(&mut self, v: u128) {
        self.bytes.extend_from_slice(&v.to_le_bytes());
    }

    /// A fixed-width u64 (authors).
    fn u64(&mut self, v: u64) {
        self.bytes.extend_from_slice(&v.to_le_bytes());
    }

    /// One status byte.
    fn status(&mut self, s: Status) {
        self.bytes.push(match s {
            Status::Alive => 0,
            Status::Dead => 1,
        });
    }

    /// Provenance — author then patch id. THE binding that makes the anti-forge
    /// tooth bite through the projection.
    fn provenance(&mut self, p: Provenance) {
        self.u64(p.author.0);
        self.u128(p.patch.0);
    }

    /// Finalize the preimage into a 32-byte heap leaf value via BLAKE3 (the
    /// cryptographic digest already present in the substrate dep tree). The
    /// substrate's `fold_bytes32` is collision-resistant over the full 32 bytes,
    /// so distinct preimages yield distinct heap leaves with overwhelming
    /// probability.
    fn finish(self) -> FieldElement {
        *blake3::hash(&self.bytes).as_bytes()
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The SINGLE leaf scheme for the heap projection. [`to_heap_map`] is the ONE
// canonical document→heap projection: the standalone commitment AND the
// executor-driven ride ([`crate::executor_drive::ExecutorDrivenDoc`], which
// imports it as `project_graph`) lay leaves the same way, so the document's
// commitment and the cell it rides can never drift apart.
// ─────────────────────────────────────────────────────────────────────────────

/// The leaf value binding one atom: `id ‖ content ‖ status ‖ provenance`.
pub(crate) fn leaf_for_atom(a: &Atom) -> FieldElement {
    let mut leaf = Leaf::new(b"atom");
    leaf.u128(a.id.0);
    // The TYPE-tagged canonical bytes bind the atom's KIND into the heap leaf, so
    // the real Poseidon2 root binds the typed atom exactly as the in-crate commit
    // does (a structural node and a text run cannot alias).
    leaf.run(&a.content.canonical_bytes());
    leaf.status(a.status);
    leaf.provenance(a.provenance);
    leaf.finish()
}

/// The leaf value binding one order-edge: `from ‖ to`.
pub(crate) fn leaf_for_edge(from: AtomId, to: AtomId) -> FieldElement {
    let mut leaf = Leaf::new(b"edge");
    leaf.u128(from.0);
    leaf.u128(to.0);
    leaf.finish()
}

/// The leaf value binding one field assignment: `name ‖ value ‖ provenance`
/// (BOTH clashing alternatives' provenance bind here).
pub(crate) fn leaf_for_field(name: &str, a: &FieldAssign) -> FieldElement {
    let mut leaf = Leaf::new(b"field");
    leaf.run(name.as_bytes());
    leaf.run(a.value.as_bytes());
    leaf.provenance(a.provenance);
    leaf.finish()
}

/// Project a [`DocGraph`] into a real cell heap: a canonical `(collection_id,
/// key) -> 32-byte value` map binding *every* atom, edge, and field assignment
/// with its provenance.
///
/// The map is the exact input the production [`compute_heap_root`] consumes; see
/// the module docs for the per-collection scheme and why it is injective +
/// canonical + anti-forge.
pub fn to_heap_map(g: &DocGraph) -> BTreeMap<(u32, u32), FieldElement> {
    let mut map = BTreeMap::new();

    // ── Atoms (id-order; the value binds id ‖ content ‖ status ‖ provenance) ──
    for (idx, a) in g.atoms().enumerate() {
        map.insert((COLL_ATOMS, idx as u32), leaf_for_atom(a));
    }

    // ── Order-edges (from-id order; successors already BTreeSet-sorted) ───────
    let mut edge_idx = 0u32;
    let froms: Vec<_> = g.atoms().map(|a| a.id).collect();
    for from in froms {
        for to in g.successors(from) {
            map.insert((COLL_EDGES, edge_idx), leaf_for_edge(from, to));
            edge_idx += 1;
        }
    }

    // ── Field assignments (name order; assignments value-then-patch sorted).
    //    BOTH clashing alternatives' provenance is bound here. ─────────────────
    let mut field_idx = 0u32;
    let names: Vec<String> = g.field_names().map(|s| s.to_string()).collect();
    for name in names {
        for a in g.field(&name) {
            map.insert((COLL_FIELDS, field_idx), leaf_for_field(&name, a));
            field_idx += 1;
        }
    }

    map
}

/// The REAL document commitment: the production sorted-Poseidon2 heap root over
/// the projected cell heap. This is `compute_heap_root(&to_heap_map(g))` — the
/// faithful commitment a light client trusts, replacing the `DefaultHasher`
/// stand-in of [`crate::commit::commit`].
pub fn substrate_commit(g: &DocGraph) -> [u8; 32] {
    compute_heap_root(&to_heap_map(g))
}

// ─────────────────────────────────────────────────────────────────────────────
// THE COMPOSITION-LAYOUT PROJECTION — a parent document COMPOSED FROM cells
// (`composition::LayoutGraph`, the `Op::Embed` algebra) committed via the SAME
// sorted-Poseidon2 heap root, with a `COLL_EMBEDS` leaf per embed-atom binding
// the embed POINTER. This closes §1.4 of `docs/DREGG-DOCUMENT-FOUNDATION.md`
// (re-bindable-yet-verifiable references) at the substrate: a forged child
// pointer, a changed pin, or a swapped name/namespace/role changes the parent
// commitment; a `Name`'s RESOLUTION (name -> cell, done by the namespace at
// render) is deliberately NOT bound, so the light client follows the SAME name
// the author committed — the indirection is what is verified, not its (mutable)
// target.
// ─────────────────────────────────────────────────────────────────────────────

/// The self-describing, length-prefixed tag for an embed's layout role. A distinct
/// run per variant, so the role is bound canonically (a re-tagged embed changes
/// the leaf) and no two roles can alias.
fn role_tag(role: EmbedRole) -> &'static [u8] {
    match role {
        EmbedRole::Section => b"section",
        EmbedRole::Figure => b"figure",
        EmbedRole::Inline => b"inline",
        EmbedRole::Block => b"block",
        EmbedRole::Citation => b"citation",
    }
}

/// The leaf value binding one **text** layout-atom: `id ‖ text ‖ status ‖
/// provenance` (the `b"atom"` section — arity-separated from an embed leaf).
fn leaf_for_layout_text(id: AtomId, text: &str, status: Status, prov: Provenance) -> FieldElement {
    let mut leaf = Leaf::new(b"atom");
    leaf.u128(id.0);
    leaf.run(text.as_bytes());
    leaf.status(status);
    leaf.provenance(prov);
    leaf.finish()
}

/// The leaf value binding one **embed** layout-atom — the embed POINTER. The two
/// `ChildRef` arms are arm-tagged (`b"cell"` / `b"name"`) so they can never alias
/// each other, and the whole preimage carries the `b"embed"` section tag so an
/// embed leaf can never collide with an atom / edge / field leaf (arity /
/// domain separation, mirroring Storage's `objectLeaf` vs Merkle-node vs MMR-leaf
/// separation):
///
/// - [`ChildRef::Cell`]`(id, pin)` → `atom_id ‖ "cell" ‖ id ‖ pin ‖ role ‖
///   status ‖ provenance`.
/// - [`ChildRef::Name`]`(namespace, name, pin)` → `atom_id ‖ "name" ‖ namespace ‖
///   name ‖ pin ‖ role ‖ status ‖ provenance` — the INDIRECTION (namespace + name
///   + pin), NOT the resolved cell, so the commitment is stable across a rebind
///   yet binds the exact reference the author placed.
///
/// The [`Pin`] rides via its canonical [`Pin::key`] string (`"live"` /
/// `"at:<receipt>"`), the same form the pin-divergence field-clash uses — so
/// `Live↔At` or a different receipt changes the leaf.
pub(crate) fn leaf_for_embed(
    atom_id: AtomId,
    child: &ChildRef,
    role: EmbedRole,
    status: Status,
    prov: Provenance,
) -> FieldElement {
    let mut leaf = Leaf::new(b"embed");
    leaf.u128(atom_id.0);
    match child {
        // Identity arm: THIS exact child cell (its content-addressed id) + pin.
        ChildRef::Cell(cell, pin) => {
            leaf.run(b"cell");
            leaf.u128(cell.0);
            leaf.run(pin.key().as_bytes());
        }
        // Binding arm: the (namespace, name) INDIRECTION + pin. Bind what the
        // author wrote — the name — never the namespace's current resolution.
        ChildRef::Name(uri, pin) => {
            leaf.run(b"name");
            leaf.u128(uri.namespace.0);
            leaf.run(uri.name.as_bytes());
            leaf.run(pin.key().as_bytes());
        }
    }
    leaf.run(role_tag(role));
    leaf.status(status);
    leaf.provenance(prov);
    leaf.finish()
}

/// Project a composition [`LayoutGraph`] (a parent document composed from cells)
/// into a real cell heap: a canonical `(collection_id, key) -> 32-byte value`
/// map binding every layout atom, order-edge, AND — the new tooth — every embed
/// POINTER (its [`ChildRef`], pin, role, and provenance) under [`COLL_EMBEDS`].
///
/// Text atoms land in [`COLL_ATOMS`], edges in [`COLL_EDGES`], embed-atoms in
/// [`COLL_EMBEDS`] — three disjoint collections, each key the sequential
/// canonical index in `LayoutGraph`'s id/BTree iteration order (injective +
/// construction-order independent, exactly like [`to_heap_map`]).
pub fn layout_to_heap_map(layout: &LayoutGraph) -> BTreeMap<(u32, u32), FieldElement> {
    let mut map = BTreeMap::new();

    // ── Atoms: text -> COLL_ATOMS, embed -> COLL_EMBEDS (id-order; per-collection
    //    sequential keys so distinct entries get distinct heap addresses) ────────
    let mut atom_idx = 0u32;
    let mut embed_idx = 0u32;
    for a in layout.atoms() {
        match &a.content {
            EmbedAtomContent::Text(t) => {
                map.insert(
                    (COLL_ATOMS, atom_idx),
                    leaf_for_layout_text(a.id, t, a.status, a.provenance),
                );
                atom_idx += 1;
            }
            EmbedAtomContent::Embed(child, role) => {
                map.insert(
                    (COLL_EMBEDS, embed_idx),
                    leaf_for_embed(a.id, child, *role, a.status, a.provenance),
                );
                embed_idx += 1;
            }
        }
    }

    // ── Order-edges (from-id order; successors already BTreeSet-sorted) ──────────
    let mut edge_idx = 0u32;
    let froms: Vec<_> = layout.atoms().map(|a| a.id).collect();
    for from in froms {
        for to in layout.successors(from) {
            map.insert((COLL_EDGES, edge_idx), leaf_for_edge(from, to));
            edge_idx += 1;
        }
    }

    map
}

/// The REAL commitment of a parent document composed from cells: the production
/// sorted-Poseidon2 heap root over [`layout_to_heap_map`]. The parent's
/// commitment binds every embed pointer, so a light client following an embed
/// reference verifies the same pointer the author committed (§1.4 of
/// `docs/DREGG-DOCUMENT-FOUNDATION.md`, closed at the substrate).
pub fn layout_substrate_commit(layout: &LayoutGraph) -> [u8; 32] {
    compute_heap_root(&layout_to_heap_map(layout))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::*;

    /// A title-clash document (mirror of `tests::title_clash`): two authors set
    /// the canonical title differently => a non-monotone field clash carrying
    /// both alternatives with their provenance.
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
    fn substrate_commit_is_construction_order_independent() {
        // The same document built two ways (merge order swapped) commits equal
        // against the REAL Poseidon2 root: the BTree canonical projection is
        // construction-independent.
        let base = DocGraph::new();
        let a = Patch::by(Author(1), [Patch::add(1, "Hello ", AtomId::ROOT).1]).apply_to(&base);
        let h = Patch::add(1, "Hello ", AtomId::ROOT).0;
        let b = Patch::by(Author(2), [Patch::add(2, "world", h).1]).apply_to(&base);
        assert_eq!(
            substrate_commit(&merge(&a, &b)),
            substrate_commit(&merge(&b, &a)),
            "equal docs commit equal against the real heap root"
        );
    }

    #[test]
    fn substrate_commit_differs_for_distinct_docs() {
        // Sanity / non-vacuity: distinct documents get distinct real roots, and
        // a non-empty doc never collides with the empty-heap root.
        let empty = DocGraph::new();
        let clash = title_clash();
        assert_ne!(
            substrate_commit(&empty),
            substrate_commit(&clash),
            "distinct documents -> distinct real roots"
        );
        assert_ne!(
            substrate_commit(&clash),
            dregg_cell::empty_heap_root(),
            "a populated doc is not the empty-heap root"
        );
    }

    #[test]
    fn substrate_anti_forge_provenance() {
        // THE ANTI-FORGE TOOTH against the REAL root: a conflict whose
        // alternatives render IDENTICALLY but whose authorship is forged MUST
        // change the substrate commitment.
        let m = title_clash();
        let c0 = substrate_commit(&m);

        let mut forged = m.clone();
        forged.forge_field_provenance("title", "Dogs", Author(7)); // was Author(2)

        // The rendered alternative VALUES are byte-identical...
        let vals = |g: &DocGraph| -> Vec<String> {
            content(g)
                .field_conflicts()
                .flat_map(|c| c.alternatives.iter().map(|a| a.text.clone()))
                .collect::<Vec<_>>()
        };
        let (mut a, mut b) = (vals(&m), vals(&forged));
        a.sort();
        b.sort();
        assert_eq!(
            a, b,
            "the forged conflict renders the same alternative values"
        );

        // ...but the REAL heap root DIFFERS — the forge cannot hide under it.
        assert_ne!(
            substrate_commit(&forged),
            c0,
            "forging an alternative's author changes the REAL Poseidon2 root"
        );
    }

    #[test]
    fn substrate_anti_forge_dropped_alternative() {
        // Hiding an alternative (dropping one side of the clash) also changes the
        // REAL root: the dropped leaf is gone and every later field key shifts.
        let m = title_clash();
        let c0 = substrate_commit(&m);

        let mut hidden = m.clone();
        hidden.drop_field_assignment("title", "Dogs");
        assert_eq!(hidden.field("title").len(), 1, "one alternative hidden");

        assert_ne!(
            substrate_commit(&hidden),
            c0,
            "dropping an alternative changes the REAL Poseidon2 root"
        );
    }

    #[test]
    fn substrate_binds_prose_alternative_provenance() {
        // The prose-conflict analogue: two concurrent inserts by different
        // authors. The projection binds each atom's provenance, so a
        // structurally-equal doc with swapped authors does NOT commit equal
        // against the real root.
        let (base, _h, w) = {
            let mut g = DocGraph::new();
            let (h, op_h) = Patch::add(1, "Hello ", AtomId::ROOT);
            let (wid, op_w) = Patch::add(2, "world", h);
            Patch::by(Author(1), [op_h]).apply(&mut g);
            Patch::by(Author(1), [op_w]).apply(&mut g);
            (g, h, wid)
        };
        let a = Patch::by(Author(1), [Patch::add(30, " ALPHA", w).1]).apply_to(&base);
        let b = Patch::by(Author(2), [Patch::add(31, " BETA", w).1]).apply_to(&base);
        let m = merge(&a, &b);
        let c0 = substrate_commit(&m);

        // Rebuild with the alternatives' authors swapped (structurally equal).
        let a2 = Patch::by(Author(2), [Patch::add(30, " ALPHA", w).1]).apply_to(&base);
        let b2 = Patch::by(Author(1), [Patch::add(31, " BETA", w).1]).apply_to(&base);
        let swapped = merge(&a2, &b2);
        assert!(
            swapped.structural_eq(&m),
            "same content/edges (structural), only provenance differs"
        );
        assert_ne!(
            substrate_commit(&swapped),
            c0,
            "provenance is bound: swapped authors -> different REAL root"
        );
    }

    #[test]
    fn substrate_commit_stable_under_remerge() {
        // The REAL commitment of a conflicted doc is stable under idempotent
        // re-merge (the conflict is a STATE with a fixed real root).
        let m = title_clash();
        assert_eq!(substrate_commit(&merge(&m, &m)), substrate_commit(&m));
    }

    // ─────────────────────────────────────────────────────────────────────────
    // THE COLL_EMBEDS TOOTH — a parent document COMPOSED FROM cells commits its
    // embed POINTERS. Mirrors `graph.rs::forge_field_provenance`'s anti-forge
    // discipline: bind exactly the pointer the author placed, prove a forge moves
    // the REAL Poseidon2 root, and prove a `Name`'s RESOLUTION is deliberately NOT
    // bound (re-bindable yet verifiable — §1.4 DREGG-DOCUMENT-FOUNDATION.md).
    // ─────────────────────────────────────────────────────────────────────────
    use crate::composition::{
        AtomContent as EmbedAtomContent, CellId as EmbedCellId, ChildRef, ChildResolver, DreggUri,
        EmbedRole, LayoutAtom, LayoutGraph, MapResolver, Op as EmbedOp, Pin,
    };

    /// A parent layout with exactly ONE embed at a FIXED slot: same atom id, same
    /// provenance, same status, same after-edge for every call — so ONLY the
    /// `ChildRef`/`role` differs, and a commitment change is attributable purely
    /// to the embed leaf binding the POINTER (not to a shifted id/provenance).
    fn one_embed(child: ChildRef, role: EmbedRole) -> LayoutGraph {
        let mut l = LayoutGraph::new();
        let id = AtomId::derive(0x5107, "the-embed-slot");
        l.insert_atom(LayoutAtom {
            id,
            content: EmbedAtomContent::Embed(child, role),
            status: Status::Alive,
            provenance: Provenance {
                author: Author(1),
                patch: crate::atom::PatchId(1),
            },
        });
        l.connect_pub(AtomId::ROOT, id);
        l
    }

    #[test]
    fn layout_commit_is_construction_order_independent_and_non_vacuous() {
        // Sanity + non-vacuity: equal layouts commit equal against the REAL root;
        // a populated layout is neither the empty-heap root nor an empty layout.
        let a = one_embed(ChildRef::live(EmbedCellId(0xF1)), EmbedRole::Figure);
        let b = one_embed(ChildRef::live(EmbedCellId(0xF1)), EmbedRole::Figure);
        assert_eq!(
            layout_substrate_commit(&a),
            layout_substrate_commit(&b),
            "equal composed layouts -> equal REAL root"
        );
        assert_ne!(
            layout_substrate_commit(&a),
            dregg_cell::empty_heap_root(),
            "a populated layout is not the empty-heap root"
        );
        assert_ne!(
            layout_substrate_commit(&a),
            layout_substrate_commit(&LayoutGraph::new()),
            "an embed-bearing layout differs from the empty (ROOT-only) layout"
        );
    }

    #[test]
    fn embed_leaves_are_arity_separated_from_text_and_edges() {
        // The embed POINTER is a COLL_EMBEDS leaf; the ROOT text sentinel a
        // COLL_ATOMS leaf; the after-edge a COLL_EDGES leaf — three disjoint
        // collections, so an embed can never alias a text atom, an edge, or a
        // field (a pure layout has NO field leaves). This is the collection-tag
        // half of the arity separation; the per-section preimage tag (b"embed" vs
        // b"atom" vs b"edge") is the other half.
        let l = one_embed(ChildRef::live(EmbedCellId(0xF1)), EmbedRole::Figure);
        let map = layout_to_heap_map(&l);
        assert!(
            map.keys().any(|&(c, _)| c == COLL_EMBEDS),
            "the embed pointer is a COLL_EMBEDS leaf"
        );
        assert!(
            map.keys().any(|&(c, _)| c == COLL_ATOMS),
            "the ROOT text sentinel is a COLL_ATOMS leaf"
        );
        assert!(
            map.keys().any(|&(c, _)| c == COLL_EDGES),
            "the after-edge is a COLL_EDGES leaf"
        );
        assert!(
            !map.keys().any(|&(c, _)| c == COLL_FIELDS),
            "a pure composition layout carries no field leaves"
        );
    }

    #[test]
    fn forging_an_embed_child_cell_changes_the_parent_commitment() {
        // FORGE THE CHILD: same slot, same provenance, same pin, same role — only
        // the child CellId differs. A light client following the reference would be
        // shown a DIFFERENT child than the author embedded; the REAL root MUST
        // change so the forge cannot hide under the parent commitment.
        let honest = one_embed(ChildRef::live(EmbedCellId(0xF1)), EmbedRole::Figure);
        let c0 = layout_substrate_commit(&honest);
        let forged = one_embed(ChildRef::live(EmbedCellId(0xBAD)), EmbedRole::Figure);
        assert_ne!(
            layout_substrate_commit(&forged),
            c0,
            "forging the child CellId changes the parent commitment"
        );
    }

    #[test]
    fn forging_an_embed_pin_changes_the_parent_commitment() {
        // FORGE THE PIN: Live↔At and a different receipt each change the pointer
        // the author committed, so each changes the REAL root.
        let live = layout_substrate_commit(&one_embed(
            ChildRef::live(EmbedCellId(0xF1)),
            EmbedRole::Figure,
        ));
        let at7 = layout_substrate_commit(&one_embed(
            ChildRef::pinned(EmbedCellId(0xF1), 7),
            EmbedRole::Figure,
        ));
        let at9 = layout_substrate_commit(&one_embed(
            ChildRef::pinned(EmbedCellId(0xF1), 9),
            EmbedRole::Figure,
        ));
        assert_ne!(at7, live, "Live -> At(7) changes the parent commitment");
        assert_ne!(
            at7, at9,
            "a different pinned receipt changes the parent commitment"
        );
    }

    #[test]
    fn name_embed_binds_the_indirection_not_the_resolution() {
        // THE LOAD-BEARING DISTINCTION (§1.4 re-bindable-yet-verifiable):
        // a `Name` embed's commitment binds the INDIRECTION (namespace ‖ name ‖
        // pin ‖ role), NOT the cell the namespace currently resolves it to.
        let ns = EmbedCellId(0x115);
        let name_embed = |name: &str, pin: Pin, role: EmbedRole| -> LayoutGraph {
            one_embed(ChildRef::Name(DreggUri::new(ns, name), pin), role)
        };
        let base = name_embed("hero", Pin::Live, EmbedRole::Figure);
        let c0 = layout_substrate_commit(&base);

        // (A) The RESOLUTION is deliberately NOT bound. Two namespaces bind "hero"
        //     to DIFFERENT cells — a genuine rebind, the resolved cell moves — yet
        //     the parent commitment is UNCHANGED (the light client follows the SAME
        //     name; a swapped binding target does not forge the parent).
        let child = ChildRef::Name(DreggUri::new(ns, "hero"), Pin::Live);
        let to_a = MapResolver::default().with_name(ns, "hero", EmbedCellId(0xA));
        let to_b = MapResolver::default().with_name(ns, "hero", EmbedCellId(0xB));
        assert_ne!(
            to_a.resolved_cell(&child),
            to_b.resolved_cell(&child),
            "the rebind genuinely moves the resolution"
        );
        assert_eq!(
            layout_substrate_commit(&base),
            c0,
            "rebinding the name's TARGET leaves the parent commitment UNCHANGED (the indirection is bound, not the resolution)"
        );

        // (B) The INDIRECTION itself IS bound: a different NAME, NAMESPACE, PIN, or
        //     ROLE each changes the parent commitment (same fixed slot/provenance,
        //     so the change is attributable to the embed leaf binding the pointer).
        assert_ne!(
            layout_substrate_commit(&name_embed("villain", Pin::Live, EmbedRole::Figure)),
            c0,
            "a different NAME changes the parent commitment"
        );
        assert_ne!(
            layout_substrate_commit(&one_embed(
                ChildRef::Name(DreggUri::new(EmbedCellId(0x999), "hero"), Pin::Live),
                EmbedRole::Figure,
            )),
            c0,
            "a different NAMESPACE changes the parent commitment"
        );
        assert_ne!(
            layout_substrate_commit(&name_embed("hero", Pin::At(7), EmbedRole::Figure)),
            c0,
            "a different PIN changes the parent commitment"
        );
        assert_ne!(
            layout_substrate_commit(&name_embed("hero", Pin::Live, EmbedRole::Citation)),
            c0,
            "a different ROLE changes the parent commitment"
        );
    }

    #[test]
    fn cell_and_name_arms_do_not_alias() {
        // Arm-tag separation: a `Cell(id)` and a `Name` embed cannot collide even
        // when the CellId and the namespace share the same u128 — the b"cell" /
        // b"name" arm tags keep their leaf preimages disjoint.
        let shared = 0x42u128;
        let as_cell = one_embed(ChildRef::live(EmbedCellId(shared)), EmbedRole::Figure);
        let as_name = one_embed(
            ChildRef::Name(DreggUri::new(EmbedCellId(shared), ""), Pin::Live),
            EmbedRole::Figure,
        );
        assert_ne!(
            layout_substrate_commit(&as_cell),
            layout_substrate_commit(&as_name),
            "a Cell arm and a Name arm over the same u128 do not alias"
        );
    }

    #[test]
    fn two_authors_different_embeds_at_the_same_position_differ() {
        // Two authors each place a DIFFERENT embed right after ROOT (the same
        // layout position). The embed pointer is genuinely IN the root: the two
        // parent commitments differ — a forged child pointer cannot be swapped in
        // without moving the parent commitment.
        let mut a = LayoutGraph::new();
        a.apply_patch(
            Author(1),
            &[EmbedOp::Embed {
                id: AtomId::derive(1, "embed-a"),
                child: ChildRef::live(EmbedCellId(0xF1)),
                after: AtomId::ROOT,
                role: EmbedRole::Figure,
            }],
        );
        let mut b = LayoutGraph::new();
        b.apply_patch(
            Author(2),
            &[EmbedOp::Embed {
                id: AtomId::derive(1, "embed-b"),
                child: ChildRef::live(EmbedCellId(0xF2)),
                after: AtomId::ROOT,
                role: EmbedRole::Figure,
            }],
        );
        assert_ne!(
            layout_substrate_commit(&a),
            layout_substrate_commit(&b),
            "different embeds at the same layout position -> different parent commitments"
        );
    }
}
