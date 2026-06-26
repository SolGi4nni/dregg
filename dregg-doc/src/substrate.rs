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
use crate::graph::{DocGraph, FieldAssign};
use dregg_cell::{FieldElement, compute_heap_root};
use std::collections::BTreeMap;

/// Heap collection holding the document's atoms (one leaf per atom).
pub const COLL_ATOMS: u32 = 0;
/// Heap collection holding the document's order-edges (one leaf per edge).
pub const COLL_EDGES: u32 = 1;
/// Heap collection holding the document's field assignments (one leaf each).
pub const COLL_FIELDS: u32 = 2;

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
    leaf.run(a.content.as_bytes());
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
}
