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
//! This is an **app/integration-layer** ride: it projects into and reseals the
//! cell's existing umem-heap. It introduces **no new kernel effect** — the writes
//! are ordinary heap writes the substrate already commits.

use crate::graph::DocGraph;
use crate::patch::Patch;
use crate::substrate::to_heap_map;
use dregg_cell::{Cell, CellId, FieldElement, compute_heap_root};
use std::collections::BTreeMap;

/// Heap collection holding `dregg://` transclusion edges. Each leaf VALUE is a
/// child cell's committed `heap_root` — a composable-umem boundary embedded by
/// reference. Disjoint from the document-content collections
/// ([`crate::COLL_ATOMS`]=0 / [`crate::COLL_EDGES`]=1 / [`crate::COLL_FIELDS`]=2),
/// so an embed can never be confused for document content (umem tag isolation).
pub const COLL_EMBED: u32 = 3;

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
}

impl DocHeapCell {
    /// Open a fresh document cell holding the empty document.
    ///
    /// The cell's umem-heap is seeded with the empty-document projection (the
    /// `DocGraph::new()` ROOT-sentinel leaf) and resealed, so the
    /// commitment-equals-projection invariant holds from genesis.
    pub fn new(seed: u8) -> Self {
        Self::from_graph(seed, DocGraph::new())
    }

    /// Open a document cell holding `graph`, projected into its umem-heap.
    pub fn from_graph(seed: u8, graph: DocGraph) -> Self {
        let mut pk = [0u8; 32];
        pk[0] = seed;
        pk[1] = 0xD0; // domain-tag the document cell's public key
        let cell = Cell::with_balance(pk, [0u8; 32], 0);
        let mut doc = DocHeapCell {
            cell,
            graph,
            embeds: BTreeMap::new(),
        };
        doc.reproject();
        doc
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

    /// **The document's commitment: the cell's committed umem-heap boundary
    /// `heap_root`.** This is the sorted-Poseidon2 root the light client trusts
    /// — the document as a sovereign, content-addressed umem (UMEM-PRIMITIVE §8).
    pub fn commitment(&self) -> [u8; 32] {
        self.cell.state.heap_root
    }

    /// Apply a patch — an edit. The patch is applied to the witness graph, the
    /// graph is re-projected into the cell's umem-heap, and the boundary
    /// `heap_root` is resealed. The returned commitment is the document's new
    /// umem boundary.
    pub fn apply(&mut self, patch: Patch) -> [u8; 32] {
        patch.apply(&mut self.graph);
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
    /// (atoms/edges/fields, [`to_heap_map`]) plus the transclusion embed leaves.
    fn expected_heap(&self) -> BTreeMap<(u32, u32), FieldElement> {
        let mut map = to_heap_map(&self.graph);
        for (&k, &root) in &self.embeds {
            map.insert((COLL_EMBED, k), root);
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
    use crate::{AtomId, Author, Op, content, merge};
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
}
