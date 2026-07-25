//! **A deos document persists to the REAL committed cell umem-heap, not a sidecar.**
//!
//! A dreggverse document IS a cell, and its commitment IS that cell's committed
//! `heap_root` — the per-cell universal-memory boundary (`docs/deos/UMEM-PRIMITIVE.md`
//! §8; `dregg_doc::DocHeapCell`). The desktop projects a document (its atom/edge/field
//! graph AND its verbatim prose) into the cell's `heap_map` and reseals `heap_root`
//! out-of-band (`World::set_cell_heap` — `set_heap` / `reseal_heap_root`, no kernel
//! effect). This test drives that exact project → reseal → read-back path through the
//! real `World` (no gpui), proving:
//!   * a doc edit commits the document INTO the cell's umem-heap (its `heap_root`
//!     boundary MOVES and IS the commitment — `DocHeapCell::commitment()`);
//!   * the prose READS BACK from the committed heap (`dregg_doc::text_from_heap`), and
//!     the projection is genuinely bound by `heap_root` (the membership witness);
//!   * a shrunk revision leaves no stale committed leaf (the heap is rebuilt wholesale);
//!   * reopen restores FROM THE LEDGER's umem boundary (a fresh read, no sidecar).
//!
//! The desktop's `commit_doc_to_umem_heap` / `read_doc_from_heap`
//! (`starbridge-v2/src/deos_desktop/mod.rs`) are thin wrappers over exactly this.

use dregg_doc::{Author, Doc, DocHeapCell, Granularity};
use starbridge_v2::world::demo_world;

/// The committed umem boundary the desktop projects for a document on `cell`: the
/// graph + verbatim prose laid into the cell's `heap_map`. Mirrors
/// `DeosDesktop::commit_doc_to_umem_heap` (which builds the SAME `DocHeapCell`).
fn project_doc(cell: dregg_types::CellId, text: &str) -> DocHeapCell {
    // Diff the prose into the patch core exactly as the editor does, then project the
    // resulting graph + verbatim prose into a document cell's umem-heap.
    let mut doc = Doc::new(Granularity::Word);
    doc.edit(Author(cell.as_bytes()[0] as u64), text);
    DocHeapCell::from_graph_with_text(cell.as_bytes()[0], doc.history().replay(), text)
}

/// Read prose back out of a cell's committed umem-heap — the read
/// `read_doc_from_heap` does off the live ledger's `heap_map`.
fn read_doc(w: &starbridge_v2::world::World, cell: &dregg_types::CellId) -> Option<String> {
    let state = &w.ledger().get(cell)?.state;
    dregg_doc::text_from_heap(&state.heap_map)
}

#[test]
fn document_commits_to_committed_cell_umem_heap_and_reopens_from_ledger() {
    let (mut w, [treasury, _service, _user]) = demo_world();
    let cell = treasury;

    // No committed document yet — the umem-heap carries no prose.
    assert!(
        read_doc(&w, &cell).is_none(),
        "a fresh cell has no committed document"
    );
    // `state.heap_root` is a wide `Faithful8`; `to_bytes32` is its canonical, exactly-invertible
    // 32-byte packing — the SAME projection `DocHeapCell::commitment()` publishes, so every
    // boundary == commitment assertion below still relates the full wide root.
    let empty_boundary = w.ledger().get(&cell).unwrap().state.heap_root.to_bytes32();

    // ── Edit #1: a doc longer than one 32-byte umem chunk ─────────────────────────
    let prose = "The document IS the cell. Its prose lives in the committed umem-heap, \
                 not a sidecar — its commitment is the boundary a light client trusts.";
    assert!(prose.len() > 32, "exercise multi-chunk encoding");

    let projected = project_doc(cell, prose);
    let commitment = projected.commitment();
    let heap = projected.cell().state.heap_map.clone();

    // The out-of-band umem write (no turn, no kernel effect): the cell's `heap_root`
    // boundary IS the document commitment after the reseal.
    assert!(
        w.set_cell_heap(&cell, heap),
        "the document projects into the cell's umem-heap and reseals"
    );
    let boundary = w.ledger().get(&cell).unwrap().state.heap_root.to_bytes32();
    assert_ne!(
        boundary, empty_boundary,
        "the edit MOVED the committed umem boundary"
    );
    assert_eq!(
        boundary, commitment,
        "the cell's committed heap_root IS the document's commitment (boundary == commitment)"
    );

    // The prose reads back FROM THE COMMITTED umem-heap (not a buffer, not a sidecar).
    assert_eq!(
        read_doc(&w, &cell).as_deref(),
        Some(prose),
        "prose reads back verbatim from the committed umem boundary"
    );

    // The projection is genuinely bound by `heap_root` (the membership witness): the
    // text-length leaf and the first atom leaf fold to the committed boundary.
    {
        let state = &w.ledger().get(&cell).unwrap().state;
        assert!(
            state
                .heap_root_membership(dregg_doc::COLL_TEXT, 0)
                .is_some(),
            "the prose-length leaf is bound by the committed heap_root"
        );
        assert!(
            state
                .heap_root_membership(dregg_doc::COLL_ATOMS, 0)
                .is_some(),
            "the first atom is bound by the committed heap_root (the structured projection)"
        );
    }

    // ── Edit #2: SHRINK the document — no stale leaf may linger in the boundary ────
    let short = "shorter.";
    let shrunk = project_doc(cell, short);
    assert!(w.set_cell_heap(&cell, shrunk.cell().state.heap_map.clone()));
    assert_eq!(
        read_doc(&w, &cell).as_deref(),
        Some(short),
        "the shrunk prose reads back exactly (no trailing garbage)"
    );
    assert_eq!(
        w.ledger().get(&cell).unwrap().state.heap_root.to_bytes32(),
        shrunk.commitment(),
        "the shrunk document's boundary IS its commitment (rebuilt wholesale, no stale leaf)"
    );
    assert_ne!(
        w.ledger().get(&cell).unwrap().state.heap_root.to_bytes32(),
        boundary,
        "the shrink moved the boundary"
    );

    // ── Reopen FROM THE LEDGER: a fresh read of the committed umem boundary ────────
    // (Model the desktop reopening the doc window: `make_kind` -> `load_doc_text` ->
    // `read_doc_from_heap` reads the committed `heap_map`, no sidecar involved.)
    let reopened = read_doc(&w, &cell);
    assert_eq!(
        reopened.as_deref(),
        Some(short),
        "reopen restores the document from the committed ledger umem boundary"
    );
}
