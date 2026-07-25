//! **The cell-heap-as-view-source** — read a cell's hosted view-tree out of its committed
//! heap (the native half of the composition keystone, `docs/deos/CELL-HOSTED-VIEWTREE.md`).
//!
//! A cell HOSTS a view-tree: its serialized `{kind,props,children}` JSON is stored as a
//! **heap blob** under collection [`VIEWTREE_COLL`], chunked across the cell's committed
//! `CellState::heap_map` (the sorted-Poseidon2 `(collection, key) → felt` map digested by
//! `heap_root`). This is the SAME proven chunked-heap-blob mechanism the program-in-cell weld
//! uses for the program blob (`deos-js::portable::{write,read}_program_blob`), under a
//! DISJOINT collection — so a cell can carry both its program and its hosted view-tree.
//!
//! Storing the view-tree in the heap means it is part of the cell's COMMITTED state: it
//! travels with the cell, is committed by `heap_root`, and a receipted edit to it (a
//! `ViewPatch` written back here) moves the root — a light client witnesses the surface
//! evolving. [`view_tree_from_cell_heap`] is the read side; a host node's mount resolves
//! through a [`MountSource`](crate::tree::MountSource) that calls it (see
//! [`ledger_mount_source`]).
//!
//! This module is NATIVE-only (it needs `dregg-cell`); the pure resolver + the `MountSource`
//! trait live in [`crate::tree`] (serde-only), so the gpui-free `web`/`discord` renderers
//! walk the resolved tree without ever depending on the heap.

use dregg_cell::state::FieldElement;
use dregg_cell::{Cell, Ledger};
use dregg_types::CellId;

use crate::tree::{parse_view_tree, MountSource, ViewNode};

/// The heap collection id reserved for a cell's hosted VIEW-TREE blob. Disjoint from the
/// program-blob collection (`deos-js::portable::PROGRAM_COLL` = `0xC0DE`) and from any
/// data collection an applet uses, so a cell can carry its program AND its view-tree.
pub const VIEWTREE_COLL: u32 = 0x1E4F;

/// Bytes of payload per heap leaf — a `FieldElement` is 32 bytes; byte 0 is the chunk fill
/// length (`0..=31`), bytes `1..=31` carry payload. Key 0 instead holds the total byte
/// length (little-endian u64). The SAME framing as the proven program-blob codec.
const CHUNK_BYTES: usize = 31;

/// Write a serialized view-tree (`{kind,props,children}` JSON bytes) into a cell's committed
/// heap under [`VIEWTREE_COLL`]. Key 0 = the length header; keys `1..` = the payload chunks.
/// Mutating the heap re-seals `heap_root`, so the hosted view-tree becomes part of the cell's
/// committed state.
pub fn write_view_blob(cell: &mut Cell, json: &[u8]) {
    let mut header = [0u8; 32];
    header[..8].copy_from_slice(&(json.len() as u64).to_le_bytes());
    cell.state.set_heap(VIEWTREE_COLL, 0, header);

    for (i, chunk) in json.chunks(CHUNK_BYTES).enumerate() {
        let mut leaf = [0u8; 32];
        leaf[0] = chunk.len() as u8;
        leaf[1..1 + chunk.len()].copy_from_slice(chunk);
        cell.state.set_heap(VIEWTREE_COLL, (i + 1) as u32, leaf);
    }
}

/// Read a hosted view-tree blob back out of a cell's committed heap. `None` if the cell hosts
/// no view-tree (no header leaf under [`VIEWTREE_COLL`]).
pub fn read_view_blob(cell: &Cell) -> Option<Vec<u8>> {
    let header: FieldElement = cell.state.get_heap(VIEWTREE_COLL, 0)?;
    let mut len_bytes = [0u8; 8];
    len_bytes.copy_from_slice(&header[..8]);
    let total = u64::from_le_bytes(len_bytes) as usize;

    // The `total` header is UNTRUSTED committed content: a malicious cell can
    // claim any u64 length. Do NOT pre-`with_capacity(total)` (a huge value is an
    // OOM-abort); grow `out` as real chunks arrive, and stop when the committed
    // heap runs out (`get_heap` → None → the whole read fails safe to None). The
    // per-leaf `fill` is clamped to the leaf's real payload width so a forged
    // `leaf[0] > 31` cannot slice past the 32-byte element (an OOB panic).
    let mut out: Vec<u8> = Vec::new();
    let mut key: u32 = 1;
    while out.len() < total {
        let leaf = cell.state.get_heap(VIEWTREE_COLL, key)?;
        let fill = (leaf[0] as usize).min(CHUNK_BYTES);
        out.extend_from_slice(&leaf[1..1 + fill]);
        key += 1;
    }
    out.truncate(total);
    Some(out)
}

/// **Read a cell's hosted view-tree off the live ledger** — the cell-heap-as-view-source. Look
/// the cell up on `ledger`, read its view-tree blob out of the committed heap, and parse it
/// into a [`ViewNode`]. `None` if the cell is absent, hosts no tree, or the blob is malformed
/// (the host then stays an unresolved placeholder — honest, never a crash).
pub fn view_tree_from_cell_heap(ledger: &Ledger, cell_id: CellId) -> Option<ViewNode> {
    let cell = ledger.get(&cell_id)?;
    let blob = read_view_blob(cell)?;
    let json = String::from_utf8(blob).ok()?;
    parse_view_tree(&json).ok()
}

/// A [`MountSource`] backed by a live [`Ledger`] — resolves each `host{cell}`'s subtree by
/// reading that cell's hosted view-tree out of its committed heap. This is what makes a
/// `host` mount the cell's REAL committed surface (not a provided snapshot). Pass it to
/// [`crate::tree::resolve_mounts`].
pub fn ledger_mount_source(ledger: &Ledger) -> impl MountSource + '_ {
    move |cell: &str| -> Option<ViewNode> {
        let id = cell_id_from_hex(cell)?;
        view_tree_from_cell_heap(ledger, id)
    }
}

/// Lowercase-hex of a cell id (the `host{cell}` reference an authored tree carries).
pub fn cell_id_hex(id: CellId) -> String {
    id.0.iter().map(|b| format!("{b:02x}")).collect()
}

/// Parse a 64-hex-char cell id back into a [`CellId`]. `None` if it is not exactly 32 bytes
/// of hex (so a malformed mount reference fail-safes to unresolved). Routed through the
/// shared char-safe [`dregg_types::parse_hex32`] — the ONE hex/id codec.
pub fn cell_id_from_hex(hex: &str) -> Option<CellId> {
    dregg_types::parse_hex32(hex).map(CellId)
}

#[cfg(test)]
mod read_view_blob_tests {
    use super::*;

    fn blank_cell() -> Cell {
        Cell::new([1u8; 32], [2u8; 32])
    }

    fn len_header(total: u64) -> FieldElement {
        let mut header = [0u8; 32];
        header[..8].copy_from_slice(&total.to_le_bytes());
        header
    }

    #[test]
    fn round_trips_a_real_blob() {
        let mut cell = blank_cell();
        let payload = b"the hosted view-tree JSON bytes".to_vec();
        write_view_blob(&mut cell, &payload);
        assert_eq!(read_view_blob(&cell), Some(payload));
    }

    #[test]
    fn oversized_length_header_is_not_pre_allocated() {
        // A malicious cell claims a u64::MAX byte length but commits NO chunks.
        // The OLD `Vec::with_capacity(total)` aborts on a ~18-exabyte allocation
        // before reading a single chunk; the fix grows the vec as chunks arrive
        // and fail-safes to None the instant the (absent) first chunk is read.
        let mut cell = blank_cell();
        cell.state.set_heap(VIEWTREE_COLL, 0, len_header(u64::MAX));
        assert_eq!(
            read_view_blob(&cell),
            None,
            "no chunks → None, no OOM-abort"
        );
    }

    #[test]
    fn forged_chunk_fill_over_31_does_not_slice_past_the_leaf() {
        // A forged leaf claims fill=255, but a leaf is only 32 bytes. The OLD
        // `&leaf[1..1 + fill]` slices to index 256 → an OOB panic. The fill is
        // clamped to the real 31-byte payload width, so the read fails safe.
        let mut cell = blank_cell();
        cell.state.set_heap(VIEWTREE_COLL, 0, len_header(100));
        let mut leaf = [0u8; 32];
        leaf[0] = 255; // forged fill, far past the 31-byte payload capacity
        cell.state.set_heap(VIEWTREE_COLL, 1, leaf);
        // Reads the clamped 31 payload bytes, then the next (absent) chunk → None.
        assert_eq!(read_view_blob(&cell), None, "clamped fill, no OOB panic");
    }
}
