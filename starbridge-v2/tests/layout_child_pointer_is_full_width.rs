//! **THE LAYOUT CHILD POINTER MUST CARRY THE WHOLE CELL ID.**
//!
//! `dregg_doc::composition::CellId` is the identity a composed document's
//! [`LayoutGraph`] uses for every embedded child: it is what `Op::Embed` places, what
//! `surface_embed_id` keys the embed-atom on, what the membrane's `Viewer` caps are
//! held over, and what `substrate::leaf_for_embed` binds into the parent document's
//! committed Poseidon2 heap root. A substrate `dregg_types::CellId` is **32 bytes**.
//!
//! Two starbridge surfaces reduce the substrate id onto that pointer:
//!
//!   * [`starbridge_v2::desktop_doc::composed_cell_id`] — the cockpit's window→embed
//!     projection;
//!   * [`starbridge_v2::document_composer::child_id`] — the hand-authoring composer's.
//!
//! This file is the gate on both: **distinct cells must stay distinct all the way into
//! the layout graph and its commitment**, and the pointer must be able to *name* the
//! cell it cites rather than merely hash it.
//!
//! Run: `cargo test -p starbridge-v2 --test layout_child_pointer_is_full_width`

#![cfg(feature = "embedded-executor")]

use dregg_doc::composition::{
    content_composed, scene_to_composed, surface_embed_id, workspace_resolver, DesktopSurface,
    Viewer,
};
use dregg_doc::{layout_substrate_commit, Author};
use dregg_types::CellId;

use starbridge_v2::desktop_doc::composed_cell_id;
use starbridge_v2::document_composer::{child_id, child_pointer_bytes};

/// **THE EXHIBIT.** Two distinct, well-formed 32-byte cell ids that the cockpit's
/// window→embed reduction folds onto ONE layout child pointer.
///
/// They are not a lucky find and not a 2^64 birthday. `composed_cell_id` is not a hash
/// at all — it is an FNV-shaped polynomial fold `f` run separately over the id's two
/// 16-byte halves and combined as `f(X) ^ rot64(f(Y))`. Because `rotate_left(64)` on a
/// `u128` simply *swaps its two 64-bit halves*, writing `f(X) = (a, b)` and
/// `f(Y) = (c, d)` gives
///
/// ```text
///   composed(X‖Y) = (a ^ d,  b ^ c)
///   composed(Y‖X) = (b ^ c,  a ^ d)
/// ```
///
/// — the same pair, swapped. So `X‖Y` and `Y‖X` collide exactly when `a ^ b == c ^ d`,
/// a **64-bit** condition. That is a ~2^32 birthday search, run once (van
/// Oorschot–Wiener parallel collision search, minutes on a laptop) to produce the two
/// constants below. The `u128` pointer's nominal 128-bit width buys 32 bits of real
/// separation here, against a house floor of ~124.
fn colliding_pair() -> (CellId, CellId) {
    let x: [u8; 16] = [
        0xb4, 0x57, 0x39, 0xbf, 0x52, 0x43, 0x17, 0xa6, 0, 0, 0, 0, 0, 0, 0, 0,
    ];
    let y: [u8; 16] = [
        0x66, 0x82, 0xa7, 0x4e, 0xd0, 0xc9, 0x3f, 0x64, 0, 0, 0, 0, 0, 0, 0, 0,
    ];
    let mut a = [0u8; 32];
    a[..16].copy_from_slice(&x);
    a[16..].copy_from_slice(&y);
    let mut b = [0u8; 32];
    b[..16].copy_from_slice(&y);
    b[16..].copy_from_slice(&x);
    (CellId::from_bytes(a), CellId::from_bytes(b))
}

/// (1) THE REDUCTION ITSELF — two different cells, two different layout children.
#[test]
fn distinct_cells_reduce_to_distinct_layout_children() {
    let (a, b) = colliding_pair();
    assert_ne!(a, b, "the exhibit is two DIFFERENT substrate cells");
    assert_ne!(
        composed_cell_id(&a),
        composed_cell_id(&b),
        "two distinct cells must not fold onto one layout child pointer\n  a = {}\n  b = {}",
        hex(&a),
        hex(&b)
    );
}

/// (2) THE LAYOUT CONSEQUENCE — the second window is SWALLOWED.
///
/// `surface_embed_id` keys an embed-atom on the child pointer, and `Op::Embed`'s apply
/// is `entry().or_insert`. Two windows whose owners share a pointer therefore share an
/// embed-atom: the second `Op::Embed` is absorbed by the first, its `after` edge is a
/// self-edge (dropped by `connect`), and the composed desktop renders ONE window where
/// the operator opened two. Nothing refuses; nothing is narrated.
#[test]
fn two_windows_on_distinct_cells_stay_two_embeds() {
    let (a, b) = colliding_pair();
    let surfaces = vec![
        DesktopSurface::new(composed_cell_id(&a), 0),
        DesktopSurface::new(composed_cell_id(&b), 1),
    ];
    assert_ne!(
        surface_embed_id(&surfaces[0]),
        surface_embed_id(&surfaces[1]),
        "two windows on distinct cells must occupy distinct embed-atoms"
    );

    let layout = scene_to_composed(&surfaces, Author(1));
    let resolver = workspace_resolver(&surfaces);
    let viewer = Viewer::able(surfaces.iter().map(|s| s.owner));
    let rendered = content_composed(&layout, &viewer, &resolver);

    assert_eq!(
        rendered.embedded_cells().len(),
        2,
        "the composed desktop must embed BOTH windows; it rendered {:?}",
        rendered.embedded_cells()
    );
}

/// (3) THE COMMITMENT CONSEQUENCE — the light client cannot tell the cells apart.
///
/// `layout_substrate_commit` is the production sorted-Poseidon2 heap root over the
/// layout, and `leaf_for_embed` binds the child pointer into it. Two single-window
/// layouts over two DIFFERENT cells must commit to two different roots; if they do not,
/// "a forged child pointer changes the parent commitment" holds only to the pointer's
/// width, not the cell's.
#[test]
fn distinct_cells_yield_distinct_layout_commitments() {
    let (a, b) = colliding_pair();
    let la = scene_to_composed(&[DesktopSurface::new(composed_cell_id(&a), 0)], Author(1));
    let lb = scene_to_composed(&[DesktopSurface::new(composed_cell_id(&b), 0)], Author(1));
    assert_ne!(
        layout_substrate_commit(&la),
        layout_substrate_commit(&lb),
        "the committed layout root must distinguish two distinct embedded cells"
    );
}

/// (4) THE POINTER MUST NAME THE CELL, NOT MERELY HASH IT.
///
/// The composer's `child_id` is a BLAKE3 digest truncated to 16 bytes: a reader holding
/// only the `LayoutGraph` sees 128 bits of a 256-bit identity and cannot recover which
/// cell is cited — the full id survives only in a side table beside the layout, which
/// is precisely what a light client does not have. The pointer must BE the id.
///
/// Checked against an independent source: the substrate `CellId`'s own bytes.
#[test]
fn the_layout_child_pointer_carries_the_whole_substrate_id() {
    for tag in [0x00u8, 0x01, 0x7f, 0xa1, 0xcd, 0xff] {
        let c = CellId::from_bytes([tag; 32]);
        assert_eq!(
            child_pointer_bytes(child_id(&c)),
            c.0.to_vec(),
            "the layout child pointer must carry the substrate id's own 32 bytes \
             (cell {})",
            hex(&c)
        );
    }
    let (a, b) = colliding_pair();
    for c in [a, b] {
        assert_eq!(
            child_pointer_bytes(child_id(&c)),
            c.0.to_vec(),
            "the layout child pointer must carry the substrate id's own 32 bytes \
             (cell {})",
            hex(&c)
        );
    }
}

fn hex(c: &CellId) -> String {
    c.0.iter().map(|b| format!("{b:02x}")).collect()
}
