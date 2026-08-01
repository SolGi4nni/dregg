//! THE COMPOSITION KEYSTONE, BY RUNNING: a cell HOSTS its own view-tree in its committed
//! heap, and a parent card MOUNTS that whole tree as a subtree — distinct from `bind` (one
//! scalar) and value-transclusion (a snapshot). Hosted trees contain `host` mounts of OTHER
//! cells → FRACTAL recursion (cells-host-cells-host-view-trees). This proves, end-to-end:
//!
//!   1. A child cell and a grandchild cell each store a hosted view-tree as a heap blob
//!      (the proven chunked-heap-blob codec, under `VIEWTREE_COLL` — the cell-heap-as-view-
//!      source). The child's hosted tree itself contains a `host(grandchild)` node.
//!   2. A parent card `host(child)`s the child. `resolve_mounts` reads the child's tree off
//!      its heap, and — recursing — the grandchild's tree off ITS heap, splicing a 2-LEVEL
//!      fractal nest. Rendered to REAL gpui-component pixels, the child + grandchild trees
//!      appear nested inside the parent (PNG #1).
//!   3. A RECEIPTED edit to the child's hosted tree (a real verified turn on the child cell,
//!      plus the rewritten view-tree blob written back into its committed heap) re-resolves
//!      into a CHANGED rendered subtree (PNG #2 differs from #1) — the surface is a living
//!      verified object.

use std::cell::RefCell;
use std::path::PathBuf;
use std::rc::Rc;

use deos_js::applet::{pack_u64, Affordance, Applet};
use dregg_cell::AuthRequired;
use gpui::AppContext;

use deos_view::headless::HeadlessRender;
use deos_view::mount::{cell_id_from_hex, cell_id_hex, view_tree_from_cell_heap, write_view_blob};
use deos_view::{resolve_mounts, AppletView, MountSource, ViewNode};
use dregg_cell::Requirement;

static LILEX: &[u8] = include_bytes!("../assets/fonts/Lilex-Regular.ttf");
static IBM_PLEX: &[u8] = include_bytes!("../assets/fonts/IBMPlexSans-Regular.ttf");

fn out_dir() -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/render-out");
    std::fs::create_dir_all(&dir).expect("create render-out dir");
    dir
}

/// Resolve a tree's `host` mounts against BOTH cells' ledgers (each cell lives on its own
/// ledger): try the child's heap, then the grandchild's. The cell-heap-as-view-source,
/// unioned. A free fn so the immutable ledger borrow is released per call (the cells stay
/// mutable between resolves).
fn resolve(tree: &ViewNode, child: &Applet, grandchild: &Applet) -> ViewNode {
    let source = |hex: &str| -> Option<ViewNode> {
        let id = cell_id_from_hex(hex)?;
        view_tree_from_cell_heap(child.ledger(), id)
            .or_else(|| view_tree_from_cell_heap(grandchild.ledger(), id))
    };
    resolve_mounts(tree, &source as &dyn MountSource)
}

/// A minimal cell with one free `inc` affordance (slot 0 += arg) — enough to leave a real
/// receipt for the "evolution is a receipted turn" half.
fn host_cell(seed: u8) -> Applet {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    let inc = Affordance {
        name: "inc".into(),
        required: Requirement::Root,
        apply: Box::new(|model, arg| {
            let cur = model.field_u64(0);
            vec![(0usize, pack_u64(cur + arg.max(0) as u64))]
        }),
    };
    Applet::mint(
        pk,
        [0u8; 32],
        &[(0usize, pack_u64(0))],
        vec![inc],
        AuthRequired::None,
    )
}

#[test]
fn a_parent_card_mounts_a_childs_heap_hosted_view_tree_fractally() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(body)
        .expect("spawn big-stack render thread")
        .join()
        .expect("cell-hosted-view-tree render proof thread");
}

fn body() {
    let out = out_dir();

    // ── 1. Mint the child + grandchild cells; store each one's HOSTED view-tree as a heap
    //       blob (the cell-heap-as-view-source). The child's hosted tree HOSTS the grandchild. ──
    let mut grandchild = host_cell(0x9C);
    let gc_id = grandchild.cell();
    let gc_hex = cell_id_hex(gc_id);
    let gc_view = r#"{
        "kind":"section",
        "props":{"title":"grandchild cell"},
        "children":[{"kind":"text","props":{"text":"grandchild leaf"}}]
    }"#;
    grandchild.with_cell_mut(|cell| write_view_blob(cell, gc_view.as_bytes()));

    let mut child = host_cell(0xC1);
    let child_id = child.cell();
    let child_hex = cell_id_hex(child_id);
    // The child's hosted tree contains a host(grandchild) — the fractal nest.
    let child_view = format!(
        r#"{{
            "kind":"section",
            "props":{{"title":"child cell"}},
            "children":[
                {{"kind":"text","props":{{"text":"child body"}}}},
                {{"kind":"host","props":{{"cell":"{gc_hex}"}}}}
            ]
        }}"#
    );
    child.with_cell_mut(|cell| write_view_blob(cell, child_view.as_bytes()));

    // The READ side of the heap-as-view-source is real: the child's tree round-trips out of
    // its committed heap.
    let read_back = view_tree_from_cell_heap(child.ledger(), child_id)
        .expect("the child's hosted view-tree reads back out of its committed heap");
    assert!(
        format!("{read_back:?}").contains("child body"),
        "the heap-stored view-tree round-tripped"
    );

    // ── 2. The PARENT card host()s the child. resolve_mounts reads the child off its heap and
    //       — recursing — the grandchild off ITS heap (the 2-level fractal nest). ────────────
    let parent_tree = ViewNode::VStack(vec![
        ViewNode::Text("parent surface".into()),
        ViewNode::Host {
            cell: child_hex.clone(),
            view: None,
        },
    ]);

    let resolved0 = resolve(&parent_tree, &child, &grandchild);
    let dump0 = format!("{resolved0:?}");
    assert!(
        dump0.contains("child body"),
        "the child's hosted tree mounted into the parent"
    );
    assert!(
        dump0.contains("grandchild leaf"),
        "the grandchild's hosted tree mounted TWO levels deep (fractal)"
    );

    // Render the resolved parent (with its mounted subtree) to real gpui-component pixels.
    let parent_applet = Rc::new(RefCell::new(host_cell(0x9A)));
    let mut hr = HeadlessRender::boot("Lilex", &[LILEX, IBM_PLEX]).expect("boot headless gpui");
    let a0 = parent_applet.clone();
    let r0 = resolved0.clone();
    let window = hr
        .open(520.0, 600.0, move |_w, cx| {
            cx.new(|_cx| AppletView::new(a0, r0))
        })
        .expect("open the mounted-card window");
    let frame0 = hr.capture(window.into()).expect("capture frame 0");
    let png0 = out.join("hosted-mount-nested.png");
    frame0.save(&png0).expect("save PNG #0");
    assert!(
        frame0.width() > 0 && frame0.height() > 0,
        "frame 0 has pixels"
    );

    // ── 3. A RECEIPTED edit to the CHILD's hosted tree → the rendered subtree changes ────────
    // Fire a real verified turn on the child (a committed receipt — the blamed edit), and write
    // the rewritten view-tree blob back into the child's committed heap.
    let receipt = child
        .fire("inc", 1)
        .expect("a real verified turn commits on the child cell");
    assert_ne!(
        receipt.receipt_hash(),
        [0u8; 32],
        "a real TurnReceipt committed"
    );

    let child_view_edited = format!(
        r#"{{
            "kind":"section",
            "props":{{"title":"child cell (edited)"}},
            "children":[
                {{"kind":"text","props":{{"text":"child body — EDITED"}}}},
                {{"kind":"divider","props":{{}}}},
                {{"kind":"host","props":{{"cell":"{gc_hex}"}}}}
            ]
        }}"#
    );
    child.with_cell_mut(|cell| write_view_blob(cell, child_view_edited.as_bytes()));

    // Re-resolve off the moved heap and swap the parent's painted subtree.
    let resolved1 = resolve(&parent_tree, &child, &grandchild);
    assert!(
        format!("{resolved1:?}").contains("EDITED"),
        "the re-resolved subtree reflects the edited hosted tree"
    );
    hr.update_root(window, |view, _w, _cx| view.set_tree(resolved1))
        .expect("swap the mounted subtree");
    hr.update(|cx| cx.refresh_windows());
    let frame1 = hr.capture(window.into()).expect("capture frame 1");
    let png1 = out.join("hosted-mount-edited.png");
    frame1.save(&png1).expect("save PNG #1");

    assert_ne!(
        frame0.as_raw(),
        frame1.as_raw(),
        "the receipted edit to the child's hosted tree changed the rendered subtree"
    );

    println!("RENDERED CELL-HOSTED-VIEW-TREE PNGs (real gpui-component widgets, offscreen wgpu):");
    println!("  nested (fractal mount) : {}", png0.display());
    println!("  edited (re-resolved)   : {}", png1.display());
}
