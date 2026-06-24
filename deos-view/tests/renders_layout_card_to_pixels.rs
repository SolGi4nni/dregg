//! THE PROOF, BY RUNNING: the cockpit's own LAYOUT (its mode→surface arrangement) is a
//! deos-js card whose view-tree renders to REAL gpui-component pixels (a PNG), and whose
//! OWN structure reshapes from within (a receipted patch that visibly changes the rendered
//! chrome).
//!
//! Rung 3 of the reflective cockpit: the arrangement that was hardcoded Rust
//! (`starbridge-v2/src/cockpit/frame.rs` `CockpitMode::surfaces()`) is editable DATA. This
//! test bakes the SAME serializable view-tree through the SAME `parse_view_tree` + `AppletView`
//! the inspector/objects/graph-card proofs use:
//!
//!   1. Build the layout card (seeded with the real five-mode arrangement) + render its
//!      GENERATED view-source → PNG #1 (a section per mode, a row per surface).
//!   2. RESHAPE FROM WITHIN — move a surface to another mode + relabel a mode's blurb — a
//!      receipted patch with blame — and render the RESHAPED view-source → PNG #2, which
//!      DIFFERS from #1 (the chrome's STRUCTURE was rewritten from inside, accountably).

use std::cell::RefCell;
use std::path::PathBuf;
use std::rc::Rc;

use deos_js::applet::{pack_u64, Applet};
use deos_js::Author;
use deos_js::{LayoutCard, LayoutPatch};
use dregg_cell::AuthRequired;
use gpui::AppContext;

use deos_view::headless::HeadlessRender;
use deos_view::{parse_view_tree, AppletView};

static LILEX: &[u8] = include_bytes!("../assets/fonts/Lilex-Regular.ttf");
static IBM_PLEX: &[u8] = include_bytes!("../assets/fonts/IBMPlexSans-Regular.ttf");

fn out_dir() -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/render-out");
    std::fs::create_dir_all(&dir).expect("create render-out dir");
    dir
}

/// A throwaway applet whose ledger the rendered button handlers can attach to (the layout
/// card carries no bound model slots — the proof here is the view-tree shape, baked to
/// pixels).
fn render_applet() -> Applet {
    Applet::mint(
        [0x5E; 32],
        [0u8; 32],
        &[(0usize, pack_u64(0))],
        Vec::new(),
        AuthRequired::None,
    )
}

#[test]
fn the_layout_card_renders_and_reshapes_from_within_to_real_gpui_pixels() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(body)
        .expect("spawn big-stack render thread")
        .join()
        .expect("layout-card render proof thread");
}

fn body() {
    let out = out_dir();
    let mut hr = HeadlessRender::boot("Lilex", &[LILEX, IBM_PLEX]).expect("boot headless gpui");

    let (png0, png1) = bake_layout(&mut hr, &out);

    println!("RENDERED LAYOUT-CARD PNGs (real gpui-component widgets, offscreen wgpu):");
    println!("  layout (generated) : {}", png0.display());
    println!("  layout (reshaped)  : {}", png1.display());
}

/// Render a card's `view_source` JSON over a live applet, capture a PNG, return its raw pixels
/// (for the differs-after-reshape assertion) and the saved path.
fn render_to_png(hr: &mut HeadlessRender, source: &str, png: PathBuf) -> (Vec<u8>, PathBuf) {
    let tree = parse_view_tree(source).expect("parse the layout view-tree");
    let applet = Rc::new(RefCell::new(render_applet()));
    let window = hr
        .open(560.0, 1100.0, move |_w, cx| {
            cx.new(|_cx| AppletView::new(applet, tree))
        })
        .expect("open the layout-card window");
    let frame = hr.capture(window.into()).expect("capture the layout frame");
    frame.save(&png).expect("save the layout PNG");
    assert!(
        frame.width() > 0 && frame.height() > 0,
        "the frame has pixels"
    );
    (frame.as_raw().clone(), png)
}

fn bake_layout(hr: &mut HeadlessRender, out: &PathBuf) -> (PathBuf, PathBuf) {
    let mut card = LayoutCard::open(
        [0x1A; 32],
        Author(42),
        AuthRequired::None,
        AuthRequired::Signature,
    );
    // The layout card's `view_source` is the editable arrangement DATA (the LayoutModel);
    // the RENDERABLE projection is its view-tree (a section per mode + a row per surface),
    // which `deos-view` paints. (Distinct from the cards whose view_source IS the view-tree —
    // here the data is the source of truth, the view-tree is derived from it.)
    let tree0 = card.view_tree().expect("derive the layout view-tree");
    let source0 = tree0.to_json();
    assert!(
        source0.contains("Cockpit layout · 5 modes · 30 surfaces"),
        "the generated layout view counts the live arrangement"
    );
    let (frame0, png0) = render_to_png(hr, &source0, out.join("layout-card.png"));

    // RESHAPE FROM WITHIN: move OBJECTS from Inhabit to Inspect + relabel a mode's blurb →
    // receipted patches that visibly change the rendered chrome's structure.
    let edit = card
        .reshape(LayoutPatch::MoveSurface {
            surface: "OBJECTS".into(),
            to_mode: "Inspect".into(),
        })
        .expect("move a surface to another mode from within");
    assert_ne!(
        edit.receipt.receipt_hash(),
        [0u8; 32],
        "the layout reshape left a real receipt on the card's chain"
    );
    card.reshape(LayoutPatch::RelabelMode {
        mode: "Operate".into(),
        blurb: "the cap & agent machinery".into(),
    })
    .expect("relabel a mode's blurb from within");

    // The arrangement (the data the cockpit reads) actually moved.
    assert_eq!(
        card.layout().mode_of("OBJECTS").as_deref(),
        Some("Inspect"),
        "OBJECTS was re-homed under Inspect"
    );

    let source1 = card
        .view_tree()
        .expect("derive the reshaped view-tree")
        .to_json();
    let (frame1, png1) = render_to_png(hr, &source1, out.join("layout-card-reshaped.png"));
    assert_ne!(
        frame0, frame1,
        "the cockpit's layout was rewritten from within — the rendered chrome differs"
    );
    (png0, png1)
}
