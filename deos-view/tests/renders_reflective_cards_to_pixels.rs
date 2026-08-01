//! THE PROOF, BY RUNNING: three more cockpit surfaces — the COMPOSER, the OBJECTS list,
//! and the GRAPH (ocap web) — are deos-js cards whose view-trees render to REAL
//! gpui-component pixels (a PNG each), and whose OWN view reshapes from within (a receipted
//! patch that visibly changes the rendered UI).
//!
//! Each card's view is a pure function of live deos substance (a composition layout / a live
//! ledger's cell roster / a live ocap web), produced gpui-FREE in `deos-js`; this test bakes
//! the SAME serializable view-tree through the SAME `parse_view_tree` + `AppletView` the
//! inspector-card proof uses. For each card:
//!
//!   1. Build the card + render its GENERATED view-source → PNG #1.
//!   2. EDIT FROM WITHIN (relabel a section + append a row) — a receipted patch with blame —
//!      and render the RESHAPED view-source → PNG #2, which DIFFERS from #1 (the surface was
//!      rewritten from inside, accountably).

use std::cell::RefCell;
use std::path::PathBuf;
use std::rc::Rc;

use deos_js::applet::{pack_u64, Applet};
use deos_js::card_editor::ViewPatch;
use deos_js::composer_card::{ComposerCard, Role as ComposerRole};
use deos_js::graph_card::GraphCard;
use deos_js::objects_card::ObjectsCard;
use deos_js::Author;
use dregg_cell::{AuthRequired, Cell, Ledger};
use dregg_types::CellId;
use gpui::AppContext;

use deos_view::headless::HeadlessRender;
use deos_view::{parse_view_tree, AppletView};
use dregg_cell::{Credential, Requirement};

static LILEX: &[u8] = include_bytes!("../assets/fonts/Lilex-Regular.ttf");
static IBM_PLEX: &[u8] = include_bytes!("../assets/fonts/IBMPlexSans-Regular.ttf");

fn out_dir() -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/render-out");
    std::fs::create_dir_all(&dir).expect("create render-out dir");
    dir
}

/// A small live World: a ledger with two cells, A granting a Signature cap to B (so the
/// ocap web has one edge, and the objects list has two cells with balances).
fn world() -> Ledger {
    let mut ledger = Ledger::new();
    let mut a = Cell::with_balance([0xA1; 32], [0u8; 32], 1_000);
    let b = Cell::with_balance([0xB2; 32], [0u8; 32], 500);
    let b_id = b.id();
    a.capabilities.grant(b_id, AuthRequired::Signature);
    ledger.insert_cell(a).expect("insert A");
    ledger.insert_cell(b).expect("insert B");
    ledger
}

/// A throwaway applet whose ledger the rendered Bind rows / button handlers can attach to
/// (the reflective cards carry no bound model slots, so any live applet suffices as the
/// AppletView substance — the proof here is the view-tree shape, baked to pixels).
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
fn reflective_cards_render_and_reshape_from_within_to_real_gpui_pixels() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(body)
        .expect("spawn big-stack render thread")
        .join()
        .expect("reflective-cards render proof thread");
}

fn body() {
    let out = out_dir();
    let mut hr = HeadlessRender::boot("Lilex", &[LILEX, IBM_PLEX]).expect("boot headless gpui");

    let composer = bake_composer(&mut hr, &out);
    let objects = bake_objects(&mut hr, &out);
    let graph = bake_graph(&mut hr, &out);

    println!("RENDERED REFLECTIVE-CARD PNGs (real gpui-component widgets, offscreen wgpu):");
    println!("  composer (generated) : {}", composer.0.display());
    println!("  composer (reshaped)  : {}", composer.1.display());
    println!("  objects  (generated) : {}", objects.0.display());
    println!("  objects  (reshaped)  : {}", objects.1.display());
    println!("  graph    (generated) : {}", graph.0.display());
    println!("  graph    (reshaped)  : {}", graph.1.display());
}

/// Render a card's `view_source` JSON over a live applet, capture a PNG, return its raw
/// pixels (for the differs-after-reshape assertion) and the saved path.
fn render_to_png(hr: &mut HeadlessRender, source: &str, png: PathBuf) -> (Vec<u8>, PathBuf) {
    let tree = parse_view_tree(source).expect("parse the card view-tree");
    let applet = Rc::new(RefCell::new(render_applet()));
    let window = hr
        .open(560.0, 900.0, move |_w, cx| {
            cx.new(|_cx| AppletView::new(applet, tree))
        })
        .expect("open the card window");
    let frame = hr.capture(window.into()).expect("capture the card frame");
    frame.save(&png).expect("save the card PNG");
    assert!(
        frame.width() > 0 && frame.height() > 0,
        "the frame has pixels"
    );
    (frame.as_raw().clone(), png)
}

// ── 1. THE COMPOSER CARD ───────────────────────────────────────────────────────────────
fn bake_composer(hr: &mut HeadlessRender, out: &PathBuf) -> (PathBuf, PathBuf) {
    let mut card = ComposerCard::open(
        deos_js::composer_card::ChildCellId(0xD0C),
        Author(42),
        AuthRequired::None,
        Requirement::AtLeast(Credential::Signature),
    );
    // Compose a document from cells (the gestures = real composition patches).
    card.add_embed(
        deos_js::composer_card::ChildCellId(0xA1),
        ComposerRole::Section,
    );
    card.add_embed(
        deos_js::composer_card::ChildCellId(0xB2),
        ComposerRole::Figure,
    );
    let source0 = card.view_source();
    assert!(
        source0.contains("Composed cells"),
        "the generated composer view has its section"
    );
    let (frame0, png0) = render_to_png(hr, &source0, out.join("composer-card.png"));

    // EDIT FROM WITHIN: relabel the section + append a note → a receipted patch.
    let edit = card
        .edit_view(ViewPatch::Relabel {
            from: "Composed cells".into(),
            to: "Document body".into(),
        })
        .expect("relabel the composer section from within");
    assert!(
        edit.receipt.is_landed(),
        "the composer reshape left a composition receipt"
    );
    card.edit_view(ViewPatch::AddText {
        text: "— composed by hand —".into(),
    })
    .expect("append a note from within");
    let source1 = card.view_source();
    let (frame1, png1) = render_to_png(hr, &source1, out.join("composer-card-reshaped.png"));
    assert_ne!(
        frame0, frame1,
        "the composer UI was rewritten from within — the frame differs"
    );
    (png0, png1)
}

// ── 2. THE OBJECTS CARD ────────────────────────────────────────────────────────────────
fn bake_objects(hr: &mut HeadlessRender, out: &PathBuf) -> (PathBuf, PathBuf) {
    let ledger = world();
    let mut card = ObjectsCard::open(
        &ledger,
        [0xCA; 32],
        Author(42),
        AuthRequired::None,
        Requirement::AtLeast(Credential::Signature),
    );
    let source0 = card.view_source();
    assert!(
        source0.contains("Objects · 2 cells"),
        "the generated objects view lists the roster"
    );
    let (frame0, png0) = render_to_png(hr, &source0, out.join("objects-card.png"));

    let edit = card
        .edit_view(ViewPatch::Relabel {
            from: "Cells".into(),
            to: "Sovereign cells".into(),
        })
        .expect("relabel the objects header from within");
    assert_ne!(
        edit.receipt.receipt_hash(),
        [0u8; 32],
        "the objects reshape left a real receipt"
    );
    card.edit_view(ViewPatch::AddButton {
        label: "refresh".into(),
        turn: "refresh".into(),
        arg: 1,
    })
    .expect("append a refresh button from within");
    let source1 = card.view_source();
    let (frame1, png1) = render_to_png(hr, &source1, out.join("objects-card-reshaped.png"));
    assert_ne!(
        frame0, frame1,
        "the objects UI was rewritten from within — the frame differs"
    );
    let _: CellId = card.card().cell(); // the card has its own sovereign cell (the receipt substance)
    (png0, png1)
}

// ── 3. THE GRAPH CARD ──────────────────────────────────────────────────────────────────
fn bake_graph(hr: &mut HeadlessRender, out: &PathBuf) -> (PathBuf, PathBuf) {
    let ledger = world();
    let mut card = GraphCard::open(
        &ledger,
        [0xC9; 32],
        Author(42),
        AuthRequired::None,
        Requirement::AtLeast(Credential::Signature),
    );
    let source0 = card.view_source();
    assert!(
        source0.contains("Ocap web · 2 cells · 1 edges"),
        "the generated graph view counts the live cap web"
    );
    let (frame0, png0) = render_to_png(hr, &source0, out.join("graph-card.png"));

    let edit = card
        .edit_view(ViewPatch::Relabel {
            from: "Cap edges (holder → target)".into(),
            to: "Who can reach what".into(),
        })
        .expect("relabel the graph section from within");
    assert_ne!(
        edit.receipt.receipt_hash(),
        [0u8; 32],
        "the graph reshape left a real receipt"
    );
    card.edit_view(ViewPatch::AddButton {
        label: "highlight cycles".into(),
        turn: "highlight_cycles".into(),
        arg: 1,
    })
    .expect("append a button from within");
    let source1 = card.view_source();
    let (frame1, png1) = render_to_png(hr, &source1, out.join("graph-card-reshaped.png"));
    assert_ne!(
        frame0, frame1,
        "the graph UI was rewritten from within — the frame differs"
    );
    (png0, png1)
}
