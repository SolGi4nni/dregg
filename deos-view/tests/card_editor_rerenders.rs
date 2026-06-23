//! THE KEYSTONE, RENDERED: editing a card's VIEW from within deos (a `CardEditor`
//! view-patch — add a button) re-folds the card's `view_source`, which `deos-view`
//! re-renders to REAL gpui-component pixels — and the edited frame DIFFERS from the
//! unedited one (the new button visibly appeared). The edit is a receipted patch, not a
//! recompile.
//!
//! This closes the keystone moment of HYPERDREGGMEDIA gap #1: *edit the UI from within →
//! it re-renders → and the change is an accountable patch.* The card-editor's re-folded
//! view-source parses through the SAME `parse_view_tree` the renderer consumes (proving
//! the structured view-tree IS renderable), and the before/after PNGs prove the change
//! reaches pixels.

use std::cell::RefCell;
use std::path::PathBuf;
use std::rc::Rc;

use deos_js::card_editor::{Author, CardEditor, ViewPatch, ViewTree};
use deos_js::portable::{AffordanceSpec, ApplyOp, AppletManifest, PortableApplet};
use deos_js::Applet;
use dregg_cell::AuthRequired;
use gpui::AppContext;

use deos_view::headless::HeadlessRender;
use deos_view::{parse_view_tree, AppletView};

static LILEX: &[u8] = include_bytes!("../assets/fonts/Lilex-Regular.ttf");
static IBM_PLEX: &[u8] = include_bytes!("../assets/fonts/IBMPlexSans-Regular.ttf");

/// A counter card whose view is a structured view-tree (title + live count bind), with
/// an `inc` affordance — the starting card the editor authors.
fn counter_card_manifest() -> AppletManifest {
    let view = ViewTree::VStack {
        children: vec![
            ViewTree::Text {
                props: deos_js::card_editor::TextProps {
                    text: "Counter card".into(),
                },
            },
            ViewTree::Bind {
                props: deos_js::card_editor::BindProps {
                    slot: 0,
                    label: "count: ".into(),
                },
            },
        ],
    };
    AppletManifest {
        seed_fields: vec![(0usize, 0u64)],
        affordances: vec![AffordanceSpec {
            name: "inc".into(),
            required: AuthRequired::Signature,
            op: ApplyOp::AddToSlot { slot: 0 },
        }],
        held: AuthRequired::Signature,
        view_source: view.to_json(),
    }
}

fn card_applet(seed: u8, manifest: &AppletManifest) -> Applet {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    PortableApplet::mint(pk, [0u8; 32], manifest)
}

fn out_dir() -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/render-out");
    std::fs::create_dir_all(&dir).expect("create render-out dir");
    dir
}

#[test]
fn editing_a_cards_view_from_within_rerenders_with_the_new_button() {
    // The headless gpui Metal renderer wants a big native stack (same pattern the sibling
    // render test uses).
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(body)
        .expect("spawn big-stack render thread")
        .join()
        .expect("render thread");
}

fn body() {
    let out = out_dir();
    let manifest = counter_card_manifest();

    // ── BEFORE: render the unedited card (title + bind, NO button) → PNG #0 ───────────
    let before_tree = parse_view_tree(&manifest.view_source)
        .expect("the card-editor's structured view-source parses as a renderer view-tree");
    let before_applet = Rc::new(RefCell::new(card_applet(0xC0, &manifest)));

    let mut hr = HeadlessRender::boot("Lilex", &[LILEX, IBM_PLEX]).expect("boot headless gpui");

    let a0 = before_applet.clone();
    let t0 = before_tree.clone();
    let w0 = hr
        .open(420.0, 240.0, move |_window, cx| {
            cx.new(|_cx| AppletView::new(a0, t0))
        })
        .expect("open the unedited card window");
    let frame0 = hr.capture(w0.into()).expect("capture before-frame");
    let png0 = out.join("card-before-edit.png");
    frame0.save(&png0).expect("save before PNG");

    // ── THE EDIT (from within): add a "+1" button via a CardEditor view-patch ─────────
    let card = card_applet(0xC0, &manifest);
    let mut editor = CardEditor::adopt(
        card,
        manifest,
        Author(7),
        AuthRequired::None,      // the editor holds a single-custody mandate
        AuthRequired::Signature, // the card's authoring authority
    );
    let edit = editor
        .edit_view(ViewPatch::AddButton {
            label: "+1".into(),
            turn: "inc".into(),
            arg: 1,
        })
        .expect("the view-patch is admitted");

    // The edit is a receipted patch (a provenance turn landed on the card's chain).
    assert_ne!(edit.receipt.receipt_hash(), [0u8; 32], "the view edit left a receipt");
    assert!(
        edit.tree.has_button_for("inc"),
        "the re-folded card view-tree carries the new button"
    );

    // The re-folded view-source PARSES through the renderer's own parser (the structured
    // view-tree IS renderable) and carries the new button as a Button node.
    let after_source = editor.view_source();
    let after_tree = parse_view_tree(&after_source)
        .expect("the re-folded view-source parses as a renderer view-tree");
    assert!(
        node_has_inc_button(&after_tree),
        "the renderer's parse of the edited card carries the inc button node"
    );

    // ── AFTER: render the re-minted edited card (now WITH the button) → PNG #1 ─────────
    // Re-mint from the authored manifest so the rendered cell carries the patched program.
    let after_applet = Rc::new(RefCell::new(editor.remint([0xC1; 32], [0u8; 32])));
    let a1 = after_applet.clone();
    let t1 = after_tree.clone();
    let w1 = hr
        .open(420.0, 240.0, move |_window, cx| {
            cx.new(|_cx| AppletView::new(a1, t1))
        })
        .expect("open the edited card window");
    let frame1 = hr.capture(w1.into()).expect("capture after-frame");
    let png1 = out.join("card-after-edit.png");
    frame1.save(&png1).expect("save after PNG");

    // THE LOAD-BEARING ASSERTION: the edited card renders DIFFERENTLY — the new "+1"
    // button visibly appeared. The UI changed from within, and it reached pixels.
    assert_ne!(
        frame0.as_raw(),
        frame1.as_raw(),
        "the edited card renders differently (the new +1 button appeared on re-render)"
    );

    println!("RENDERED the card-edit keystone (real gpui-component pixels):");
    println!("  before : {}", png0.display());
    println!("  after  : {}", png1.display());
}

/// Walk a renderer `ViewNode` looking for a button whose onClick fires `inc`.
fn node_has_inc_button(node: &deos_view::ViewNode) -> bool {
    use deos_view::ViewNode;
    match node {
        ViewNode::Button { turn, .. } => turn == "inc",
        ViewNode::VStack(kids)
        | ViewNode::Row(kids)
        | ViewNode::List(kids)
        | ViewNode::Table(kids) => kids.iter().any(node_has_inc_button),
        _ => false,
    }
}
