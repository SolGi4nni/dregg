//! THE PROOF, BY RUNNING: a deos-js applet's view-tree renders to REAL gpui-component
//! pixels (a PNG), a button click fires a REAL verified turn, and the bound value
//! updates on re-render.
//!
//! The flow (all in ONE `#[test]` — SpiderMonkey is a process-global, thread-bound
//! singleton, so the JS engine boots once):
//!
//!   1. Mint a counter applet (slot 0 = count; `inc` is a Signature-gated affordance the
//!      driver holds). Run its JS in real SpiderMonkey: build the `deos.ui.*` view-tree
//!      (text + bound count + +1 button), tag the bind's slot, and stash
//!      `JSON.stringify(tree)` into ephemeral view-state. The bridge reads it back and
//!      parses the REAL engine-produced tree.
//!   2. Render the tree to a gpui frame via the headless offscreen-wgpu path (the same
//!      one the cockpit bakes through) → capture PNG #1 (count = 0).
//!   3. Fire the button's handler = a REAL cap-gated verified turn (a `TurnReceipt`) on
//!      the shared applet; assert exactly one receipt committed and the model advanced.
//!   4. Re-render (immediate-mode: the `bind` re-reads the live ledger) → capture PNG #2
//!      (count = 1). Assert the two frames DIFFER (the bound value visibly updated).
//!   5. Also render the moldable `present()` faces through the SAME widget vocabulary
//!      (the §7 unification) → capture PNG #3.

use std::cell::RefCell;
use std::path::PathBuf;
use std::rc::Rc;

use deos_js::applet::{pack_u64, Affordance, Applet};
use deos_js::JsRuntime;
use dregg_cell::AuthRequired;
use gpui::AppContext;

use deos_view::headless::HeadlessRender;
use deos_view::{build_live_view, AppletView, FacesView};

static LILEX: &[u8] = include_bytes!("../assets/fonts/Lilex-Regular.ttf");
static IBM_PLEX: &[u8] = include_bytes!("../assets/fonts/IBMPlexSans-Regular.ttf");

/// A counter applet: slot 0 holds the count; `inc` adds `arg` (Signature-gated, held).
fn counter_applet(seed: u8) -> Applet {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    let inc = Affordance {
        name: "inc".into(),
        required: AuthRequired::Signature,
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
        AuthRequired::Signature,
    )
}

fn out_dir() -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/render-out");
    std::fs::create_dir_all(&dir).expect("create render-out dir");
    dir
}

#[test]
fn applet_view_tree_renders_to_real_gpui_pixels_with_a_live_turn() {
    // SpiderMonkey (with the JIT) needs a large native stack and is thread-bound: the
    // default ~2MB test-harness worker stack underflows SM's stack-quota guard. Run the
    // whole flow (engine + headless render) on a dedicated 64MB-stack thread — the same
    // pattern deos-js's own spike test uses. The headless Metal renderer creates a
    // bare MTLDevice (no Cocoa window: `show:false`), which is fine off the main thread.
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(render_proof_body)
        .expect("spawn big-stack render thread")
        .join()
        .expect("render proof thread");
}

fn render_proof_body() {
    let out = out_dir();

    // ── 1. Drive the applet's JS in real SpiderMonkey + extract its view-tree ────────
    // The bind closure is not serializable, so we tag the bind node with the model slot
    // it reads (slot 0) — the renderer re-reads that slot off the live ledger. The view
    // build commits NOTHING; only firing the button does.
    let key = deos_view::view_tree_key();
    let applet_js = format!(
        r#"
        var app = deos.applet({{ affordances: ["inc"] }});
        var b = deos.ui.bind(function() {{ return app.get(0); }});
        b.props.slot = 0;            // tag the slot the renderer re-reads
        b.props.label = "count: ";   // a human prefix on the bound value
        var tree = deos.ui.vstack(
            deos.ui.text("Counter applet"),
            b,
            deos.ui.button("+1", "inc", 1)
        );
        app.view.set("{key}", JSON.stringify(tree));
        0;
    "#
    );

    let mut rt = JsRuntime::new().expect("boot SpiderMonkey");
    let live = build_live_view(&mut rt, counter_applet(0xF2), &applet_js)
        .expect("extract the applet view-tree");

    // The view-tree build left NO receipt (it is data, not a turn).
    assert_eq!(
        live.applet.receipt_count(),
        0,
        "building the view-tree committed nothing"
    );
    assert_eq!(live.applet.get_u64(0), 0, "the counter starts at 0");

    // Share the live applet so the rendered button's handler + the bind re-read both
    // drive the SAME sovereign cell.
    let shared = Rc::new(RefCell::new(live.applet));
    let tree = live.tree;

    // ── 2. Boot the headless renderer + open the applet view → PNG #1 (count = 0) ────
    let mut hr = HeadlessRender::boot("Lilex", &[LILEX, IBM_PLEX]).expect("boot headless gpui");

    let view_applet = shared.clone();
    let view_tree = tree.clone();
    let window = hr
        .open(420.0, 240.0, move |_window, cx| {
            cx.new(|_cx| AppletView::new(view_applet, view_tree))
        })
        .expect("open the applet window");

    let frame0 = hr.capture(window.into()).expect("capture frame 0");
    let png0 = out.join("applet-count-0.png");
    frame0.save(&png0).expect("save PNG #0");
    assert!(frame0.width() > 0 && frame0.height() > 0, "frame 0 has pixels");

    // ── 3. Fire the button's handler — a REAL cap-gated verified turn ────────────────
    // This is exactly what the rendered Button's `on_click` does (fire the affordance
    // named by the view-tree's onClick). We invoke it on the shared applet directly so
    // the test can assert on the receipt.
    let receipt = shared
        .borrow_mut()
        .fire("inc", 1)
        .expect("the +1 affordance fires a verified turn");
    assert_ne!(
        receipt.receipt_hash(),
        [0u8; 32],
        "a real TurnReceipt committed"
    );
    assert_eq!(
        shared.borrow().receipt_count(),
        1,
        "exactly one verified turn committed"
    );
    assert_eq!(
        shared.borrow().get_u64(0),
        1,
        "the model advanced 0 -> 1 (the bound value will re-read this)"
    );

    // ── 4. Re-render — drive the FINE-GRAINED hook → PNG #2 (count = 1) ──────────────
    // The committed turn touched slot 0. Feed that to the renderer's signal registry via
    // `on_committed_turn(&[0])`: ONLY the slot-0 binding re-reads the live ledger into its
    // value cache (the whole tree is NOT re-evaluated). The dirty set is exactly that one
    // binding. `capture` then refreshes + bakes the new frame (the bind paints the cache).
    let dirty = hr
        .update_root(window, |view, _w, _cx| view.on_committed_turn(&[0]))
        .expect("drive the fine-grained turn hook");
    assert_eq!(
        dirty,
        vec![deos_js::signals::BindingId(0)],
        "the +1 turn dirtied ONLY the slot-0 binding (fine-grained, not the whole tree)"
    );
    hr.update(|cx| cx.refresh_windows());
    let frame1 = hr.capture(window.into()).expect("capture frame 1");
    let png1 = out.join("applet-count-1.png");
    frame1.save(&png1).expect("save PNG #1");

    // THE LOAD-BEARING ASSERTION: the bound value visibly changed (0 -> 1), so the two
    // frames are NOT byte-identical. The view-tree rendered REAL widgets whose bound
    // content tracked a real verified turn.
    assert_ne!(
        frame0.as_raw(),
        frame1.as_raw(),
        "the rendered frame changed after the turn (the bound count re-read 0 -> 1)"
    );

    // ── 5. The moldable present() faces through the SAME widget vocabulary ───────────
    let faces = FacesView::for_applet(&shared.borrow()).expect("the applet cell has faces");
    assert!(faces.face_count() >= 1, "at least the RawFields face is present");
    let window_faces = hr
        .open(520.0, 420.0, move |_window, cx| {
            cx.new(|_cx| FacesView::for_applet(&shared.borrow()).expect("faces"))
        })
        .expect("open the faces window");
    let frame_faces = hr.capture(window_faces.into()).expect("capture faces frame");
    let png_faces = out.join("applet-faces.png");
    frame_faces.save(&png_faces).expect("save faces PNG");

    println!("RENDERED PNGs (real gpui-component widgets, offscreen wgpu):");
    println!("  count=0 : {}", png0.display());
    println!("  count=1 : {}", png1.display());
    println!("  faces   : {}", png_faces.display());
    println!(
        "frame dims: {}x{} (device px, 2x scale)",
        frame0.width(),
        frame0.height()
    );
}
