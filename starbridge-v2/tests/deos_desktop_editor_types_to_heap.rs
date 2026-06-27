//! **TYPING INTO THE REAL EDITOR WIDGET COMMITS TO THE CELL HEAP.**
//!
//! The deos desktop's document surface is a real `gpui-component` `InputState`
//! (rope-backed, multi-line) — not a static label with append-buttons. This test
//! drives the GENUINE keystroke seam end-to-end in a headless gpui app:
//!
//!   1. boot the live `DeosDesktop` over the demo `World`, open a document on a cell,
//!      and render it once so `ensure_doc_input` builds the live editor entity;
//!   2. TYPE into the REAL `InputState` widget via `insert` (the same path a keystroke
//!      takes — it emits `InputEvent::Change`), which fires the desktop's `Change`
//!      subscription → `edit_doc` → `commit_doc_to_umem_heap`;
//!   3. assert the document committed to the cell's umem-heap: its `heap_root`
//!      boundary MOVED and IS the commitment, the prose reads back verbatim from the
//!      umem-heap, and a reopen re-seeds from that committed boundary.
//!
//! This locks the widget→heap wiring: if the subscription, the editor, or the heap
//! commit regress, this test breaks. It is the companion to
//! `deos_doc_persists_to_cell_heap` (which proves the heap encoding gpui-free); this
//! one proves the REAL WIDGET drives it.
//!
//! Run: `cd starbridge-v2 && cargo test --no-default-features \
//!   --features "gpui-ui,embedded-executor,render-capture" \
//!   --test deos_desktop_editor_types_to_heap -- --nocapture`

#![cfg(all(feature = "gpui-ui", feature = "embedded-executor"))]

use std::borrow::Cow;
use std::cell::RefCell;
use std::rc::Rc;
use std::sync::Arc;

use gpui::{px, size, AppContext, HeadlessAppContext, PlatformTextSystem};
use gpui_wgpu::CosmicTextSystem;

use starbridge_v2::deos_desktop::DeosDesktop;
use starbridge_v2::world::demo_world;

static LILEX: &[u8] = include_bytes!("../assets/fonts/Lilex-Regular.ttf");
static IBM_PLEX: &[u8] = include_bytes!("../assets/fonts/IBMPlexSans-Regular.ttf");

/// Read prose back out of a cell's committed **umem-heap** (`heap_map`, collection
/// `dregg_doc::COLL_TEXT`) — the same read the desktop's `read_doc_from_heap` does,
/// inlined here over the live ledger's umem boundary.
fn read_doc(w: &starbridge_v2::world::World, cell: &dregg_types::CellId) -> Option<String> {
    let state = &w.ledger().get(cell)?.state;
    dregg_doc::text_from_heap(&state.heap_map)
}

/// The cell's committed umem boundary — its resealed `heap_root`, which IS the
/// document's commitment after a `commit_doc_to_umem_heap`.
fn heap_root(w: &starbridge_v2::world::World, cell: &dregg_types::CellId) -> Option<[u8; 32]> {
    Some(w.ledger().get(cell)?.state.heap_root)
}

#[test]
fn typing_into_the_real_input_widget_commits_to_the_cell_heap() {
    let layout_path =
        std::env::temp_dir().join(format!("deos-editor-test-{}.json", std::process::id()));
    let _ = std::fs::remove_file(&layout_path);

    let (world, anchors) = demo_world();
    let [_treasury, _service, user] = anchors;
    let pre_height = world.height();
    let shared = Rc::new(RefCell::new(world));

    // No committed document on `user` yet.
    assert!(
        read_doc(&shared.borrow(), &user).is_none(),
        "a fresh cell carries no committed document"
    );

    let text_system: Arc<dyn PlatformTextSystem> =
        Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
    text_system
        .add_fonts(vec![Cow::Borrowed(LILEX), Cow::Borrowed(IBM_PLEX)])
        .expect("fonts");
    let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
        gpui_platform::current_headless_renderer()
    });
    cx.update(gpui_component::init);

    // The desktop must sit under a `gpui_component::Root` — the `InputState` widget
    // reaches `Root::read(window)` on interactive edits (it panics otherwise). We keep
    // a handle to the inner `DeosDesktop` entity to drive it, exactly as main.rs's
    // interactive surfaces do.
    let world_for_view = shared.clone();
    let lp = layout_path.clone();
    let desk_cell: Rc<RefCell<Option<gpui::Entity<DeosDesktop>>>> = Rc::new(RefCell::new(None));
    let desk_sink = desk_cell.clone();
    let window = cx
        .open_window(size(px(900.), px(640.)), move |window, cx| {
            let view = cx.new(|cx| DeosDesktop::new(world_for_view, user, lp, window, cx));
            *desk_sink.borrow_mut() = Some(view.clone());
            cx.new(|cx| gpui_component::Root::new(gpui::AnyView::from(view), window, cx))
        })
        .expect("open the headless desktop window");
    cx.run_until_parked();
    let desk = desk_cell.borrow().clone().expect("desktop entity captured");

    // Open the document editor + render once: this is what builds the live `InputState`
    // (lazily, in `render_doc_body`).
    window
        .update(&mut cx, |_root, _w, cx| {
            desk.update(cx, |d, cx| {
                d.bake_open_doc(user);
                cx.notify();
            });
        })
        .unwrap();
    cx.run_until_parked();

    let input = window
        .update(&mut cx, |_root, _w, cx| desk.read(cx).bake_doc_input(user))
        .unwrap()
        .expect("the live editor entity exists after the doc body rendered");

    let pre = shared.borrow().height();
    assert_eq!(
        pre, pre_height,
        "no turn yet (just opened the empty editor)"
    );
    // The empty document's committed umem boundary (a fresh cell's empty-heap root).
    let boundary_before = heap_root(&shared.borrow(), &user).expect("user cell exists");

    // TYPE into the REAL widget — `insert` emits `InputEvent::Change`, which fires the
    // desktop's subscription → `edit_doc` → `commit_doc_to_umem_heap`.
    let typed = "the operator typed THIS into the real editor widget.";
    window
        .update(&mut cx, |_desk, window, cx| {
            input.update(cx, |st, cx| st.insert(typed, window, cx));
        })
        .unwrap();
    cx.run_until_parked();

    // The keystroke landed a REAL verified revision turn on the committed heap.
    let post = shared.borrow().height();
    assert!(
        post > pre,
        "typing into the editor must land a verified turn on the heap ({pre} -> {post})"
    );
    assert_eq!(
        read_doc(&shared.borrow(), &user).as_deref(),
        Some(typed),
        "the typed prose reads back verbatim from the COMMITTED umem-heap (not a buffer)"
    );

    // ── THE BOUNDARY IS THE COMMITMENT ── the edit MOVED the cell's committed umem
    // `heap_root`, and that live boundary equals what the desktop surfaces. The
    // document genuinely committed TO the umem-heap (boundary == commitment).
    let boundary_after = heap_root(&shared.borrow(), &user).expect("user cell exists");
    assert_ne!(
        boundary_after, boundary_before,
        "the edit moved the cell's committed umem boundary (heap_root)"
    );
    let surfaced = window
        .update(&mut cx, |_desk, _w, cx| {
            desk.read(cx).bake_doc_umem_boundary(user)
        })
        .unwrap()
        .expect("the live umem boundary is readable");
    assert_eq!(
        surfaced, boundary_after,
        "the surfaced umem boundary IS the cell's committed heap_root (not a derived witness)"
    );

    // The editor's own value agrees with what was committed (the widget IS the buffer).
    let widget_value = window
        .update(&mut cx, |_desk, _w, cx| input.read(cx).value().to_string())
        .unwrap();
    assert_eq!(
        widget_value, typed,
        "the live editor widget holds exactly the committed prose"
    );

    // ── THE DOCUMENT IS THE CELL: close + reopen re-seeds FROM THE COMMITTED HEAP ──
    // Wipe the sidecar so the only surviving source of the prose is the cell's
    // committed umem-heap. Close the doc window (drops the live editor + its sub),
    // then reopen + render — the FRESH `InputState` must re-seed verbatim from the
    // umem boundary, with NO new turn (reopening reads; it does not write).
    let _ = std::fs::remove_file(&layout_path);
    window
        .update(&mut cx, |_root, _w, cx| {
            desk.update(cx, |d, cx| {
                d.bake_close_doc(user);
                cx.notify();
            });
        })
        .unwrap();
    cx.run_until_parked();

    let height_after_close = shared.borrow().height();
    window
        .update(&mut cx, |_root, _w, cx| {
            desk.update(cx, |d, cx| {
                d.bake_open_doc(user);
                cx.notify();
            });
        })
        .unwrap();
    cx.run_until_parked();

    let reopened = window
        .update(&mut cx, |_root, _w, cx| {
            desk.read(cx)
                .bake_doc_input(user)
                .map(|e| e.read(cx).value().to_string())
        })
        .unwrap()
        .expect("a fresh editor exists after reopen");
    assert_eq!(
        reopened, typed,
        "the reopened editor re-seeds VERBATIM from the committed umem-heap (the \
         document IS the cell; the sidecar was wiped)"
    );
    // The committed boundary is unchanged by a read-only reopen, and still equals the
    // boundary that bound the typed prose — the commitment persisted across reopen.
    assert_eq!(
        heap_root(&shared.borrow(), &user),
        Some(boundary_after),
        "the committed umem boundary persists across close + reopen (a read does not move it)"
    );
    assert_eq!(
        shared.borrow().height(),
        height_after_close,
        "reopening a document READS the heap — it must not write a new turn"
    );

    let _ = std::fs::remove_file(&layout_path);
    println!(
        "OK typed {} bytes into the REAL gpui-component editor → Change → edit_doc → \
         committed umem-heap (boundary moved + IS the commitment; height {pre} -> {post}); \
         reads back verbatim from the ledger umem boundary; and after close + sidecar-wipe \
         + reopen, the FRESH editor re-seeds verbatim from the committed boundary with no \
         new turn — the document IS the cell, its commitment IS its umem heap_root.",
        typed.len()
    );
}
