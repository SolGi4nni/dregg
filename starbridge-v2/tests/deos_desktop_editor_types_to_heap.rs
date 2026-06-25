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
//!      subscription → `edit_doc` → `commit_doc_text_to_heap`;
//!   3. assert the prose landed on the COMMITTED cell heap (a verified `SetField`
//!      revision turn: the World height grew, and the text reads back from the ledger).
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

use gpui::{AppContext, HeadlessAppContext, PlatformTextSystem, px, size};
use gpui_wgpu::CosmicTextSystem;

use starbridge_v2::deos_desktop::{DOC_TEXT_BASE, DeosDesktop};
use starbridge_v2::world::demo_world;

static LILEX: &[u8] = include_bytes!("../assets/fonts/Lilex-Regular.ttf");
static IBM_PLEX: &[u8] = include_bytes!("../assets/fonts/IBMPlexSans-Regular.ttf");

/// Read prose back out of a cell's committed heap (`fields_map`) — the same read the
/// desktop's `read_doc_from_heap` does, inlined here over the live ledger.
fn read_doc(w: &starbridge_v2::world::World, cell: &dregg_types::CellId) -> Option<String> {
    const CHUNK: usize = 32;
    const MAX: u64 = 1024;
    let state = &w.ledger().get(cell)?.state;
    let len_fe = state.get_field_ext(DOC_TEXT_BASE)?;
    let byte_len = u64::from_le_bytes(len_fe[..8].try_into().ok()?) as usize;
    let mut bytes = Vec::with_capacity(byte_len);
    let mut chunk = 0u64;
    while bytes.len() < byte_len && chunk < MAX {
        let fe = state
            .get_field_ext(DOC_TEXT_BASE + 1 + chunk)
            .unwrap_or([0u8; 32]);
        let take = (byte_len - bytes.len()).min(CHUNK);
        bytes.extend_from_slice(&fe[..take]);
        chunk += 1;
    }
    Some(String::from_utf8_lossy(&bytes).into_owned())
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
    cx.update(|cx| gpui_component::init(cx));

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

    // TYPE into the REAL widget — `insert` emits `InputEvent::Change`, which fires the
    // desktop's subscription → `edit_doc` → `commit_doc_text_to_heap`.
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
        "the typed prose reads back verbatim from the COMMITTED cell heap (not a buffer)"
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
    // committed `fields_map`. Close the doc window (drops the live editor + its sub),
    // then reopen + render — the FRESH `InputState` must re-seed verbatim from the
    // ledger heap, with NO new turn (reopening reads; it does not write).
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
        "the reopened editor re-seeds VERBATIM from the committed cell heap (the \
         document IS the cell; the sidecar was wiped)"
    );
    assert_eq!(
        shared.borrow().height(),
        height_after_close,
        "reopening a document READS the heap — it must not write a new turn"
    );

    let _ = std::fs::remove_file(&layout_path);
    println!(
        "OK typed {} bytes into the REAL gpui-component editor → Change → edit_doc → \
         committed heap (height {pre} -> {post}); reads back verbatim from the ledger; \
         and after close + sidecar-wipe + reopen, the FRESH editor re-seeds verbatim \
         from the committed heap with no new turn — the document IS the cell.",
        typed.len()
    );
}
