//! **A DOCUMENT CONFLICT IS A FIRST-CLASS STATE, RESOLVED BY A LATER PATCH.**
//!
//! The deos desktop's document editor rides the `dregg_doc` Pijul-shaped patch core
//! (DOCUMENT-LANGUAGE.md): an author forks a confined co-author DRAFT branch, the
//! co-author diverges it, and a STITCH (the pushout) of two edits to the same region
//! yields a **first-class conflict state** — an antichain of live alternatives, each
//! attributed to its author — *not* a rejected merge. Resolution is **just another
//! additive authored patch**; when the document is conflict-free again the merge is
//! PUBLISHED to the committed cell heap (a real verified turn).
//!
//! This drives that whole loop through the live `DeosDesktop` over the real `World`:
//!
//!   1. type a base document → committed to the heap;
//!   2. fork a draft branch, diverge it as a second author, STITCH → assert a genuine
//!      first-class CONFLICT arises (the antichain), with NO heap write (a conflicted
//!      stitch is held, not committed);
//!   3. RESOLVE the conflict with a one-click choice → assert the conflict collapses
//!      AND the published merge lands on the committed heap (height grows; the resolved
//!      prose reads back from the ledger).
//!
//! It locks the branch/stitch/conflict/resolve wiring of the desktop document language.
//!
//! Run: `cd starbridge-v2 && cargo test --no-default-features \
//!   --features "gpui-ui,embedded-executor,render-capture" \
//!   --test deos_desktop_conflict_is_a_state -- --nocapture`

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

/// Read prose back out of a cell's committed heap (the desktop's `read_doc_from_heap`).
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
fn a_document_conflict_is_a_first_class_state_resolved_by_a_later_patch() {
    let layout_path =
        std::env::temp_dir().join(format!("deos-conflict-test-{}.json", std::process::id()));
    let _ = std::fs::remove_file(&layout_path);

    let (world, anchors) = demo_world();
    let [_treasury, _service, user] = anchors;
    let shared = Rc::new(RefCell::new(world));

    let text_system: Arc<dyn PlatformTextSystem> =
        Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
    text_system
        .add_fonts(vec![Cow::Borrowed(LILEX), Cow::Borrowed(IBM_PLEX)])
        .expect("fonts");
    let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
        gpui_platform::current_headless_renderer()
    });
    cx.update(|cx| gpui_component::init(cx));

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

    // ── 1. A base document, committed to the heap. ──
    desk.update(&mut cx, |d, _cx| {
        d.bake_open_doc(user);
        d.bake_edit_doc(user, "Cats are nice.\n");
    });
    let h0 = shared.borrow().height();
    assert_eq!(
        read_doc(&shared.borrow(), &user).as_deref(),
        Some("Cats are nice.\n"),
        "the base document committed to the heap"
    );

    // ── 2. Fork a draft, diverge it as a co-author, STITCH → a first-class conflict. ──
    // The original author also edits the same tail region, so the stitch genuinely
    // contests it (both authors appended different content at the same point).
    desk.update(&mut cx, |d, _cx| {
        d.bake_fork_branch(user);
        // The co-author's divergent line on the draft.
        d.bake_diverge_branch(user, "Dogs are nice too.\n");
        // The original author's own divergent continuation on the main document.
        d.bake_edit_doc(user, "Cats are nice.\nBirds are nice three.\n");
    });
    let h_pre_stitch = shared.borrow().height();
    desk.update(&mut cx, |d, _cx| {
        d.bake_stitch_branch(user);
    });

    let conflicts = cx
        .update(|cx| desk.read(cx).bake_conflict_count(user))
        .expect("a stitch is pending (merged document held)");
    assert!(
        conflicts >= 1,
        "a stitch of two divergent edits to the same region is a FIRST-CLASS conflict \
         (got {conflicts} regions)"
    );
    assert_eq!(
        shared.borrow().height(),
        h_pre_stitch,
        "a CONFLICTED stitch is HELD, not committed — no heap write while the conflict stands"
    );

    // ── 3. Resolve the conflict (one-click choice 0) → the merge PUBLISHES to heap. ──
    let h_pre_resolve = shared.borrow().height();
    desk.update(&mut cx, |d, _cx| {
        d.bake_resolve_conflict(user, 0, 0);
    });
    cx.run_until_parked();

    // After resolving every region, the conflict is gone and the merge is published.
    let remaining = cx.update(|cx| desk.read(cx).bake_conflict_count(user));
    assert!(
        remaining.is_none() || remaining == Some(0),
        "resolving collapses the antichain — no conflict remains (got {remaining:?})"
    );
    let h_post = shared.borrow().height();
    assert!(
        h_post > h_pre_resolve,
        "publishing the resolved merge lands a REAL verified turn on the heap \
         ({h_pre_resolve} -> {h_post})"
    );
    let published = read_doc(&shared.borrow(), &user).unwrap_or_default();
    assert!(
        published.contains("Cats are nice."),
        "the published document retains the shared clean prefix: {published:?}"
    );
    // The resolution kept at least one of the contested alternatives (nothing silently lost).
    assert!(
        published.contains("Birds are nice three.") || published.contains("Dogs are nice too."),
        "the published resolution carries a chosen alternative (no silent loss): {published:?}"
    );

    let _ = std::fs::remove_file(&layout_path);
    println!(
        "OK conflict-as-state: base committed (h{h0}); fork+diverge+stitch → {conflicts} \
         first-class conflict(s) HELD (no heap write at h{h_pre_stitch}); resolve → \
         collapsed + PUBLISHED to heap (h{h_pre_resolve} -> {h_post}); reads back: {:?}",
        published.lines().collect::<Vec<_>>()
    );
}
