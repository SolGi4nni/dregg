//! **THE DOCUMENT COMPOSER IS REACHABLE BY A REAL GESTURE, NOT ONLY BY A TEST HOOK.**
//!
//! The compose-a-document-from-cells surface (`document_composer`) was wired to the
//! desktop, but every one of `DeosDesktop`'s `compose_*` methods was private and called
//! by NOTHING except its own `bake_compose_*` test hook. No keyboard, mouse or menu path
//! reached it: the feature was green, exercised, and unreachable by a user — a shape the
//! test suite proves works and the shipped desktop cannot perform. "Had no entry point"
//! is not fixed by an entry point only tests can use.
//!
//! THE GATE: drive the gesture the way a user does. Right-click a cell (the REAL
//! `actions_for` menu), find the compose entry among the offered actions, and click it
//! through the same dispatch `render_context_menu`'s row listener runs — no
//! `bake_compose_*` anywhere in this file. If the menu does not OFFER the gesture, or
//! the click does not reach the composer, this test fails. (The only thing standing in
//! for the user is the mouse hit-test, which a headless window cannot perform; the
//! menu, its enablement, and the actuation are the shipped ones.)
//!
//! The refusal half rides along: with no document open there is nothing to compose INTO,
//! and the menu must say so with a DIMMED row rather than an entry that silently does
//! nothing.
//!
//! Run: `cd starbridge-v2 && cargo test --no-default-features \
//!   --features "gpui-ui,embedded-executor,render-capture" \
//!   --test deos_desktop_composer_has_a_real_entry_point -- --nocapture`

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

/// The menu entry index whose label contains `needle`, if any.
fn entry_with(entries: &[(String, bool)], needle: &str) -> Option<usize> {
    entries.iter().position(|(l, _)| l.contains(needle))
}

#[test]
fn the_right_click_menu_composes_a_cell_into_an_open_document() {
    let layout_path =
        std::env::temp_dir().join(format!("deos-composer-entry-{}.json", std::process::id()));
    let _ = std::fs::remove_file(&layout_path);

    let (world, anchors) = demo_world();
    let [treasury, _service, user] = anchors;
    let shared = Rc::new(RefCell::new(world));

    let text_system: Arc<dyn PlatformTextSystem> =
        Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
    text_system
        .add_fonts(vec![Cow::Borrowed(LILEX), Cow::Borrowed(IBM_PLEX)])
        .expect("fonts");
    let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
        gpui_platform::current_headless_renderer()
    });
    cx.update(gpui_component::init);

    let world_for_view = shared.clone();
    let lp = layout_path.clone();
    let desk_cell: Rc<RefCell<Option<gpui::Entity<DeosDesktop>>>> = Rc::new(RefCell::new(None));
    let desk_sink = desk_cell.clone();
    let _window = cx
        .open_window(size(px(900.), px(640.)), move |window, cx| {
            let view = cx.new(|cx| DeosDesktop::new(world_for_view, user, lp, window, cx));
            *desk_sink.borrow_mut() = Some(view.clone());
            cx.new(|cx| gpui_component::Root::new(gpui::AnyView::from(view), window, cx))
        })
        .expect("open the headless desktop window");
    cx.run_until_parked();
    let desk = desk_cell.borrow().clone().expect("desktop entity captured");

    // ── (1) NO DOCUMENT OPEN: the gesture is still OFFERED, and it is DIM. ──
    //    A surface that hides the verb entirely teaches nobody it exists.
    desk.update(&mut cx, |d, _cx| d.bake_open_menu(treasury, 40.0, 40.0));
    let cold = cx.update(|cx| desk.read(cx).bake_menu_entries());
    let cold_idx = entry_with(&cold, "Compose into").unwrap_or_else(|| {
        panic!(
            "the cell menu must OFFER a compose-into-document gesture; it offered: {:?}",
            cold.iter().map(|(l, _)| l).collect::<Vec<_>>()
        )
    });
    assert!(
        !cold[cold_idx].1,
        "with no document open there is nothing to compose INTO — the entry must be \
         dimmed, not live: {:?}",
        cold[cold_idx]
    );
    let clicked_cold = desk.update(&mut cx, |d, _cx| d.bake_menu_click(cold_idx));
    assert!(
        !clicked_cold,
        "a dimmed row must not actuate (it is the refusal, made visible)"
    );

    // ── (2) OPEN A DOCUMENT, then compose the treasury cell into it. ──
    desk.update(&mut cx, |d, _cx| {
        d.bake_open_doc(user);
        d.bake_edit_doc(user, "A document that will cite a live cell.\n");
    });
    cx.run_until_parked();

    let before_text = cx.update(|cx| desk.read(cx).bake_doc_text(user));
    let before_height = shared.borrow().height();
    let before_children = cx.update(|cx| desk.read(cx).bake_composed_children(user));
    assert!(
        before_children.is_empty(),
        "nothing is composed yet: {before_children:?}"
    );

    // The REAL right-click menu on the treasury icon.
    desk.update(&mut cx, |d, _cx| d.bake_open_menu(treasury, 40.0, 40.0));
    let entries = cx.update(|cx| desk.read(cx).bake_menu_entries());
    let idx = entry_with(&entries, "Compose into").unwrap_or_else(|| {
        panic!(
            "with a document open the menu must offer composing INTO it; it offered: {:?}",
            entries.iter().map(|(l, _)| l).collect::<Vec<_>>()
        )
    });
    assert!(
        entries[idx].1,
        "with a document open the compose entry must be LIVE: {:?}",
        entries[idx]
    );
    println!("menu entry driven: {:?}", entries[idx]);

    // THE CLICK — the same dispatch the rendered menu row runs.
    let clicked = desk.update(&mut cx, |d, _cx| d.bake_menu_click(idx));
    cx.run_until_parked();
    assert!(clicked, "the live compose entry must actuate");

    // ── (3) THE COMPOSER RAN: a live child, a spliced block, a verified turn. ──
    let children = cx.update(|cx| desk.read(cx).bake_composed_children(user));
    assert!(
        children
            .iter()
            .any(|(c, _, _, live)| *c == treasury && *live),
        "the clicked gesture must have embedded the treasury cell as a LIVE child of \
         the document's composition; got {children:?}"
    );

    let after_text = cx.update(|cx| desk.read(cx).bake_doc_text(user));
    assert_ne!(
        after_text, before_text,
        "the composed block must be spliced into the document's prose"
    );
    assert!(
        after_text.contains("{composition") && after_text.contains("{compose dregg://"),
        "the document must carry the composed block with its dregg:// citation: \
         {after_text:?}"
    );
    assert!(
        after_text.contains("A document that will cite a live cell."),
        "the splice must preserve the prose it was composed into: {after_text:?}"
    );

    let after_height = shared.borrow().height();
    assert!(
        after_height > before_height,
        "a composition gesture is a REAL verified turn on the heap ({before_height} -> \
         {after_height})"
    );

    // The menu closed on the click, as a real menu does.
    assert!(
        cx.update(|cx| desk.read(cx).bake_menu_entries()).is_empty(),
        "actuating a menu row dismisses the menu"
    );

    let _ = std::fs::remove_file(&layout_path);
    println!(
        "OK composer entry point: right-click → '{}' → {} live child(ren), height \
         {before_height} -> {after_height}",
        entries[idx].0,
        children.len()
    );
}
