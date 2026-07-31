//! **THE DESKTOP'S TRANSCLUDE GESTURE IS A VERIFIED TRANSCLUSION — AND IT REFUSES A FORGERY.**
//!
//! `DeosDesktop::transclude_into` (the drag-a-cell-icon-onto-a-document compose) used
//! to build a `format!` string of four ledger fields and append it to the buffer. A
//! `format!` interpolates ANY 32 bytes: a cell id that names nothing on the ledger —
//! never published, never finalized, never attested — rendered a perfectly ordinary
//! looking `{transclude dregg://…}` line, indistinguishable from a real quote.
//!
//! THE TOOTH THIS TEST IS: a transclusion must resolve through the REAL verified
//! finalized read (`WholeCellTransclusion::embed` — content → commitment → receipt →
//! receipt-stream root → quorum) before a single character reaches the document. An id
//! the live World does not hold is not a `dregg://` origin, so there is nothing to
//! open, so the document is left EXACTLY as it was and the desktop narrates the
//! refusal. No line, no patch, no verified turn, no receipt.
//!
//! The positive half rides along: a transclusion of a REAL live cell writes a line
//! carrying the CITED RECEIPT of the finalized read and its per-viewer visibility —
//! and it still parses back through `parse_transclusion_ref`, so the two-way backlink
//! inversion the Links window reads keeps working.
//!
//! Run: `cd starbridge-v2 && cargo test --features native-full \
//!   --test deos_desktop_transclude_is_verified -- --nocapture`

#![cfg(all(feature = "gpui-ui", feature = "embedded-executor"))]

use std::borrow::Cow;
use std::cell::RefCell;
use std::rc::Rc;
use std::sync::Arc;

use gpui::{px, size, AppContext, HeadlessAppContext, PlatformTextSystem};
use gpui_wgpu::CosmicTextSystem;

use dregg_types::CellId;
use starbridge_v2::deos_desktop::DeosDesktop;
use starbridge_v2::world::demo_world;

static LILEX: &[u8] = include_bytes!("../assets/fonts/Lilex-Regular.ttf");
static IBM_PLEX: &[u8] = include_bytes!("../assets/fonts/IBMPlexSans-Regular.ttf");

/// A cell id that names NOTHING on the live ledger — 32 bytes a forger picked. It is a
/// perfectly well-formed `CellId` (that is the point: the id space is not a permission
/// system), it is simply not a cell of this World and was therefore never published as
/// a `dregg://` origin.
fn forged_id() -> CellId {
    CellId::from_bytes([0xAB; 32])
}

#[test]
fn transcluding_an_unpublished_cell_leaves_the_document_unchanged_and_refuses() {
    let layout_path =
        std::env::temp_dir().join(format!("deos-transclude-test-{}.json", std::process::id()));
    let _ = std::fs::remove_file(&layout_path);

    let (world, anchors) = demo_world();
    let [treasury, _service, user] = anchors;
    let shared = Rc::new(RefCell::new(world));

    // The forged id really is absent from the live ledger (the premise of the gate).
    assert!(
        shared.borrow().ledger().get(&forged_id()).is_none(),
        "the forged id must name no cell of the live World"
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

    // Open a document on the user cell (the host the compose drops INTO).
    window
        .update(&mut cx, |_root, _w, cx| {
            desk.update(cx, |d, cx| {
                d.bake_open_doc(user);
                cx.notify();
            });
        })
        .unwrap();
    cx.run_until_parked();

    let before_text = window
        .update(&mut cx, |_root, _w, cx| desk.read(cx).bake_doc_text(user))
        .unwrap();
    let before_height = window
        .update(&mut cx, |_root, _w, cx| desk.read(cx).bake_world_height())
        .unwrap();

    // ── THE FORGERY ── drag a cell that does not exist onto the open document.
    window
        .update(&mut cx, |_root, _w, cx| {
            desk.update(cx, |d, cx| {
                d.bake_transclude(forged_id(), user);
                cx.notify();
            });
        })
        .unwrap();
    cx.run_until_parked();

    let after_text = window
        .update(&mut cx, |_root, _w, cx| desk.read(cx).bake_doc_text(user))
        .unwrap();
    let after_height = window
        .update(&mut cx, |_root, _w, cx| desk.read(cx).bake_world_height())
        .unwrap();
    let narration = window
        .update(&mut cx, |_root, _w, cx| desk.read(cx).bake_status_line())
        .unwrap();

    // (1) THE DOCUMENT IS UNCHANGED — not one character of the forged quote landed.
    assert_eq!(
        after_text, before_text,
        "a transclusion of an unpublished cell must leave the document EXACTLY as it was; \
         instead the buffer grew to {after_text:?}"
    );
    let forged_hex: String = forged_id().0.iter().map(|b| format!("{b:02x}")).collect();
    assert!(
        !after_text.contains(&forged_hex),
        "the forged cell id must never appear in the document, got {after_text:?}"
    );
    assert!(
        !after_text.contains("dregg://"),
        "no dregg:// citation may be minted for a cell that was never published"
    );

    // (2) NO VERIFIED TURN LANDED — a refusal does not advance the chronicle.
    assert_eq!(
        after_height, before_height,
        "a refused compose must not commit a revision turn"
    );

    // (3) THE REFUSAL IS NARRATED — the operator is told, not silently ignored.
    let n = narration.to_ascii_lowercase();
    assert!(
        n.contains("refus") || n.contains("not a") || n.contains("unresolvable"),
        "the desktop must narrate the refusal; the status bar said {narration:?}"
    );

    // ── THE POSITIVE HALF ── a REAL live cell transcludes, carries its cited receipt,
    //    and still parses back for the two-way backlink inversion.
    window
        .update(&mut cx, |_root, _w, cx| {
            desk.update(cx, |d, cx| {
                d.bake_transclude(treasury, user);
                cx.notify();
            });
        })
        .unwrap();
    cx.run_until_parked();

    let real_text = window
        .update(&mut cx, |_root, _w, cx| desk.read(cx).bake_doc_text(user))
        .unwrap();
    let treasury_hex: String = treasury.0.iter().map(|b| format!("{b:02x}")).collect();
    assert!(
        real_text.contains(&format!("dregg://{treasury_hex}")),
        "a live cell transcludes to its content-addressed dregg:// origin, got {real_text:?}"
    );
    assert!(
        real_text.contains("receipt"),
        "the transclusion line must cite the finalized read's RECEIPT, got {real_text:?}"
    );

    // The backlink inversion still reads it: the desktop's own two-way scan sees BOTH
    // the forward quote (the host document cites the treasury) and its inverse (the
    // treasury's backlinks list the host document).
    let (outbound, back) = window
        .update(&mut cx, |_root, _w, cx| {
            desk.read(cx).bake_doc_links(user, treasury)
        })
        .unwrap();
    assert!(
        outbound,
        "the verified transclusion must still parse as a forward quote"
    );
    assert!(
        back,
        "the two-way link inversion must still see the verified transclusion as a backlink"
    );

    // …and the FORGERY is in neither direction (nothing was ever written for it).
    let (forged_out, forged_back) = window
        .update(&mut cx, |_root, _w, cx| {
            desk.read(cx).bake_doc_links(user, forged_id())
        })
        .unwrap();
    assert!(
        !forged_out && !forged_back,
        "a refused transclusion must leave NO link in either direction"
    );

    let _ = std::fs::remove_file(&layout_path);
}
