//! **THE TWO THINGS THE `Stitcher` HAS THAT THE DELETED INLINE COPY DID NOT — REACHABLE.**
//!
//! The desktop's conflict surface was cut over to `starbridge_v2::stitcher` and the
//! inline duplicate deleted. But `Stitcher::custom_resolution` (a reader types their OWN
//! reading — neither side verbatim) and `Stitcher::blame` (who authored the reading that
//! SURVIVED a settlement) existed **only in the module, called only by its own unit
//! tests**. They are the entire reason routing through the `Stitcher` was worth doing,
//! and no user could reach either — which also made `Stitcher::with_granularity` steer
//! nothing observable in the shipped desktop, since the one thing it steers is the grain
//! a typed resolution is diffed at.
//!
//! THE GATE, driven through the painted surface (`conflict_rows` → what the renderer
//! paints, verbatim) and the same dispatch its rows' buttons run:
//!
//!   1. A held conflict OFFERS a typed resolution per region. Before any settlement it
//!      shows NO authorship face (blame that is always on is not evidence a settlement
//!      was attributed — it is wallpaper).
//!   2. Settling one region of two with the CO-AUTHOR's reading makes the surface
//!      attribute that surviving line **to the co-author** — the atom-stable blame, on
//!      the surface, naming an author that is not the operator.
//!   3. Typing a reading that is NEITHER alternative and committing it lands a real,
//!      content-addressed **receipt**, collapses the last region, and publishes the
//!      merge — with the typed words in the document and both contested readings of
//!      that region gone from it.
//!
//! Run: `cd starbridge-v2 && cargo test --features native-full \
//!   --test deos_desktop_typed_resolution_and_blame -- --nocapture`

#![cfg(all(feature = "gpui-ui", feature = "embedded-executor"))]

use std::borrow::Cow;
use std::cell::RefCell;
use std::rc::Rc;
use std::sync::Arc;

use gpui::{px, size, AppContext, HeadlessAppContext, PlatformTextSystem};
use gpui_wgpu::CosmicTextSystem;

use starbridge_v2::deos_desktop::DeosDesktop;
use starbridge_v2::stitcher::Side;
use starbridge_v2::world::demo_world;

static LILEX: &[u8] = include_bytes!("../assets/fonts/Lilex-Regular.ttf");
static IBM_PLEX: &[u8] = include_bytes!("../assets/fonts/IBMPlexSans-Regular.ttf");

/// The index of the single surface row containing `needle`, or a panic that prints the
/// whole painted surface (an unoffered gesture is exactly what this test catches).
fn row_with(rows: &[String], needle: &str, why: &str) -> usize {
    rows.iter()
        .position(|r| r.contains(needle))
        .unwrap_or_else(|| {
            panic!("{why}\n  looked for {needle:?} in the painted conflict surface:\n    {rows:#?}")
        })
}

#[test]
fn a_typed_resolution_is_receipted_and_blame_attributes_the_surviving_line() {
    let layout_path =
        std::env::temp_dir().join(format!("deos-typedres-{}.json", std::process::id()));
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

    // ── A divergence with TWO contested regions: both authors rewrote the first line
    //    AND the last line, differently. Two regions is the point — settling one must
    //    leave the surface HELD, which is the only state in which "who wrote the
    //    reading that survived a settlement" is a question the surface can answer.
    desk.update(&mut cx, |d, _cx| {
        d.bake_open_doc(user);
        d.bake_edit_doc(user, "one\ntwo\nthree\n");
        d.bake_fork_branch(user);
        d.bake_set_branch_text(user, "one-COAUTHOR\ntwo\nthree-COAUTHOR\n");
        d.bake_edit_doc(user, "one-MINE\ntwo\nthree-MINE\n");
        d.bake_stitch_branch(user);
    });
    cx.run_until_parked();

    assert_eq!(
        cx.update(|cx| desk.read(cx).bake_conflict_count(user)),
        Some(2),
        "the premise: two rewritten lines are TWO first-class conflict regions"
    );

    // ── (1) THE TYPED RESOLUTION IS OFFERED, AND BLAME IS NOT YET WALLPAPER. ──
    let rows = cx.update(|cx| desk.read(cx).bake_conflict_surface(user));
    println!("── CONFLICT SURFACE ({} rows) ──", rows.len());
    for r in &rows {
        println!("    {r:?},");
    }
    let typed_rows: Vec<&String> = rows
        .iter()
        .filter(|r| r.starts_with("resolve (typed):"))
        .collect();
    assert_eq!(
        typed_rows.len(),
        2,
        "every held region must offer the reader their OWN wording — neither side \
         verbatim; the surface offered {typed_rows:?} of {rows:#?}"
    );
    assert!(
        !rows.iter().any(|r| r.starts_with("blame")),
        "nothing has been settled yet, so there is no surviving settled reading to \
         attribute — an always-on authorship face proves nothing: {rows:#?}"
    );

    // ── (2) SETTLE ONE REGION WITH THE CO-AUTHOR'S READING — the surface must then
    //        attribute the surviving line TO THE CO-AUTHOR (not to whoever clicked).
    //    Region 1 is settled first so the remaining region keeps index 0.
    let keep_coauthor = rows
        .iter()
        .position(|r| r.starts_with("resolve: keep") && r.contains("three-COAUTHOR"))
        .unwrap_or_else(|| {
            panic!(
                "the surface must offer a one-click resolution KEEPING the co-author's \
                 reading of the contested last line: {rows:#?}"
            )
        });
    println!("clicking row {keep_coauthor}: {:?}", rows[keep_coauthor]);
    assert!(
        desk.update(&mut cx, |d, _cx| d
            .bake_conflict_row_click(user, keep_coauthor)),
        "a resolution row must actuate"
    );
    cx.run_until_parked();

    let rows = cx.update(|cx| desk.read(cx).bake_conflict_surface(user));
    println!("── AFTER ONE SETTLEMENT ({} rows) ──", rows.len());
    for r in &rows {
        println!("    {r:?},");
    }
    assert!(
        !rows.is_empty(),
        "one region of two settled — the stitch is still HELD and still painted"
    );
    let blamed = rows
        .iter()
        .position(|r| r.starts_with("blame") && r.contains("three-COAUTHOR"))
        .unwrap_or_else(|| {
            panic!(
                "after a settlement the surface must attribute the SURVIVING reading to \
                 whoever authored it (the atom-stable blame): {rows:#?}"
            )
        });
    assert!(
        rows[blamed].contains("co-author (@"),
        "the surviving line was written by the CO-AUTHOR and must be attributed to them, \
         not to the operator who clicked the settlement: {:?}",
        rows[blamed]
    );

    // ── (3) A TYPED RESOLUTION: neither alternative, in the reader's own words. ──
    //    The base is exactly what picking that side would leave, so what the reader
    //    edits is what the diff is taken against (the shipped input is seeded with it).
    let base = cx
        .update(|cx| desk.read(cx).bake_custom_resolution_base(user, 0, Side::A))
        .expect("a held region previews the reading a pick would leave");
    println!("typed-resolution base: {base:?}");
    assert!(
        base.contains("three-COAUTHOR"),
        "the base carries the ALREADY-settled region's reading: {base:?}"
    );
    let typed = base
        .replace("one-MINE", "one-AGREED")
        .replace("one-COAUTHOR", "one-AGREED");
    assert!(
        typed.contains("one-AGREED") && typed != base,
        "the reader types a reading that is NEITHER alternative: {typed:?}"
    );
    desk.update(&mut cx, |d, _cx| {
        d.bake_type_custom_resolution(user, &typed)
    });

    let rows = cx.update(|cx| desk.read(cx).bake_conflict_surface(user));
    let typed_row = row_with(
        &rows,
        "resolve (typed):",
        "the last held region must still offer the typed resolution",
    );
    println!("clicking row {typed_row}: {:?}", rows[typed_row]);
    let before_height = shared.borrow().height();
    assert!(
        desk.update(&mut cx, |d, _cx| d.bake_conflict_row_click(user, typed_row)),
        "the typed-resolution row must actuate"
    );
    cx.run_until_parked();

    // THE RECEIPT — a typed resolution is a real, content-addressed turn, not a
    // buffer edit that skipped the patch algebra.
    let receipt = cx
        .update(|cx| desk.read(cx).bake_last_resolution_receipt(user))
        .expect("the typed resolution lands a receipted patch");
    assert_ne!(receipt, 0, "the receipt is a real patch id: {receipt}");

    // The last region collapsed, so the merge PUBLISHED and the held stitch is gone.
    let after = cx.update(|cx| desk.read(cx).bake_conflict_surface(user));
    assert!(
        after.is_empty(),
        "settling every region publishes the merge and drops the held stitch: {after:#?}"
    );
    assert_eq!(
        cx.update(|cx| desk.read(cx).bake_conflict_count(user)),
        None,
        "no stitch is held after publication"
    );

    // …and the published document reads the TYPED words, with both contested readings
    // of that region gone — the reader's reading, not either author's.
    let text = cx.update(|cx| desk.read(cx).bake_doc_text(user));
    println!("published document: {text:?}");
    assert!(
        text.contains("one-AGREED"),
        "the published document reads the typed resolution: {text:?}"
    );
    assert!(
        !text.contains("one-MINE") && !text.contains("one-COAUTHOR"),
        "neither contested reading of the typed region survives: {text:?}"
    );
    assert!(
        text.contains("three-COAUTHOR"),
        "the earlier settlement is still in the published reading: {text:?}"
    );
    assert!(
        shared.borrow().height() > before_height,
        "publishing the resolved merge is a REAL verified turn on the document cell"
    );

    let _ = std::fs::remove_file(&layout_path);
    println!("OK typed resolution receipted (#{receipt}) and blame attributed on the surface");
}
