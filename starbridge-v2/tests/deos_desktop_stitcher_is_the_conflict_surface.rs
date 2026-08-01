//! **THE DESKTOP'S CONFLICT SURFACE IS THE `Stitcher`, AND THE CUTOVER CHANGED NOTHING.**
//!
//! `starbridge_v2::stitcher` (authoring surface #3) and `deos_desktop`'s inline
//! branch/stitch/resolve code were TWO IMPLEMENTATIONS of one thing: both stitched two
//! divergent `dregg_doc::History`s into a pushout, both read the antichain off
//! `content(&graph).conflicts()`, both built the one-click menu from `resolutions_for`,
//! both committed the chosen patch. Two shapes that agree today are two shapes that
//! disagree later, so the desktop now CALLS the stitcher and the inline copy is gone.
//!
//! ⚠ THIS IS A BEHAVIOUR-PRESERVATION GATE, NOT A RED-TO-GREEN ONE. A refactor whose
//! whole claim is "nothing observable changed" has no honest failing-first state, and
//! manufacturing one would be a lie. What this test does instead is PIN the surface: it
//! drives the real desktop through fork → diverge → stitch and asserts the conflict
//! view's rows — every string a user reads, in paint order, including the umem boundary
//! that binds both alternatives — against a literal captured from the pre-cutover build.
//! The renderer paints exactly these rows and decides no string of its own
//! (`DeosDesktop::conflict_rows` / `ConflictRow`), so this IS the painted surface rather
//! than a summary of it, and any drift in what the user sees breaks this assertion.
//!
//! The anti-vacuity teeth, so an emptied or trivialised surface cannot pass: the row
//! list must be non-empty, must carry BOTH authors' provenance labels and BOTH of their
//! contested readings, and must offer at least one live resolution — and after the
//! resolve the surface must go EMPTY (the held stitch is published and dropped).
//!
//! Run: `cd starbridge-v2 && cargo test --features native-full \
//!   --test deos_desktop_stitcher_is_the_conflict_surface -- --nocapture`

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

/// The conflict surface the PRE-CUTOVER desktop painted for this exact scenario,
/// captured verbatim. The post-cutover desktop — which reads the same rows off a live
/// `Stitcher` — must reproduce it byte for byte.
const PINNED_SURFACE: &[&str] = &[
    "CONFLICT (1 region, first-class state · held, NOT committed)",
    "binds both alts  213f8a0f…a65b",
    "region 0  ·  prose · always-resolvable",
    "you (@26922): Birds are nice three.",
    "co-author (@26923): Dogs are nice too.",
    "resolve: keep author 7d1af13da669692a's “Birds are nice three.”",
    "resolve: keep author 7d1af13da669692b's “Dogs are nice too.”",
    "resolve: order: author 7d1af13da669692a's then author 7d1af13da669692b's (keep both)",
    "resolve: order (swapped): author 7d1af13da669692b's then author 7d1af13da669692a's (keep both)",
];

#[test]
fn the_conflict_surface_is_byte_identical_through_the_stitcher() {
    let layout_path =
        std::env::temp_dir().join(format!("deos-stitchsurface-{}.json", std::process::id()));
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

    // ── The same divergence the conflict-is-a-state gate drives. ──
    desk.update(&mut cx, |d, _cx| {
        d.bake_open_doc(user);
        d.bake_edit_doc(user, "Cats are nice.\n");
        d.bake_fork_branch(user);
        d.bake_diverge_branch(user, "Dogs are nice too.\n");
        d.bake_edit_doc(user, "Cats are nice.\nBirds are nice three.\n");
        d.bake_stitch_branch(user);
    });
    cx.run_until_parked();

    let rows: Vec<String> = cx.update(|cx| desk.read(cx).bake_conflict_surface(user));
    println!("── CONFLICT SURFACE ({} rows) ──", rows.len());
    for r in &rows {
        println!("    {r:?},");
    }

    // ── ANTI-VACUITY: the surface is real before it is pinned. ──
    assert!(
        !rows.is_empty(),
        "a held stitch MUST paint a conflict surface; got nothing"
    );
    let all = rows.join("\n");
    assert!(
        all.contains("CONFLICT (") && all.contains("binds both alts"),
        "the surface must name the conflict AND the umem boundary binding both \
         alternatives: {rows:?}"
    );
    assert!(
        all.contains("Dogs are nice too.") && all.contains("Birds are nice three."),
        "BOTH contested readings must be on the surface — the loser is shown, never \
         silently dropped: {rows:?}"
    );
    assert!(
        all.contains("you (@") && all.contains("co-author (@"),
        "each alternative must be attributed to WHO wrote it (a fact, not a guess): \
         {rows:?}"
    );
    assert!(
        rows.iter().any(|r| r.starts_with("resolve: ")),
        "the surface must offer at least one live one-click resolution: {rows:?}"
    );

    // ── THE PIN: byte-identical to what the pre-cutover desktop painted. ──
    assert_eq!(
        rows.iter().map(String::as_str).collect::<Vec<_>>(),
        PINNED_SURFACE,
        "the conflict surface DRIFTED across the stitcher cutover"
    );

    // ── The held stitch is published by the resolve, so the surface goes empty. ──
    desk.update(&mut cx, |d, _cx| d.bake_resolve_conflict(user, 0, 0));
    cx.run_until_parked();
    let after: Vec<String> = cx.update(|cx| desk.read(cx).bake_conflict_surface(user));
    assert!(
        after.is_empty(),
        "resolving every region publishes the merge and drops the held stitch — the \
         conflict surface must go away, got {after:?}"
    );

    let _ = std::fs::remove_file(&layout_path);
}
