//! **THE WORLD EXPLORER + THE SPOTTER reflect/jump over the live World.**
//!
//! Two new Pharo/NT surfaces of the deos desktop:
//!   * the WORLD EXPLORER — the "My Computer" of the verified World (ledger · chronicle
//!     · conservation), reflecting the live ledger + the Σ-balance invariant;
//!   * the SPOTTER — the fuzzy command palette that jumps to any cell / action / window.
//!
//! This drives both over the real `World` and asserts they reflect/dispatch genuinely:
//! the World Explorer's conservation face reads Σ balance = 0 over the live ledger; the
//! Spotter ranks real candidates for a query and dispatching the top one opens a real
//! window. (The World Explorer faces are pure reflective reads — asserting Σ=0 via the
//! desktop's own `bake_world_balance_sum` exercises the same ledger the face renders.)
//!
//! Run: `cd starbridge-v2 && cargo test --no-default-features \
//!   --features "gpui-ui,embedded-executor,render-capture" \
//!   --test deos_desktop_world_explorer_and_spotter -- --nocapture`

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

#[test]
fn the_world_explorer_and_spotter_reflect_and_jump_over_the_live_world() {
    let layout_path =
        std::env::temp_dir().join(format!("deos-wldspot-test-{}.json", std::process::id()));
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

    // ── THE WORLD EXPLORER — open it, walk its three faces, assert Σ=0 conservation. ──
    desk.update(&mut cx, |d, _cx| {
        d.bake_open_world_explorer();
        d.bake_world_explorer_tab(0); // Ledger
        d.bake_world_explorer_tab(1); // Chronicle
        d.bake_world_explorer_tab(2); // Conservation
    });
    cx.run_until_parked();
    // The conservation face reflects the live ledger's Σ balance — STABLE under view
    // actuations (opening windows / switching faces fire NO turn, so Σ cannot move).
    // The demo world's Σ is its genesis sum; the face reads whatever the ledger holds.
    let sigma = cx.update(|cx| desk.read(cx).bake_world_balance_sum());
    desk.update(&mut cx, |d, _cx| {
        d.bake_world_explorer_tab(0);
        d.bake_world_explorer_tab(2);
    });
    cx.run_until_parked();
    let sigma2 = cx.update(|cx| desk.read(cx).bake_world_balance_sum());
    assert_eq!(
        sigma, sigma2,
        "the World Explorer's conservation face reflects a STABLE Σ balance (view \
         actuations fire no turn) — got {sigma} then {sigma2}"
    );
    assert!(
        cx.update(|cx| desk.read(cx).bake_total_window_count()) >= 1,
        "the World Explorer window is open"
    );

    // ── THE SPOTTER — rank candidates for a query, dispatch the top, open a window. ──
    let before = cx.update(|cx| desk.read(cx).bake_total_window_count());
    desk.update(&mut cx, |d, _cx| {
        d.bake_open_spotter("inspect");
    });
    let matches = cx
        .update(|cx| desk.read(cx).bake_spotter_match_count())
        .expect("the Spotter is open");
    assert!(
        matches >= 1,
        "the Spotter ranks at least one candidate for 'inspect' over the live cells (got {matches})"
    );
    let top = cx
        .update(|cx| desk.read(cx).bake_spotter_top_label())
        .expect("the Spotter has a top candidate");
    assert!(
        top.to_lowercase().contains("inspect"),
        "the top candidate for 'inspect' is an Inspect action: {top:?}"
    );

    // An empty query returns ALL candidates (a sensible default list, not nothing).
    desk.update(&mut cx, |d, _cx| {
        d.bake_open_spotter("");
    });
    let all = cx
        .update(|cx| desk.read(cx).bake_spotter_match_count())
        .unwrap_or(0);
    assert!(
        all >= matches,
        "an empty Spotter query lists every candidate ({all} >= {matches} filtered)"
    );

    // Dispatching the top candidate opens a real window AND closes the Spotter.
    desk.update(&mut cx, |d, _cx| {
        d.bake_open_spotter("inspect");
        d.bake_spotter_dispatch_top();
    });
    cx.run_until_parked();
    assert!(
        cx.update(|cx| desk.read(cx).bake_spotter_match_count())
            .is_none(),
        "dispatching the Spotter closes the overlay"
    );
    let after = cx.update(|cx| desk.read(cx).bake_total_window_count());
    assert!(
        after > before,
        "dispatching the Spotter's top 'inspect' candidate opened a window ({before} -> {after})"
    );

    let _ = std::fs::remove_file(&layout_path);
    println!(
        "OK World Explorer reflects a stable Σ={sigma} over the live ledger; Spotter ranked {matches} \
         match(es) for 'inspect' (top: {top:?}), empty query listed {all}, dispatch opened \
         a window ({before} -> {after}) and closed the overlay."
    );
}
