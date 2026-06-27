//! THE CARD MOUNTS AS A LIVE DOCK SURFACE — AND ITS BUTTON FIRES A REAL TURN.
//!
//! The keystone joy-path weld, proven headlessly. `--render-card-pane`
//! (`main.rs::render_card_pane_headless`) proved the `CardPane` renders to pixels
//! and its fire advances the live cell — but over the BAKE path. This test proves
//! the DOCK path: [`build_card_surface`](starbridge_v2::dock::card_surface) (the
//! exact builder `Cockpit::open_card_pane` grafts) produces a real
//! [`CockpitSurface`] over a live `World`, renders it in a headless window (the
//! graft+render the dock does), and FIRES the card's `+1` button affordance =
//! one cap-gated verified turn on the live ledger. We assert:
//!
//!   * the surface satisfies the `CockpitSurface` shape the dock hosts (a stable
//!     id, a tab label, a cheap `boxed_clone` sharing the same live applet);
//!   * the body RENDERS in a headless window (the graft is paintable); and
//!   * the button's fire advances the LIVE cell by one AND lands exactly one
//!     receipt on the cockpit's own tape (the +1 a child presses bottoms out in
//!     the verified executor — light-client unfoolability inherited).
//!
//! Run: `cd starbridge-v2 && cargo test --features native-full --test card_surface_grafts_live -- --nocapture`
//! (or `--features card-pane,dev-surfaces`; the headless renderer rides
//! `render-capture`, which `card-pane` implies).

#![cfg(all(feature = "card-pane", feature = "dev-surfaces"))]

use std::borrow::Cow;
use std::sync::Arc;

use gpui::{px, size, AppContext, HeadlessAppContext, PlatformTextSystem};
use gpui_wgpu::CosmicTextSystem;

use starbridge_v2::agent_attach::AGENT_COUNTER_SLOT;
use starbridge_v2::dock::card_surface::build_card_surface;
use starbridge_v2::dock::CockpitSurface;
use starbridge_v2::world::demo_world;

static LILEX: &[u8] = include_bytes!("../assets/fonts/Lilex-Regular.ttf");
static IBM_PLEX: &[u8] = include_bytes!("../assets/fonts/IBMPlexSans-Regular.ttf");

#[test]
fn card_surface_grafts_over_live_world_and_its_button_fires_a_real_turn() {
    use std::cell::RefCell;
    use std::rc::Rc;

    // The cockpit's real image — the SAME demo `World` the windowed cockpit runs.
    let (world, anchors) = demo_world();
    let [_treasury, _service, user] = anchors;
    let live = Rc::new(RefCell::new(world));

    let pre_height = live.borrow().height();
    let pre_field = live
        .borrow()
        .ledger()
        .get(&user)
        .and_then(|c| {
            c.state
                .get_field(AGENT_COUNTER_SLOT)
                .map(deos_js::applet::unpack_u64)
        })
        .unwrap_or(0);

    // The headless offscreen renderer (the same path the cockpit bakes through).
    let text_system: Arc<dyn PlatformTextSystem> =
        Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
    text_system
        .add_fonts(vec![Cow::Borrowed(LILEX), Cow::Borrowed(IBM_PLEX)])
        .expect("fonts");
    let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
        gpui_platform::current_headless_renderer()
    });
    cx.update(gpui_component::init);

    // Boot SpiderMonkey ONCE (process-global engine), then build the dock card
    // surface over the LIVE World + the operator's `user` cell — exactly what
    // `Cockpit::open_card_pane` does before `graft_dev_pane`.
    let mut rt = deos_js::JsRuntime::new().expect("boot SpiderMonkey");

    let surface = cx
        .update(|cx| build_card_surface(1000, &mut rt, live.clone(), user, cx))
        .expect("build the card surface over the live World");

    // It satisfies the `CockpitSurface` shape the dock hosts.
    assert_eq!(surface.item_id().as_u64(), 1000, "stable surface id");
    assert_eq!(
        surface.tab_label().as_ref(),
        "card",
        "the dock tab reads 'card'"
    );
    // A split clones the surface; the clone shares the SAME live applet (one cell,
    // mirrored) — its receipt count tracks the same tape.
    let clone = surface.boxed_clone();
    assert_eq!(clone.item_id().as_u64(), 1000, "the clone keeps the id");
    assert_eq!(surface.receipt_count(), 0, "no fire yet");

    // The body RENDERS in a headless window (the graft is paintable). We host the
    // surface's `CockpitSurface` body in a tiny root view so `render_body` runs.
    // The window builder closure is `FnOnce`-by-move but typed `FnMut`, so move
    // the surface into an `Option` and `take` it (the builder runs exactly once).
    let applet = surface.applet();
    let boxed: Box<dyn CockpitSurface> = Box::new(surface);
    let mut slot = Some(boxed);
    let _window = cx
        .open_window(size(px(420.), px(220.)), move |_window, cx| {
            let surface = slot.take().expect("the card-window builder runs once");
            cx.new(|_cx| RootView { surface })
        })
        .expect("open the headless card window");
    cx.run_until_parked();

    // FIRE the card's `+1` button affordance — the EXACT call the rendered Button's
    // `on_click` makes: one cap-gated verified turn committed THROUGH
    // `World::commit_turn` onto the live ledger.
    let _receipt = applet
        .borrow_mut()
        .fire("bump", 1)
        .expect("the card's +1 button committed a live turn");

    let post_height = live.borrow().height();
    let post_field = live
        .borrow()
        .ledger()
        .get(&user)
        .and_then(|c| {
            c.state
                .get_field(AGENT_COUNTER_SLOT)
                .map(deos_js::applet::unpack_u64)
        })
        .unwrap_or(0);

    assert_eq!(
        post_field,
        pre_field + 1,
        "the card's button advanced the LIVE user cell ({pre_field} -> {post_field})"
    );
    assert_eq!(
        post_height,
        pre_height + 1,
        "the live ledger height grew by exactly one ({pre_height} -> {post_height})"
    );
    assert_eq!(
        applet.borrow().receipt_count(),
        1,
        "exactly ONE receipt landed on the card's live tape"
    );

    println!(
        "OK card-surface grafts over the LIVE World: tab 'card', cell slot-0 \
         {pre_field}->{post_field}, height {pre_height}->{post_height}, 1 receipt — \
         the +1 button fired a real verified turn on the cockpit's live ledger."
    );
}

/// A minimal root that hosts a [`CockpitSurface`]'s body, so opening a window
/// drives the surface's `render_body` (the graft+paint the dock performs).
struct RootView {
    surface: Box<dyn CockpitSurface>,
}

impl gpui::Render for RootView {
    fn render(
        &mut self,
        window: &mut gpui::Window,
        cx: &mut gpui::Context<Self>,
    ) -> impl gpui::IntoElement {
        use gpui::{div, ParentElement, Styled};
        let app: &mut gpui::App = cx;
        div()
            .size_full()
            .child(self.surface.render_body(window, app))
    }
}
