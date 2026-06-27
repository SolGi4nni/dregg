//! THE SIX LANDED CARDS ARE THEIR MODE'S MAIN-PANE SURFACE — MOUNTED OVER THE LIVE WORLD,
//! AND RESHAPED FROM WITHIN.
//!
//! The generalization of `inspector_card_is_the_inspect_surface` to the other landed
//! cards. This proves the MOUNT: the exact builder the cockpit grafts as each mode's
//! main-pane surface ([`build_mode_card_surface`]) produces a real [`CardPane`] over the
//! cockpit's LIVE `World`, whose view-tree is GENERATED from the live ledger — and whose
//! affordance fires ONE cap-gated verified turn on that ledger; and that the open
//! edit-from-within seam is CLOSED through the live mount (a `ViewPatch` re-folds the view
//! document as a receipted patch and the change is observable in the surface's view-source).
//!
//! Run: `cd starbridge-v2 && cargo test --features native-full --test mode_cards_are_the_surfaces -- --nocapture`

#![cfg(all(feature = "card-pane", feature = "dev-surfaces"))]

use std::borrow::Cow;
use std::cell::RefCell;
use std::rc::Rc;
use std::sync::Arc;

use gpui::{px, size, AppContext, HeadlessAppContext, PlatformTextSystem};
use gpui_wgpu::CosmicTextSystem;

use deos_js::card_editor::ViewPatch;
use dregg_cell::AuthRequired;
use starbridge_v2::agent_attach::AGENT_COUNTER_SLOT;
use starbridge_v2::dock::card_surface::{build_mode_card_surface, ModeCard};
use starbridge_v2::world::demo_world;

static LILEX: &[u8] = include_bytes!("../assets/fonts/Lilex-Regular.ttf");
static IBM_PLEX: &[u8] = include_bytes!("../assets/fonts/IBMPlexSans-Regular.ttf");

#[test]
fn every_mode_card_mounts_over_the_live_world_and_reshapes_from_within() {
    // The cockpit's real image — the SAME demo `World` the windowed cockpit runs.
    let (world, anchors) = demo_world();
    let [_treasury, _service, user] = anchors;
    let live = Rc::new(RefCell::new(world));
    let held = AuthRequired::Signature;

    let text_system: Arc<dyn PlatformTextSystem> =
        Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
    text_system
        .add_fonts(vec![Cow::Borrowed(LILEX), Cow::Borrowed(IBM_PLEX)])
        .expect("fonts");
    let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
        gpui_platform::current_headless_renderer()
    });
    cx.update(gpui_component::init);

    let read_field = |w: &starbridge_v2::world::World| -> u64 {
        w.ledger()
            .get(&user)
            .and_then(|c| {
                c.state
                    .get_field(AGENT_COUNTER_SLOT)
                    .map(deos_js::applet::unpack_u64)
            })
            .unwrap_or(0)
    };

    // Each of the six landed cards, as its mode's surface over the LIVE World.
    for (n, kind) in [
        ModeCard::Composer,
        ModeCard::Objects,
        ModeCard::Graph,
        ModeCard::Dynamics,
        ModeCard::Agent,
        ModeCard::Links,
    ]
    .into_iter()
    .enumerate()
    {
        let id = 3000 + n as u64;
        let surface = cx
            .update(|cx| build_mode_card_surface(id, kind, live.clone(), user, held.clone(), cx))
            .unwrap_or_else(|e| panic!("build the {kind:?} mode card surface: {e}"));

        // (A) THE BODY RENDERS in a headless window (the graft is paintable).
        let entity = surface.entity_handle();
        let _window = cx
            .open_window(size(px(560.), px(420.)), move |_window, cx| {
                cx.new(|_cx| RootView {
                    entity: entity.clone(),
                })
            })
            .unwrap_or_else(|_| panic!("open the headless {kind:?} card window"));
        cx.run_until_parked();

        // (B) THE AFFORDANCE FIRES A LIVE TURN — the EXACT call the rendered Button's
        // on_click makes: one cap-gated verified turn through `World::commit_turn`.
        let applet = surface.applet();
        let pre_height = live.borrow().height();
        let pre_field = read_field(&live.borrow());
        applet.borrow_mut().fire("bump", 1).unwrap_or_else(|e| {
            panic!("the {kind:?} card's affordance committed a live turn: {e}")
        });
        let post_height = live.borrow().height();
        let post_field = read_field(&live.borrow());
        assert_eq!(
            post_field,
            pre_field + 1,
            "{kind:?}: the affordance advanced the LIVE cell ({pre_field} -> {post_field})"
        );
        assert_eq!(
            post_height,
            pre_height + 1,
            "{kind:?}: the live ledger height grew by exactly one"
        );
        assert_eq!(
            surface.receipt_count(),
            1,
            "{kind:?}: exactly ONE receipt landed on the card's live tape"
        );

        // (C) EDIT-FROM-WITHIN through the live mount: a `ViewPatch` re-folds the view
        // document (a receipted patch); the new line is observable in the view-source.
        let before = surface.view_source();
        let marker = format!("reshaped {kind:?} from within");
        cx.update(|cx| {
            cx.new(|cx| {
                surface
                    .edit_view(
                        ViewPatch::AddText {
                            text: marker.clone(),
                        },
                        cx,
                    )
                    .unwrap_or_else(|e| panic!("{kind:?}: edit-from-within: {e}"));
                Probe
            })
        });
        let after = surface.view_source();
        assert_ne!(
            before, after,
            "{kind:?}: the reshape changed the view document"
        );
        assert!(
            after.contains(&marker),
            "{kind:?}: the from-within patch line is in the re-folded view-source"
        );

        println!(
            "OK {kind:?} card IS the surface: rendered, affordance fired a real verified \
             turn ({pre_field}->{post_field}, height {pre_height}->{post_height}, 1 receipt), \
             and the view was reshaped from within (a receipted patch landed in the document)."
        );
    }
}

/// A minimal probe entity so an `edit_view` (which needs a live `&mut Context`) can run.
struct Probe;
impl gpui::Render for Probe {
    fn render(
        &mut self,
        _window: &mut gpui::Window,
        _cx: &mut gpui::Context<Self>,
    ) -> impl gpui::IntoElement {
        gpui::div()
    }
}

/// A minimal root that hosts the card's [`CardPane`] entity, so opening a window drives its
/// `render` (the paint a mode's main-pane surface performs).
struct RootView {
    entity: gpui::Entity<starbridge_v2::card_pane::CardPane>,
}
impl gpui::Render for RootView {
    fn render(
        &mut self,
        _window: &mut gpui::Window,
        _cx: &mut gpui::Context<Self>,
    ) -> impl gpui::IntoElement {
        use gpui::{div, ParentElement, Styled};
        div().size_full().child(self.entity.clone())
    }
}
