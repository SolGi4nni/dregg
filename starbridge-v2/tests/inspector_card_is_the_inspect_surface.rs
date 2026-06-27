//! THE INSPECT SURFACE IS A LIVE deos-js CARD — AND ITS AFFORDANCE FIRES A REAL TURN.
//!
//! Rung 2 of the reflective cockpit. Rung 1 ([`deos_js::inspector_card`]) reborn the
//! inspector as a deos-js card over an EMBEDDED engine. This proves the MOUNT: the
//! exact builder the cockpit's Inspect-mode surface grafts
//! ([`build_inspector_card_surface`]) produces a real [`CardPane`] over the cockpit's
//! LIVE `World`, focused on a real cell, whose view-tree is GENERATED from that cell's
//! moldable faces — and whose affordance button fires ONE cap-gated verified turn on
//! the live ledger. We assert:
//!
//!   * the inspector view-tree GENERATED over the live World carries the focused
//!     cell's RawFields rows + the cap-gated affordance buttons (so the rendered
//!     surface IS the focused cell's faces, not a hand-authored card); and
//!   * firing the inspector's `bump` affordance = ONE verified turn committed THROUGH
//!     `World::commit_turn` onto the live ledger (height +1, one receipt), and the
//!     focused cell's slot advances — the bound row the renderer re-reads moves; while
//!     the `escalate` over-reach (Proof the operator's Signature does not hold) is
//!     refused IN-BAND (no turn, no receipt) and never even surfaces as a button.
//!
//! Run: `cd starbridge-v2 && cargo test --features native-full --test inspector_card_is_the_inspect_surface -- --nocapture`

#![cfg(all(feature = "card-pane", feature = "dev-surfaces"))]

use std::borrow::Cow;
use std::cell::RefCell;
use std::rc::Rc;
use std::sync::Arc;

use gpui::{px, size, AppContext, HeadlessAppContext, PlatformTextSystem};
use gpui_wgpu::CosmicTextSystem;

use dregg_cell::AuthRequired;
use starbridge_v2::agent_attach::{attach_agent, WorldSinkAdapter, AGENT_COUNTER_SLOT};
use starbridge_v2::dock::card_surface::build_inspector_card_surface;
use starbridge_v2::world::demo_world;

static LILEX: &[u8] = include_bytes!("../assets/fonts/Lilex-Regular.ttf");
static IBM_PLEX: &[u8] = include_bytes!("../assets/fonts/IBMPlexSans-Regular.ttf");

#[test]
fn inspector_card_mounts_over_live_world_and_its_affordance_fires_a_real_turn() {
    // The cockpit's real image — the SAME demo `World` the windowed cockpit runs.
    let (world, anchors) = demo_world();
    let [_treasury, _service, user] = anchors;
    let live = Rc::new(RefCell::new(world));

    // ── (A) THE VIEW-TREE IS GENERATED FROM THE FOCUSED CELL'S FACES ────────────
    // The exact generation the cockpit mount uses (gpui-free), proving the view is
    // the focused cell's moldable faces, not a hand-authored card.
    let held = AuthRequired::Signature;
    let affordances = vec![
        ("bump".to_string(), AuthRequired::Signature),
        ("escalate".to_string(), AuthRequired::Proof),
    ];
    let probe = attach_agent(
        WorldSinkAdapter::live(live.clone()),
        user,
        held.clone(),
        affordances,
    );
    let tree = deos_js::inspector_card::inspector_view_over_attached(&probe, &held);
    // The RawFields face: a `nonce` row off the live cell renders (a structural field).
    let json = tree.to_json();
    assert!(
        json.contains("nonce"),
        "the inspector view carries the focused cell's RawFields face: {json}"
    );
    // The cap-gated affordance face: `bump` (held → admitted) is a button; `escalate`
    // (Proof the operator's Signature does NOT hold) is NEVER surfaced.
    assert!(
        tree.has_button_for("bump"),
        "the held affordance `bump` is a fireable button on the inspector card"
    );
    assert!(
        !tree.has_button_for("escalate"),
        "the over-reach `escalate` (Proof) is not surfaced (reflective project_for(held))"
    );
    drop(probe);

    // ── (B) THE MOUNT BUILDS + RENDERS, AND ITS AFFORDANCE FIRES A LIVE TURN ────
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

    let pre_height = live.borrow().height();
    let pre_field = read_field(&live.borrow());

    let text_system: Arc<dyn PlatformTextSystem> =
        Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
    text_system
        .add_fonts(vec![Cow::Borrowed(LILEX), Cow::Borrowed(IBM_PLEX)])
        .expect("fonts");
    let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
        gpui_platform::current_headless_renderer()
    });
    cx.update(gpui_component::init);

    // Build the inspector card surface over the LIVE World + the `user` cell — the
    // EXACT builder `Cockpit::ensure_inspector_card` grafts as the Inspect surface.
    let surface = cx
        .update(|cx| build_inspector_card_surface(2000, live.clone(), user, held.clone(), cx))
        .expect("build the live inspector card surface");
    let applet = surface.applet();

    // The body RENDERS in a headless window (the graft is paintable).
    let entity = surface.entity_handle();
    let _window = cx
        .open_window(size(px(520.), px(360.)), move |_window, cx| {
            cx.new(|_cx| RootView {
                entity: entity.clone(),
            })
        })
        .expect("open the headless inspector-card window");
    cx.run_until_parked();

    // FIRE the inspector's `bump` affordance — the EXACT call the rendered Button's
    // `on_click` makes: one cap-gated verified turn through `World::commit_turn`.
    applet
        .borrow_mut()
        .fire("bump", 1)
        .expect("the inspector's affordance committed a live turn");

    let post_height = live.borrow().height();
    let post_field = read_field(&live.borrow());

    assert_eq!(
        post_field,
        pre_field + 1,
        "the inspector's affordance advanced the LIVE focused cell ({pre_field} -> {post_field})"
    );
    assert_eq!(
        post_height,
        pre_height + 1,
        "the live ledger height grew by exactly one ({pre_height} -> {post_height})"
    );
    assert_eq!(
        applet.borrow().receipt_count(),
        1,
        "exactly ONE receipt landed on the inspector card's live tape"
    );

    // The over-reach (`escalate`, Proof) is refused IN-BAND — no turn, no receipt.
    let over = applet.borrow_mut().fire("escalate", 1);
    assert!(
        over.is_err(),
        "the over-reach `escalate` was refused by the cap tooth"
    );
    assert_eq!(
        live.borrow().height(),
        post_height,
        "the refused over-reach committed NOTHING"
    );

    println!(
        "OK the Inspect surface IS a live deos-js inspector card: view = focused \
         cell's faces (nonce row + bump button, escalate hidden), slot {pre_field}->{post_field}, \
         height {pre_height}->{post_height}, 1 receipt — the affordance fired a real \
         verified turn on the cockpit's live ledger."
    );
}

/// A minimal root that hosts the inspector card's [`CardPane`] entity, so opening a
/// window drives its `render` (the paint the Inspect surface performs).
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
