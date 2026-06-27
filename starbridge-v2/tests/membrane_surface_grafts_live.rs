//! THE MEMBRANE MOUNTS AS A LIVE DOCK SURFACE — AND A MESSAGE IS A REAL WORLD-FORK.
//!
//! The social-primitive joy-path weld, proven headlessly. The deos-matrix
//! [`ChatPane`](starbridge_v2::dock::chat_surface) previously rendered ONLY in the
//! `--render-guest`/`--render-showcase` headless PNG bakes (`guest.rs`/`showcase.rs`)
//! — never grafted into the windowed dock. This test proves the DOCK path: the
//! exact `ChatPane` construction `Cockpit::open_membrane_pane` grafts (a
//! [`CommsPdSource`](starbridge_v2::comms_pd_source::CommsPdSource) over the
//! world-backed [`WorldChatSource`](starbridge_v2::world_chat::WorldChatSource)
//! transport) produces a real [`CockpitSurface`] and renders in a headless window
//! (the graft+render the dock does). We assert:
//!
//!   * the surface satisfies the `CockpitSurface` shape the dock hosts (a tab
//!     label, a cheap `boxed_clone`);
//!   * the body RENDERS in a headless window (the graft is paintable); and
//!   * **a message IS a cap-bounded world-fork** — the source is `membrane_capable`
//!     (it holds an executor, so the membrane fire button is LIVE, not the disabled
//!     "open in deos to rehydrate" of a bare transport), `mint_membrane` mints a
//!     REAL frustum (an anti-amplification cut in view of the focus cell), and
//!     `rehydrate_drive_stitch` drives + stitches that fork back through the
//!     branch-and-stitch settlement gate (the math proven in
//!     `SettlementSoundness.lean`).
//!
//! Run: `cd starbridge-v2 && cargo test --features native-full --test membrane_surface_grafts_live -- --nocapture`
//! (or `--features dev-surfaces,embedded-executor,render-capture`).

#![cfg(all(
    feature = "dev-surfaces",
    feature = "embedded-executor",
    feature = "render-capture"
))]

use std::borrow::Cow;
use std::sync::Arc;

use gpui::{px, size, AppContext, HeadlessAppContext, PlatformTextSystem};
use gpui_wgpu::CosmicTextSystem;

use deos_matrix::source::ChatSource;

use starbridge_v2::comms_pd_source::CommsPdSource;
use starbridge_v2::dock::chat_surface::ChatPane;
use starbridge_v2::dock::CockpitSurface;
use starbridge_v2::world_chat::WorldChatSource;

static LILEX: &[u8] = include_bytes!("../assets/fonts/Lilex-Regular.ttf");
static IBM_PLEX: &[u8] = include_bytes!("../assets/fonts/IBMPlexSans-Regular.ttf");

#[test]
fn membrane_surface_grafts_windowed_and_a_message_is_a_real_world_fork() {
    // The chat transport IS the dregg world (rooms are real cells, a send is a real
    // verified turn) — exactly the `guest.rs`/`showcase.rs` bake construction that
    // `open_membrane_pane` mounts windowed. The comms-PD source wraps it with a real
    // executor fork so the membrane affordances are GENUINE.
    let world_chat = WorldChatSource::seeded("@ember:deos.local");
    let membrane_world = world_chat.fork_world();
    let focus = world_chat.me_cell();
    let transport: Arc<dyn ChatSource> = Arc::new(world_chat);
    let source: Arc<dyn ChatSource> =
        Arc::new(CommsPdSource::new(transport, membrane_world, focus, 3));

    // A MESSAGE IS A CAP-BOUNDED WORLD-FORK — proven against the source seam BEFORE
    // any rendering (the membrane operations are executor-real here, never a mock).
    assert!(
        source.membrane_capable(),
        "the comms-PD source holds an executor, so the membrane fire button is LIVE \
         (not the disabled bare-transport 'open in deos to rehydrate')"
    );
    let room = source
        .rooms()
        .expect("the world-chat transport lists real rooms")
        .first()
        .map(|r| r.room_id.to_string())
        .expect("at least one seeded room");

    // MINT — fork the live chat world and cull a real anti-amplification frustum in
    // view of the focus cell (the "screenshot of the moment"). A message that IS a
    // cap-bounded fork of the sender's world.
    let envelope = source
        .mint_membrane(&room)
        .expect("mint a real executor-backed membrane frustum");
    assert!(
        envelope.cut.authority_bounded,
        "the minted frustum is authority-bounded (anti-amplification — culled in \
         view of the focus cell only)"
    );
    assert_eq!(
        envelope.cut.focus_cell, focus.0,
        "the frustum is cut around the focus cell (the membrane is a frustum of THIS \
         world)"
    );
    assert!(
        envelope.cut.cell_count >= 1,
        "the frustum carries at least the focus cell's real state"
    );

    // REHYDRATE + DRIVE + STITCH — open the envelope into a real `World` fork
    // (anti-substitution root tooth, fail-closed), drive a real verified turn on it,
    // and stitch the diff back through the branch-and-stitch settlement gate (the
    // `SettlementSoundness.lean` math). A human summary comes back.
    let summary = source
        .rehydrate_drive_stitch(&envelope)
        .expect("rehydrate → drive → stitch a real fork through the settlement gate");
    assert!(
        summary.contains("settled"),
        "the stitch settled the driven fork back (summary: {summary:?})"
    );

    // --- THE WINDOWED DOCK GRAFT (the surface the dock hosts) ------------------
    let text_system: Arc<dyn PlatformTextSystem> =
        Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
    text_system
        .add_fonts(vec![Cow::Borrowed(LILEX), Cow::Borrowed(IBM_PLEX)])
        .expect("fonts");
    let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
        gpui_platform::current_headless_renderer()
    });
    cx.update(gpui_component::init);

    // Build the dock surface over the SAME executor-backed source — exactly what
    // `Cockpit::open_membrane_pane` constructs before `graft_dev_pane`. The window
    // builder closure is `FnOnce`-by-move but typed `FnMut`, so move the `source`
    // into an `Option` and `take` it (the builder runs exactly once), mirroring the
    // card-surface graft test.
    let mut slot = Some(source.clone());
    let _window = cx
        .open_window(size(px(640.), px(420.)), move |window, cx| {
            let src = slot.take().expect("the membrane-window builder runs once");
            let pane = ChatPane::new(2000, src, window, cx);
            // It satisfies the `CockpitSurface` shape the dock hosts.
            assert_eq!(
                pane.tab_label().as_ref(),
                "chat",
                "the dock tab reads 'chat' (the membrane/social pane)"
            );
            // A split clones the surface cheaply.
            let clone = pane.boxed_clone();
            assert_eq!(
                clone.tab_label().as_ref(),
                "chat",
                "the clone keeps the tab label"
            );
            cx.new(|_cx| RootView {
                surface: Box::new(pane),
            })
        })
        .expect("open the headless membrane window");
    cx.run_until_parked();

    println!(
        "OK membrane-surface grafts windowed: tab 'chat', a message IS a cap-bounded \
         world-fork — minted a real frustum (cells {}, authority-bounded) and \
         rehydrate→drive→stitched it back ({summary}).",
        envelope.cut.cell_count
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
