//! `deos-chat` — the windowed deos Matrix chat demo.
//!
//! Opens a gpui window with a room-list sidebar, a timeline, and a real
//! `gpui-component` composer (Enter to send, Shift-Enter for newline). It renders
//! against a [`ChatSource`](deos_matrix::source::ChatSource):
//!
//!   * **default** — a [`MockSource`](deos_matrix::source::MockSource): a recorded
//!     deos-flavoured sync (several rooms, seeded timelines), so the UI is REAL
//!     and fully exercisable with NO homeserver. The composer actually appends.
//!   * **roadmap** — point it at the live `matrix-rust-sdk` worker (login + sync)
//!     by handing the `MatrixHandle` (also a `ChatSource`) to `ChatView::new`.
//!
//! `--headless` runs the source seam with no window (CI-runnable): list rooms,
//! read a timeline, send a message, assert it landed — proving the data path the
//! UI renders, without a display.

use std::sync::Arc;

use deos_matrix::source::{ChatSource, MockSource};

fn headless() -> anyhow::Result<()> {
    let source: Arc<dyn ChatSource> = Arc::new(MockSource::seeded());

    let rooms = source.rooms()?;
    anyhow::ensure!(rooms.len() >= 3, "expected several seeded rooms");
    println!("rooms ({}):", rooms.len());
    for r in &rooms {
        println!(
            "  {} {} · {} members{}",
            if r.is_encrypted { "🔒" } else { "  " },
            r.display_name,
            r.joined_members,
            r.topic
                .as_deref()
                .map(|t| format!(" — {t}"))
                .unwrap_or_default()
        );
    }

    let first = rooms[0].room_id.to_string();
    let tl = source.timeline(&first, 80)?;
    anyhow::ensure!(!tl.is_empty(), "first room has a seeded timeline");
    println!(
        "\ntimeline of {} ({} messages):",
        rooms[0].display_name,
        tl.len()
    );
    for m in &tl {
        println!("  {}: {}", m.sender, m.body);
    }

    let before = tl.len();
    let id = source.send(&first, "hello from the headless deos-chat seam")?;
    let after = source.timeline(&first, 80)?;
    anyhow::ensure!(after.len() == before + 1, "send did not append");
    anyhow::ensure!(
        after.last().unwrap().body.contains("headless"),
        "echo mismatch"
    );
    println!("\nsent {id}; timeline grew {before} → {}", after.len());

    println!("\nALL CHECKS PASSED — the deos-chat data path (rooms · timeline · send) works.");
    Ok(())
}

/// Parse `--screenshot <out.png>` from argv, returning the output path.
fn screenshot_arg() -> Option<String> {
    let args: Vec<String> = std::env::args().collect();
    let i = args.iter().position(|a| a == "--screenshot")?;
    args.get(i + 1).cloned()
}

fn main() -> anyhow::Result<()> {
    let headless_mode = std::env::args().any(|a| a == "--headless" || a == "--verify");
    if headless_mode {
        return headless();
    }
    if let Some(out) = screenshot_arg() {
        return gui::screenshot(&out);
    }
    gui::run();
    Ok(())
}

mod gui {
    use std::sync::Arc;

    use deos_matrix::chat::ChatView;
    use deos_matrix::source::{ChatSource, MockSource};
    use gpui::{
        div, px, size, AppContext as _, ParentElement as _, Styled as _, WindowBounds,
        WindowOptions,
    };
    use gpui_component::{v_flex, Root, TitleBar};

    pub fn run() {
        let source: Arc<dyn ChatSource> = Arc::new(MockSource::seeded());

        let app = gpui_platform::application().with_assets(gpui_component_assets::Assets);
        app.run(move |cx| {
            gpui_component::init(cx);
            cx.activate(true);

            let opts = WindowOptions {
                window_bounds: Some(WindowBounds::centered(size(px(1100.), px(740.)), cx)),
                ..Default::default()
            };
            let source = source.clone();
            cx.spawn(async move |cx| {
                cx.open_window(opts, |window, cx| {
                    let label = source.backend_label();
                    let view = cx.new(|cx| ChatView::new(source, window, cx));
                    let shell = cx.new(|_cx| Shell { view, label });
                    cx.new(|cx| Root::new(shell, window, cx))
                })
                .expect("open window");
            })
            .detach();
        });
    }

    /// OFFSCREEN SCREENSHOT — render the chat UI to a PNG with no window/display
    /// (`screencapture` is blocked in CI/the sandbox; the atlas calls this to bake
    /// the chat surface headlessly). Mirrors starbridge-v2's `render_cockpit_headless`:
    /// a `HeadlessAppContext` over a `CosmicTextSystem` (deterministic, no system
    /// fonts — vendored Lilex/IBMPlex) + the offscreen wgpu renderer, with
    /// `gpui_component::init` so the kit widgets (the composer `Input`, buttons)
    /// find their `Theme` global instead of panicking, then capture the painted
    /// frame and re-encode it to a PNG via the `image` crate.
    pub fn screenshot(out: &str) -> anyhow::Result<()> {
        use std::borrow::Cow;

        use gpui::{px, size, AppContext as _, HeadlessAppContext, PlatformTextSystem};
        use gpui_component::Root;
        use gpui_wgpu::CosmicTextSystem;

        // Logical window geometry. gpui's headless `TestWindow` reports a fixed 2.0
        // scale factor, so the captured frame is 2x in device pixels (2560x1664).
        const W: f32 = 1280.0;
        const H: f32 = 832.0;

        // Vendored OFL fonts: the kit's default family resolves through these (the
        // CosmicTextSystem falls back to "Lilex" for any unknown family), so the
        // bake renders REAL shaped text with no dependence on system fonts.
        static LILEX: &[u8] = include_bytes!("../../assets/fonts/Lilex-Regular.ttf");
        static IBM_PLEX: &[u8] = include_bytes!("../../assets/fonts/IBMPlexSans-Regular.ttf");

        let text_system: Arc<dyn PlatformTextSystem> =
            Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
        text_system.add_fonts(vec![Cow::Borrowed(LILEX), Cow::Borrowed(IBM_PLEX)])?;

        // Headless app over the TestPlatform + the offscreen wgpu renderer.
        let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
            gpui_platform::current_headless_renderer()
        });

        // The kit's `Theme` global — ChatView's gpui-component widgets read it at
        // render time; without this the composer `Input` panics on the missing
        // `gpui_component::theme::Theme` (the windowed path inits it at boot).
        cx.update(gpui_component::init);

        let source: Arc<dyn ChatSource> = Arc::new(MockSource::seeded());
        let label = source.backend_label();

        // Offscreen window whose root is the same `Shell` over `ChatView` the
        // windowed demo opens — rooms sidebar · timeline · composer.
        let window = cx.open_window(size(px(W), px(H)), |window, cx| {
            let view = cx.new(|cx| ChatView::new(source, window, cx));
            let shell = cx.new(|_cx| Shell { view, label });
            cx.new(|cx| Root::new(shell, window, cx))
        })?;

        // Drive to a fully-painted frame, then capture the resolved scene.
        cx.run_until_parked();
        cx.update_window(window.into(), |_, window, _cx| window.refresh())?;
        cx.run_until_parked();
        let captured = cx.capture_screenshot(window.into())?;

        let (ww, hh) = (captured.width(), captured.height());
        captured.save(out)?;
        println!(
            "OK offscreen deos-chat render -> {out} ({ww}x{hh}, logical {W}x{H}); \
             LIVE ChatView over MockSource::seeded, gpui Scene via offscreen wgpu."
        );
        Ok(())
    }

    /// A thin shell: a title bar over the chat view (so the window reads as a real
    /// app, like the deos-zed demo).
    struct Shell {
        view: gpui::Entity<ChatView>,
        label: &'static str,
    }

    impl gpui::Render for Shell {
        fn render(
            &mut self,
            _window: &mut gpui::Window,
            _cx: &mut gpui::Context<Self>,
        ) -> impl gpui::IntoElement {
            v_flex()
                .size_full()
                .child(TitleBar::new().child(div().child(format!(
                    "deos-chat — the social layer over the dregg world (backend: {})",
                    self.label
                ))))
                .child(div().flex_1().min_h(px(0.)).child(self.view.clone()))
        }
    }
}
