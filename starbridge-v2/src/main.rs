//! Starbridge v2 — the native dregg master interface.
//!
//! TWO BUILDS, ONE CODEBASE (see Cargo.toml + docs/STARBRIDGE-V2.md):
//!
//!   * `native-full` (DEFAULT) — EMBEDS THE REAL VERIFIED EXECUTOR and runs a
//!     LIVE LOCAL dregg world natively (`crate::world::World` over
//!     `dregg_turn::executor::TurnExecutor`). It opens a gpui window: the
//!     comprehensive cockpit (`crate::cockpit::Cockpit`) rendering that image
//!     across the four dregg-surpasses-Smalltalk axes. This is the master
//!     interface. (On a host with a working Metal path — see the
//!     `runtime_shaders` note in Cargo.toml — the window renders; absent a GPU/
//!     display it still runs its headless self-check via `--headless`.)
//!
//!   * `sel4-thin` (`--no-default-features --features sel4-thin`) — the Lean-
//!     free thin HTTP client / verifier path for the eventual seL4 component
//!     (docs/SEL4-EMBEDDING.md). No embedded executor, no gpui: it speaks the
//!     node's wire contract (`client`/`model`) against a remote node.
//!
//! The `NodeClient::{Mock,Http}` surface (`client`/`model`) is compiled in BOTH
//! builds: the master interface can ALSO connect to remote nodes/federations.

// The wire-contract client + mirrored models now live in the LIBRARY
// (`starbridge_v2::{client, model}`) so BOTH the embedded master interface's
// live-node panel and the sel4-thin path share one mirror. The thin path below
// references them through the library crate.
#[cfg(feature = "sel4-thin")]
use starbridge_v2::client;

// The embedded engine + reflective model + dynamics live in the library crate
// (`starbridge_v2::{world, dynamics, reflect}`) so they are `cargo test`-able.

// The gpui presentation plane (`cockpit`, `login`, `views`, `dock`) now lives in
// the LIBRARY (`starbridge_v2::{cockpit, login, views, dock}`, gpui-gated) so the
// SAME cockpit renders on EITHER platform — natively here, and in the browser via
// the `starbridge-v2/web` cdylib on `gpui_web` (see docs/deos/WEB-DEOS.md). The bin
// reaches them through the library crate; this alias keeps `cockpit::Cockpit` /
// `login::LoginSurface` paths below unchanged.
#[cfg(feature = "gpui-ui")]
use starbridge_v2::{cockpit, login};

#[cfg(feature = "embedded-executor")]
use starbridge_v2::{demo, reflect, world};

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let headless = args.iter().any(|a| a == "--headless");

    // `--render-cockpit <out>`: the HEADLESS COCKPIT BAKE (the seL4 deos-image
    // weld). Drive the REAL `cockpit::Cockpit` element tree through a headless
    // gpui `App`/`Window` (no GPU, no display) and render the resolved gpui
    // `Scene` offscreen via the wgpu lavapipe path to an 800x600 RGBA8 frame —
    // the byte image the deos-image PD bakes in and blits onto its ramfb
    // framebuffer. See `render_cockpit_headless`. Builds only under the
    // `headless-render` feature (which pulls gpui's `test-support` headless
    // window + capture API). Mutually independent of the windowed `run_window`.
    // `--explore-ui <outdir>`: the UI-EXPLORATION crawl — BFS-walk the cockpit's
    // navigation state-space (drive the real interaction handlers), screenshot
    // each distinct UI state, and emit `<outdir>/ui-graph.json` + `states/*.png`.
    // The atlas's "UI tree": exploring inside and through the surfaces.
    #[cfg(feature = "render-capture")]
    {
        if let Some(dir) = explore_ui_arg(&args) {
            match explore_ui_headless(&dir) {
                Ok(()) => std::process::exit(0),
                Err(e) => {
                    eprintln!("explore-ui FAILED: {e:#}");
                    std::process::exit(1);
                }
            }
        }
    }

    // `--serve-ie6 <port>`: THE LIVE IE6 COCKPIT SERVER — Path B. A single-threaded
    // blocking server (gpui is !Send, so one accept→apply→render→respond loop on the
    // gpui thread is exactly right) that holds a LIVE cockpit, renders it to a PNG per
    // request, and serves it as image-map HTML. Clicking a region / link hits the
    // server, which applies the interaction to the live world and re-renders. Frame-
    // streaming for any user-agent back to 1996 — the real thing, not a flip-through.
    #[cfg(feature = "render-capture")]
    {
        if let Some(port) = serve_ie6_arg(&args) {
            match serve_ie6_headless(port) {
                Ok(()) => std::process::exit(0),
                Err(e) => {
                    eprintln!("serve-ie6 FAILED: {e:#}");
                    std::process::exit(1);
                }
            }
        }
    }

    #[cfg(feature = "render-capture")]
    {
        if let Some(out) = render_cockpit_arg(&args) {
            // `--replay <cell>:<msg>` (repeatable) — apply a recorded act-trail to
            // the demo image BEFORE rendering, so a screenshot reflects a driven
            // session's state (the dregg-mcp server passes its committed act log
            // here). Each act fires through the SAME real executor the cockpit uses.
            let replays = render_replay_args(&args);
            // `--render-size WxH` (logical) defaults to the seL4 framebuffer 800x600
            // (which still downscales + writes the .rgba the PD blits); any other
            // size renders the full-resolution cockpit (no truncation, PNG only).
            // `--render-tab NAME` selects a surface (inspector/graph/proofs/…).
            let (w, h) = render_size_arg(&args).unwrap_or((800.0, 600.0));
            let tab = render_tab_arg(&args);
            match render_cockpit_headless(&out, &replays, w, h, tab.as_deref()) {
                Ok(()) => std::process::exit(0),
                Err(e) => {
                    eprintln!("render-cockpit FAILED: {e:#}");
                    std::process::exit(1);
                }
            }
        }
    }

    // `--render-showcase <out>`: THE SHOWCASE BAKE — one gorgeous high-res PNG of
    // the full working deos desktop with EVERY dev surface mounted + seeded (chat
    // with the membrane card, editor with on-ledger patches, a recorded terminal
    // session, the confined-Hermes tool-call ledger) over the real cell world.
    // The marketing money shot. Renders the same headless gpui way the cockpit
    // bakes. Defaults to 2560x1600 (overridable via `--render-size`).
    #[cfg(all(
        feature = "render-capture",
        feature = "gpui-ui",
        feature = "dev-surfaces"
    ))]
    {
        if let Some(out) = render_showcase_arg(&args) {
            let (w, h) = render_size_arg(&args).unwrap_or((2560.0, 1600.0));
            match render_showcase_headless(&out, w, h) {
                Ok(()) => std::process::exit(0),
                Err(e) => {
                    eprintln!("render-showcase FAILED: {e:#}");
                    std::process::exit(1);
                }
            }
        }
    }

    // `--render-login <out>`: render the LOGIN CEREMONY surface offscreen (the
    // boot front door) the same headless way the cockpit bakes — the MCP-
    // screenshottable proof that the login surface lays out (the identity picker
    // for the demo seed identities). `<out>.png` is written.
    #[cfg(all(feature = "render-capture", feature = "gpui-ui"))]
    {
        if let Some(out) = render_login_arg(&args) {
            let (w, h) = render_size_arg(&args).unwrap_or((1280.0, 832.0));
            match render_login_headless(&out, w, h) {
                Ok(()) => std::process::exit(0),
                Err(e) => {
                    eprintln!("render-login FAILED: {e:#}");
                    std::process::exit(1);
                }
            }
        }
    }

    // `--node <url>`: ALSO connect the master interface to a LIVE remote dregg
    // node (its receipt nervous system + cell reflections), alongside the embedded
    // image. The embedded world is the headline; this is the additional remote
    // federation panel (the SSE stream advances the live receipt list per receipt).
    let node_url = node_url_arg(&args);

    #[cfg(feature = "embedded-executor")]
    {
        if headless || !cfg!(feature = "gpui-ui") {
            // The HEADLESS / CI path wants the fully-populated image up front, so
            // it builds it EAGERLY (all five seed turns run now).
            let (world, _anchors) = world::demo_world();
            headless_report(&world);
            // THE FOUR-SURFACE KILLER DEMO (N5) — the pug-handoff evaluation
            // artifact: mint → agent turn → notify handoff → the dual refusal, all
            // through the REAL embedded executor. Prints the four frames + both
            // refusals (each citing the executor's reason) and EXITS NON-ZERO if the
            // headline contract does not hold (a regression) — CI-friendly.
            let code = headless_killer_demo();
            std::process::exit(code);
        }

        #[cfg(feature = "gpui-ui")]
        {
            // THE WINDOW PATH — open INSTANTLY on the at-rest genesis image (the
            // four cells installed via the genesis path; NO executor turns yet), so
            // the cockpit paints sub-second. The five demo seed turns run AFTER the
            // window is up, driven one-at-a-time from a foreground async task (see
            // `run_window`) so the cells fill in LIVE — same content, off the paint
            // path. (`demo_world`'s eager seeding is exactly what made `main` grind
            // through the embedded executor before the window ever opened.)
            let (world, anchors, seed) = world::demo_genesis();
            run_window(world, anchors, seed, node_url);
            return;
        }
    }

    // In the embedded-but-headless build (no gpui), `node_url` is never moved into
    // `run_window`; consume it so it isn't flagged unused. (With gpui on, the gpui
    // branch above moved it and returned; with embedded off, the sel4-thin block
    // below consumes it.)
    #[cfg(all(feature = "embedded-executor", not(feature = "gpui-ui")))]
    let _ = node_url;

    #[cfg(not(feature = "embedded-executor"))]
    {
        // sel4-thin: no embedded executor. Speak the wire contract to a node.
        let _ = headless;
        // `--node <url>` resolves the same as the positional base URL below; the
        // thin path takes the positional form, so just consume the parsed value.
        let _ = node_url;
        let base = args.iter().nth(1).cloned();
        match base {
            Some(url) if url.starts_with("http") => {
                let client = client::NodeClient::http(url);
                thin_report(&client);
            }
            _ => {
                let client = client::NodeClient::mock();
                thin_report(&client);
            }
        }
    }
}

/// Headless self-check of the embedded world — proves the executor heart runs
/// without a window (CI-friendly; also the fallback when no display is present).
#[cfg(feature = "embedded-executor")]
fn headless_report(world: &world::World) {
    println!("== Starbridge v2 · embedded verified world ==");
    println!("cells:    {}", world.cell_count());
    println!("height:   {}", world.height());
    println!("receipts: {}", world.receipts().len());
    println!("image root: {}", hex::encode(world.state_root()));
    println!("-- cell world --");
    let mut ids: Vec<_> = world.ledger().iter().map(|(id, _)| *id).collect();
    ids.sort_by(|a, b| a.as_bytes().cmp(b.as_bytes()));
    for id in &ids {
        if let Some(c) = world.ledger().get(id) {
            println!(
                "  {} · balance {:>9} · {} caps{}",
                reflect::short_hex(id.as_bytes()),
                c.state.balance(),
                c.capabilities.len(),
                if c.delegate.is_some() { " · delegate" } else { "" },
            );
        }
    }
    println!("-- provenance (receipt chain) --");
    for (i, r) in world.receipts().iter().enumerate() {
        println!(
            "  h{:<3} receipt {} · {} actions · {} computrons",
            i + 1,
            reflect::short_hex(&r.receipt_hash()),
            r.action_count,
            r.computrons_used
        );
    }
    println!("-- dynamics --");
    for ev in world.dynamics().tail(20) {
        println!("  · {}", ev.label());
    }
    println!("(the master interface engine is live; pass no --headless to open the window)");
    println!();
}

/// Run the FOUR-SURFACE KILLER DEMO (N5) as the `--headless` self-check and print
/// its report. Returns the process exit code: `0` iff the headline contract holds
/// (the four frames committed, the handoff produced two distinct receipts, BOTH
/// refusals fired fail-closed), `1` otherwise (a regression — the substrate's
/// guarantees did not fire). This is the single runnable story a stranger / CI runs.
#[cfg(feature = "embedded-executor")]
fn headless_killer_demo() -> i32 {
    let mut d = demo::HeadlineDemo::boot();
    match d.run_headless() {
        Ok(_) => {
            print!("{}", demo::render_headless_report(&d));
            if d.contract_holds() {
                0
            } else {
                // The script ran but the contract is not satisfied (e.g. a missing
                // frame) — still a regression.
                eprintln!("FAIL: the killer-demo contract did not hold.");
                1
            }
        }
        Err(e) => {
            // A SETUP failure (a real regression in the substrate — NOT one of the
            // in-script refusals, which are the point). Print what we captured + the
            // failure, and exit non-zero so CI catches it.
            print!("{}", demo::render_headless_report(&d));
            eprintln!("FAIL: the killer demo could not complete — {}", e.label());
            1
        }
    }
}

/// Parse an optional `--node <url>` (or `--node=<url>`) argument — the live
/// remote-node base URL. Returns `None` when absent.
fn node_url_arg(args: &[String]) -> Option<String> {
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "--node" {
            return it.next().cloned();
        }
        if let Some(rest) = a.strip_prefix("--node=") {
            return Some(rest.to_string());
        }
    }
    None
}

#[cfg(feature = "gpui-ui")]
fn run_window(
    world: world::World,
    anchors: [dregg_cell::CellId; 3],
    seed: world::DemoSeed,
    node_url: Option<String>,
) {
    use gpui::{
        px, size, App, AppContext, Bounds, TitlebarOptions, WindowBounds, WindowOptions,
    };
    use gpui_platform::application;
    use std::cell::RefCell;
    use std::rc::Rc;

    // STARTUP PROOF (the no-blank-screen receipt): build the HOME landing
    // portal's text model from the live world and report how many real lines of
    // text the boot view will render. Because the HOME tab renders exactly this
    // model, a non-zero count here is a non-blank rendered tree — the thing to
    // confirm if the window ever looks empty. (Printed before the run loop so it
    // shows even though `application().run` never returns.)
    //
    // NOTE: this image is the at-rest GENESIS image — the four cells exist but the
    // five demo seed turns have not run yet (they seed in live, after first paint).
    // The portal is full and alive regardless (it greets + names the heart + shows
    // "the image is at rest, waiting for your first turn"); the receipt/height
    // numbers simply climb as the seeding completes.
    {
        let portal = starbridge_v2::landing::LandingPortal::build(&world);
        println!("== Starbridge v2 · opening the window — boot view: HOME landing portal ==");
        println!(
            "HOME portal: {} lines of real text render (headline + {} cards + invitation)",
            portal.line_count(),
            portal.sections.len()
        );
        println!("  headline: {}", portal.headline);
        println!(
            "  the window opens INSTANTLY on the at-rest image; the {} demo seed turns \
             then seed in live (cells appear as each commits) — off the paint path.",
            world::DemoSeed::TOTAL
        );
        println!(
            "  (if the window looks blank, the text above is what should be on screen — \
             a render/display issue, not an empty UI)"
        );
    }

    let shared = Rc::new(RefCell::new(world));

    application().run(move |cx: &mut App| {
        // Register the embedded UI fonts. The windowed app uses the native platform
        // text system (CoreText), which does NOT have "Lilex" (the cockpit's default
        // font) — without this, every panel renders with BLANK text (the chrome lays
        // out, but no glyphs). The headless render paths load these the same way.
        {
            static LILEX: &[u8] = include_bytes!("../assets/fonts/Lilex-Regular.ttf");
            static IBM_PLEX: &[u8] = include_bytes!("../assets/fonts/IBMPlexSans-Regular.ttf");
            if let Err(e) = cx.text_system().add_fonts(vec![
                std::borrow::Cow::Borrowed(LILEX),
                std::borrow::Cow::Borrowed(IBM_PLEX),
            ]) {
                eprintln!("warning: failed to register embedded UI fonts: {e}");
            }
        }
        // Initialize gpui-component — the real widget library (text `Input`,
        // `Button`, the shadcn-style set). This installs its theme + the global
        // state every widget reads (focus trap, input registry, color/date
        // pickers, dock, popovers, …); without it any gpui-component widget the
        // cockpit constructs would panic on a missing global. One call at boot,
        // alongside the font registration. (See docs comment on the
        // `gpui-component` dep in Cargo.toml for the byte-identical-gpui rationale.)
        gpui_component::init(cx);
        // Install the deos theme: gpui-component's `init` leaves the kit in its
        // LIGHT default (the flashbang). Follow the OS appearance here (windowed),
        // defaulting to Dark, and tune the kit palette to the cockpit's GitHub-dark.
        apply_deos_theme(None, false, cx);
        let bounds = Bounds::centered(None, size(px(1280.), px(820.)), cx);
        // Move the seed into the LOGIN surface builder (the login surface hands it
        // to the cockpit at the post-login transition). `Option` so it is consumed
        // exactly once.
        let mut seed = Some(seed);
        // BOOT INTO THE LOGIN CEREMONY — the window root is the login surface, not
        // the cockpit. Picking an identity runs the real session ceremony and swaps
        // the root to the cockpit (wrapped in the session shell that owns logout +
        // the post-paint seeding/live-node tasks). See `login::LoginSurface`.
        cx.open_window(
            WindowOptions {
                window_bounds: Some(WindowBounds::Windowed(bounds)),
                titlebar: Some(TitlebarOptions {
                    title: Some("deos — login".into()),
                    ..Default::default()
                }),
                ..Default::default()
            },
            |window, cx| {
                let node_url = node_url.clone();
                let pending_seed = seed.take().expect("seed consumed once");
                let view = cx.new(|cx| {
                    let focus = cx.focus_handle();
                    login::LoginSurface::boot(
                        shared.clone(),
                        anchors,
                        pending_seed,
                        node_url,
                        focus,
                    )
                });
                view.update(cx, |c, cx| c.focus_on_open(window, cx));
                view
            },
        )
        .expect("failed to open window");
        cx.activate(true);
    });
}

/// Install the deos theme on the gpui-component kit, the SINGLE call every init
/// site makes immediately after `gpui_component::init(cx)`.
///
/// `gpui_component::init` ends with `Theme::change(ThemeMode::Light, …)` — it
/// installs the kit's LIGHT theme by default. Left alone, kit widgets (`Button`,
/// `Input`, list/table) render as bright patches against the cockpit's dark
/// chrome — the "flashbang". This routes through the kit's own theme API to:
///
///  1. Pick the mode. Windowed: follow the OS appearance (`cx.window_appearance()`)
///     so a user in OS dark mode gets dark deos and OS light mode gets light —
///     defaulting to Dark when the platform is ambiguous. Headless bakes pass
///     `force_dark = true` (the marketing shot is always the dark desktop).
///  2. `Theme::change(mode, …)` to swap the kit to that mode's palette.
///  3. In dark, re-tune the kit `ThemeColor` tokens to the cockpit's GitHub-dark
///     palette (the same values as `views::theme` / `dock::theme` / `showcase`)
///     so the kit widgets, the dock chrome, and the hand-rolled panels are ONE
///     cohesive dark look — same backgrounds, borders, text, accent — instead of
///     the kit's flat near-black neutral sitting next to the cockpit's blue-tinted
///     slate.
#[cfg(feature = "gpui-ui")]
fn apply_deos_theme(window: Option<&mut gpui::Window>, force_dark: bool, cx: &mut gpui::App) {
    use gpui::{rgb, Hsla};
    use gpui_component::{Theme, ThemeMode};

    let mode = if force_dark {
        ThemeMode::Dark
    } else {
        // Follow the OS appearance, defaulting to Dark. `WindowAppearance ->
        // ThemeMode` maps Dark/VibrantDark -> Dark and Light/VibrantLight -> Light.
        ThemeMode::from(cx.window_appearance())
    };

    Theme::change(mode, window, cx);

    if !mode.is_dark() {
        // OS light mode: leave the kit's light theme as-is (no flashbang the other
        // direction — the chrome the cockpit hand-rolls reads dark, but the kit
        // surfaces stay coherent light; the windowed light path is the minority
        // case a user explicitly opted into via their OS).
        return;
    }

    // The cockpit's GitHub-dark palette — the single source of truth mirrored by
    // `views::theme`, `dock::theme`, and `showcase::theme`.
    let bg: Hsla = rgb(0x0e1116).into(); // surface
    let panel: Hsla = rgb(0x161b22).into(); // raised card / popover / sidebar
    let panel_hi: Hsla = rgb(0x1f2630).into(); // hover / active fill
    let border: Hsla = rgb(0x2b3340).into();
    let text: Hsla = rgb(0xd7dee8).into();
    let muted: Hsla = rgb(0x7d8794).into();
    let accent: Hsla = rgb(0x6cb6ff).into(); // the blue the cockpit accents with
    let on_accent: Hsla = rgb(0x0e1116).into(); // dark text on the bright accent
    // The status hues — the SAME values the cockpit hand-rolls in `views::theme`
    // (good / warn / bad), so a kit `.success()`/`.warning()`/`.danger()` button
    // matches a hand-rolled status pill exactly.
    let good: Hsla = rgb(0x57d977).into();
    let warn: Hsla = rgb(0xe3b341).into();
    let bad: Hsla = rgb(0xe5534b).into();

    // CRITICAL: kit `Button` variants read their FILL from `theme.tokens.button_*`,
    // which derive 1:1 from the `colors.button_*` source fields. Start from the
    // kit's own canonical DARK `ThemeColor` (every button_* already a correct dark
    // value — no light field is left to flashbang), THEN overlay the cockpit
    // palette, THEN regenerate the token table. (Setting only a handful of `colors`
    // fields would leave the rest at whatever `apply_config` produced — that was
    // the residual white-button bug.)
    let mut c = *gpui_component::ThemeColor::dark();

    // Surfaces.
    c.background = bg;
    c.foreground = text;
    c.popover = panel;
    c.popover_foreground = text;
    c.border = border;
    c.input = border;
    c.ring = accent;
    c.caret = accent;
    c.selection = accent.opacity(0.30);
    c.muted = panel;
    c.muted_foreground = muted;
    c.accordion = panel;
    c.accordion_hover = panel_hi;
    c.group_box = panel;
    c.group_box_foreground = text;
    c.scrollbar_thumb = border;
    c.scrollbar_thumb_hover = muted;
    c.link = accent;
    c.link_hover = rgb(0x8cc6ff).into();
    c.link_active = rgb(0x4f9fe6).into();

    // Secondary fills (the quiet button family + ghost text).
    c.secondary = panel;
    c.secondary_foreground = text;
    c.secondary_hover = panel_hi;
    c.secondary_active = panel_hi;

    // Accent (hover backgrounds on menu/list items).
    c.accent = panel_hi;
    c.accent_foreground = text;

    // The plain (Default) + Secondary button families → read the surface, dark text.
    c.button = panel;
    c.button_hover = panel_hi;
    c.button_active = panel_hi;
    c.button_foreground = text;
    c.button_secondary = panel;
    c.button_secondary_hover = panel_hi;
    c.button_secondary_active = panel_hi;
    c.button_secondary_foreground = text;

    // Primary = the cockpit's signature blue, dark text on it.
    c.primary = accent;
    c.primary_hover = rgb(0x8cc6ff).into();
    c.primary_active = rgb(0x4f9fe6).into();
    c.primary_foreground = on_accent;
    c.button_primary = accent;
    c.button_primary_hover = rgb(0x8cc6ff).into();
    c.button_primary_active = rgb(0x4f9fe6).into();
    c.button_primary_foreground = on_accent;
    c.sidebar_primary = accent;
    c.sidebar_primary_foreground = on_accent;

    // Status button families — match the cockpit's good/warn/bad with dark text so
    // they read as saturated chips, never bright-white panels.
    c.success = good;
    c.success_hover = rgb(0x6fe88c).into();
    c.success_active = rgb(0x44c265).into();
    c.success_foreground = on_accent;
    c.button_success = good;
    c.button_success_hover = rgb(0x6fe88c).into();
    c.button_success_active = rgb(0x44c265).into();
    c.button_success_foreground = on_accent;

    c.warning = warn;
    c.warning_hover = rgb(0xf0c662).into();
    c.warning_active = rgb(0xc99a2f).into();
    c.warning_foreground = on_accent;
    c.button_warning = warn;
    c.button_warning_hover = rgb(0xf0c662).into();
    c.button_warning_active = rgb(0xc99a2f).into();
    c.button_warning_foreground = on_accent;

    c.danger = bad;
    c.danger_hover = rgb(0xef6f68).into();
    c.danger_active = rgb(0xc83f38).into();
    c.danger_foreground = text;
    c.button_danger = bad;
    c.button_danger_hover = rgb(0xef6f68).into();
    c.button_danger_active = rgb(0xc83f38).into();
    c.button_danger_foreground = text;

    c.info = accent;
    c.info_hover = rgb(0x8cc6ff).into();
    c.info_active = rgb(0x4f9fe6).into();
    c.info_foreground = on_accent;
    c.button_info = accent;
    c.button_info_hover = rgb(0x8cc6ff).into();
    c.button_info_active = rgb(0x4f9fe6).into();
    c.button_info_foreground = on_accent;

    // Lists.
    c.list = bg;
    c.list_even = bg;
    c.list_head = panel;
    c.list_hover = panel_hi;
    c.list_active = panel_hi;
    c.list_active_border = accent;

    // Tables.
    c.table = bg;
    c.table_even = panel;
    c.table_head = panel;
    c.table_head_foreground = muted;
    c.table_hover = panel_hi;
    c.table_active = panel_hi;
    c.table_active_border = accent;
    c.table_row_border = border;

    // Tabs.
    c.tab = bg;
    c.tab_bar = bg;
    c.tab_foreground = muted;
    c.tab_active = panel;
    c.tab_active_foreground = text;

    // Title bar / sidebar / status bar chrome.
    c.title_bar = panel;
    c.title_bar_border = border;
    c.status_bar = panel;
    c.status_bar_border = border;
    c.sidebar = panel;
    c.sidebar_foreground = text;
    c.sidebar_border = border;
    c.sidebar_accent = panel_hi;
    c.sidebar_accent_foreground = text;

    // Commit the tuned palette + regenerate the token table (the buttons, badges,
    // and callouts read `tokens`, which is derived 1:1 from these `colors`).
    let t = Theme::global_mut(cx);
    t.colors = c;
    t.tokens = gpui_component::ThemeTokens::from(&t.colors);
}

/// Parse the `--render-cockpit <out>` (or `--render-cockpit=<out>`) argument —
/// the output base path for the headless cockpit bake. Returns `None` when
/// absent. `<out>` names the file stem; `<out>.rgba` (the raw 800x600 RGBA8 the
/// seL4 PD bakes) and `<out>.png` (a visual check) are written.
#[cfg(feature = "render-capture")]
fn render_cockpit_arg(args: &[String]) -> Option<String> {
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "--render-cockpit" {
            return it.next().cloned();
        }
        if let Some(rest) = a.strip_prefix("--render-cockpit=") {
            return Some(rest.to_string());
        }
    }
    None
}

/// Parse the `--render-showcase <out>` (or `--render-showcase=<out>`) argument —
/// the output base path for the SHOWCASE BAKE (the full-desktop money shot).
/// Returns `None` when absent. `<out>.png` is written.
#[cfg(all(
    feature = "render-capture",
    feature = "gpui-ui",
    feature = "dev-surfaces"
))]
fn render_showcase_arg(args: &[String]) -> Option<String> {
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "--render-showcase" {
            return it.next().cloned();
        }
        if let Some(rest) = a.strip_prefix("--render-showcase=") {
            return Some(rest.to_string());
        }
    }
    None
}

/// Parse the `--render-login <out>` (or `--render-login=<out>`) argument — the
/// output base path for the headless LOGIN-surface render. Returns `None` absent.
#[cfg(all(feature = "render-capture", feature = "gpui-ui"))]
fn render_login_arg(args: &[String]) -> Option<String> {
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "--render-login" {
            return it.next().cloned();
        }
        if let Some(rest) = a.strip_prefix("--render-login=") {
            return Some(rest.to_string());
        }
    }
    None
}

/// Parse repeatable `--replay <cell>:<message>` arguments (the act-trail the
/// dregg-mcp server records and hands to the bake so a screenshot reflects the
/// driven session). `<cell>` is a hex-id prefix (matched against the live
/// ledger); `<message>` is an affordance verb (`peek`/`touch`/`write`/…).
#[cfg(feature = "render-capture")]
fn render_replay_args(args: &[String]) -> Vec<(String, String)> {
    let mut out = Vec::new();
    let mut it = args.iter();
    while let Some(a) = it.next() {
        let spec = if a == "--replay" {
            it.next().cloned()
        } else {
            a.strip_prefix("--replay=").map(|s| s.to_string())
        };
        if let Some(spec) = spec {
            if let Some((cell, msg)) = spec.split_once(':') {
                out.push((cell.to_string(), msg.to_string()));
            }
        }
    }
    out
}

/// Parse `--render-size <W>x<H>` (logical pixels) for the cockpit bake. `None`
/// keeps the seL4 framebuffer default (800x600). e.g. `--render-size 1280x832`.
#[cfg(feature = "render-capture")]
fn render_size_arg(args: &[String]) -> Option<(f32, f32)> {
    let mut it = args.iter();
    while let Some(a) = it.next() {
        let spec = if a == "--render-size" {
            it.next().cloned()
        } else {
            a.strip_prefix("--render-size=").map(|s| s.to_string())
        };
        if let Some(spec) = spec {
            if let Some((w, h)) = spec.split_once(['x', 'X', '*']) {
                if let (Ok(w), Ok(h)) = (w.trim().parse::<f32>(), h.trim().parse::<f32>()) {
                    if w >= 320.0 && h >= 240.0 {
                        return Some((w, h));
                    }
                }
            }
        }
    }
    None
}

/// Parse `--render-tab <name>` — the cockpit surface to screenshot (matched
/// against [`cockpit::Cockpit::select_tab_named`]). `None` keeps the default.
#[cfg(feature = "render-capture")]
fn render_tab_arg(args: &[String]) -> Option<String> {
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "--render-tab" {
            return it.next().cloned();
        }
        if let Some(rest) = a.strip_prefix("--render-tab=") {
            return Some(rest.to_string());
        }
    }
    None
}

/// Parse `--explore-ui <outdir>`.
#[cfg(feature = "render-capture")]
fn explore_ui_arg(args: &[String]) -> Option<String> {
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "--explore-ui" {
            return it.next().cloned();
        }
        if let Some(rest) = a.strip_prefix("--explore-ui=") {
            return Some(rest.to_string());
        }
    }
    None
}

/// Parse `--serve-ie6 <port>` (default 8600).
#[cfg(feature = "render-capture")]
fn serve_ie6_arg(args: &[String]) -> Option<u16> {
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "--serve-ie6" {
            return Some(it.next().and_then(|p| p.parse().ok()).unwrap_or(8600));
        }
        if let Some(rest) = a.strip_prefix("--serve-ie6=") {
            return Some(rest.parse().unwrap_or(8600));
        }
    }
    None
}

/// THE LIVE IE6 COCKPIT SERVER (Path B). Holds a live cockpit, renders it per
/// request, and serves it as image-map HTML so any browser back to 1996 can drive
/// the real verified cockpit — server-side state, a round-trip per click.
#[cfg(feature = "render-capture")]
fn serve_ie6_headless(port: u16) -> anyhow::Result<()> {
    use gpui::{px, size, AppContext, HeadlessAppContext, PlatformTextSystem};
    use gpui_wgpu::CosmicTextSystem;
    use std::borrow::Cow;
    use std::cell::RefCell;
    use std::io::{Read, Write};
    use std::net::TcpListener;
    use std::rc::Rc;
    use std::sync::Arc;

    const W: f32 = 1280.0;
    const H: f32 = 832.0;
    // The navigable surfaces (the 4 live-animated tabs stall headless stepping; they
    // are reachable in the native cockpit + the UI atlas, just not the IE6 server loop).
    const TABS: &[&str] = &[
        "home", "inspector", "inspect-act", "graph", "web-of-cells", "objects", "proofs",
        "lanes", "powerbox", "links-here", "organs", "cipherclerk", "editor", "composer",
        "simulate", "shell", "terminal", "buffer", "trust", "docs", "replay",
    ];

    static LILEX: &[u8] = include_bytes!("../assets/fonts/Lilex-Regular.ttf");
    static IBM_PLEX: &[u8] = include_bytes!("../assets/fonts/IBMPlexSans-Regular.ttf");
    let text_system: Arc<dyn PlatformTextSystem> =
        Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
    text_system.add_fonts(vec![Cow::Borrowed(LILEX), Cow::Borrowed(IBM_PLEX)])?;
    let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
        gpui_platform::current_headless_renderer()
    });
    // gpui-component init (the kit `Button`/widgets the cockpit now uses read the
    // kit `Theme`/global at render; without it they panic). See the same weld in
    // `render_cockpit_headless`.
    cx.update(|cx| gpui_component::init(cx));
    // Force the deos DARK theme for the headless bake (the marketing/atlas shot
    // is always the dark desktop) + tune the kit palette to the cockpit GitHub-dark.
    cx.update(|cx| apply_deos_theme(None, true, cx));
    let (world, anchors) = world::demo_world();
    let shared = Rc::new(RefCell::new(world));
    let window = cx.open_window(size(px(W), px(H)), |window, cx| {
        let view = cx.new(|cx| {
            let focus = cx.focus_handle();
            cockpit::Cockpit::with_node(shared.clone(), anchors, focus, None, None)
        });
        view.update(cx, |c, cx| c.focus_on_open(window, cx));
        view
    })?;
    let wh = window.into();
    window.update(&mut cx, |c, _w, _cx| {
        c.select_tab_named("home");
    })?;

    let listener = TcpListener::bind(("127.0.0.1", port))?;
    println!("IE6 cockpit server: http://127.0.0.1:{port}/   (the live verified cockpit, for timetravelers)");

    fn qget(q: &str, key: &str) -> Option<String> {
        q.split('&').find_map(|kv| {
            let (k, v) = kv.split_once('=')?;
            if k == key {
                Some(v.replace('+', " "))
            } else {
                None
            }
        })
    }
    fn respond(stream: &mut std::net::TcpStream, ctype: &str, body: &[u8]) {
        let head = format!(
            "HTTP/1.0 200 OK\r\nContent-Type: {ctype}\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
            body.len()
        );
        let _ = stream.write_all(head.as_bytes());
        let _ = stream.write_all(body);
    }
    fn redirect(stream: &mut std::net::TcpStream, to: &str) {
        let _ = stream.write_all(
            format!("HTTP/1.0 302 Found\r\nLocation: {to}\r\nConnection: close\r\n\r\n").as_bytes(),
        );
    }

    for stream in listener.incoming() {
        let mut stream = match stream {
            Ok(s) => s,
            Err(_) => continue,
        };
        let mut buf = [0u8; 2048];
        let n = stream.read(&mut buf).unwrap_or(0);
        let req = String::from_utf8_lossy(&buf[..n]);
        let line = req.lines().next().unwrap_or("");
        let path = line.split_whitespace().nth(1).unwrap_or("/");
        let (route, query) = path.split_once('?').unwrap_or((path, ""));

        match route {
            "/frame.png" => {
                cx.run_until_parked();
                let _ = cx.update_window(wh, |_, w, _| w.refresh());
                cx.run_until_parked();
                match cx.capture_screenshot(wh) {
                    Ok(img) => {
                        let mut png = Vec::new();
                        if image::DynamicImage::ImageRgba8(img)
                            .write_to(&mut std::io::Cursor::new(&mut png), image::ImageFormat::Png)
                            .is_ok()
                        {
                            respond(&mut stream, "image/png", &png);
                        }
                    }
                    Err(_) => respond(&mut stream, "text/plain", b"render error"),
                }
            }
            "/tab" => {
                if let Some(name) = qget(query, "name") {
                    let _ = window.update(&mut cx, |c, _w, _cx| {
                        c.select_tab_named(&name);
                    });
                }
                redirect(&mut stream, "/");
            }
            "/nav" => {
                let i: usize = qget(query, "i").and_then(|s| s.parse().ok()).unwrap_or(0);
                let _ = window.update(&mut cx, |c, _w, cx| {
                    let navs = c.available_nav();
                    if let Some((_, act)) = navs.get(i) {
                        let act = *act;
                        c.apply_nav(&act, cx);
                    }
                });
                redirect(&mut stream, "/");
            }
            _ => {
                // render-reconcile: select_tab_named sets the visible tab, but the
                // WITNESSED active_tab() (what nav_key reads) only catches up on a
                // render/witness — drive one so the page text matches the live frame.
                let _ = cx.update_window(wh, |_, w, _| w.refresh());
                cx.run_until_parked();
                let (tab, navs): (String, Vec<String>) = window
                    .update(&mut cx, |c, _w, _cx| {
                        let key = c.nav_key();
                        let tab = key.split('|').next().unwrap_or("").to_string();
                        (tab, c.available_nav().into_iter().map(|(l, _)| l).collect())
                    })
                    .unwrap_or_default();
                let html = ie6_page(&tab, &navs, TABS);
                respond(&mut stream, "text/html", html.as_bytes());
            }
        }
    }
    Ok(())
}

/// The IE6 page: HTML 4.01, the LIVE frame as an `<img usemap>`, a `<map>` of
/// `<area>` regions over it for the in-surface interactions, and a text tab/nav bar.
#[cfg(feature = "render-capture")]
fn ie6_page(tab: &str, navs: &[String], tabs: &[&str]) -> String {
    // image-map regions: a row of equal cells across the bottom strip of the frame,
    // one per available interaction (the live frame is 1000px wide as displayed).
    let iw = 1000;
    let areas: String = navs
        .iter()
        .enumerate()
        .map(|(i, label)| {
            let n = navs.len().max(1);
            let x0 = i * iw / n;
            let x1 = (i + 1) * iw / n;
            format!(
                "<area shape=\"rect\" coords=\"{x0},560,{x1},650\" href=\"/nav?i={i}\" alt=\"{l}\" title=\"{l}\">",
                l = html_escape(label)
            )
        })
        .collect();
    let tab_links: String = tabs
        .iter()
        .map(|t| {
            let on = tab.to_lowercase().contains(&t.replace('-', "").to_lowercase())
                || tab.to_lowercase().replace(['-', ' ', '⏳', '⤳', '📄', '⚷'], "").contains(&t.replace('-', ""));
            if on {
                format!("<b>[{}]</b> ", html_escape(t))
            } else {
                format!("<a href=\"/tab?name={t}\">{}</a> ", html_escape(t))
            }
        })
        .collect();
    let nav_links: String = navs
        .iter()
        .enumerate()
        .map(|(i, l)| format!("<a href=\"/nav?i={i}\">[{}]</a> ", html_escape(l)))
        .collect();
    format!(
        "<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.01 Transitional//EN\">\n\
<html><head><title>dregg - live cockpit (IE6 floor)</title></head>\n\
<body bgcolor=\"#0a0e14\" text=\"#c9d1d9\" link=\"#58a6ff\" vlink=\"#bc8cff\">\n\
<font face=\"monospace\" size=\"2\">\n\
<b><font color=\"#58a6ff\">dregg</font></b> - the live verified cockpit, server-rendered for any user-agent (no script, no canvas, no wasm). \
You are at: <b>{tab}</b>. Each click is a round-trip: the server applies it to the live world and re-renders.\n\
<p><img src=\"/frame.png\" width=\"1000\" usemap=\"#m\" border=\"1\" alt=\"the live cockpit\"></p>\n\
<map name=\"m\">{areas}</map>\n\
<p><b>surfaces:</b> {tab_links}</p>\n\
<p><b>here you can:</b> {nav_links}</p>\n\
<p><font color=\"#8b949e\" size=\"1\">The image-map regions along the lower band of the frame map to the in-surface \
interactions; the text links do the same. Refresh-free navigation by clicking the rendered frame - the way a remote \
screen was driven before canvas existed.</font></p>\n\
</font></body></html>",
        tab = html_escape(tab),
    )
}

#[cfg(feature = "render-capture")]
fn html_escape(s: &str) -> String {
    s.replace('&', "&amp;").replace('<', "&lt;").replace('>', "&gt;").replace('"', "&quot;")
}

/// THE UI-EXPLORATION CRAWL — BFS-walk the cockpit's navigation state-space by
/// driving the real interaction handlers, screenshot each distinct UI state, and
/// emit a graph of states + interaction edges. The atlas's "UI tree".
#[cfg(feature = "render-capture")]
fn explore_ui_headless(outdir: &str) -> anyhow::Result<()> {
    use cockpit::NavAction;
    use gpui::{px, size, AppContext, HeadlessAppContext, PlatformTextSystem};
    use gpui_wgpu::CosmicTextSystem;
    use std::borrow::Cow;
    use std::cell::RefCell;
    use std::collections::{HashSet, VecDeque};
    use std::rc::Rc;
    use std::sync::Arc;

    const W: f32 = 1280.0;
    const H: f32 = 832.0;
    let max_nodes: usize = std::env::var("ATLAS_UI_NODES").ok().and_then(|s| s.parse().ok()).unwrap_or(220);

    let states_dir = format!("{outdir}/states");
    std::fs::create_dir_all(&states_dir)?;

    static LILEX: &[u8] = include_bytes!("../assets/fonts/Lilex-Regular.ttf");
    static IBM_PLEX: &[u8] = include_bytes!("../assets/fonts/IBMPlexSans-Regular.ttf");
    let text_system: Arc<dyn PlatformTextSystem> =
        Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
    text_system.add_fonts(vec![Cow::Borrowed(LILEX), Cow::Borrowed(IBM_PLEX)])?;
    let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
        gpui_platform::current_headless_renderer()
    });

    // The cockpit's panels now use gpui-component kit widgets (`Button`, …) which
    // read the kit's `Theme`/global state at render; init it in this headless app
    // (the windowed path does so at boot) or any kit widget panics on the missing
    // global. (See `render_cockpit_headless` for the same weld.)
    cx.update(|cx| gpui_component::init(cx));
    // Force the deos DARK theme for the headless bake (the marketing/atlas shot
    // is always the dark desktop) + tune the kit palette to the cockpit GitHub-dark.
    cx.update(|cx| apply_deos_theme(None, true, cx));

    let (world, anchors) = world::demo_world();
    let shared = Rc::new(RefCell::new(world));
    let window = cx.open_window(size(px(W), px(H)), |window, cx| {
        let view = cx.new(|cx| {
            let focus = cx.focus_handle();
            cockpit::Cockpit::with_node(shared.clone(), anchors, focus, None, None)
        });
        view.update(cx, |c, cx| c.focus_on_open(window, cx));
        view
    })?;
    let wh = window.into();

    // root at HOME; capture the initial nav state to restore between nodes
    let initial = window.update(&mut cx, |c, _window, cx| {
        c.select_tab_named("home");
        c.capture_nav()
    })?;

    let sanitize = |k: &str| -> String {
        k.chars().map(|ch| if ch.is_ascii_alphanumeric() { ch } else { '_' }).collect::<String>()
    };

    let mut visited: HashSet<String> = HashSet::new();
    let mut queue: VecDeque<Vec<NavAction>> = VecDeque::new();
    let mut nodes: Vec<(String, String, String)> = Vec::new(); // (key, tab, png)
    let mut edges: Vec<(String, String, String)> = Vec::new(); // (from, label, to)
    queue.push_back(Vec::new());

    while let Some(path) = queue.pop_front() {
        if nodes.len() >= max_nodes {
            eprintln!("explore-ui: node cap {max_nodes} hit ({} queued)", queue.len());
            break;
        }
        // reconstruct to `path`, read key + children (all inside one update)
        let dbg = std::env::var("ATLAS_UI_DEBUG").is_ok();
        let (key, tab, children) = window.update(&mut cx, |c, _window, cx| {
            if dbg { eprintln!("  reconstruct: restore_initial"); }
            c.restore_nav(&initial, cx);
            for (i, a) in path.iter().enumerate() {
                if dbg { eprintln!("  reconstruct: apply path[{i}] {a:?}"); }
                c.apply_nav(a, cx);
            }
            let key = c.nav_key();
            let tab = key.split('|').next().unwrap_or("").to_string();
            let node_state = c.capture_nav();
            let mut kids = Vec::new();
            for (label, action) in c.available_nav() {
                if dbg { eprintln!("  child: apply {action:?} ({label})"); }
                c.apply_nav(&action, cx);
                kids.push((label, action, c.nav_key()));
                if dbg { eprintln!("  child: restore"); }
                c.restore_nav(&node_state, cx);
            }
            (key, tab, kids)
        })?;

        if visited.contains(&key) {
            continue;
        }
        visited.insert(key.clone());
        eprintln!("explore-ui: [{}] visiting {key}", nodes.len());

        // drive a fully-laid-out frame + capture
        cx.run_until_parked();
        cx.update_window(wh, |_, window, _cx| window.refresh())?;
        cx.run_until_parked();
        let captured = cx.capture_screenshot(wh)?;
        let png = format!("states/{}.png", sanitize(&key));
        captured.save(format!("{outdir}/{png}"))?;
        nodes.push((key.clone(), tab, png));

        for (label, action, child_key) in children {
            edges.push((key.clone(), label, child_key.clone()));
            if !visited.contains(&child_key) {
                let mut p = path.clone();
                p.push(action);
                queue.push_back(p);
            }
        }
    }

    // emit ui-graph.json
    let nodes_json: Vec<_> = nodes.iter().map(|(k, t, p)| {
        serde_json::json!({ "key": k, "tab": t, "png": p })
    }).collect();
    let edges_json: Vec<_> = edges.iter().map(|(f, l, t)| {
        serde_json::json!({ "from": f, "label": l, "to": t })
    }).collect();
    let blob = serde_json::json!({
        "node_count": nodes.len(),
        "edge_count": edges.len(),
        "max_nodes": max_nodes,
        "nodes": nodes_json,
        "edges": edges_json,
    });
    std::fs::write(format!("{outdir}/ui-graph.json"), serde_json::to_string_pretty(&blob)?)?;
    println!("OK explore-ui -> {outdir}/ui-graph.json ({} states, {} edges)", nodes.len(), edges.len());
    Ok(())
}

/// THE HEADLESS COCKPIT BAKE — render the REAL `cockpit::Cockpit` element tree
/// to an 800x600 RGBA8 frame with no GPU and no window, for the seL4 deos-image
/// PD to blit onto its ramfb framebuffer.
///
/// This is the closure of the desktop keystone's last swap: the deos-image PD
/// used to bake a *hand-built* cockpit-shaped `gpui::Scene`; this bakes the
/// LIVE element tree. The mechanism is gpui's own headless capture path
/// (`HeadlessAppContext` over `TestPlatform`), wired on Linux to the offscreen
/// wgpu renderer (`gpui_platform::current_headless_renderer` →
/// `gpui_wgpu::WgpuHeadlessRenderer`, the patched `render_scene_to_image` on
/// lavapipe / software Vulkan):
///
///  1. A `CosmicTextSystem` (real glyph shaping) is the platform text system;
///     the cockpit asks for the "Menlo" family, which falls back to the vendored
///     Lilex (`assets/fonts`). Glyphs rasterize into the headless renderer's own
///     sprite atlas, the same atlas the capture later samples.
///  2. A headless `App` + `Window` is opened at exactly 800x600 with the REAL
///     [`cockpit::Cockpit`] (over the fully-seeded [`world::demo_world`] image —
///     all five verified executor turns already run) as its root view. Opening
///     the window draws it once; a `refresh()` + `run_until_parked()` drives it
///     to a fully-laid-out frame.
///  3. `Window::render_to_image` (`capture_screenshot`) resolves that frame's
///     `gpui::Scene` and renders it offscreen to RGBA — the bytes written here.
///
/// The geometry MUST equal the framebuffer's (`sel4/.../fb.rs` = 800x600) so the
/// PD's blit is a straight RGBA→XRGB8888 copy.
#[cfg(feature = "render-capture")]
fn render_cockpit_headless(
    out: &str,
    replays: &[(String, String)],
    w: f32,
    h: f32,
    tab: Option<&str>,
) -> anyhow::Result<()> {
    use gpui::{px, size, AppContext, HeadlessAppContext, PlatformTextSystem};
    use gpui_wgpu::CosmicTextSystem;
    use std::borrow::Cow;
    use std::cell::RefCell;
    use std::rc::Rc;
    use std::sync::Arc;

    // The seL4 deos-image framebuffer geometry (sel4/dregg-pd/deos-image/src/fb.rs).
    // When the bake is asked for EXACTLY this size we downscale the 2x capture to
    // it and write the `.rgba` the PD blits; any other size renders the full-res
    // cockpit (no downscale, no truncation, PNG only).
    let sel4_geometry = (w as u32, h as u32) == (800, 600);

    // Vendored OFL fonts (the cockpit uses "Menlo"; unknown families fall back
    // to the system_font_fallback — here Lilex — inside CosmicTextSystem).
    static LILEX: &[u8] = include_bytes!("../assets/fonts/Lilex-Regular.ttf");
    static IBM_PLEX: &[u8] = include_bytes!("../assets/fonts/IBMPlexSans-Regular.ttf");

    // 1. Real text shaping with no system fonts (deterministic), Lilex fallback.
    let text_system: Arc<dyn PlatformTextSystem> =
        Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
    text_system.add_fonts(vec![Cow::Borrowed(LILEX), Cow::Borrowed(IBM_PLEX)])?;

    // 2. Headless app over TestPlatform + the Linux offscreen wgpu renderer.
    //    `current_headless_renderer` returns the `WgpuHeadlessRenderer` (lavapipe
    //    when `ZED_OFFSCREEN_PREFER_CPU=1`); its sprite atlas backs the window.
    let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
        gpui_platform::current_headless_renderer()
    });

    // 2b. Initialize gpui-component in the headless app too — the cockpit's panels
    //     now use the real `Button` (and other kit widgets), which read the kit's
    //     `Theme` + global state at render time. The WINDOWED path inits it at boot
    //     (main.rs `gpui_component::init(cx)`); the headless renderer is a separate
    //     `App` and must do the same, or any kit widget panics on the missing
    //     `gpui_component::theme::Theme` global. This is what makes the seL4
    //     framebuffer bake + the dregg-mcp screenshot render the migrated buttons.
    cx.update(|cx| gpui_component::init(cx));
    // Force the deos DARK theme for the headless bake (the marketing/atlas shot
    // is always the dark desktop) + tune the kit palette to the cockpit GitHub-dark.
    cx.update(|cx| apply_deos_theme(None, true, cx));

    // 3. The fully-seeded demo image — the same `World` the windowed cockpit runs,
    //    with every verified executor turn already committed (eager seeding).
    let (mut world, anchors) = world::demo_world();

    // 3b. Apply any recorded act-trail (`--replay <cell>:<msg>`) through the REAL
    //     executor so the rendered frame reflects a driven session (dregg-mcp).
    //     Each act is fired as the cell upon itself with the `Either` tier — the
    //     same self-operator projection the inspect→act panel uses; a refusal is
    //     reported to stderr and skipped (the screenshot stays honest).
    for (cell_pfx, msg) in replays {
        let resolved = world
            .ledger()
            .iter()
            .map(|(id, _)| *id)
            .find(|id| hex::encode(id.as_bytes()).starts_with(cell_pfx.trim_start_matches("0x")));
        match resolved {
            Some(cell) => {
                let ia = starbridge_v2::inspect_act::InspectAct::build(
                    &world,
                    starbridge_v2::inspect_act::InspectFocus::Cell(cell),
                    cell,
                    dregg_cell::permissions::AuthRequired::Either,
                );
                match ia.send(&mut world, msg, dregg_cell::permissions::AuthRequired::Either) {
                    starbridge_v2::inspect_act::SendResult::Committed { .. } => {}
                    starbridge_v2::inspect_act::SendResult::Refused { reason, .. } => {
                        eprintln!("replay {cell_pfx}:{msg} refused: {reason}");
                    }
                }
            }
            None => eprintln!("replay {cell_pfx}:{msg} — no cell matched prefix"),
        }
    }

    let shared = Rc::new(RefCell::new(world));
    let tab_owned = tab.map(|s| s.to_string());

    // 4. Open a headless window (logical w×h) whose ROOT IS the real Cockpit, on
    //    the requested surface (`--render-tab`). No node, no pending seed.
    let window = cx.open_window(size(px(w), px(h)), |window, cx| {
        let view = cx.new(|cx| {
            let focus = cx.focus_handle();
            let mut c = cockpit::Cockpit::with_node(shared.clone(), anchors, focus, None, None);
            if let Some(t) = &tab_owned {
                if !c.select_tab_named(t) {
                    eprintln!("render-tab: no tab named `{t}` — keeping default");
                }
            }
            c
        });
        view.update(cx, |c, cx| c.focus_on_open(window, cx));
        view
    })?;

    // 5. Drive to a fully-rendered frame, then capture the resolved gpui Scene.
    cx.run_until_parked();
    cx.update_window(window.into(), |_, window, _cx| window.refresh())?;
    cx.run_until_parked();
    let captured = cx.capture_screenshot(window.into())?;

    // gpui's headless `TestWindow` reports a FIXED 2.0 scale factor (HiDPI), so a
    // logical w×h window resolves to a 2w×2h DEVICE-pixel render. For the seL4
    // geometry we Lanczos3-downscale to the framebuffer's exact 800x600 (the PD's
    // blit stays a straight copy); for any other size we keep the crisp 2x capture
    // (full layout, no truncation).
    let (cw, ch) = (captured.width(), captured.height());
    let img = if sel4_geometry && !(cw == 800 && ch == 600) {
        image::imageops::resize(&captured, 800, 600, image::imageops::FilterType::Lanczos3)
    } else {
        captured
    };
    let (ww, hh) = (img.width(), img.height());

    // (a) the raw RGBA the seL4 deos-image PD bakes in (only at framebuffer geometry).
    if sel4_geometry {
        std::fs::write(format!("{out}.rgba"), img.as_raw())?;
    }
    // (b) the PNG (always).
    img.save(format!("{out}.png"))?;

    println!(
        "OK headless cockpit render -> {out}.png ({ww}x{hh}, logical {w}x{h}{}{}); \
         LIVE cockpit::Cockpit element tree, gpui Scene via lavapipe offscreen.",
        if sel4_geometry { " + .rgba" } else { "" },
        tab.map(|t| format!(", tab={t}")).unwrap_or_default()
    );
    Ok(())
}

/// THE SHOWCASE BAKE — render the full deos desktop offscreen to a high-res PNG:
/// every dev surface mounted + seeded (chat with the membrane card, editor over a
/// seeded on-ledger document, a recorded terminal session, the confined-Hermes
/// tool-call ledger) over the real `world::demo_world` cell image, composed into a
/// curated multi-pane layout ([`starbridge_v2::showcase::ShowcaseView`]). Same
/// headless gpui path the cockpit bake uses (HeadlessAppContext + gpui-component
/// + offscreen wgpu → PNG via the `image` crate). The marketing money shot.
#[cfg(all(
    feature = "render-capture",
    feature = "gpui-ui",
    feature = "dev-surfaces"
))]
fn render_showcase_headless(out: &str, w: f32, h: f32) -> anyhow::Result<()> {
    use gpui::{px, size, AppContext, HeadlessAppContext, PlatformTextSystem};
    use gpui_wgpu::CosmicTextSystem;
    use std::borrow::Cow;
    use std::cell::RefCell;
    use std::rc::Rc;
    use std::sync::Arc;

    static LILEX: &[u8] = include_bytes!("../assets/fonts/Lilex-Regular.ttf");
    static IBM_PLEX: &[u8] = include_bytes!("../assets/fonts/IBMPlexSans-Regular.ttf");

    // Real text shaping, no system fonts (deterministic), Lilex fallback — the
    // cockpit + every surface asks for "Menlo" and falls back to Lilex.
    let text_system: Arc<dyn PlatformTextSystem> =
        Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
    text_system.add_fonts(vec![Cow::Borrowed(LILEX), Cow::Borrowed(IBM_PLEX)])?;

    let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
        gpui_platform::current_headless_renderer()
    });
    // The surfaces use real gpui-component widgets (the editor's InputState, the
    // kit Buttons) which read the kit Theme global at render time — init it.
    cx.update(|cx| gpui_component::init(cx));
    // Force the deos DARK theme for the headless bake (the marketing/atlas shot
    // is always the dark desktop) + tune the kit palette to the cockpit GitHub-dark.
    cx.update(|cx| apply_deos_theme(None, true, cx));

    // The fully-seeded demo image — the real cell world the chrome reads off.
    let (world, _anchors) = world::demo_world();
    let shared = Rc::new(RefCell::new(world));

    let window = cx.open_window(size(px(w), px(h)), |window, cx| {
        starbridge_v2::showcase::build_root(shared.clone(), window, cx)
    })?;

    // Drive to a fully-laid-out frame, then capture the resolved gpui Scene. Two
    // refresh+park cycles let each surface's own async repaint loop (the terminal
    // grid, the chat list) settle before the capture.
    cx.run_until_parked();
    cx.update_window(window.into(), |_, window, _cx| window.refresh())?;
    cx.run_until_parked();
    cx.update_window(window.into(), |_, window, _cx| window.refresh())?;
    cx.run_until_parked();
    let captured = cx.capture_screenshot(window.into())?;

    let (ww, hh) = (captured.width(), captured.height());
    captured.save(format!("{out}.png"))?;
    println!(
        "OK headless SHOWCASE render -> {out}.png ({ww}x{hh}, logical {w}x{h}); \
         LIVE deos desktop — chat+membrane / editor / terminal / agent over the real \
         cell world, gpui Scene via lavapipe offscreen."
    );
    Ok(())
}

/// THE HEADLESS LOGIN RENDER — render the real [`login::LoginSurface`] element
/// tree (the boot front door's identity picker) offscreen to a PNG, no GPU and
/// no window, the same gpui headless capture path the cockpit bake uses. The
/// MCP-screenshottable proof that the login surface lays out. Provisions the
/// system principal over the demo image's anchors and offers the seed identities.
#[cfg(all(feature = "render-capture", feature = "gpui-ui"))]
fn render_login_headless(out: &str, w: f32, h: f32) -> anyhow::Result<()> {
    use gpui::{px, size, AppContext, HeadlessAppContext, PlatformTextSystem};
    use gpui_wgpu::CosmicTextSystem;
    use std::borrow::Cow;
    use std::cell::RefCell;
    use std::rc::Rc;
    use std::sync::Arc;

    static LILEX: &[u8] = include_bytes!("../assets/fonts/Lilex-Regular.ttf");
    static IBM_PLEX: &[u8] = include_bytes!("../assets/fonts/IBMPlexSans-Regular.ttf");
    let text_system: Arc<dyn PlatformTextSystem> =
        Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
    text_system.add_fonts(vec![Cow::Borrowed(LILEX), Cow::Borrowed(IBM_PLEX)])?;
    let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
        gpui_platform::current_headless_renderer()
    });
    cx.update(|cx| gpui_component::init(cx));
    // Force the deos DARK theme for the headless bake (the marketing/atlas shot
    // is always the dark desktop) + tune the kit palette to the cockpit GitHub-dark.
    cx.update(|cx| apply_deos_theme(None, true, cx));

    // The at-rest genesis image — the login surface only needs the anchors to
    // provision the system principal; no seed turns need to have run.
    let (world, anchors, seed) = world::demo_genesis();
    let shared = Rc::new(RefCell::new(world));

    let window = cx.open_window(size(px(w), px(h)), |window, cx| {
        let view = cx.new(|cx| {
            let focus = cx.focus_handle();
            login::LoginSurface::boot(shared.clone(), anchors, seed, None, focus)
        });
        view.update(cx, |c, cx| c.focus_on_open(window, cx));
        view
    })?;

    cx.run_until_parked();
    cx.update_window(window.into(), |_, window, _cx| window.refresh())?;
    cx.run_until_parked();
    let captured = cx.capture_screenshot(window.into())?;
    captured.save(format!("{out}.png"))?;
    println!(
        "OK headless login render -> {out}.png ({}x{}, logical {w}x{h}); LIVE login::LoginSurface.",
        captured.width(),
        captured.height()
    );
    Ok(())
}

/// The thin-client report (sel4-thin / remote-node path).
#[cfg(not(feature = "embedded-executor"))]
fn thin_report(client: &client::NodeClient) {
    println!("== Starbridge v2 · thin client ==");
    println!("node: {}", client.describe());
    match client.status() {
        Ok(s) => println!(
            "status: healthy={} height={} producer={}",
            s.healthy, s.latest_height, s.state_producer
        ),
        Err(e) => println!("status: <unreachable: {e}>"),
    }
    match client.cells() {
        Ok(cells) => {
            println!("cells: {}", cells.len());
            for c in cells.iter().take(8) {
                println!("  {} · balance {}", &c.id[..12.min(c.id.len())], c.balance);
            }
        }
        Err(e) => println!("cells: <error: {e}>"),
    }
}
