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

#[cfg(feature = "gpui-ui")]
mod cockpit;
#[cfg(feature = "gpui-ui")]
mod views;
// `views` (the older NodeClient-bound rail components) is also what a future
// remote-federation panel reuses; it is gpui-gated.

#[cfg(feature = "embedded-executor")]
use starbridge_v2::{demo, reflect, world};

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let headless = args.iter().any(|a| a == "--headless");
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
    use std::time::Duration;

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
        let bounds = Bounds::centered(None, size(px(1280.), px(820.)), cx);
        // Move the seed into the window builder (it is installed onto the cockpit,
        // which drives it after first paint). `Option` so it is consumed exactly once.
        let mut seed = Some(seed);
        let window = cx
            .open_window(
                WindowOptions {
                    window_bounds: Some(WindowBounds::Windowed(bounds)),
                    titlebar: Some(TitlebarOptions {
                        title: Some("Starbridge v2 — the live verified image".into()),
                        ..Default::default()
                    }),
                    ..Default::default()
                },
                |window, cx| {
                    let node_url = node_url.clone();
                    let pending_seed = seed.take();
                    let view = cx.new(|cx| {
                        let focus = cx.focus_handle();
                        cockpit::Cockpit::with_node(
                            shared.clone(),
                            anchors,
                            focus,
                            node_url,
                            pending_seed,
                        )
                    });
                    // Focus the cockpit root so it receives ⌘K + palette keystrokes.
                    view.update(cx, |c, cx| c.focus_on_open(window, cx));
                    view
                },
            )
            .expect("failed to open window");
        cx.activate(true);

        // THE POST-PAINT SEEDING TASK — the window is now up (this runs on the
        // FOREGROUND executor, after the first frame). Drive the demo seed turns
        // one at a time, yielding a beat between each so the UI paints the new cell/
        // receipt before the next verified turn runs. Each `seed_next_demo_turn`
        // commits ONE real executor turn and `cx.notify()`s; the loop ends when the
        // image is fully seeded. The window was alive the whole time.
        cx.spawn(async move |cx| {
            loop {
                // A short beat so the just-committed turn paints (and the embedded
                // executor's next turn doesn't monopolize the frame).
                cx.background_executor()
                    .timer(Duration::from_millis(60))
                    .await;
                let more = match window.update(cx, |cockpit, _window, cx| {
                    cockpit.seed_next_demo_turn(cx)
                }) {
                    Ok(more) => more,
                    // The window closed (or its root changed) — stop seeding.
                    Err(_) => break,
                };
                if !more {
                    break;
                }
            }
        })
        .detach();
    });
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
