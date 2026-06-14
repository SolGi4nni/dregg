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

// The wire-contract client + mirrored models — the sel4-thin path (and the
// seed of a native remote-federation panel). reqwest is only linked under
// `sel4-thin`, so these are gated to that build for now (a native remote-
// federation connection is a designed-pending lane — see docs/STARBRIDGE-V2.md).
#[cfg(feature = "sel4-thin")]
mod client;
#[cfg(feature = "sel4-thin")]
mod model;

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

    #[cfg(feature = "embedded-executor")]
    {
        // Boot a LIVE local image off the embedded verified executor.
        let (world, anchors) = world::demo_world();

        if headless || !cfg!(feature = "gpui-ui") {
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
            run_window(world, anchors);
            return;
        }
    }

    #[cfg(not(feature = "embedded-executor"))]
    {
        // sel4-thin: no embedded executor. Speak the wire contract to a node.
        let _ = headless;
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

#[cfg(feature = "gpui-ui")]
fn run_window(world: world::World, anchors: [dregg_cell::CellId; 3]) {
    use gpui::{
        px, size, App, AppContext, Bounds, TitlebarOptions, WindowBounds, WindowOptions,
    };
    use gpui_platform::application;
    use std::cell::RefCell;
    use std::rc::Rc;

    let shared = Rc::new(RefCell::new(world));

    application().run(move |cx: &mut App| {
        let bounds = Bounds::centered(None, size(px(1280.), px(820.)), cx);
        cx.open_window(
            WindowOptions {
                window_bounds: Some(WindowBounds::Windowed(bounds)),
                titlebar: Some(TitlebarOptions {
                    title: Some("Starbridge v2 — the live verified image".into()),
                    ..Default::default()
                }),
                ..Default::default()
            },
            |window, cx| {
                let view = cx.new(|cx| {
                    let focus = cx.focus_handle();
                    cockpit::Cockpit::new(shared.clone(), anchors, focus)
                });
                // Focus the cockpit root so it receives ⌘K + palette keystrokes.
                view.update(cx, |c, cx| c.focus_on_open(window, cx));
                view
            },
        )
        .expect("failed to open window");
        cx.activate(true);
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
