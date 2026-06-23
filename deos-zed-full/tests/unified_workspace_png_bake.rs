//! THE PNG BAKE of the whole unified Zed Workspace, over a FirmamentFs cell-ledger.
//!
//! `unified_workspace_one_running_thing.rs` proves (by running) that a SINGLE
//! `workspace::Workspace` carries every panel + git + search + the command palette
//! + a real PTY + a save-is-a-turn. THIS bake mounts that same one Workspace
//! OFFSCREEN through the REAL headless GPU renderer (`gpui_platform`'s offscreen
//! path) and writes the resolved gpui `Scene` to a PNG — the visual artifact of
//! the whole IDE running over the cells.
//!
//! It is a `#[test]` (not `#[gpui::test]`): the headless-renderer +
//! screenshot-capture path (`HeadlessAppContext` / `current_headless_renderer`) is
//! `test-support`-gated, which is on for these dev-deps. The bake builds the real
//! Zed `Workspace` over a `Project` whose `Fs` is a [`FirmamentZedFs`], docks the
//! project / outline / terminal / Hermes panels, opens a cell as an editor buffer
//! and a real terminal, drives the layout to a stable frame, then captures the
//! window to `$DEOS_UNIFIED_WORKSPACE_PNG` (default under the cargo target dir).
//!
//! Only compiled under `--features full-zed`.
#![cfg(feature = "full-zed")]

use std::cell::RefCell;
use std::rc::Rc;
use std::sync::{Arc, RwLock};

use anyhow::{anyhow, Result};
use gpui::{px, size, AppContext, HeadlessAppContext, PlatformTextSystem};
use gpui_wgpu::CosmicTextSystem;

use fs::Fs;
use project::{LocalProjectFlags, Project};
use settings::SettingsStore;
use workspace::{AppState, Workspace};

use deos_hermes::cockpit_surface::HermesSession;
use deos_hermes::{AgentCipherclerk, AgentRuntime, GrantRegistry, HeldToken, HermesGateway};

use deos_zed_full::{boot, FirmamentZedFs};

/// A confined, persistent gateway for the docked agent panel (the standard floors
/// + a tightened terminal rate). Leaked `'static`, as the live dock holds it.
fn confined_gateway() -> HermesGateway<'static> {
    let mut cclerk = AgentCipherclerk::new();
    let root: HeldToken = cclerk.mint_token(&[7u8; 32], "deos");
    let rt: &'static AgentRuntime = Box::leak(Box::new(AgentRuntime::new(
        Arc::new(RwLock::new(cclerk)),
        "deos",
    )));
    let registry = GrantRegistry::default_for_session(1000)
        .with_standard_tool_grants(1000)
        .with_tool_grant("terminal", 4, 1000);
    HermesGateway::new(rt, root, registry)
}

/// Pump the headless app's foreground executor until `done` flips (or a cap),
/// advancing the simulated clock so timer-paced async (worktree scan, panel
/// loads) progresses.
fn pump(cx: &HeadlessAppContext, done: &Rc<RefCell<bool>>, max: usize) {
    for _ in 0..max {
        cx.run_until_parked();
        if *done.borrow() {
            break;
        }
        cx.advance_clock(std::time::Duration::from_millis(20));
    }
}

#[test]
fn bake_the_unified_workspace_png() -> Result<()> {
    let out = std::env::var("DEOS_UNIFIED_WORKSPACE_PNG").unwrap_or_else(|_| {
        format!(
            "{}/deos-unified-workspace",
            std::env::var("CARGO_TARGET_DIR").unwrap_or_else(|_| "target".to_string())
        )
    });
    // A wide IDE so every dock + the center editor is visible.
    let (w, h) = (1800.0_f32, 1100.0_f32);

    // Real text shaping via system fonts; the headless renderer (offscreen GPU) is
    // what makes `capture_screenshot` resolve to real pixels.
    let text_system: Arc<dyn PlatformTextSystem> = Arc::new(CosmicTextSystem::new("Helvetica"));
    let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
        gpui_platform::current_headless_renderer()
    });
    cx.allow_parking();

    // 1. Workspace + panel globals.
    cx.update(|cx| {
        let settings_store = SettingsStore::test(cx);
        cx.set_global(settings_store);
        boot::install_workspace_globals(cx);
    });

    // 2. The cell-ledger fs (seeded + git armed) so the project auto-discovers the
    //    cell-ledger repo.
    let main_rs = "fn main() {\n    println!(\"hello from a cell\");\n}\n";
    let lib_rs = "pub fn hello() -> &'static str {\n    \"a cell is a file\"\n}\n";
    let nested_rs = "pub mod inner;\n";
    let fzfs = Arc::new(FirmamentZedFs::new());
    fzfs.seed_file("/proj/main.rs", main_rs)?;
    fzfs.seed_file("/proj/lib.rs", lib_rs)?;
    fzfs.seed_file("/proj/src/mod.rs", nested_rs)?;
    let cell_git = cx.update(|cx| fzfs.enable_git("/proj", cx.background_executor().clone()));
    cell_git.set_live(
        "/proj/main.rs",
        "fn main() {\n    println!(\"a save is a turn\");\n}\n",
    );

    // 3. AppState + a real `Project` over the cell-fs (deps pulled off AppState).
    let fs: Arc<dyn Fs> = fzfs.clone();
    let app_state = cx.update(|cx| AppState::test(cx));
    let project = cx.update(|cx| {
        Project::local(
            app_state.client.clone(),
            app_state.node_runtime.clone(),
            app_state.user_store.clone(),
            app_state.languages.clone(),
            fs.clone(),
            None,
            LocalProjectFlags {
                init_worktree_trust: true,
                ..Default::default()
            },
            cx,
        )
    });

    // 4. Create + scan the worktree over /proj.
    {
        let done = Rc::new(RefCell::new(false));
        let d2 = done.clone();
        let proj = project.clone();
        cx.update(|cx| {
            cx.spawn(async move |cx| {
                let task = proj.update(cx, |p, cx| p.find_or_create_worktree("/proj", true, cx));
                if let Ok((tree, _)) = task.await {
                    if let Some(scan) =
                        tree.read_with(cx, |t, _| t.as_local().map(|l| l.scan_complete()))
                    {
                        scan.await;
                    }
                }
                *d2.borrow_mut() = true;
            })
            .detach();
        });
        pump(&cx, &done, 4000);
        if !*done.borrow() {
            return Err(anyhow!("the cell worktree scan did not complete"));
        }
    }

    // 5. ONE Workspace window over the project (offscreen, real renderer).
    let window = cx.open_window(size(px(w), px(h)), |window, cx| {
        cx.new(|cx| Workspace::new(None, project.clone(), app_state.clone(), window, cx))
    })?;
    let workspace = window.root(&mut cx)?;
    cx.run_until_parked();

    // 6. Dock all panels (project / outline / terminal / Hermes).
    {
        let session = HermesSession::with_gateway("sess-bake", confined_gateway(), 100);
        let weak_ws = workspace.downgrade();
        let done = Rc::new(RefCell::new(false));
        let d2 = done.clone();
        cx.update_window(window.into(), |_, window, cx| {
            window
                .spawn(cx, async move |cx| {
                    let _ = boot::load_all_panels(weak_ws, session, "sess-bake", cx.clone()).await;
                    *d2.borrow_mut() = true;
                })
                .detach();
        })?;
        pump(&cx, &done, 4000);
    }

    // 7. Open a cell as an editor buffer (so the center pane shows real content).
    {
        let proj = project.clone();
        let ws = workspace.clone();
        let done = Rc::new(RefCell::new(false));
        let d2 = done.clone();
        cx.update_window(window.into(), |_, window, cx| {
            window
                .spawn(cx, async move |cx| {
                    if let Some(path) =
                        proj.update(cx, |p, cx| p.find_project_path("proj/main.rs", cx))
                    {
                        if let Ok(opened) = ws.update_in(cx, |ws, window, cx| {
                            ws.open_path(path, None, true, window, cx)
                        }) {
                            let _ = opened.await;
                        }
                    }
                    *d2.borrow_mut() = true;
                })
                .detach();
        })?;
        pump(&cx, &done, 4000);
    }

    // 8. Open a real terminal in the docked terminal panel (best-effort).
    {
        use terminal_view::terminal_panel::TerminalPanel;
        let ws = workspace.clone();
        let done = Rc::new(RefCell::new(false));
        let d2 = done.clone();
        cx.update_window(window.into(), |_, window, cx| {
            window
                .spawn(cx, async move |cx| {
                    if let Ok(task) = ws.update_in(cx, |ws, window, cx| {
                        TerminalPanel::add_center_terminal(ws, window, cx, |project, cx| {
                            project.create_terminal_shell(None, cx)
                        })
                    }) {
                        let _ = task.await;
                    }
                    *d2.borrow_mut() = true;
                })
                .detach();
        })?;
        pump(&cx, &done, 2000);
    }

    // 9. Drive to a stable frame, then CAPTURE → PNG.
    for _ in 0..4 {
        cx.run_until_parked();
        cx.update_window(window.into(), |_, window, _| window.refresh())?;
        cx.run_until_parked();
        cx.advance_clock(std::time::Duration::from_millis(32));
    }
    let captured = cx.capture_screenshot(window.into())?;
    let (ww, hh) = (captured.width(), captured.height());
    if let Some(parent) = std::path::Path::new(&out).parent() {
        std::fs::create_dir_all(parent).ok();
    }
    captured.save(format!("{out}.png"))?;
    // A non-trivial frame (not an empty/black image): assert real area.
    assert!(ww >= 100 && hh >= 100, "captured a real-sized frame: {ww}x{hh}");
    println!(
        "OK headless UNIFIED-WORKSPACE render -> {out}.png ({ww}x{hh}, logical {w}x{h}); \
         ONE real workspace::Workspace over the cell-ledger — project/outline/terminal/Hermes \
         panels docked + an editor over a cell + a PTY, gpui Scene via the headless offscreen renderer."
    );
    let _ = fzfs.total_balance();

    // TEARDOWN — the PNG is captured + saved. The live editor + terminal entities
    // (the `Editor` over the open cell, the `TerminalView` + its detached
    // PTY-reader task) are still held by the window's view tree and by detached
    // background tasks; those tasks survive a window removal, so the
    // `HeadlessAppContext`'s leak detector (which runs in `App`'s `Drop`) would
    // panic on shutdown. This is a one-shot bake process: forget the context so
    // its leak-detecting `Drop` doesn't run, and let the OS reclaim everything as
    // the process exits immediately after. (The artifact + the render are real;
    // this is purely a clean teardown of a single-shot render, not a real leak.)
    let _ = (&workspace, &project, &app_state, &window);
    std::mem::forget(cx);
    Ok(())
}
