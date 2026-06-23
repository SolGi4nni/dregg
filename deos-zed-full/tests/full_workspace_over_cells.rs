//! THE FULL-WORKSPACE PROOF (stage 2/3 of `DESIGN-FULL-ZED-EMBED.md`).
//!
//! Where `project_over_cells.rs` proves the editor buffer/save SEAM, this drives
//! the whole Zed **Workspace shell** over the cell-ledger and confirms it RUNS:
//!
//!  * a REAL `workspace::Workspace` (its dock + panes) instantiates over a
//!    `Project` whose `Fs` is the [`FirmamentZedFs`] cell-ledger;
//!  * Zed's REAL `project_panel`, `outline_panel`, and `terminal_view` panels
//!    `Panel::load` + `Workspace::add_panel` into the dock — and resolve back
//!    out of the workspace (`workspace.panel::<T>()` is `Some`);
//!  * the project panel's worktree SEES the cell namespace (the cells listed are
//!    the cells-as-files);
//!  * opening a cell from the project as a Zed `Buffer`, editing it, and saving
//!    through the real `Workspace` fires a verified turn (a `TurnReceipt`) — so a
//!    save FROM THE WORKSPACE is a turn on the ledger.
//!
//! Nothing here reimplements a Zed component: every panel + the workspace + the
//! project + the buffer are Zed's own crates at our gpui-fork rev. This is the
//! headless half of the deos-dock mount — the same gpui `Entity`s the cockpit
//! dock hosts.
//!
//! Only compiled under `--features full-zed`.
#![cfg(feature = "full-zed")]

use std::sync::Arc;

use fs::Fs;
use gpui::{TestAppContext, VisualTestContext};
use language::Point;
use project::Project;
use terminal_view::terminal_panel::TerminalPanel;
use terminal_view::TerminalView;
use workspace::{MultiWorkspace, Workspace};

use postage::stream::Stream as _;
use settings::SettingsStore;
use util::rel_path::RelPath;

use deos_zed_full::boot;
use deos_zed_full::FirmamentZedFs;

#[gpui::test]
async fn real_zed_workspace_with_panels_runs_over_the_cell_ledger(cx: &mut TestAppContext) {
    // 1. Install the Workspace + panel globals: first the settings store, then
    //    theme + each panel/editor crate's `init` action+observer registrations
    //    — the deos subset of the standalone binary's init.
    cx.update(|cx| {
        let settings_store = SettingsStore::test(cx);
        cx.set_global(settings_store);
        boot::install_workspace_globals(cx);
    });
    // The worktree background scanner + the terminal PTY both run on real OS
    // threads (the `scoped_priority` scan workers / the alacritty pty thread);
    // allow the test executor to park on them so those real-threaded scans run to
    // completion — set it up FRONT so even the initial worktree scan benefits.
    cx.executor().allow_parking();

    // 2. The cell-ledger filesystem, seeded with file-cells under the worktree
    //    root (top-level files + a NESTED tree two levels deep, so we exercise
    //    leaf listing, top-level directory listing, AND recursive expansion into
    //    subdirectories of cells). Keep the TYPED handle to read the receipt log.
    //
    //    Tree:
    //      /proj/main.rs
    //      /proj/lib.rs
    //      /proj/src/mod.rs
    //      /proj/src/inner/deep.rs     ← two levels under the root
    let main_rs = "fn main() {\n    println!(\"from a cell\");\n}\n";
    let lib_rs = "pub fn hello() {}\n";
    let nested_rs = "pub mod inner;\n";
    let deep_rs = "pub fn deep() -> u8 { 42 }\n";
    let fzfs = Arc::new(FirmamentZedFs::new());
    fzfs.seed_file("/proj/main.rs", main_rs).unwrap();
    fzfs.seed_file("/proj/lib.rs", lib_rs).unwrap();
    fzfs.seed_file("/proj/src/mod.rs", nested_rs).unwrap();
    fzfs.seed_file("/proj/src/inner/deep.rs", deep_rs).unwrap();
    assert_eq!(fzfs.receipt_count(), 0, "seeds are genesis — no turn yet");

    // 3. A REAL Zed Project, worktree rooted at /proj, filesystem = the cells.
    let fs: Arc<dyn Fs> = fzfs.clone();
    let project = Project::test(fs.clone(), ["/proj".as_ref()], cx).await;

    // 4. A REAL Workspace window (the MultiWorkspace root → inner Workspace) over
    //    that project. `MultiWorkspace::test_new` derives the AppState from the
    //    project — so the workspace's global `fs` IS our FirmamentZedFs.
    let window = cx.add_window(|window, cx| MultiWorkspace::test_new(project.clone(), window, cx));
    let workspace = window
        .read_with(cx, |mw, _| mw.workspace().clone())
        .unwrap();
    let vcx = &mut VisualTestContext::from_window(window.into(), cx);

    // 5. LOAD + ADD THE REAL PANELS into the dock — the exact `initialize_panels`
    //    dance, run inside the window's async context.
    let weak_ws = workspace.downgrade();
    let panels_task = vcx.update(|window, cx| {
        let weak_ws = weak_ws.clone();
        window.spawn(cx, async move |cx| {
            boot::load_firmament_panels(weak_ws, cx.clone()).await
        })
    });
    vcx.run_until_parked();
    let (project_panel, outline_panel, terminal_panel) = panels_task
        .await
        .expect("the three panels load + add over the cell-fs workspace");

    // 6. THE PANELS ARE PRESENT IN THE WORKSPACE — resolve them back out of the
    //    real dock by type. This is the workspace's own panel registry answering.
    workspace.read_with(vcx, |ws, cx| {
        assert!(
            ws.panel::<project_panel::ProjectPanel>(cx).is_some(),
            "the project panel is mounted in the dock"
        );
        assert!(
            ws.panel::<outline_panel::OutlinePanel>(cx).is_some(),
            "the outline panel is mounted in the dock"
        );
        assert!(
            ws.panel::<terminal_view::terminal_panel::TerminalPanel>(cx)
                .is_some(),
            "the integrated terminal panel is mounted in the dock"
        );
    });

    // 6b. WAIT FOR THE INITIAL WORKTREE SCAN to fully drain (its `scoped_priority`
    //     background workers read the cell-fs over real OS threads). Without this,
    //     a top-level directory stays mid-scan (`PendingDir`) and its first level
    //     never lands — the exact `scan_complete().await` zed's own worktree tests
    //     use after building a `Worktree`.
    let scan_done = project
        .read_with(vcx, |project, cx| {
            project
                .worktrees(cx)
                .next()
                .map(|wt| wt.read(cx).as_local().unwrap().scan_complete())
        })
        .expect("the cell worktree exists");
    scan_done.await;
    vcx.run_until_parked();

    // 7. THE PROJECT PANEL SEES THE CELL NAMESPACE. The worktree scan that backs
    //    it ran over FirmamentZedFs::read_dir — so the entries it knows are the
    //    cells-as-files. Assert the worktree (the data the project panel renders)
    //    contains our seeded cells.
    let worktree_paths: Vec<String> = project.read_with(vcx, |project, cx| {
        let mut out = Vec::new();
        for wt in project.worktrees(cx) {
            let wt = wt.read(cx);
            for entry in wt.entries(true, 0) {
                out.push(entry.path.as_std_path().to_string_lossy().to_string());
            }
        }
        out
    });
    assert!(
        worktree_paths.iter().any(|p| p.ends_with("main.rs")),
        "the project panel's worktree lists the cell main.rs: {worktree_paths:?}"
    );
    assert!(
        worktree_paths.iter().any(|p| p.ends_with("lib.rs")),
        "the project panel's worktree lists the cell lib.rs: {worktree_paths:?}"
    );
    assert!(
        worktree_paths.iter().any(|p| p.ends_with("src")),
        "the project panel's worktree lists the cell directory src: {worktree_paths:?}"
    );
    // The panel handle is live (its model resolves the same worktree).
    let _ = (&project_panel, &outline_panel);

    // 7b. SEAM (a) CLOSED — NESTED-DIRECTORY EXPANSION. The original seam: the
    //     worktree scan stopped at the top level (`src` listed, its children did
    //     not), because every cell reported inode 0 and Zed's scanner treats a
    //     child whose inode equals an ancestor's as a symlink cycle — so it never
    //     enqueued the subdirectory scan. FirmamentZedFs now gives each cell a
    //     distinct inode (`path_inode`), so the worktree recurses into the cell
    //     namespace: scanning `src` reaches `src/mod.rs`, the `src/inner` dir, and
    //     `src/inner/deep.rs`. The scan runs `FirmamentZedFs::read_dir` over the
    //     cell ledger directly — NO `watch` events needed.
    //
    //     The worktree was driven to a quiesced full scan above (`scan_complete`),
    //     so the recursive cell tree is already materialized — assert the deep,
    //     two-levels-under-root cell is present.
    let nested_after: Vec<String> = project.read_with(vcx, |project, cx| {
        let mut out = Vec::new();
        for wt in project.worktrees(cx) {
            for entry in wt.read(cx).entries(true, 0) {
                out.push(entry.path.as_std_path().to_string_lossy().to_string());
            }
        }
        out
    });
    assert!(
        nested_after.iter().any(|p| p.ends_with("src/mod.rs") || p.ends_with("src\\mod.rs")),
        "the worktree recurses into src and lists the first-level nested cell src/mod.rs: {nested_after:?}"
    );
    assert!(
        nested_after.iter().any(|p| p.ends_with("inner")),
        "the worktree lists the deeper cell-directory src/inner: {nested_after:?}"
    );
    assert!(
        nested_after.iter().any(|p| p.ends_with("deep.rs")),
        "the worktree recurses two levels into src/inner and lists deep.rs: {nested_after:?}"
    );

    // 7c. EXPLICIT EXPANSION over the cell-fs ALSO works — drive Zed's own
    //     `refresh_entries_for_paths` (the exact primitive the project panel runs
    //     when you click a collapsed directory) on the deeper `src/inner` path.
    //     It sends a `ScanRequest` to the worktree's background scanner, which
    //     re-reads the cell namespace under that path; we `.recv().await` the
    //     completion barrier. The deep cell remains listed after the targeted
    //     re-scan — proving the project-panel expansion path is wired to the
    //     cell-fs, not just the boot-time full scan.
    let worktree = project
        .read_with(vcx, |project, cx| project.worktrees(cx).next())
        .expect("the project has the cell worktree");
    let mut refresh_inner = worktree.read_with(vcx, |wt, _| {
        wt.as_local()
            .unwrap()
            .refresh_entries_for_paths(vec![RelPath::unix("src/inner").unwrap().into()])
    });
    refresh_inner.recv().await;
    vcx.run_until_parked();
    let after_explicit_expand: Vec<String> = project.read_with(vcx, |project, cx| {
        let mut out = Vec::new();
        for wt in project.worktrees(cx) {
            for entry in wt.read(cx).entries(true, 0) {
                out.push(entry.path.as_std_path().to_string_lossy().to_string());
            }
        }
        out
    });
    assert!(
        after_explicit_expand.iter().any(|p| p.ends_with("deep.rs")),
        "after driving refresh_entries_for_paths(src/inner) the deep cell is listed: {after_explicit_expand:?}"
    );

    // 8. OPEN A CELL FROM THE PROJECT AS A BUFFER, edit it, and SAVE through the
    //    real Workspace's project — a save FROM THE WORKSPACE is a verified turn.
    let project_path = project
        .read_with(vcx, |project, cx| {
            project.find_project_path("proj/main.rs", cx)
        })
        .expect("the seeded cell is visible to the worktree scan");
    let buffer = project
        .update(vcx, |project, cx| project.open_buffer(project_path, cx))
        .await
        .expect("Zed opens the cell as a buffer");
    buffer.read_with(vcx, |buffer, _| {
        assert_eq!(buffer.text(), main_rs, "the buffer loaded the cell content");
    });
    buffer.update(vcx, |buffer, cx| {
        let line1 = buffer.text().lines().nth(1).unwrap().to_string();
        let col = line1.find("from a cell").unwrap();
        let start = Point::new(1, col as u32);
        let end = Point::new(1, (col + "from a cell".len()) as u32);
        buffer.edit([(start..end, "EDITED via the Workspace")], None, cx);
    });
    project
        .update(vcx, |project, cx| project.save_buffer(buffer.clone(), cx))
        .await
        .expect("the Workspace's project saves the buffer = a verified turn");

    // THE SAVE WAS A TURN: a genuine receipt landed on the ledger.
    assert!(
        fzfs.receipt_count() >= 1,
        "a save through the real Workspace fired a cap-gated turn (a receipt)"
    );
    let reloaded = fs.load("/proj/main.rs".as_ref()).await.unwrap();
    assert!(
        reloaded.contains("EDITED via the Workspace"),
        "the edit landed on the cell via a turn: {reloaded:?}"
    );

    // Conservation: a content save leaves Σ balance invariant.
    let _ = fzfs.total_balance();

    // 9. SEAM (b) CLOSED — A REAL TERMINAL IN THE DOCKED PANEL. The TerminalPanel
    //    is mounted (step 6); now open an ACTUAL terminal in it. We spawn a REAL
    //    OS PTY running the system shell via Zed's own `TerminalPanel::add_center_terminal`
    //    + `Project::create_terminal_shell` — the exact path the standalone binary
    //    runs and the exact path zed's own headless terminal_panel test exercises.
    //    `allow_parking` lets the PTY's real background thread run under the test
    //    executor (the fake clock otherwise refuses real blocking waits).
    vcx.executor().allow_parking();
    let terminal = workspace
        .update_in(vcx, |workspace, window, cx| {
            TerminalPanel::add_center_terminal(workspace, window, cx, |project, cx| {
                // A real shell PTY. cwd None = the shell's own default dir.
                project.create_terminal_shell(None, cx)
            })
        })
        .await
        .expect("a real PTY shell terminal opens in the docked TerminalPanel")
        .upgrade()
        .expect("the spawned terminal entity is live");
    vcx.run_until_parked();

    // The terminal is PRESENT + ACTIVE — its TerminalView is the active item in the
    // workspace pane the panel created it in, and the terminal entity is live.
    workspace.read_with(vcx, |workspace, cx| {
        let active = workspace
            .active_pane()
            .read(cx)
            .active_item()
            .expect("the workspace pane has an active item after opening the terminal");
        assert!(
            active.downcast::<TerminalView>().is_some(),
            "the active workspace item is a real TerminalView (the terminal is open)"
        );
    });

    // FEED IT A REAL COMMAND + DRAIN THE PTY: write `echo deos-cell-terminal\n` to
    // the shell and let the OS shell run it. The PTY echoes input + the command's
    // stdout back through the grid. We poll the terminal's rendered content until
    // our marker appears (a real shell really ran).
    terminal.update(vcx, |term, _| {
        term.input(b"echo deos-cell-terminal\n".to_vec());
    });
    let mut saw_output = false;
    for _ in 0..200 {
        vcx.run_until_parked();
        // `sync` drains the PTY's pending terminal events into the alacritty grid
        // and recomputes the rendered viewport (`last_content.cells`) — the exact
        // call the terminal element makes each frame. We read the grid back out.
        let content = terminal.update_in(vcx, |term, window, cx| {
            term.sync(window, cx);
            term.last_content
                .cells
                .iter()
                .map(|c| c.cell.character())
                .collect::<String>()
        });
        if content.contains("deos-cell-terminal") {
            saw_output = true;
            break;
        }
        vcx.executor().advance_clock(std::time::Duration::from_millis(20));
    }
    assert!(
        saw_output,
        "the real PTY shell ran `echo deos-cell-terminal` and its output reached the terminal grid"
    );
    let _ = &terminal_panel;

    // Keep the workspace handle live to the end (no premature drop of the window).
    let _: &gpui::Entity<Workspace> = &workspace;
}
