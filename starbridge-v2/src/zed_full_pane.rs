//! `zed_full_pane` — mount the WHOLE Zed `workspace::Workspace` (the real
//! `editor`/`workspace`/`project` crates + every panel, over a FirmamentFs
//! cell-ledger) as a deos cockpit pane.
//!
//! Where [`crate::dock::editor_surface`] mounts deos-zed's THIN editor as a
//! cockpit surface, this mounts the FULL Zed Workspace shell — the same one
//! [`deos_zed_full`] proves runs as one thing in
//! `deos-zed-full/tests/unified_workspace_one_running_thing.rs` (project /
//! outline / terminal / Hermes panels docked + git auto-discovered + search + the
//! command palette + a real PTY + a save-is-a-turn) and bakes a PNG of in
//! `deos-zed-full/tests/unified_workspace_png_bake.rs`.
//!
//! ## The graph merge — RESOLVED (one gpui)
//!
//! `deos-zed-full` is its OWN cargo workspace pulling Zed's editor crates from
//! `emberian/zed@407a6ff`; those crates depend on `gpui`, which THIS workspace's
//! `[patch."https://github.com/emberian/zed"]` redirects to the local `407a6ff`
//! checkout. Because the patch is path-based and applies graph-wide, the merged
//! graph resolves to ONE gpui — the editor `Entity`/`Window`/`Render` types unify
//! with the cockpit's gpui, so an `Entity<workspace::Workspace>` drops straight
//! into a cockpit pane. (Confirmed: `cargo metadata --features zed-full-pane`
//! resolves; this module compiles under `--features zed-full-pane`.)
//!
//! ## The mount seam — CLOSED (the live-cockpit `AppState`)
//!
//! A `workspace::Workspace` is built by `Workspace::new(id, project, app_state,
//! window, cx)`. The `project` is `Project::local(…, fzfs, …)` over a
//! [`deos_zed_full::FirmamentZedFs`] — `Project::local` is a plain `pub fn` (NOT
//! test-support), so it is available in the live cockpit, and the panels'
//! `Panel::load` (`deos_zed_full::boot::load_all_panels`) are likewise plain.
//!
//! The one piece the live cockpit used to lack was a non-test [`AppState`]:
//! `AppState::test` is `#[cfg(test/test-support)]`. That seam is now CLOSED by
//! [`deos_zed_full::boot::build_live_app_state`] — a genuine `AppState` from the
//! production parts (a real `client::Client` over `clock::RealSystemClock` + an
//! `HttpClientWithUrl`, a `session::Session` over the real `db::AppDatabase`, a
//! `client::UserStore`, a `workspace::WorkspaceStore`, a real
//! `language::LanguageRegistry`, and `node_runtime::NodeRuntime::unavailable`),
//! built once and `AppState::set_global`'d on the cockpit App.
//!
//! ## The window-able API
//!
//! [`ZedWindow::open`] is the clean entry the deos desktop calls to host a Zed
//! window: it builds (or reuses) the cockpit `AppState`, a fresh
//! [`FirmamentZedFs`] cell-ledger seeded at the given path, a real `Project` over
//! it, a docked `Workspace`, and returns a [`ZedFullPane`] (a [`CockpitSurface`]).
//! Each call is an independent Zed window (its own `Entity<Workspace>` + ledger),
//! so the desktop can host one or MANY. [`ZedFullPane::mount`] /
//! [`ZedFullPane::build_project_and_workspace`] remain as the lower-level seam a
//! host with its own `AppState` (or the headless proof) drives.
//!
//! Gated on the `zed-full-pane` feature.
#![cfg(feature = "zed-full-pane")]

use std::sync::Arc;

use gpui::{
    AnyElement, App, Entity, FocusHandle, IntoElement, ParentElement as _, SharedString,
    Styled as _, Window, div,
};

use deos_zed_full::FirmamentZedFs;
use deos_zed_full::fs;
use deos_zed_full::zed::{project, settings, theme, workspace};
use workspace::{AppState, Workspace};

use crate::dock::surface::{CockpitSurface, SurfaceId};

/// A cockpit pane that hosts the WHOLE Zed `Workspace` over a cell-ledger. The
/// pane owns the live `Entity<Workspace>`; `render_body` renders it, so the full
/// IDE (dock + panes + every panel) appears as one cockpit surface/tab.
pub struct ZedFullPane {
    id: SurfaceId,
    /// The live, fully-docked Zed Workspace (the same entity the headless proof +
    /// PNG bake build). Renders as a gpui view.
    workspace: Entity<Workspace>,
    /// The cell-ledger fs the Workspace's project rides — kept so the pane can
    /// read the receipt log (a save through the IDE is a verified turn here).
    fzfs: Arc<FirmamentZedFs>,
    focus: FocusHandle,
}

impl ZedFullPane {
    /// Mount a full-Workspace pane from a caller-built [`Workspace`] entity (built
    /// over `fzfs` via `Workspace::new` + `boot::load_all_panels`). The host
    /// supplies the workspace because the live `AppState` is the named mount seam
    /// (see module docs); the headless proof + a future cockpit-AppState builder
    /// both produce one and call this.
    pub fn mount(
        id: SurfaceId,
        workspace: Entity<Workspace>,
        fzfs: Arc<FirmamentZedFs>,
        cx: &mut App,
    ) -> Self {
        Self {
            id,
            workspace,
            fzfs,
            focus: cx.focus_handle(),
        }
    }

    /// Build the cell-ledger fs + a real Zed `Project` over it + a docked
    /// `Workspace`, given a real (or test) [`AppState`]. This is the construction
    /// the cockpit calls once it has an `AppState`; it is the SAME sequence the
    /// headless proof runs, minus the test-support `MultiWorkspace::test_new`
    /// wrapper (here the plain `Workspace::new`).
    ///
    /// Returns the workspace entity + the fs; the caller drives the async panel
    /// load (`deos_zed_full::boot::load_all_panels`) on its window context, then
    /// `ZedFullPane::mount`s the result.
    pub fn build_project_and_workspace(
        app_state: Arc<AppState>,
        fzfs: Arc<FirmamentZedFs>,
        window: &mut Window,
        cx: &mut App,
    ) -> (Entity<Workspace>, Entity<project::Project>) {
        use project::{LocalProjectFlags, Project};
        let fs: Arc<dyn fs::Fs> = fzfs.clone();
        let project = Project::local(
            app_state.client.clone(),
            app_state.node_runtime.clone(),
            app_state.user_store.clone(),
            app_state.languages.clone(),
            fs,
            None,
            LocalProjectFlags {
                init_worktree_trust: true,
                ..Default::default()
            },
            cx,
        );
        let workspace = cx.new(|cx| Workspace::new(None, project.clone(), app_state, window, cx));
        (workspace, project)
    }

    /// The live Workspace entity (host-side inspection / driving).
    pub fn workspace(&self) -> &Entity<Workspace> {
        &self.workspace
    }

    /// The receipt count on the cell-ledger — a save through the IDE grows this.
    pub fn receipt_count(&self) -> usize {
        self.fzfs.receipt_count()
    }

    /// The cell-ledger fs this pane's Workspace rides (host-side inspection).
    pub fn fzfs(&self) -> &Arc<FirmamentZedFs> {
        &self.fzfs
    }
}

/// THE WINDOW-ABLE ENTRY — open a full Zed `Workspace` as a hostable cockpit
/// window. The deos desktop calls [`ZedWindow::open`] to host one (or many) Zed
/// windows; each open is an independent Zed IDE (its own `Entity<Workspace>` +
/// its own [`FirmamentZedFs`] cell-ledger), returned as a [`ZedFullPane`] — a
/// [`CockpitSurface`] the desktop drops into any pane/window slot.
///
/// This is the public mount/open API the sibling desktop lane wires; it owns
/// the whole boot (globals, the live `AppState`, the seeded ledger, the project,
/// the docked Workspace, the opened buffer) so the caller need only place the
/// returned surface.
pub struct ZedWindow;

impl ZedWindow {
    /// Open a Zed `Workspace` window rooted at `root` (an in-ledger path like
    /// `/proj`), seeded with `files` (path → contents) so the project panel has a
    /// namespace to show. Returns a live [`ZedFullPane`] whose body IS the whole
    /// Zed IDE (dock + every panel) over a fresh cell-ledger.
    ///
    /// Idempotent on the cockpit globals: the first call installs the workspace
    /// globals + the live `AppState`; subsequent calls reuse them, so EACH call
    /// yields an independent Zed window. The async panel-load + buffer-open run as
    /// detached tasks on `window` (the same dance the headless bake drives); the
    /// returned pane renders the live Workspace immediately and fills in as the
    /// tasks resolve.
    pub fn open(
        id: SurfaceId,
        root: &str,
        files: &[(&str, &str)],
        window: &mut Window,
        cx: &mut App,
    ) -> ZedWindowHandle {
        // 1. The cockpit globals (idempotent — installed once per App). A
        //    SettingsStore must exist first; the live cockpit sets its own earlier,
        //    so install one only if absent. `install_workspace_globals` registers
        //    the editor/panel/theme globals + action handlers; `theme::GlobalTheme`
        //    (set by `theme_settings::init`) is the marker that they are installed,
        //    so a second `ZedWindow::open` reuses them instead of double-registering.
        if !cx.has_global::<settings::SettingsStore>() {
            // The real settings initializer (installs the `SettingsStore` global
            // over the bundled default settings). The live cockpit normally calls
            // its own settings init earlier; this is the fallback path.
            settings::init(cx);
        }
        if !cx.has_global::<theme::GlobalTheme>() {
            deos_zed_full::boot::install_workspace_globals(cx);
        }

        // 2. A fresh cell-ledger fs for THIS window, seeded.
        let fzfs = Arc::new(FirmamentZedFs::new());
        for (path, content) in files {
            let _ = fzfs.seed_file(*path, content);
        }

        // 3. The live AppState (built once, AppState::set_global'd) + a real
        //    Project over this window's ledger + a docked Workspace.
        let fs: Arc<dyn fs::Fs> = fzfs.clone();
        let app_state = deos_zed_full::boot::build_live_app_state(fs, cx);
        let (workspace, project) =
            ZedFullPane::build_project_and_workspace(app_state, fzfs.clone(), window, cx);

        // 4. Drive the worktree scan + the async panel load + open the root file,
        //    all on this window — detached, so the surface is returned now and the
        //    IDE fills in as the tasks resolve (the same dance the headless bake
        //    drives).
        let root_owned = root.to_string();
        let first_file = files
            .first()
            .map(|(p, _)| p.trim_start_matches('/').to_string());
        let proj = project.clone();
        let weak_ws = workspace.downgrade();
        window
            .spawn(cx, async move |cx| {
                // Materialize the worktree over `root` so the project panel lists
                // the cells, then wait for the scan to quiesce. (`Entity::update`
                // in an async window context returns the value directly — the same
                // shape the headless bake drives.)
                let task =
                    proj.update(cx, |p, cx| p.find_or_create_worktree(&root_owned, true, cx));
                if let Ok((tree, _)) = task.await {
                    if let Some(scan) =
                        tree.read_with(cx, |t, _| t.as_local().map(|l| l.scan_complete()))
                    {
                        scan.await;
                    }
                }
                // Dock the project / outline / terminal panels.
                let _ =
                    deos_zed_full::boot::load_firmament_panels(weak_ws.clone(), cx.clone()).await;
                // Open the first seeded file as a center editor buffer.
                if let Some(rel) = first_file {
                    if let Some(path) = proj.update(cx, |p, cx| p.find_project_path(&rel, cx)) {
                        if let Ok(opened) = weak_ws.update_in(cx, |ws, window, cx| {
                            ws.open_path(path, None, true, window, cx)
                        }) {
                            let _ = opened.await;
                        }
                    }
                }
            })
            .detach();

        let pane = ZedFullPane::mount(id, workspace, fzfs, cx);
        ZedWindowHandle { pane, project }
    }
}

/// The result of [`ZedWindow::open`] — the hostable [`ZedFullPane`] surface plus
/// the live `Project` (so the desktop lane can inspect / drive the project, e.g.
/// open more buffers or read the worktree). Take `.pane` and drop it into any
/// dock pane / window slot; keep `.project` to drive the IDE host-side.
pub struct ZedWindowHandle {
    /// The hostable surface — drop it into any dock pane / window slot.
    pub pane: ZedFullPane,
    /// The live Zed project over the cell-ledger.
    pub project: Entity<project::Project>,
}

impl CockpitSurface for ZedFullPane {
    fn item_id(&self) -> SurfaceId {
        self.id
    }

    fn tab_label(&self) -> SharedString {
        SharedString::from("Zed Workspace")
    }

    fn render_body(&mut self, _window: &mut Window, _cx: &mut App) -> AnyElement {
        // The pane body IS the live Zed Workspace view — the whole IDE (dock +
        // panes + panels) rendered as one cockpit surface.
        div()
            .track_focus(&self.focus)
            .size_full()
            .child(self.workspace.clone())
            .into_any_element()
    }

    fn focus_handle(&self, _cx: &App) -> FocusHandle {
        self.focus.clone()
    }

    fn boxed_clone(&self) -> Box<dyn CockpitSurface> {
        // Thin handles (an `Entity<Workspace>` + an `Arc` + a `FocusHandle`) — the
        // clone shares the same live Workspace, like the other cockpit surfaces
        // share the `Rc<RefCell<World>>`.
        Box::new(ZedFullPane {
            id: self.id,
            workspace: self.workspace.clone(),
            fzfs: self.fzfs.clone(),
            focus: self.focus.clone(),
        })
    }
}
