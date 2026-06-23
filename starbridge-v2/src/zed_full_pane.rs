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
//! ## The mount seam — the live-cockpit `AppState`
//!
//! A `workspace::Workspace` is built by `Workspace::new(id, project, app_state,
//! window, cx)`. The `project` is `Project::local(…, fzfs, …)` over a
//! [`deos_zed_full::FirmamentZedFs`] — `Project::local` is a plain `pub fn` (NOT
//! test-support), so it is available in the live cockpit, and the panels'
//! `Panel::load` (`deos_zed_full::boot::load_all_panels`) are likewise plain.
//!
//! The ONE piece the live cockpit still needs is a non-test [`AppState`]:
//! `AppState::test` (the constructor the headless proofs use) is
//! `#[cfg(any(test, feature = "test-support"))]`, and `deos-zed-full`'s `full-zed`
//! feature does not turn on `workspace`/`project` test-support outside its own
//! dev-deps. The real cockpit therefore needs a real `AppState` — a real
//! `client::Client` (real `SystemClock` + `HttpClientWithUrl`), a `session::Session`
//! (async, over a `KeyValueStore`), a `client::UserStore`, a
//! `workspace::WorkspaceStore`, a `language::LanguageRegistry`, and a
//! `node_runtime::NodeRuntime` — built once and `AppState::set_global`'d on the
//! cockpit App. That is a bounded, real construction (the named seam), tracked in
//! HORIZONLOG; until it lands, [`ZedFullPane::mount`] takes a caller-built
//! `AppState`, so a host that already has one (or the headless proof, which has
//! `AppState::test`) mounts the full Workspace today.
//!
//! Gated on the `zed-full-pane` feature.
#![cfg(feature = "zed-full-pane")]

use std::sync::Arc;

use gpui::{
    div, AnyElement, App, Entity, FocusHandle, IntoElement, ParentElement as _, SharedString,
    Styled as _, Window,
};

use deos_zed_full::FirmamentZedFs;
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
