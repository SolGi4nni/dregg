//! `boot` — instantiate a REAL Zed `Workspace` (with its real panels) over a
//! [`FirmamentZedFs`] cell-ledger, headlessly.
//!
//! This is stage 2/3 of the ladder in `DESIGN-FULL-ZED-EMBED.md`: not just the
//! editor buffer/save seam (proven in `tests/project_over_cells.rs`), but the
//! whole Zed **Workspace shell** — the `Workspace` entity, its dock, and the
//! real `project_panel` / `outline_panel` / `terminal_view` panels — mounted on
//! top of a `Project` whose filesystem IS the dregg cell-ledger.
//!
//! Every method here drives Zed's OWN crates (`workspace`, `project_panel`,
//! `outline_panel`, `terminal_view`, `editor`, `command_palette`, `search`) —
//! nothing is reimplemented. We replicate the exact init + panel-load sequence
//! the standalone `zed` binary runs in `crates/zed/src/zed.rs::initialize_panels`
//! (spawn `Panel::load`, then `workspace.add_panel`), minus the OS-shell pieces
//! (crash handler, auto-update, CLI/IPC, OS menu, login/collab).
//!
//! Because the panels and `Workspace` are all gpui `Entity`s on the SAME gpui
//! instance the deos cockpit dock uses (the zed-fork gpui at our rev), the
//! resulting `Workspace` drops into the deos dock exactly like deos-zed's thin
//! editor surface — this is the headless, testable half of that mount.
//!
//! Only built under `--features full-zed` (it needs the heavy Zed graph).
#![cfg(feature = "full-zed")]

use std::sync::Arc;

use anyhow::Result;
use gpui::{AsyncWindowContext, Entity, WeakEntity};
use outline_panel::OutlinePanel;
use project_panel::ProjectPanel;
use terminal_view::terminal_panel::TerminalPanel;
use workspace::{AppState, Workspace};

/// Install the global state every Zed `Workspace` + the enabled panels need:
/// the theme registry and the per-crate action/observer registrations
/// (`editor::init`, `project_panel::init`, `outline_panel::init`,
/// `terminal_view::init`, `command_palette::init`, `search::init`).
///
/// This is the deos-side subset of `crates/zed/src/main.rs`'s ~97 `::init`
/// calls — only the panels we mount, none of the standalone-binary shell.
///
/// The caller must have installed a `settings::SettingsStore` global FIRST
/// (`theme::init` reads it). The headless boot uses `SettingsStore::test`; a
/// real deos boot uses `SettingsStore::new` — either way, this runs after it.
pub fn install_workspace_globals(cx: &mut gpui::App) {
    // `theme_settings::init` (NOT bare `theme::init`) — it loads the base theme
    // AND installs the `GlobalThemeSettingsProvider` the panels read. This is the
    // exact call `AppState::test` / the standalone binary make.
    theme_settings::init(theme::LoadThemes::JustBase, cx);

    // The panel + editor crate registrations. Each is `fn init(&mut App)` and
    // installs action handlers / `observe_new` hooks that the Workspace's panel
    // machinery dispatches to — exactly what the standalone binary runs.
    editor::init(cx);
    project_panel::init(cx);
    outline_panel::init(cx);
    terminal_view::init(cx);
    command_palette::init(cx);
    search::init(cx);
}

/// Build a REAL (non-test) [`AppState`] for the live deos cockpit and
/// `AppState::set_global` it — the load-bearing **mount seam** for hosting the
/// whole Zed `Workspace` as a live cockpit window.
///
/// This is the same shape as `AppState::test` (the constructor the headless
/// proofs use), but with every fake replaced by its production part:
///
///  * `client::Client::new` over a real [`clock::RealSystemClock`] + an
///    [`http_client::HttpClientWithUrl`] wrapping a [`http_client::BlockedHttpClient`]
///    (editing cells over the FirmamentFs ledger needs no network — the blocked
///    client makes that explicit; a host that wants collab can swap in a real
///    `ReqwestClient` and call `client.set_id`/sign-in itself);
///  * `session::Session::new` over the real [`db::AppDatabase`]'s
///    [`db::kvp::KeyValueStore`] (the on-disk session store the standalone Zed
///    binary uses), wrapped in a `session::AppSession`;
///  * `client::UserStore::new` + `workspace::WorkspaceStore::new` over that
///    client (the same plain `pub fn` constructors `AppState::test` calls);
///  * `language::LanguageRegistry::new` (the real, non-`::test` registry);
///  * `node_runtime::NodeRuntime::unavailable` (cell editing needs no node
///    runtime; a host that wants LSP/extensions can build a real `NodeRuntime`);
///  * the cockpit's own `build_window_options` (a plain default — the cockpit
///    hosts the Workspace as a *pane*, so the OS-window options are unused by the
///    embed; supplied to satisfy the field).
///
/// The caller passes the cell-ledger `fs` (a `FirmamentZedFs`) so the returned
/// `AppState.fs` IS the ledger. After this returns, `AppState::global(cx)` and
/// `Client::set_global` are live, so the panels' `*::load` and the Workspace's
/// machinery resolve their globals exactly as in the standalone binary.
///
/// Call this ONCE per cockpit `App` (it `set_global`s); a second call is
/// idempotent on the client global but rebuilds the state. The caller must have
/// installed a `settings::SettingsStore` global FIRST (and typically called
/// [`install_workspace_globals`]).
pub fn build_live_app_state(fs: Arc<dyn fs::Fs>, cx: &mut gpui::App) -> Arc<AppState> {
    use gpui::AppContext as _;

    use client::{Client, UserStore};
    use http_client::{BlockedHttpClient, HttpClientWithUrl};
    use language::LanguageRegistry;
    use node_runtime::NodeRuntime;
    use session::{AppSession, Session};
    use workspace::WorkspaceStore;

    // Make the cell-ledger fs the App's global `Fs` (the panels + project read it).
    <dyn fs::Fs>::set_global(fs.clone(), cx);

    // A real client over the real system clock. No network is needed to edit
    // cells, so the HTTP carrier is a `BlockedHttpClient` behind the URL wrapper —
    // a genuine `Arc<HttpClientWithUrl>`, just one that refuses outbound requests.
    let clock = Arc::new(clock::RealSystemClock);
    let http: Arc<HttpClientWithUrl> = Arc::new(HttpClientWithUrl::new(
        Arc::new(BlockedHttpClient),
        "https://zed.dev",
        None,
    ));
    let client = Client::new(clock, http, cx);

    // The real session over the on-disk app database (the same KV store the
    // standalone Zed binary uses). `Session::new` is async; the App's foreground
    // executor blocks on it here exactly as `main.rs` does.
    let app_db = db::AppDatabase::new();
    let kv = db::kvp::KeyValueStore::from_app_db(&app_db);
    let session_id = uuid::Uuid::new_v4().to_string();
    // Build the session off the background executor and block the foreground on the
    // resulting task — the exact pattern `crates/zed/src/main.rs` uses.
    let session_task = cx.background_executor().spawn(Session::new(session_id, kv));
    let session = cx.foreground_executor().block_on(session_task);
    let app_session = cx.new(|cx| AppSession::new(session, cx));

    let languages = Arc::new(LanguageRegistry::new(cx.background_executor().clone()));
    let user_store = cx.new(|cx| UserStore::new(client.clone(), cx));
    let workspace_store = cx.new(|cx| WorkspaceStore::new(client.clone(), cx));

    // Register the client's per-App globals/handlers (the same call `AppState::test`
    // and the standalone binary make) so the Workspace's client-driven paths work.
    Client::set_global(client.clone(), cx);
    client::init(&client, cx);

    let app_state = Arc::new(AppState {
        client,
        fs,
        languages,
        user_store,
        workspace_store,
        node_runtime: NodeRuntime::unavailable(),
        build_window_options: |_, _| Default::default(),
        session: app_session,
    });
    AppState::set_global(app_state.clone(), cx);
    app_state
}

/// Load the three FirmamentFs-relevant panels (`project_panel`, `outline_panel`,
/// `terminal_view`) into an already-built `Workspace`, then `add_panel` each into
/// the dock — the exact dance `initialize_panels` performs in the standalone
/// binary, run inside an async window context so the `Panel::load` futures
/// resolve.
///
/// Returns the three panel entities for assertion. The caller drives this from a
/// `cx.spawn_in(window, …)` future (so `cx` is an [`AsyncWindowContext`]).
pub async fn load_firmament_panels(
    workspace: WeakEntity<Workspace>,
    mut cx: AsyncWindowContext,
) -> Result<(
    Entity<ProjectPanel>,
    Entity<OutlinePanel>,
    Entity<TerminalPanel>,
)> {
    // Spawn all three `Panel::load` tasks (each reads the workspace handle +
    // async window cx), then await — the panels build their views over the
    // workspace's `Project`, whose `Fs` is the FirmamentZedFs.
    let project_panel = ProjectPanel::load(workspace.clone(), cx.clone()).await?;
    let outline_panel = OutlinePanel::load(workspace.clone(), cx.clone()).await?;
    let terminal_panel = TerminalPanel::load(workspace.clone(), cx.clone()).await?;

    // Add each panel into the dock — `add_panel` is the real workspace API that
    // registers the panel with the dock, wires its subscriptions, and restores
    // its persisted size. After this, `workspace.panel::<T>(cx)` resolves.
    workspace.update_in(&mut cx, |workspace, window, cx| {
        workspace.add_panel(project_panel.clone(), window, cx);
        workspace.add_panel(outline_panel.clone(), window, cx);
        workspace.add_panel(terminal_panel.clone(), window, cx);
    })?;

    Ok((project_panel, outline_panel, terminal_panel))
}

/// Load the three FirmamentFs panels (project/outline/terminal) AND dock the
/// confined-Hermes AGENT panel into one already-built `Workspace` — the full
/// dock complement of the embedded deos IDE. This is `load_firmament_panels`
/// plus the agent surface, so a single Workspace instance carries every docked
/// panel of the embed at once.
///
/// The Hermes panel wraps a live [`crate::hermes_panel::HermesPanel`] over the
/// supplied confined [`HermesSession`](crate::hermes_panel::HermesSession). After
/// this resolves, `workspace.panel::<T>(cx)` is `Some` for the project, outline,
/// terminal, AND Hermes panels.
///
/// Returns the four docked panel entities for assertion.
pub async fn load_all_panels(
    workspace: WeakEntity<Workspace>,
    session: crate::hermes_panel::HermesSession,
    session_id: &str,
    mut cx: AsyncWindowContext,
) -> Result<(
    Entity<ProjectPanel>,
    Entity<OutlinePanel>,
    Entity<TerminalPanel>,
    Entity<crate::hermes_panel::HermesPanel>,
)> {
    let (project_panel, outline_panel, terminal_panel) =
        load_firmament_panels(workspace.clone(), cx.clone()).await?;

    // Dock the confined-Hermes agent panel ALONGSIDE the IDE panels — the same
    // `add_panel` registration, for the agent surface. `add_hermes_panel` builds
    // the panel over the session's live gateway and inserts it into the dock.
    let hermes_panel = workspace.update_in(&mut cx, |workspace, window, cx| {
        crate::hermes_panel::add_hermes_panel(workspace, session, session_id, window, cx)
    })?;

    Ok((project_panel, outline_panel, terminal_panel, hermes_panel))
}
