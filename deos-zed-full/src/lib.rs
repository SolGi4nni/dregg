//! `deos-zed-full` — the REAL Zed editor stack mounted over a cell-ledger
//! filesystem.
//!
//! Where [`deos-zed`](deos_zed) ships a *thin* custom editor (a gpui-component
//! `Input` + a [`Fs`](deos_zed::fs::Fs) seam), this crate mounts Zed's ACTUAL
//! `editor` / `workspace` / `project` crates — pulled as git deps at the SAME
//! zed fork rev our `gpui` comes from — over [`FirmamentZedFs`]: an
//! implementation of Zed's async [`fs::Fs`] trait backed by the dregg
//! cell-ledger (a file IS a cell, a save IS a verified `SetField` turn leaving a
//! `TurnReceipt`).
//!
//! ## Layers
//!
//! * [`firmament_zed_fs`] (ALWAYS built) — the [`fs::Fs`] adapter over the
//!   cell-ledger. Needs only Zed's `fs` crate, so it compiles light, with no
//!   editor graph. THIS is the seam the whole embed rides.
//! * The real Zed editor stack (`editor`/`workspace`/`project`/`language`),
//!   gated behind the `full-zed` feature (the heavy ~96-zed-crate / ~983-package
//!   graph — see `DESIGN-FULL-ZED-EMBED.md`).
//!
//! The first slice proves the seam end-to-end: a `FirmamentZedFs` satisfies Zed's
//! `Fs` trait, a Zed `Project` can be built over it, a seeded file-cell opens as
//! a buffer, and a save runs a real turn. The full-Workspace embed (project
//! panel, terminal, agent panel, git UI, command palette) is mapped in the
//! design doc and staged on top of this foundation.

pub mod sync_cell_fs;
pub use sync_cell_fs::SyncCellFs;

pub mod firmament_zed_fs;
pub use firmament_zed_fs::FirmamentZedFs;

/// The GIT SURFACE over the cell-ledger: a [`git::repository::GitRepository`]
/// whose change history, status, blame, and diffs are derived from the dregg
/// **receipt chain** (each save = a verified turn = a "commit") and the
/// **dregg-doc patch theory** (each edit = a Pijul-shaped patch; blame is correct
/// by construction) — NOT a host `.git`. This is the real substrate Zed's
/// `git_ui` panel renders. ALWAYS built (it needs only the base `git`/`rope`/
/// `text`/`gpui` deps + `dregg-doc`, no editor graph).
pub mod cell_git;
pub use cell_git::CellLedgerGit;

// Re-export Zed's `fs::Fs` trait so callers can treat `FirmamentZedFs` as an
// `Arc<dyn fs::Fs>` without depending on the zed `fs` crate directly.
pub use fs;

/// The real Zed editor stack, re-exported when built with `--features full-zed`.
/// Callers mount a `Workspace`/`Editor` over a `Project` whose `Fs` is a
/// [`FirmamentZedFs`].
#[cfg(feature = "full-zed")]
pub mod zed {
    pub use editor;
    pub use language;
    pub use project;
    pub use workspace;
    // The settings store + theme globals, re-exported so a cockpit host can name
    // `settings::SettingsStore` / `theme::GlobalTheme` (the idempotency markers a
    // window-opener checks) without a direct dep on the zed crates.
    pub use settings;
    pub use theme;
}

/// Boot a REAL Zed [`workspace::Workspace`] (with its real `project_panel` /
/// `outline_panel` / `terminal_view` panels) over a [`FirmamentZedFs`]
/// cell-ledger — the full-Workspace embed, headlessly instantiable. Built only
/// under `--features full-zed`.
#[cfg(feature = "full-zed")]
pub mod boot;

/// The CONFINED-HERMES AGENT PANEL — a [`workspace::Panel`] wrapping deos-hermes's
/// live [`AgentDockView`], docked into the real Zed [`workspace::Workspace`]
/// alongside the project/outline/terminal panels. Every agent tool-call a
/// cap-gated, metered, receipted dregg turn on the verified executor. Built only
/// under `--features full-zed`.
#[cfg(feature = "full-zed")]
pub mod hermes_panel;
