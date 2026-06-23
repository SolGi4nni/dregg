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

pub mod firmament_zed_fs;
pub use firmament_zed_fs::FirmamentZedFs;

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
}
