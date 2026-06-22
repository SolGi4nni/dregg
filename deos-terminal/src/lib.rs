//! deos-terminal — a real terminal emulator as a deos surface.
//!
//! Run commands — cargo, git, shells — INSIDE deos. The terminal half of the
//! self-hosting dev loop.
//!
//! - [`model`] — the PTY + alacritty event-loop + grid (`Terminal`), and a
//!   self-contained [`model::TerminalContent`] snapshot.
//! - [`view`] — a lean gpui [`view::TerminalView`] entity that paints the grid,
//!   handles keyboard/scroll input, and repaints as output streams.
//! - [`keymap`] — gpui `Keystroke` → xterm escape bytes (adapted from Zed).
//!
//! The cockpit dock adapter lives in starbridge-v2 (`dock::terminal_surface`),
//! because the `CockpitSurface` trait it implements is defined there; this crate
//! stays UI-host-agnostic (it just exposes the `TerminalView` entity).
//!
//! ## Quick start (standalone window)
//!
//! ```ignore
//! use deos_terminal::view::TerminalView;
//!
//! // The windowing platform builds the `Application` (see `src/bin/demo.rs`).
//! gpui_platform::application().run(|cx| {
//!     // ... open a window whose root entity is
//!     // `cx.new(|cx| TerminalView::spawn_shell(cx).unwrap())`
//! });
//! ```

pub mod keymap;
pub mod model;
pub mod view;

/// The dock-surface adapter shape (behind the `cockpit-surface` feature), so the
/// base crate stays UI-host-agnostic and the demo doesn't pull it.
#[cfg(feature = "cockpit-surface")]
pub mod cockpit_surface;

pub use model::{Terminal, TerminalContent, TermSize};
pub use view::TerminalView;
