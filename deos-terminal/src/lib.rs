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
//! ```no_run
//! // NO_RUN: opens a real OS window on the native windowing platform and spawns `$SHELL`
//! // on a PTY. Compiles and links here; `cargo run --bin deos-terminal-demo` is the way
//! // to actually run it (`src/bin/demo.rs` is this example, verbatim).
//! use deos_terminal::view::TerminalView;
//! use gpui::{App, AppContext, Bounds, Focusable, WindowBounds, WindowOptions, px, size};
//!
//! // The windowing platform (metal/wgpu) builds the concrete `Application` — the same
//! // entry starbridge-v2 uses.
//! gpui_platform::application().run(|cx: &mut App| {
//!     let bounds = Bounds::centered(None, size(px(900.), px(560.)), cx);
//!     cx.open_window(
//!         WindowOptions {
//!             window_bounds: Some(WindowBounds::Windowed(bounds)),
//!             ..Default::default()
//!         },
//!         |window, cx| {
//!             let view = cx.new(|cx| TerminalView::spawn_shell(cx).expect("spawn $SHELL"));
//!             // Focus the terminal so keystrokes flow to the PTY immediately.
//!             let handle = view.read(cx).focus_handle(cx);
//!             window.focus(&handle, cx);
//!             view
//!         },
//!     )
//!     .expect("failed to open window");
//!     cx.activate(true);
//! });
//! ```

// The PTY+grid model, the gpui view, and the xterm keymap are the NATIVE
// presentation stack: they pull `alacritty_terminal` (whose `polling`/`home`
// deps do not compile to wasm32) and the native gpui platform. On wasm32 the
// gpui view mounts on `gpui_web` from the cockpit-web crate (a sibling step),
// driving its byte I/O through the [`transport`] WS client below — so these
// modules are native-only here.
// The `not(wasm32)` is belt-and-suspenders: the native presentation stack can
// NEVER compile to wasm (alacritty + native gpui), so even a `default-features`
// wasm build (which leaves `native-ui` on) cleanly skips it and builds only the
// `transport` WS client. The wasm build needs no special feature flags.
#[cfg(all(feature = "native-ui", not(target_arch = "wasm32")))]
pub mod keymap;
#[cfg(all(feature = "native-ui", not(target_arch = "wasm32")))]
pub mod model;
#[cfg(all(feature = "native-ui", not(target_arch = "wasm32")))]
pub mod view;

/// The byte-transport seam: where the [`TerminalView`] grid reads PTY output and
/// writes keystrokes. Two impls — a native PTY (today) and a `web_sys::WebSocket`
/// (the browser) — behind one [`transport::TerminalTransport`] trait, so the same
/// grid drives either. This module compiles on EVERY target (the trait + wire
/// codec are platform-free; the wasm `WsTransport` is `cfg(wasm32)`).
pub mod transport;

/// The dock-surface adapter shape (behind the `cockpit-surface` feature), so the
/// base crate stays UI-host-agnostic and the demo doesn't pull it.
#[cfg(all(feature = "cockpit-surface", not(target_arch = "wasm32")))]
pub mod cockpit_surface;

#[cfg(all(feature = "native-ui", not(target_arch = "wasm32")))]
pub use model::{TermSize, Terminal, TerminalContent};
#[cfg(all(feature = "native-ui", not(target_arch = "wasm32")))]
pub use view::TerminalView;

pub use transport::{TerminalTransport, WireMsg};
