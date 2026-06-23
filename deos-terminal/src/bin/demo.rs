//! deos-terminal-demo — a standalone gpui window running a REAL shell.
//!
//! `cargo run --bin deos-terminal-demo` opens a window, spawns `$SHELL` on a
//! PTY, and you have a working terminal: type `ls`, `cargo --version`, `git
//! status`, an editor, anything. This is the proof that the terminal model +
//! view run a real shell; the same `TerminalView` mounts into the cockpit dock
//! via `starbridge-v2/src/dock/terminal_surface.rs`.

// Native-only: a gpui window over the native PTY. On wasm the gpui view mounts
// via `gpui_web` from the cockpit-web crate, not a standalone bin — a stub `main`
// keeps the bin target compiling (inert) there.
#![cfg_attr(target_arch = "wasm32", allow(unused))]

#[cfg(target_arch = "wasm32")]
fn main() {}

#[cfg(not(target_arch = "wasm32"))]
use deos_terminal::view::TerminalView;
#[cfg(not(target_arch = "wasm32"))]
use gpui::{
    px, size, App, AppContext, Bounds, Focusable, TitlebarOptions, WindowBounds, WindowOptions,
};

#[cfg(not(target_arch = "wasm32"))]
fn main() {
    // The windowing platform (metal/wgpu) is provided by `gpui_platform`, which
    // builds the concrete `Application` — the same entry starbridge-v2 uses.
    gpui_platform::application().run(|cx: &mut App| {
        let bounds = Bounds::centered(None, size(px(900.), px(560.)), cx);
        let window = cx
            .open_window(
                WindowOptions {
                    window_bounds: Some(WindowBounds::Windowed(bounds)),
                    titlebar: Some(TitlebarOptions {
                        title: Some("deos-terminal — a real shell in gpui".into()),
                        ..Default::default()
                    }),
                    ..Default::default()
                },
                |window, cx| {
                    let view = cx.new(|cx| {
                        TerminalView::spawn_shell(cx).expect("failed to spawn shell")
                    });
                    // Focus the terminal so keystrokes flow to the PTY immediately.
                    let handle = view.read(cx).focus_handle(cx);
                    window.focus(&handle, cx);
                    view
                },
            )
            .expect("failed to open window");

        // Close the app when the window closes.
        window
            .update(cx, |_view, _window, _cx| {})
            .ok();
        cx.activate(true);
    });
}
