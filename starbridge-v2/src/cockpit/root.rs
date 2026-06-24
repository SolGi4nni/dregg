//! THE WINDOW ROOT WELD — wrap a cockpit-bearing view in a gpui-component
//! [`Root`](gpui_component::Root) so its surfaces' kit INPUTS paint without
//! crashing.
//!
//! THE CRASH THIS FIXES: gpui-component's `TextElement::paint` (every kit text
//! INPUT — the web-shell URL bar, the composer/editor/agent prompts, …) reads
//! the window's `gpui_component::Root` global (`Root::read(window)`), which
//! `unwrap`s the window's first layer as a `Root`. If the window root view is NOT
//! a `Root` (it was the bare `Cockpit` / `SessionShell` / login surface), that
//! `unwrap` hits `None` and the process ABORTS the instant such an input paints.
//!
//! The fix is window-level (it belongs to the frame): the window's ROOT VIEW must
//! be a `Root` wrapping the chrome+content. [`wrap_root`] is the single weld every
//! cockpit-bearing `open_window` / `replace_root` builder calls, so every surface's
//! inputs paint clean. The `Root` also gives the frame its notification / tooltip /
//! dialog layers for free.

use gpui::{AnyView, Context, Window};
use gpui_component::Root;

/// Wrap `view` as the content of a fresh [`Root`], returning the `Root` to
/// install as the window's root view. The single window-root weld for the
/// coherent frame (`docs/deos/COCKPIT-UX.md`): the top bar + rail + main pane +
/// dock all live inside this one `Root`, so every kit text input paints without
/// the `Root::read(window).unwrap()` abort that crashed the cockpit. Call from a
/// `replace_root` / `open_window` builder (its `cx` is `Context<Root>`):
///
/// ```ignore
/// window.replace_root(cx, |window, cx| {
///     let inner = cx.new(|cx| SessionShell { .. });
///     crate::cockpit::root::wrap_root(inner, window, cx)
/// });
/// ```
pub fn wrap_root(view: impl Into<AnyView>, window: &mut Window, cx: &mut Context<Root>) -> Root {
    Root::new(view.into(), window, cx)
}
