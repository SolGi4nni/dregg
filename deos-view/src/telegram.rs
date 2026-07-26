//! **The Telegram text backend** — walk a [`ViewNode`] IR into Telegram message text.
//!
//! A Telegram message is plain text plus an inline keyboard. This is the *text* half: room prose,
//! party state, section titles. The affordance half (a [`ViewNode::Menu`]/[`ViewNode::Button`])
//! becomes the inline keyboard the frontend builds from the passed actions, NOT text — so those
//! nodes are omitted here.
//!
//! This is the moved-in `dreggnet-telegram::render::walk` (formerly a subset walker in the
//! frontend crate); the walk itself now lives in [`crate::text`] — the ONE prose projection the
//! WeChat OA backend shares (its numbered-reply message is the same prose + a numbered block), so
//! a second chat transport never forks a second walker. [`render_text`] IS `crate::text::render_text`.

use crate::affordance::AffordanceTransport;
use crate::backend::SurfaceBackend;
use crate::tree::ViewNode;

/// **Render a [`ViewNode`] surface into Telegram message text** (the *non-affordance* half) — the
/// shared [`crate::text::render_text`] walk. [`ViewNode::Menu`]/[`ViewNode::Button`] are OMITTED
/// (rendered as the inline keyboard, not text); section titles head their blocks; text nodes are
/// lines. Trailing whitespace is trimmed.
pub use crate::text::render_text;

/// **Render a surface for a `parse_mode: HTML` Telegram message** — the SAME
/// [`crate::text`] walk as [`render_text`], with the board fenced in `<pre>` (Telegram's monospace
/// guarantee, without which the fixed-width grid is laid out in a PROPORTIONAL font and its rows do
/// not line up into columns) and every content run HTML-escaped.
///
/// ⚑ A message rendered with this MUST be sent with `parse_mode` set, and a message sent with
/// `parse_mode` set MUST be rendered with this: the two halves are one decision. The plain
/// [`render_text`] output contains raw `<`/`&` from any surface that happens to use them, which a
/// live parse mode would either mis-render or reject outright.
pub fn render_html(tree: &ViewNode) -> String {
    crate::text::render_text_styled(tree, &crate::text::ChatTextStyle::telegram_html())
}

/// **The Telegram [`SurfaceBackend`]** — the [`ViewNode`] IR → message text ([`render_text`]).
/// Binds are unused (Telegram text has no in-place live re-read); [`decode`](SurfaceBackend::decode)
/// uses the Telegram affordance codec (`<turn>:<arg>` `callback_data`).
///
/// PLAIN text on purpose: this is the backend every cross-surface parity harness reads, and the
/// prose it compares is the surface's WORDS. The wire form the live bot sends is
/// [`render_html`] — the same walk, escaped and fenced (see [`crate::text::ChatTextStyle`]).
pub struct TelegramBackend;

impl SurfaceBackend for TelegramBackend {
    type Rendered = String;

    fn transport(&self) -> AffordanceTransport {
        AffordanceTransport::Telegram
    }

    fn render(&self, tree: &ViewNode, _binds: &[u64]) -> String {
        render_text(tree)
    }
}
