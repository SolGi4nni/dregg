//! **The deos-`ViewNode` → Telegram message text renderer.** An offering's [`Surface`] is a
//! deos affordance view-tree; a Telegram message is plain text plus an inline keyboard. This walks
//! the tree into the *text* half (room prose, party state, verified-turn count, section titles);
//! the *affordance* half (the [`deos_view::ViewNode::Menu`] rows / the passed [`Action`]s) becomes
//! the inline keyboard in [`crate::api::build_present_request`], NOT text — so the same surface
//! that paints Discord buttons paints a Telegram keyboard, no reinvention.

use deos_view::{SurfaceBackend, TelegramBackend};
use dreggnet_offerings::Surface;

/// Render a [`Surface`] into Telegram message text (the *non-affordance* half of the surface).
/// [`deos_view::ViewNode::Menu`]/`Button` are OMITTED — they are rendered as the inline keyboard,
/// not as text. Section titles head their blocks; text nodes are lines.
///
/// Renders through the deos-view [`TelegramBackend`] (the moved-in walker — full node coverage);
/// this crate no longer maintains its own subset walker.
///
/// ⚑ This is the PLAIN reading of the surface — the prose, as words. What the live bot puts on the
/// wire is [`render_surface_html`]; see its note for why the two exist.
pub fn render_surface_text(surface: &Surface) -> String {
    TelegramBackend.render(surface.view(), &[])
}

/// **Render a [`Surface`] for the wire** — the SAME walk as [`render_surface_text`], HTML-escaped
/// with the board fenced in `<pre>`, to be sent with
/// [`parse_mode`](crate::api::SendMessageRequest::parse_mode) set to
/// [`TELEGRAM_PARSE_MODE`](crate::api::TELEGRAM_PARSE_MODE).
///
/// ⚑ **WHY THIS IS NOT COSMETIC.** A `sendMessage` with no `parse_mode` is rendered by every
/// Telegram client in a PROPORTIONAL font. [`deos_view::coordgrid_text`] builds a board out of
/// fixed-3-character cells whose only claim to being a grid is that every cell occupies the same
/// number of characters — which is a grid in a monospace font and a ragged pile in a proportional
/// one. Every board this bot has ever sent was misaligned for that reason alone.
///
/// ⚑ **AND WHY THE ESCAPE TRAVELS WITH IT.** `parse_mode` is per-MESSAGE, not per-span: the moment
/// the board is fenced, every other line of the message — section titles, prose, identities, a
/// game's own copy — is text Telegram's HTML parser reads, and one raw `<` in any of them is a
/// `can't parse entities` refusal for the WHOLE message. So the fence and the escape are one
/// decision, made once, inside the shared walk ([`deos_view::ChatTextStyle`]) where no caller can
/// take half of it. HTML is the parse mode rather than MarkdownV2 because its escape surface is
/// three characters (`&`, `<`, `>`) instead of eighteen.
pub fn render_surface_html(surface: &Surface) -> String {
    // By module path, not the crate root: `deos_view::render_html` is the WEB backend's HTML/DOM
    // document renderer, a different renderer for a different channel.
    deos_view::telegram::render_html(surface.view())
}
