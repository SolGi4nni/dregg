//! **The deos-`ViewNode` → WeChat *prose* renderer** — the PROSE-ONLY projection, kept for the RICH
//! Mini-Program card body. An offering's [`Surface`] is a deos affordance view-tree; this walks it
//! into the plain-text prose half (room text, party state, verified-turn count, section titles),
//! WITHOUT any affordance block.
//!
//! ## The OA numbered-reply surface adopts the shared `WeChatBackend`
//! The CANONICAL OA surface — prose + the numbered reply list, and the codec that resolves a reply —
//! is now [`deos_view::WeChatBackend`] (via [`crate::api::present_message`] /
//! [`crate::WeChatFrontend`]), not this module. So `render_surface_text` is no longer on the OA
//! present path; it survives only for [`crate::api::build_miniprogram_card`], which wants the prose
//! WITHOUT the numbered block (the Mini-Program renders its own WXML buttons for the affordances).
//!
//! ## Routed through the shared deos-view walk (no bespoke subset walker)
//! The prose projection is the ONE deos-view [`ViewNode`]→text walk ([`deos_view::render_text`], the
//! primitive the [`deos_view::TelegramBackend`] exposes and the [`deos_view::WeChatBackend`]'s own
//! prose half reuses), NOT a WeChat-private walker. That shared walk omits
//! [`deos_view::ViewNode::Menu`]/`Button` (affordances ride the numbered reply list / the MP buttons,
//! not the prose) and heads section blocks with their titles, with FULL node coverage
//! (`Grid`/`Tabs`/`Host`/`Adept` recurse rather than being dropped).

use deos_view::render_text;
use dreggnet_offerings::Surface;

/// Render a [`Surface`] into WeChat prose text (the *non-affordance* half of the surface) — the body
/// of the RICH [`crate::api::build_miniprogram_card`] payload (which carries the affordances as its
/// own WXML buttons). [`deos_view::ViewNode::Menu`]/`Button` are OMITTED; section titles head their
/// blocks; text nodes are lines. The canonical OA numbered-reply surface renders through the shared
/// [`deos_view::WeChatBackend`] instead (see [`crate::api::present_message`]).
///
/// Renders through the shared deos-view text walk ([`deos_view::render_text`], full node coverage);
/// this crate no longer maintains its own subset walker.
pub fn render_surface_text(surface: &Surface) -> String {
    render_text(surface.view())
}
