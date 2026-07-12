//! **The deos-`ViewNode` → WeChat message text renderer.** An offering's [`Surface`] is a deos
//! affordance view-tree; a WeChat Official Account text message is one plain-text blob (WeChat OA
//! forbids arbitrary per-message buttons — see the crate doc). This projects the tree onto the
//! *prose* half (room text, party state, verified-turn count, section titles); the *affordance* half
//! (the [`deos_view::ViewNode::Menu`] rows / the passed [`Action`]s) is appended by
//! [`crate::api::build_present_request`] as a NUMBERED REPLY LIST, NOT a keyboard — the WeChat-native
//! way to offer dynamic choices (the user replies with the number).
//!
//! ## Routed through the shared deos-view walk (no bespoke subset walker)
//! The prose projection is the ONE deos-view [`ViewNode`]→text walk ([`deos_view::render_text`], the
//! primitive the [`deos_view::TelegramBackend`] exposes), NOT a WeChat-private walker. That shared
//! walk omits [`deos_view::ViewNode::Menu`]/`Button` (they ride as the numbered reply list here, the
//! inline keyboard on Telegram) and heads section blocks with their titles — the SAME prose shape
//! this crate produced before, now with FULL node coverage (`Grid`/`Tabs`/`Host`/`Adept` recurse
//! rather than being dropped, which the old WeChat `child_slice` subset walker did). WeChat renders
//! VIA the shared text-walk primitive; only the affordance ENCODING (position→number, in
//! [`crate::api`]) stays WeChat-specific.
//!
//! HONEST SCOPE — WHERE A `WeChatBackend` WOULD LIVE: a dedicated `WeChatBackend:
//! deos_view::SurfaceBackend` is a follow-up in deos-view, not this crate. [`SurfaceBackend`] pairs a
//! text `render` with a `decode` through the ONE affordance codec keyed by an
//! [`deos_view::AffordanceTransport`] — but that enum has only `Discord`/`Telegram`/`Web`, and
//! WeChat's affordance is a NUMBERED REPLY (position→number, [`crate::api::parse_reply_index`]), not
//! an id the codec mints. So a real `WeChatBackend` needs a new `AffordanceTransport::WeChat` variant
//! (a deos-view edit, out of this lane's scope). Until then WeChat reuses the shared `render_text`
//! text-walk primitive directly (its RENDER half is transport-independent prose), and keeps the
//! numbered codec WeChat-local — no duplicate walker, no deos-view edit.

use deos_view::render_text;
use dreggnet_offerings::Surface;

/// Render a [`Surface`] into WeChat message text (the *non-affordance* half of the surface).
/// [`deos_view::ViewNode::Menu`]/`Button` are OMITTED here — they are rendered as the numbered reply
/// list in [`crate::api::build_present_request`], not inline in the prose. Section titles head their
/// blocks; text nodes are lines.
///
/// Renders through the shared deos-view text walk ([`deos_view::render_text`] — the primitive the
/// [`deos_view::TelegramBackend`] exposes, full node coverage); this crate no longer maintains its
/// own subset walker.
pub fn render_surface_text(surface: &Surface) -> String {
    render_text(surface.view())
}
