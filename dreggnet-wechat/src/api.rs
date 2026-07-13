//! **The PURE WeChat API layer** — request-building with NO transport, NO access-token, NO
//! network. Mirrors the telegram frontend's pure/live split ([`build_present_request`] separate
//! from a [`crate::transport::Transport`]): it turns an already-rendered [`WeChatMessage`] into a
//! [`CustomSendRequest`] whose serde encoding IS the real WeChat `cgi-bin/message/custom/send` JSON
//! wire body. A test that asserts the request shape asserts the wire shape; a
//! [`crate::transport::Transport`] is the only thing that ever touches the network.
//!
//! ## Render + affordance-encoding = the SHARED backend (no crate-local codec)
//! A WeChat Official Account forbids arbitrary per-message buttons, so an offering's affordances
//! ride as a **numbered reply list appended to the message text** and the user **replies with the
//! number**. That WHOLE projection — the prose (the shared `ViewNode`→text walk) plus the numbered
//! block (the whole gated tree's actuations in walk order, a `!enabled` one shown LOCKED, keeping
//! its number) — is [`deos_view::WeChatBackend::render`]. [`present_message`] renders a [`Surface`]
//! through it; the returned [`WeChatMessage`] carries the options table an inbound reply is
//! [`resolve`](deos_view::WeChatMessage::resolve)d against (a reply number, or the `#<turn>:<arg>`
//! marked id a Mini-Program button posts back). This crate no longer carries a numbered-reply codec
//! — the render + affordance-encoding is the ONE deos-view home for that shape.
//!
//! What stays here is genuinely WeChat-specific: the `custom/send` wire body ([`CustomSendRequest`])
//! and the RICH Mini-Program card payload.
//!
//! ## The RICH alternative — a Mini-Program card
//! For a Mini-Program surface (which CAN render real buttons in WXML), [`build_miniprogram_card`]
//! produces a [`MiniProgramCard`] payload: one [`MiniProgramButton`] per affordance carrying its
//! `{turn, arg, enabled}`. This is the heavier path (MP review + custom WXML); the OA numbered-reply
//! is the CANONICAL surface (lightest, OA-native). Both map the SAME affordances — no reinvention.

use deos_view::{SurfaceBackend, WeChatBackend, WeChatMessage};
use dreggnet_offerings::{Action, Surface};
use serde::{Deserialize, Serialize};

use crate::render::render_surface_text;

/// The `msgtype` of an OA text message — the only message type the numbered-reply loop uses
/// (both the outbound [`CustomSendRequest`] and the inbound reply are `"text"`).
pub const MSG_TYPE_TEXT: &str = "text";

/// **Render `surface` into the WeChat OA message** — prose + the numbered reply list — through the
/// SHARED [`deos_view::WeChatBackend`]. The affordances are the whole gated view-tree's actuations
/// (full node coverage — every container recurses), numbered 1-based in walk order; a `!enabled`
/// one is shown LOCKED (keeps its number, the cap tooth shown not hidden). The returned
/// [`WeChatMessage`] carries the options table a later reply is
/// [`resolve`](deos_view::WeChatMessage::resolve)d against — this replaces the crate-local
/// numbered-reply codec entirely.
pub fn present_message(surface: &Surface) -> WeChatMessage {
    WeChatBackend.render(surface.view(), &[])
}

/// The **text payload** of an OA message — `{ "content": "…" }` (the WeChat `text` object).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TextPayload {
    /// The full message body: the rendered surface prose + the numbered affordance block.
    pub content: String,
}

/// A **Customer Service `custom/send` request** — the WeChat `cgi-bin/message/custom/send` body,
/// verbatim. Its serde encoding is exactly the JSON wire body a live OA POSTs to
/// `https://api.weixin.qq.com/cgi-bin/message/custom/send?access_token=<TOKEN>` (a test asserting
/// this struct's shape asserts the real wire shape). Built purely by [`build_present_request`];
/// sent by a [`crate::transport::Transport`]. This is an ACTIVE push (matching the `Frontend`
/// trait's `present`); WeChat also allows a token-free PASSIVE REPLY in the webhook HTTP response,
/// but the active push is the general shape the orchestrator drives (honest scope: it needs a token).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CustomSendRequest {
    /// The target user — the recipient's WeChat OpenID (per-OA opaque handle).
    pub touser: String,
    /// The message type — always [`MSG_TYPE_TEXT`] for the numbered-reply loop.
    pub msgtype: String,
    /// The text body (surface prose + numbered affordance block).
    pub text: TextPayload,
}

/// **Build the `custom/send` request carrying an already-rendered [`WeChatMessage`] body to
/// `openid`** — the WeChat wire-body seam (genuinely WeChat-specific). Render the surface with
/// [`present_message`] (the shared [`deos_view::WeChatBackend`]) first, then wrap its
/// [`content`](WeChatMessage::content) — the prose + numbered reply list — into the
/// `cgi-bin/message/custom/send` body. Kept separate from the render so `present` can also retain
/// the message's options table for a later reply [`resolve`](deos_view::WeChatMessage::resolve).
pub fn build_present_request(openid: &str, message: &WeChatMessage) -> CustomSendRequest {
    CustomSendRequest {
        touser: openid.to_string(),
        msgtype: MSG_TYPE_TEXT.to_string(),
        text: TextPayload {
            content: message.content.clone(),
        },
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The RICH alternative — a Mini-Program card payload (real buttons in WXML).
// ─────────────────────────────────────────────────────────────────────────────

/// One **Mini-Program card button** — a real tappable affordance in a Mini-Program's WXML (which,
/// unlike the OA, CAN render arbitrary buttons). Carries the affordance `{turn, arg}` a tap fires
/// back to the MP backend, and `enabled` (a `!enabled` button renders dimmed but still fires — the
/// executor is the sole referee).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MiniProgramButton {
    /// The button label (the affordance's human text).
    pub label: String,
    /// The affordance verb (the dungeon's `"choose"`).
    pub turn: String,
    /// The affordance argument (the scene choice index).
    pub arg: i64,
    /// Whether the affordance is currently eligible (a decoration; the executor still refuses an
    /// ineligible move on `advance`).
    pub enabled: bool,
}

/// A **Mini-Program card** payload — the RICH surface alternative to the OA numbered reply. The MP
/// renders `body` as text and `buttons` as real WXML buttons (each tap fires its `{turn, arg}` back
/// to the MP backend, which resolves it on the core exactly like a numbered reply). This is the
/// heavier path (Mini-Program review + custom WXML); the OA numbered-reply is canonical.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MiniProgramCard {
    /// The card body text (the rendered surface prose).
    pub body: String,
    /// One button per cap-gated affordance (the ballot options).
    pub buttons: Vec<MiniProgramButton>,
}

/// **Build the Mini-Program card payload** presenting `surface` + `actions` — the pure
/// Surface→(text + real buttons) mapping for the rich MP surface. One [`MiniProgramButton`] per
/// affordance, carrying its `{turn, arg, enabled}`. Same affordances as the OA numbered list.
pub fn build_miniprogram_card(surface: &Surface, actions: &[Action]) -> MiniProgramCard {
    MiniProgramCard {
        body: render_surface_text(surface),
        buttons: actions
            .iter()
            .map(|a| MiniProgramButton {
                label: a.label.clone(),
                turn: a.turn.clone(),
                arg: a.arg,
                enabled: a.enabled,
            })
            .collect(),
    }
}
