//! # `dreggnet-wechat` — the FOURTH frontend for DreggNet Cloud (after Discord #0, Telegram, web).
//!
//! A [`WeChatFrontend`] implementing the frontend-agnostic [`dreggnet_offerings::Frontend`] trait
//! over the committed `dreggnet-offerings` core, so a **WeChat user plays the SAME
//! [`DungeonOffering`](dreggnet_offerings::dungeon::DungeonOffering) on the SAME real dregg
//! substrate** as the Discord bot — the same cap-gated affordances, the same real verifiable
//! [`TurnReceipt`](dregg_app_framework::TurnReceipt)s, the same executor-is-sole-referee anti-ghost
//! tooth. Only the SURFACE differs. This proves the core is frontend-agnostic.
//!
//! ## The WeChat surface model — Official Account numbered replies (canonical)
//! WeChat is the heaviest platform, and an Official Account **forbids arbitrary per-message
//! buttons**: its persistent menu is static (configured once, ≤3×5, not per-turn), and a template
//! message is a fixed-format notification. So dynamic, per-turn cap-gated affordances cannot be
//! buttons. The cleanest OA-native surface is a **numbered reply list**: the room + its affordances
//! are one text message with a `1.`-indexed list, and the user **replies with the number** to pick
//! a move (the reply arrives as an inbound text message — [`WeChatMessage`]). This is the lightest
//! path (a subscription/service OA, no Mini-Program review). A [`api::MiniProgramCard`] payload is
//! provided for the RICH surface (real buttons in a Mini-Program's WXML), but the OA numbered-reply
//! is CANONICAL. Both map the SAME offering affordances — no reinvention.
//!
//! ## The three mappings (a `Frontend` is an affordance-renderer)
//! - **identity(openid) → a derived dregg identity.** A WeChat OpenID → a BLAKE3-derived 32-byte
//!   seed → a REAL `AgentCipherclerk` Ed25519 identity, hex-encoded into a [`DreggIdentity`]. Same
//!   primitive as telegram/discord, a WeChat-scoped domain ([`cipherclerk`]) so id-spaces never
//!   collide.
//! - **present(Surface) → an OA text message.** The offering's deos [`Surface`] view-tree is
//!   rendered by the SHARED [`deos_view::WeChatBackend`] ([`api::present_message`]) into prose + a
//!   numbered reply list over the whole gated tree's actuations (full node coverage); the body is
//!   wrapped into the `custom/send` wire request ([`api::build_present_request`]) and sent through
//!   an INJECTED [`transport::Transport`] — the whole thing drives with [`transport::MockTransport`]
//!   (no token, no network). The rendered [`deos_view::WeChatMessage`] (its options table) is kept
//!   per session for the reply.
//! - **collect(inbound message) → (SessionId, Action, DreggIdentity).** A user's reply is resolved
//!   against the presented [`deos_view::WeChatMessage`] ([`deos_view::WeChatMessage::resolve`] — a
//!   reply number or a `#<turn>:<arg>` marked id), reconstructed into the typed [`Action`], and the
//!   firing user's derived identity attributes the move.
//!
//! ## Session shape: per-OpenID, single-player
//! A WeChat OA conversation is **1:1** — there is no group-chat affordance surface (unlike Telegram
//! groups / forum topics). So each session is keyed by the user's OpenID ([`WeChatFrontend::session_id`]
//! → `wx:<openid>`) and is single-player. (A crowd-driven session would need a Mini-Program's own
//! multiplayer surface; that ballot/tally lives one layer up in the orchestrator, unchanged from the
//! other frontends — the core still resolves the single typed [`Action`] picked.)

pub mod api;
pub mod cipherclerk;
pub mod host;
pub mod render;
pub mod transport;

use std::collections::HashMap;

use deos_view::WeChatMessage as PresentedMessage;
use dreggnet_offerings::{Action, DreggIdentity, Frontend, SessionId, Surface};

use crate::api::{MSG_TYPE_TEXT, build_present_request, present_message};
use crate::cipherclerk::WeChatCipherclerk;
use crate::transport::{Transport, TransportError};

/// A WeChat **OpenID** — the per-Official-Account opaque user handle (a UTF-8 string). The identity
/// derivation hashes its raw bytes; the session id embeds it.
pub type OpenId = String;

/// A **synthetic WeChat inbound message** — what the OA webhook delivers when a user sends a text
/// (the fields we use). Stands in for the live update a live OA receives; the driven test mints one
/// directly (no network). [`WeChatFrontend::collect`] maps a numbered-reply text back to a typed
/// [`Action`] + the sender's derived identity.
#[derive(Debug, Clone)]
pub struct WeChatMessage {
    /// The sender's WeChat OpenID (the OA-webhook `FromUserName`) — mapped to a [`DreggIdentity`].
    pub from_openid: OpenId,
    /// The message type (the OA-webhook `MsgType`). The numbered-reply loop handles [`MSG_TYPE_TEXT`].
    pub msg_type: String,
    /// The message text (the OA-webhook `Content`) — the user's numbered reply (e.g. `"2"`).
    pub content: String,
}

impl WeChatMessage {
    /// A **text** message `content` from `openid` — the numbered-reply the loop expects.
    pub fn text(openid: impl Into<OpenId>, content: impl Into<String>) -> Self {
        WeChatMessage {
            from_openid: openid.into(),
            msg_type: MSG_TYPE_TEXT.to_string(),
            content: content.into(),
        }
    }
}

/// The live surface slot for one WeChat session — the OpenID it messages and the affordances
/// currently on offer (matched, by 1-based reply number, against an inbound [`WeChatMessage`] in
/// [`WeChatFrontend::collect`]).
#[derive(Debug, Clone)]
pub struct WeChatSession {
    /// The user (OpenID) hosting the 1:1 session.
    pub openid: OpenId,
    /// The last presented [`deos_view::WeChatMessage`] — the rendered body PLUS its numbered options
    /// table (from the shared [`deos_view::WeChatBackend`]). An inbound reply is
    /// [`resolve`](deos_view::WeChatMessage::resolve)d against this (a reply number naming one of the
    /// options, or a `#<turn>:<arg>` marked id); a reply that names nothing here is a move the
    /// frontend never offered, and [`collect`](WeChatFrontend::collect) returns `None`.
    pub presented: PresentedMessage,
}

/// **The WeChat frontend** — an affordance-renderer over the ONE offering core, generic over the
/// injected [`Transport`] `T` so it drives token- and network-free with [`transport::MockTransport`]
/// in a test and over a live [`transport::RawWeChatApi`] in production. It NEVER re-implements
/// offering logic: it derives identity, presents the surface as an OA text message + numbered reply
/// list, collects a reply into a typed [`Action`], and hands it to the core (which resolves it on
/// the substrate — the executor stays the sole referee).
pub struct WeChatFrontend<T: Transport> {
    /// The bot's master secret — the root of every user's deterministic derived identity.
    bot_secret: [u8; 32],
    /// The injected transport (mock in tests, `RawWeChatApi` in a deploy).
    transport: T,
    /// The live session slots, keyed by the [`SessionId`] derived from the OpenID.
    sessions: HashMap<SessionId, WeChatSession>,
    /// The last transport error a (infallible-signature) [`present`](Frontend::present) hit — so a
    /// caller using the trait method can still observe a send failure. Cleared on a successful send.
    last_send_error: Option<TransportError>,
}

impl<T: Transport> WeChatFrontend<T> {
    /// A frontend for `bot_secret`, sending through `transport`.
    pub fn new(bot_secret: [u8; 32], transport: T) -> Self {
        WeChatFrontend {
            bot_secret,
            transport,
            sessions: HashMap::new(),
            last_send_error: None,
        }
    }

    /// The [`SessionId`] naming the 1:1 session with `openid`. Canonical + reversible
    /// ([`Self::openid_of`]), so [`collect`](Frontend::collect) can reconstruct the session key from
    /// a raw inbound [`WeChatMessage`] with no side table.
    pub fn session_id(openid: &str) -> SessionId {
        SessionId::new(format!("wx:{openid}"))
    }

    /// Parse a [`SessionId`] minted by [`Self::session_id`] back into the OpenID. `None` for a
    /// session id this frontend did not mint.
    pub fn openid_of(session: &SessionId) -> Option<OpenId> {
        session.0.strip_prefix("wx:").map(|s| s.to_string())
    }

    /// The live session slot for `session`, if open.
    pub fn session(&self, session: &SessionId) -> Option<&WeChatSession> {
        self.sessions.get(session)
    }

    /// Borrow the injected transport (e.g. a test's [`transport::MockTransport`] to assert the sent
    /// requests).
    pub fn transport(&self) -> &T {
        &self.transport
    }

    /// The last send error a trait-`present` swallowed (its signature is infallible), if any.
    pub fn last_send_error(&self) -> Option<&TransportError> {
        self.last_send_error.as_ref()
    }

    /// Derive `openid`'s [`WeChatCipherclerk`] (the full handle — for a deploy that signs on the
    /// user's behalf; [`identity`](Frontend::identity) returns just the public [`DreggIdentity`]).
    pub fn cipherclerk(&self, openid: &str) -> WeChatCipherclerk {
        WeChatCipherclerk::derive(&self.bot_secret, openid)
    }

    /// **Present `surface` in `session`** — the fallible inherent form of
    /// [`present`](Frontend::present). Renders the surface through the SHARED
    /// [`deos_view::WeChatBackend`] ([`present_message`] — prose + the numbered reply list over the
    /// whole gated tree), wraps the body into the `custom/send` request ([`build_present_request`]),
    /// sends it through the transport, and records the rendered [`deos_view::WeChatMessage`] (its
    /// options table) so a later [`collect`](Frontend::collect) can resolve a reply. The `actions`
    /// slice is now advisory: the numbered list is derived from the surface tree itself (the tree's
    /// [`ViewNode::Menu`](deos_view::ViewNode)/`Button` actuations), full node coverage. Opens (or
    /// replaces) the session slot.
    pub fn present_result(
        &mut self,
        session: &SessionId,
        surface: &Surface,
        _actions: &[Action],
    ) -> Result<(), TransportError> {
        let openid = Self::openid_of(session)
            .ok_or_else(|| TransportError(format!("not a wechat session id: {}", session.0)))?;
        let message = present_message(surface);
        let req = build_present_request(&openid, &message);
        self.transport.send_message(&req)?;
        self.sessions.insert(
            session.clone(),
            WeChatSession {
                openid,
                presented: message,
            },
        );
        self.last_send_error = None;
        Ok(())
    }
}

impl<T: Transport> Frontend for WeChatFrontend<T> {
    type PlatformUser = OpenId;
    type PlatformEvent = WeChatMessage;

    /// Derive `user`'s frontend-agnostic [`DreggIdentity`] — the hex of a REAL Ed25519 key derived
    /// from the bot secret + the WeChat OpenID (the telegram/discord derivation mirror). The SAME
    /// OpenID always maps to the SAME dregg identity.
    fn identity(&self, user: OpenId) -> DreggIdentity {
        WeChatCipherclerk::derive(&self.bot_secret, &user).identity()
    }

    /// Open a surface slot for `session` (register the OpenID). A live OA has no separate "spin"
    /// call — a 1:1 conversation already exists — so this just registers the slot; the first
    /// [`present`](Frontend::present) sends the opening message.
    fn spin_session(&mut self, session: SessionId) {
        if let Some(openid) = Self::openid_of(&session) {
            self.sessions.entry(session).or_insert(WeChatSession {
                openid,
                // Nothing presented yet — an empty options table; the first `present` fills it.
                presented: PresentedMessage {
                    content: String::new(),
                    options: Vec::new(),
                },
            });
        }
    }

    /// Present the offering's [`Surface`] + [`Action`]s as a WeChat OA text message + numbered reply
    /// list (send it through the transport). Infallible per the trait; a transport error is recorded
    /// in [`last_send_error`](Self::last_send_error) (use [`present_result`](Self::present_result)
    /// for the fallible form).
    fn present(&mut self, session: &SessionId, surface: &Surface, actions: &[Action]) {
        if let Err(e) = self.present_result(session, surface, actions) {
            self.last_send_error = Some(e);
        }
    }

    /// Collect an inbound [`WeChatMessage`] (a numbered reply) into `(SessionId, Action,
    /// DreggIdentity)`: reconstruct the session from the sender's OpenID, [`resolve`] the reply
    /// against the presented [`deos_view::WeChatMessage`] (a reply number naming an option, or a
    /// `#<turn>:<arg>` marked id — the ONE shared codec), reconstruct the typed [`Action`] from the
    /// resolved option (its label + `enabled` cap-tooth bit), and attribute it to the sender's
    /// derived identity. `None` if the message is not a text, the session is unknown, or the reply
    /// resolves to nothing the frontend presented (ordinary prose, an out-of-range number, an id
    /// this transport never minted).
    ///
    /// [`resolve`]: deos_view::WeChatMessage::resolve
    fn collect(&self, ev: WeChatMessage) -> Option<(SessionId, Action, DreggIdentity)> {
        if ev.msg_type != MSG_TYPE_TEXT {
            return None;
        }
        let session = Self::session_id(&ev.from_openid);
        let slot = self.sessions.get(&session)?;
        // The shared codec: a reply number resolved against the presented list, or a marked id.
        let (turn, arg) = slot.presented.resolve(&ev.content)?;
        // Reconstruct the typed Action from the option (its label + the render-time `enabled` bit —
        // a locked cap-tooth resolves to enabled=false, and the executor stays the sole referee on
        // `advance`). A marked id for an affordance not in this list (a stale Mini-Program button)
        // still fires; the executor gates it.
        let action = slot
            .presented
            .options
            .iter()
            .find(|o| o.turn == turn && o.arg == arg)
            .map(|o| Action::new(o.label.clone(), o.turn.clone(), o.arg, o.enabled))
            .unwrap_or_else(|| Action::new(String::new(), turn, arg, true));
        let identity = self.identity(ev.from_openid);
        Some((session, action, identity))
    }

    /// Tear a session's surface down (drop the slot). A live OA would additionally send a closing
    /// text (the OA cannot retract a delivered message).
    fn teardown(&mut self, session: &SessionId) {
        self.sessions.remove(session);
    }
}
