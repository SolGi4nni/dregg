//! # `dreggnet-telegram` — the FIRST non-Discord frontend for DreggNet Cloud.
//!
//! A [`TelegramFrontend`] implementing the frontend-agnostic [`dreggnet_offerings::Frontend`]
//! trait over the committed `dreggnet-offerings` core, so a **Telegram user plays the SAME
//! [`DungeonOffering`](dreggnet_offerings::dungeon::DungeonOffering) on the SAME real dregg
//! substrate** as the Discord bot — the same cap-gated affordances, the same real verifiable
//! [`TurnReceipt`](dregg_app_framework::TurnReceipt)s, the same executor-is-sole-referee anti-ghost
//! tooth. Only the SURFACE differs: an inline keyboard instead of Discord buttons. This proves the
//! core is frontend-agnostic (the doc's claim, `docs/DREGGNET-CLOUD-OFFERINGS.md`).
//!
//! ## The three mappings (a `Frontend` is an affordance-renderer)
//! - **identity(telegram_user_id) → a derived dregg identity.** Mirrors the discord bot's
//!   `UserCipherclerk::derive`: a Telegram user id → a BLAKE3-derived 32-byte seed → a REAL
//!   `AgentCipherclerk` Ed25519 identity, hex-encoded into a [`DreggIdentity`]. Same primitive,
//!   Telegram-scoped domain ([`cipherclerk`]).
//! - **present(Surface) → a Telegram message + inline keyboard.** The offering's deos
//!   [`Surface`](dreggnet_offerings::Surface) view-tree is walked into message text; its cap-gated
//!   [`Action`](dreggnet_offerings::Action)s become inline-keyboard buttons whose `callback_data`
//!   carries `{turn, arg}` ([`api::build_present_request`]). Sent through an INJECTED
//!   [`transport::Transport`] — the whole thing drives with [`transport::MockTransport`] (no token,
//!   no network).
//! - **collect(callback_query) → (SessionId, Action, DreggIdentity).** A button press's
//!   `callback_data` is decoded back into the typed [`Action`] the core resolves on the substrate;
//!   the firing Telegram user's derived identity attributes the move.
//!
//! ## Session shape: a group chat = a collective, a DM = single-player
//! A Telegram **chat** hosts one session (a [`SessionId`] over the chat id; a supergroup **forum
//! topic** scopes a session under one topic thread). A DM (a positive chat id) is single-player; a
//! group/supergroup (a negative chat id) is a **collective** — many users press affordances on the
//! ONE session, exactly the ballot shape the dungeon's collective-choice layer resolves (the core
//! resolves the single typed [`Action`] a presser picked; the ballot/quorum lives one layer up in
//! the orchestrator, unchanged from Discord). This crate classifies the chat ([`ChatKind`]) and
//! attributes every press to its presser's derived identity; the collective tally is the
//! orchestrator's job, identical across frontends.

pub mod api;
pub mod cipherclerk;
pub mod host;
pub mod render;
pub mod reqwest_transport;
pub mod runtime;
pub mod seated;
pub mod transport;
pub mod webapp;

use std::collections::HashMap;

use dreggnet_offerings::{Action, DreggIdentity, Frontend, SessionId, Surface};

use crate::api::{
    InlineKeyboardButton, InlineKeyboardMarkup, SendMessageRequest, build_present_request,
    decode_callback,
};
use crate::cipherclerk::TelegramCipherclerk;
use crate::transport::{MessageId, Transport, TransportError};

/// A Telegram user id (the Bot API `from.id`) — always positive, ≤ 52 bits.
pub type TelegramUserId = u64;

/// A Telegram chat id (the Bot API `chat.id`) — **negative for groups/supergroups**, positive for
/// private chats (DMs). This sign is exactly how [`ChatKind`] tells a collective from single-player.
pub type ChatId = i64;

/// What kind of Telegram chat hosts a session — the single-player vs collective distinction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ChatKind {
    /// A private chat (positive chat id): **single-player**. One user drives the session.
    Dm,
    /// A group / supergroup (negative chat id): a **collective**. Many users press affordances on
    /// the one session (the dungeon's ballot shape; the tally is the orchestrator's job).
    Group,
    /// A supergroup **forum topic** (a `message_thread_id` under a group): a collective scoped to
    /// one topic thread — a topic-per-session, so several sessions coexist in one supergroup.
    ForumTopic,
}

impl ChatKind {
    /// Classify a chat from its id + optional forum-topic thread. A `message_thread_id` → a forum
    /// topic; a negative chat id → a group collective; otherwise a single-player DM.
    pub fn classify(chat_id: ChatId, message_thread_id: Option<i64>) -> ChatKind {
        if message_thread_id.is_some() {
            ChatKind::ForumTopic
        } else if chat_id < 0 {
            ChatKind::Group
        } else {
            ChatKind::Dm
        }
    }

    /// Whether this chat is a collective (many drivers → one session).
    pub fn is_collective(&self) -> bool {
        matches!(self, ChatKind::Group | ChatKind::ForumTopic)
    }
}

/// A **synthetic Telegram callback query** — a press of an inline-keyboard button (the Bot API
/// `CallbackQuery`, the fields we use). Stands in for the live update a bot receives; the driven
/// test mints one directly (no network). [`TelegramFrontend::collect`] maps it back to a typed
/// [`Action`] + the presser's derived identity.
#[derive(Debug, Clone)]
pub struct CallbackQuery {
    /// The chat the pressed message lives in (the session's chat).
    pub chat_id: ChatId,
    /// The forum-topic thread, if the session is a topic-per-session.
    pub message_thread_id: Option<i64>,
    /// The Telegram user who pressed the button (mapped to a [`DreggIdentity`] via the cclerk).
    pub from_user_id: TelegramUserId,
    /// The pressed button's `callback_data` — the [`api::encode_callback`]-encoded `{turn, arg}`.
    pub data: String,
}

impl CallbackQuery {
    /// A press of `data` in `chat_id` by `from_user_id` (no forum topic).
    pub fn press(chat_id: ChatId, from_user_id: TelegramUserId, data: impl Into<String>) -> Self {
        CallbackQuery {
            chat_id,
            message_thread_id: None,
            from_user_id,
            data: data.into(),
        }
    }

    /// A press within a forum topic thread.
    pub fn press_in_topic(
        chat_id: ChatId,
        message_thread_id: i64,
        from_user_id: TelegramUserId,
        data: impl Into<String>,
    ) -> Self {
        CallbackQuery {
            chat_id,
            message_thread_id: Some(message_thread_id),
            from_user_id,
            data: data.into(),
        }
    }
}

/// The live surface slot for one Telegram session — the chat it posts to, the last message it sent
/// (edited on re-present), the chat kind, and the affordances currently on offer (matched against
/// a [`CallbackQuery`] in [`TelegramFrontend::collect`]).
#[derive(Debug, Clone)]
pub struct TelegramSession {
    /// The chat hosting the session.
    pub chat_id: ChatId,
    /// The forum-topic thread, for a topic-per-session.
    pub message_thread_id: Option<i64>,
    /// Single-player vs collective.
    pub kind: ChatKind,
    /// The last message posted for this session (a re-present would EDIT it in place).
    pub message_id: Option<MessageId>,
    /// The affordances last presented — a press must match one of these (else the frontend never
    /// offered it, and [`collect`](TelegramFrontend::collect) returns `None`).
    pub presented: Vec<Action>,
}

/// **The Telegram frontend** — an affordance-renderer over the ONE offering core, generic over the
/// injected [`Transport`] `T` so it drives token- and network-free with [`transport::MockTransport`]
/// in a test and over a live `RawBotApi` in production. It NEVER re-implements offering logic: it
/// derives identity, presents the surface as a message + inline keyboard, collects a press into a
/// typed [`Action`], and hands it to the core (which resolves it on the substrate — the executor
/// stays the sole referee).
pub struct TelegramFrontend<T: Transport> {
    /// The bot's master secret — the root of every user's deterministic derived identity.
    bot_secret: [u8; 32],
    /// The injected transport (mock in tests, `RawBotApi` in a deploy).
    transport: T,
    /// The live session slots, keyed by the [`SessionId`] derived from the chat (+topic).
    sessions: HashMap<SessionId, TelegramSession>,
    /// The last transport error a (infallible-signature) [`present`](Frontend::present) hit — so a
    /// caller using the trait method can still observe a send failure. Cleared on a successful send.
    last_send_error: Option<TransportError>,
}

impl<T: Transport> TelegramFrontend<T> {
    /// A frontend for `bot_secret`, sending through `transport`.
    pub fn new(bot_secret: [u8; 32], transport: T) -> Self {
        TelegramFrontend {
            bot_secret,
            transport,
            sessions: HashMap::new(),
            last_send_error: None,
        }
    }

    /// The [`SessionId`] naming the session hosted in `chat_id` (optionally scoped to a forum
    /// topic). Canonical + reversible ([`Self::chat_of`]), so [`collect`](Frontend::collect) can
    /// reconstruct the session key from a raw [`CallbackQuery`] with no side table.
    pub fn session_id(chat_id: ChatId, message_thread_id: Option<i64>) -> SessionId {
        match message_thread_id {
            Some(t) => SessionId::new(format!("tg:{chat_id}:{t}")),
            None => SessionId::new(format!("tg:{chat_id}")),
        }
    }

    /// Parse a [`SessionId`] minted by [`Self::session_id`] back into `(chat_id, topic)`. `None`
    /// for a session id this frontend did not mint.
    pub fn chat_of(session: &SessionId) -> Option<(ChatId, Option<i64>)> {
        let rest = session.0.strip_prefix("tg:")?;
        let mut parts = rest.split(':');
        let chat_id: ChatId = parts.next()?.parse().ok()?;
        let topic = match parts.next() {
            Some(t) => Some(t.parse().ok()?),
            None => None,
        };
        Some((chat_id, topic))
    }

    /// The live session slot for `session`, if open.
    pub fn session(&self, session: &SessionId) -> Option<&TelegramSession> {
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

    /// Derive `user`'s [`TelegramCipherclerk`] (the full handle — for a deploy that signs on the
    /// user's behalf; [`identity`](Frontend::identity) returns just the public [`DreggIdentity`]).
    pub fn cipherclerk(&self, user: TelegramUserId) -> TelegramCipherclerk {
        TelegramCipherclerk::derive(&self.bot_secret, user)
    }

    /// **Present `surface` + `actions` in `session`, returning the sent message id** — the
    /// fallible inherent form of [`present`](Frontend::present). Builds the `sendMessage` request
    /// purely ([`build_present_request`]) and sends it through the transport, recording the
    /// affordances so a later [`collect`](Frontend::collect) can match a press. Opens the session
    /// slot on first present if not already spun.
    pub fn present_result(
        &mut self,
        session: &SessionId,
        surface: &Surface,
        actions: &[Action],
    ) -> Result<MessageId, TransportError> {
        self.present_result_with(session, surface, actions, &[])
    }

    /// [`present_result`](Self::present_result) plus **trailing launch rows**: each
    /// `extra_buttons` entry is appended as its own keyboard row AFTER the affordance rows.
    /// These are frontend-level launch controls (the Mini App [`crate::webapp::play_button`]) —
    /// NOT offering [`Action`]s: they are not recorded among the session's `presented`
    /// affordances, so [`collect`](Frontend::collect) never matches one and the executor is
    /// never reached through them (a `web_app` button produces no callback at all).
    pub fn present_result_with(
        &mut self,
        session: &SessionId,
        surface: &Surface,
        actions: &[Action],
        extra_buttons: &[InlineKeyboardButton],
    ) -> Result<MessageId, TransportError> {
        let (chat_id, topic) = Self::chat_of(session)
            .ok_or_else(|| TransportError(format!("not a telegram session id: {}", session.0)))?;
        let mut req = build_present_request(chat_id, topic, surface, actions);
        if !extra_buttons.is_empty() {
            let markup = req
                .reply_markup
                .get_or_insert_with(|| InlineKeyboardMarkup {
                    inline_keyboard: Vec::new(),
                });
            for b in extra_buttons {
                markup.inline_keyboard.push(vec![b.clone()]);
            }
        }
        let req = req;
        // A RE-present EDITS the session's existing message in place (`editMessageText`) instead
        // of spamming a new one; the first present sends. A transport that cannot edit falls back
        // to sending (the [`Transport::edit_message`] default), so `MockTransport`-driven behavior
        // is unchanged: every present is still recorded as a sent request.
        let prior = self.sessions.get(session).and_then(|s| s.message_id);
        let message_id = match prior {
            Some(mid) => self.transport.edit_message(mid, &req)?,
            None => self.transport.send_message(&req)?,
        };
        let slot = self
            .sessions
            .entry(session.clone())
            .or_insert_with(|| TelegramSession {
                chat_id,
                message_thread_id: topic,
                kind: ChatKind::classify(chat_id, topic),
                message_id: None,
                presented: Vec::new(),
            });
        slot.message_id = Some(message_id);
        slot.presented = actions.to_vec();
        self.last_send_error = None;
        Ok(message_id)
    }

    /// The infallible form of [`present_result_with`](Self::present_result_with) — mirrors the
    /// trait [`present`](Frontend::present): a transport error is recorded in
    /// [`last_send_error`](Self::last_send_error) instead of returned.
    pub fn present_with(
        &mut self,
        session: &SessionId,
        surface: &Surface,
        actions: &[Action],
        extra_buttons: &[InlineKeyboardButton],
    ) {
        if let Err(e) = self.present_result_with(session, surface, actions, extra_buttons) {
            self.last_send_error = Some(e);
        }
    }

    /// Send a **control message** through the injected transport, bypassing the session-slot
    /// bookkeeping — for messages that are not a session's presented surface (the `/play` Mini
    /// App launch menu, whose `web_app` buttons produce no callbacks to match).
    pub fn send_raw(&mut self, req: &SendMessageRequest) -> Result<MessageId, TransportError> {
        self.transport.send_message(req)
    }
}

impl<T: Transport> Frontend for TelegramFrontend<T> {
    type PlatformUser = TelegramUserId;
    type PlatformEvent = CallbackQuery;

    /// Derive `user`'s frontend-agnostic [`DreggIdentity`] — the hex of a REAL Ed25519 key derived
    /// from the bot secret + the Telegram user id (the discord `UserCipherclerk::derive` mirror).
    /// Deterministic: the SAME Telegram user always maps to the SAME dregg identity.
    fn identity(&self, user: TelegramUserId) -> DreggIdentity {
        TelegramCipherclerk::derive(&self.bot_secret, user).identity()
    }

    /// Open a surface slot for `session` (record the chat + its [`ChatKind`]). A live bot has no
    /// separate "spin" call — a Telegram chat already exists — so this just registers the slot; the
    /// first [`present`](Frontend::present) sends the opening message.
    fn spin_session(&mut self, session: SessionId) {
        if let Some((chat_id, topic)) = Self::chat_of(&session) {
            self.sessions.entry(session).or_insert(TelegramSession {
                chat_id,
                message_thread_id: topic,
                kind: ChatKind::classify(chat_id, topic),
                message_id: None,
                presented: Vec::new(),
            });
        }
    }

    /// Present the offering's [`Surface`] + [`Action`]s as a Telegram message + inline keyboard
    /// (send it through the transport). Infallible per the trait; a transport error is recorded in
    /// [`last_send_error`](Self::last_send_error) (use [`present_result`](Self::present_result) for
    /// the fallible form).
    fn present(&mut self, session: &SessionId, surface: &Surface, actions: &[Action]) {
        if let Err(e) = self.present_result(session, surface, actions) {
            self.last_send_error = Some(e);
        }
    }

    /// Collect a [`CallbackQuery`] (a button press) into `(SessionId, Action, DreggIdentity)`:
    /// reconstruct the session from the press's chat (+topic), decode its `callback_data` into
    /// `{turn, arg}`, match it against the affordances currently presented for that session, and
    /// attribute it to the presser's derived identity. `None` if the session is unknown, the data
    /// is malformed, or the affordance was never presented (an event the frontend did not offer).
    fn collect(&self, ev: CallbackQuery) -> Option<(SessionId, Action, DreggIdentity)> {
        let session = Self::session_id(ev.chat_id, ev.message_thread_id);
        let slot = self.sessions.get(&session)?;
        let (turn, arg) = decode_callback(&ev.data)?;
        let action = slot
            .presented
            .iter()
            .find(|a| a.turn == turn && a.arg == arg)
            .cloned()?;
        let identity = self.identity(ev.from_user_id);
        Some((session, action, identity))
    }

    /// Tear a session's surface down (drop the slot). A live bot would additionally
    /// `editMessageReplyMarkup` to strip the keyboard from the archived message.
    fn teardown(&mut self, session: &SessionId) {
        self.sessions.remove(session);
    }
}
