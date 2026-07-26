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
//! A Telegram **chat** hosts a session per offering — the chat-scoped [`SessionId`] names it on the
//! host ([`TelegramFrontend::session_id`]; a supergroup **forum topic** scopes it under one topic
//! thread), while its Telegram-side SURFACE is one message per `(chat, offering)`
//! ([`TelegramFrontend::surface_id`]), so several offerings coexist in a chat and a press routes by
//! the message it was pressed on. A DM (a positive chat id) is single-player; a
//! group/supergroup (a negative chat id) is a **collective** — many users press affordances on the
//! ONE session, exactly the ballot shape the dungeon's collective-choice layer resolves (the core
//! resolves the single typed [`Action`] a presser picked; the ballot/quorum lives one layer up in
//! the orchestrator, unchanged from Discord). This crate classifies the chat ([`ChatKind`]) and
//! attributes every press to its presser's derived identity; the collective tally is the
//! orchestrator's job, identical across frontends.
//!
//! ## A shared surface never carries a private projection
//! A group's surface is ONE message every member reads, and a re-present EDITS it in place — so
//! the per-viewer projection ([`dreggnet_offerings::Offering::render_for`]: a card hand, a sealed
//! move) is served only in a DM. A collective chat is always served the viewer-blind
//! [`dreggnet_offerings::Offering::render`], and an offering that DECLARES hidden information
//! ([`dreggnet_offerings::Offering::hidden_information`]) is not hosted in one at all — it is
//! refused at open with a legible redirect (`host::OpenError::HiddenInSharedChat`).

pub mod api;
pub mod audit;
/// Viewer-blind Telegram consent and public receipt provenance for explicit Chutes turns.
pub mod chutes_consent;
pub mod cipherclerk;
pub mod commands;
pub mod host;
pub mod render;
pub mod reqwest_transport;
pub mod runtime;
pub mod seated;
pub mod transport;
pub mod verify_control;
pub mod webapp;

use std::collections::HashMap;

use dreggnet_offerings::{Action, DreggIdentity, Frontend, SessionId, Surface};

use crate::api::{
    InlineKeyboardButton, InlineKeyboardMarkup, SendMessageRequest, TELEGRAM_TEXT_LIMIT,
    build_present_request_with_callback_data, decode_callback,
};
use crate::cipherclerk::TelegramCipherclerk;
use crate::transport::{MessageId, Transport, TransportError};

/// The separator between a chat-scoped session id and the OFFERING whose surface is meant — the
/// `#tug` in `tg:-700#tug` (see [`TelegramFrontend::surface_id`]). Chosen because a chat id is
/// `-?[0-9]+` and a topic is `[0-9]+`, so `#` can never appear in the chat part: parsing back is
/// unambiguous ([`TelegramFrontend::chat_of`] / [`TelegramFrontend::offering_of`]).
pub const SURFACE_SEP: char = '#';

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
    /// **WHICH message the pressed button belongs to** (the Bot API `callback_query.message.
    /// message_id`) — the field that says which of a chat's several live surfaces the press
    /// addresses. With more than one offering open in a chat, each has its own message + its own
    /// keyboard, and only this distinguishes them; `None` (a synthesized press — a `/act` command,
    /// a Mini App round-trip, a test) falls back to the chat's most recent surface.
    pub message_id: Option<i64>,
    /// The Telegram user who pressed the button (mapped to a [`DreggIdentity`] via the cclerk).
    pub from_user_id: TelegramUserId,
    /// The pressed button's `callback_data` — the [`api::encode_callback`]-encoded `{turn, arg}`.
    pub data: String,
}

impl CallbackQuery {
    /// A press of `data` in `chat_id` by `from_user_id` (no forum topic, no message address — it
    /// routes to the chat's most recent surface).
    pub fn press(chat_id: ChatId, from_user_id: TelegramUserId, data: impl Into<String>) -> Self {
        CallbackQuery {
            chat_id,
            message_thread_id: None,
            message_id: None,
            from_user_id,
            data: data.into(),
        }
    }

    /// A press of a button **on a specific message** — the live-bot shape, and the only way to
    /// address one of several offerings open in the same chat.
    pub fn press_on_message(
        chat_id: ChatId,
        message_id: MessageId,
        from_user_id: TelegramUserId,
        data: impl Into<String>,
    ) -> Self {
        CallbackQuery {
            chat_id,
            message_thread_id: None,
            message_id: Some(message_id.0),
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
            message_id: None,
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
    /// The live SURFACE slots — one per live message, keyed by the surface id
    /// ([`TelegramFrontend::surface_id`]: the chat, plus the offering whose message it is). A chat
    /// can hold several at once; a bare chat-scoped id ([`TelegramFrontend::session_id`]) is the
    /// chat's own single surface, as a lone frontend (no host, one offering) uses it.
    sessions: HashMap<SessionId, TelegramSession>,
    /// **(chat, topic, message id) → the surface it belongs to** — how a press on a specific
    /// message routes to the right offering when several are open in one chat. Keyed by the FULL
    /// chat-scoped address, never the bare `message_id`: a Telegram `message_id` is unique only
    /// WITHIN a chat, so two different chats routinely mint the same id (chat B's message 2 would
    /// otherwise overwrite chat A's, and A's press would then resolve B's offering — a dead
    /// button / cross-chat misroute). The chat context comes straight off the [`CallbackQuery`].
    by_message: HashMap<(ChatId, Option<i64>, i64), SessionId>,
    /// **chat-scoped id → that chat's MOST RECENTLY presented surface.** The fallback for a press
    /// that names no message (a `/act` command, a Mini App round-trip), and what keeps the
    /// single-offering UX ("the chat's surface") meaningful now that a chat may host several.
    latest: HashMap<SessionId, SessionId>,
    /// Stable, non-interactive companion messages keyed by `(surface, slot)`. They are deliberately
    /// absent from `by_message` and `latest`: a proof guide can never become an action-routing
    /// surface, even while it is edited in place beside one.
    companions: HashMap<(SessionId, String), Vec<MessageId>>,
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
            by_message: HashMap::new(),
            latest: HashMap::new(),
            companions: HashMap::new(),
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

    /// **The SURFACE id for `key`'s message in this chat** — the chat-scoped session id with the
    /// offering appended (`tg:-700#tug`). One Telegram message per `(chat, offering)`, so opening
    /// a second offering posts a SECOND live surface instead of stealing the first one's message.
    ///
    /// Distinct from [`session_id`](Self::session_id), which stays the chat-scoped *host* session
    /// id: the [`dreggnet_offerings::OfferingHost`] already addresses a session by `(key, id)`, so
    /// two offerings in one chat are already two separate host sessions. What used to collide was
    /// the SURFACE — one message slot, one presented keyboard, one "active" offering per chat —
    /// and that is what this id splits. Host-side session identity (its seed, its durable resume
    /// log, its Mini App deep link) is untouched.
    pub fn surface_id(chat_id: ChatId, message_thread_id: Option<i64>, key: &str) -> SessionId {
        let chat = Self::session_id(chat_id, message_thread_id);
        SessionId::new(format!("{}{SURFACE_SEP}{key}", chat.0))
    }

    /// Parse a [`SessionId`] minted by [`Self::session_id`] or [`Self::surface_id`] back into
    /// `(chat_id, topic)` — the offering suffix, if any, is dropped. `None` for a session id this
    /// frontend did not mint.
    pub fn chat_of(session: &SessionId) -> Option<(ChatId, Option<i64>)> {
        let rest = session.0.strip_prefix("tg:")?;
        // Drop the `#offering` suffix: a surface id addresses the same chat as its session id.
        let rest = rest.split(SURFACE_SEP).next()?;
        let mut parts = rest.split(':');
        let chat_id: ChatId = parts.next()?.parse().ok()?;
        let topic = match parts.next() {
            Some(t) => Some(t.parse().ok()?),
            None => None,
        };
        Some((chat_id, topic))
    }

    /// The offering key a SURFACE id names (`tg:-700#tug` → `"tug"`), or `None` for a bare
    /// chat-scoped session id (a chat-level surface: the offerings menu, or a lone frontend's one
    /// offering).
    pub fn offering_of(session: &SessionId) -> Option<&str> {
        session.0.split_once(SURFACE_SEP).map(|(_, key)| key)
    }

    /// The chat-scoped session id `session` belongs to — itself, if it is already one.
    pub fn chat_session_of(session: &SessionId) -> Option<SessionId> {
        let (chat, topic) = Self::chat_of(session)?;
        Some(Self::session_id(chat, topic))
    }

    /// The live surface slot for `session`. An exact surface id resolves exactly; a bare
    /// chat-scoped id resolves to the chat's own surface if it has one, else to the chat's MOST
    /// RECENTLY presented surface — so "the surface this chat is showing" keeps its meaning for a
    /// caller that only knows the chat.
    pub fn session(&self, session: &SessionId) -> Option<&TelegramSession> {
        if let Some(slot) = self.sessions.get(session) {
            return Some(slot);
        }
        let latest = self.latest.get(session)?;
        self.sessions.get(latest)
    }

    /// The surface slot for EXACTLY this id — no "the chat's latest surface" fallback. Use this
    /// when the question is "does this precise surface exist", which
    /// [`session`](Self::session)'s fallback would answer `true` for any live surface in the
    /// chat.
    pub fn surface_slot(&self, session: &SessionId) -> Option<&TelegramSession> {
        self.sessions.get(session)
    }

    /// The surface a live message belongs to — how a press on a specific message finds its
    /// offering when a chat hosts several.
    pub fn surface_of_message(
        &self,
        chat_id: ChatId,
        message_thread_id: Option<i64>,
        message_id: MessageId,
    ) -> Option<&SessionId> {
        self.by_message
            .get(&(chat_id, message_thread_id, message_id.0))
    }

    /// The chat's most recently presented surface id, if any.
    pub fn latest_surface(&self, chat_session: &SessionId) -> Option<&SessionId> {
        self.latest.get(chat_session)
    }

    /// **Repost `session`'s surface on the NEXT present** instead of editing its live message.
    ///
    /// A re-present normally EDITS the session's message in place — the right thing when a turn
    /// LANDS (one live surface per offering, no chat spam). It is the wrong thing when the user
    /// EXPLICITLY asks for a surface (`/offerings`, `/open`, a menu press): that message may be
    /// hundreds of messages up the scrollback, so editing it produces NO VISIBLE RESPONSE and the
    /// bot reads as dead. Clearing the recorded message id makes the next present SEND, so an
    /// explicit request always lands something the user can see.
    ///
    /// The old message stays in the message index, so a press on it still resolves to THIS
    /// surface (matched against whatever the surface presents now) rather than becoming a dead
    /// button.
    pub fn repost_next(&mut self, session: &SessionId) {
        if let Some(slot) = self.sessions.get_mut(session) {
            slot.message_id = None;
        }
    }

    /// Whether `(chat, topic, message_id)` is one of this frontend's non-interactive COMPANION
    /// pages (a proof-operation guide). Companions are deliberately absent from the routing
    /// index, so a press on one must be refused OUTRIGHT — never resolved against the chat's
    /// latest game keyboard. Distinguishing "a known companion" from "a message this process has
    /// never heard of" is what lets an unknown message (every button in the chat, after a
    /// restart) take the resume path instead of being refused as a dead button.
    pub fn is_companion_message(
        &self,
        chat_id: ChatId,
        message_thread_id: Option<i64>,
        message_id: MessageId,
    ) -> bool {
        self.companions.iter().any(|((surface, _), ids)| {
            Self::chat_of(surface) == Some((chat_id, message_thread_id))
                && ids.iter().any(|id| id.0 == message_id.0)
        })
    }

    /// **Tear down every surface this chat owns** — the frontend half of the `/cancel` escape.
    /// Drops each surface slot, its message-index entries and its companion pages, plus the
    /// chat's "latest surface" pointer. Returns the surface ids that were live, so the caller can
    /// clear its own per-surface state (an armed free-text slot). Purely presentation state: no
    /// host session and no committed move-log is touched.
    pub fn teardown_chat(&mut self, chat_session: &SessionId) -> Vec<SessionId> {
        let live: Vec<SessionId> = self
            .sessions
            .keys()
            .filter(|sid| Self::chat_session_of(sid).as_ref() == Some(chat_session))
            .cloned()
            .collect();
        for surface in &live {
            if let Some(slot) = self.sessions.remove(surface) {
                if let Some(mid) = slot.message_id {
                    self.by_message
                        .remove(&(slot.chat_id, slot.message_thread_id, mid.0));
                }
            }
            self.companions.retain(|(owner, _), _| owner != surface);
        }
        self.latest.remove(chat_session);
        // A chat's surfaces may also be indexed under messages whose slot was already replaced by
        // a repost; drop every index entry addressed to this chat so no stale id survives.
        if let Some((chat_id, topic)) = Self::chat_of(chat_session) {
            self.by_message
                .retain(|(c, t, _), _| !(*c == chat_id && *t == topic));
        }
        live
    }

    /// Every live surface in a chat, in stable (surface-id) order — what "two offerings are both
    /// live here" is read off.
    pub fn surfaces_in_chat(&self, chat_session: &SessionId) -> Vec<&SessionId> {
        let mut out: Vec<&SessionId> = self
            .sessions
            .keys()
            .filter(|sid| Self::chat_session_of(sid).as_ref() == Some(chat_session))
            .collect();
        out.sort_by(|a, b| a.0.cmp(&b.0));
        out
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

    /// [`present_result`](Self::present_result) plus **trailing frontend-control rows**: each
    /// `extra_buttons` entry is appended as its own keyboard row AFTER the affordance rows.
    /// These are frontend-level controls (the standing [`crate::verify_control`] button or the
    /// Mini App [`crate::webapp::play_button`]), NOT offering [`Action`]s: they are not recorded
    /// among the session's `presented` affordances, so [`collect`](Frontend::collect) never
    /// mistakes one for a game move. A callback control is routed explicitly by its host; a
    /// `web_app` button produces no callback at all.
    pub fn present_result_with(
        &mut self,
        session: &SessionId,
        surface: &Surface,
        actions: &[Action],
        extra_buttons: &[InlineKeyboardButton],
    ) -> Result<MessageId, TransportError> {
        let callback_data: Vec<String> = actions
            .iter()
            .map(|action| crate::api::encode_callback(&action.turn, action.arg))
            .collect();
        self.present_result_with_callback_data(
            session,
            surface,
            actions,
            &callback_data,
            extra_buttons,
        )
    }

    /// [`present_result_with`](Self::present_result_with) with exact callback
    /// data supplied for every action. The game host uses this to put the full
    /// bound action-reference digest on the Telegram wire while retaining raw
    /// [`Action`]s in the session for presentation introspection.
    pub fn present_result_with_callback_data(
        &mut self,
        session: &SessionId,
        surface: &Surface,
        actions: &[Action],
        callback_data: &[String],
        extra_buttons: &[InlineKeyboardButton],
    ) -> Result<MessageId, TransportError> {
        let (chat_id, topic) = Self::chat_of(session)
            .ok_or_else(|| TransportError(format!("not a telegram session id: {}", session.0)))?;
        let mut req = build_present_request_with_callback_data(
            chat_id,
            topic,
            surface,
            actions,
            callback_data,
        )
        .map_err(TransportError)?;
        // ⚑ Measured on the WIRE text, which is now entity-escaped and `<pre>`-fenced. Telegram
        // counts characters AFTER entity parsing, so `&amp;` costs it 1 and costs us 5: this guard
        // is CONSERVATIVE by exactly the markup, never permissive. That is the safe direction (it
        // refuses a hair early rather than letting the Bot API reject ambiguously), and the markup
        // is small in practice — a board is `·─│×@RAab` and digits, none of which escape at all.
        if req.text.chars().count() > TELEGRAM_TEXT_LIMIT {
            return Err(TransportError(format!(
                "interactive Telegram surface is {} characters; maximum is {TELEGRAM_TEXT_LIMIT}",
                req.text.chars().count()
            )));
        }
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
        // Index the live message → this surface (a press names its message), and record this as
        // the chat's most recent surface (the fallback for a press that names none).
        self.by_message
            .insert((chat_id, topic, message_id.0), session.clone());
        self.latest
            .insert(Self::session_id(chat_id, topic), session.clone());
        self.last_send_error = None;
        Ok(message_id)
    }

    /// The live message ids for a non-interactive companion slot, in page order.
    pub fn companion_messages(&self, session: &SessionId, slot: &str) -> Vec<MessageId> {
        self.companions
            .get(&(session.clone(), slot.to_string()))
            .cloned()
            .unwrap_or_default()
    }

    /// Present or edit a stable set of non-interactive companion pages beside `session`.
    ///
    /// Companion messages never carry a keyboard and are never inserted into `by_message` or
    /// `latest`. Shrinking/closing a guide edits surplus pages to an inert tombstone instead of
    /// leaving stale proof instructions visible. A later expansion reuses those same message ids.
    pub fn present_companion_pages_result(
        &mut self,
        session: &SessionId,
        slot: &str,
        pages: &[String],
    ) -> Result<Vec<MessageId>, TransportError> {
        let (chat_id, topic) = Self::chat_of(session)
            .ok_or_else(|| TransportError(format!("not a telegram session id: {}", session.0)))?;
        if slot.is_empty() {
            return Err(TransportError(
                "Telegram companion slot must be non-empty".to_string(),
            ));
        }
        for page in pages {
            let characters = page.chars().count();
            if characters == 0 || characters > TELEGRAM_TEXT_LIMIT {
                return Err(TransportError(format!(
                    "Telegram companion page has {characters} characters; expected 1..={TELEGRAM_TEXT_LIMIT}"
                )));
            }
        }

        let key = (session.clone(), slot.to_string());
        let mut ids = self.companions.get(&key).cloned().unwrap_or_default();
        for (index, page) in pages.iter().enumerate() {
            let request = SendMessageRequest {
                chat_id,
                text: page.clone(),
                reply_markup: None,
                message_thread_id: topic,
                // A companion page is PLAIN text: no board to fence, so no parse mode — and
                // therefore no guide prose that could fail to send on an unescaped character.
                parse_mode: None,
            };
            if let Some(message_id) = ids.get(index).copied() {
                self.transport.edit_message(message_id, &request)?;
            } else {
                let message_id = self.transport.send_message(&request)?;
                ids.push(message_id);
                // Bank a newly-created id immediately: if a later page fails, the next repaint
                // can still edit this already-visible message instead of orphaning it.
                self.companions.insert(key.clone(), ids.clone());
            }
        }

        let inert = SendMessageRequest {
            chat_id,
            text: "Proof-operation guide inactive. /status shows the current session record."
                .to_string(),
            reply_markup: None,
            message_thread_id: topic,
            parse_mode: None,
        };
        for message_id in ids.iter().copied().skip(pages.len()) {
            self.transport.edit_message(message_id, &inert)?;
        }
        self.companions.insert(key, ids.clone());
        self.last_send_error = None;
        Ok(ids)
    }

    /// Infallible companion presentation mirroring [`present_with`](Self::present_with): transport
    /// failures are retained in [`last_send_error`](Self::last_send_error).
    pub fn present_companion_pages(&mut self, session: &SessionId, slot: &str, pages: &[String]) {
        if let Err(error) = self.present_companion_pages_result(session, slot, pages) {
            self.last_send_error = Some(error);
        }
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

    /// Infallible game-host form of
    /// [`present_result_with_callback_data`](Self::present_result_with_callback_data).
    pub fn present_with_callback_data(
        &mut self,
        session: &SessionId,
        surface: &Surface,
        actions: &[Action],
        callback_data: &[String],
        extra_buttons: &[InlineKeyboardButton],
    ) {
        if let Err(error) = self.present_result_with_callback_data(
            session,
            surface,
            actions,
            callback_data,
            extra_buttons,
        ) {
            self.last_send_error = Some(error);
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
        // The press's OWN message names its surface (the only way to tell apart several offerings
        // live in one chat); a press that names no message falls back to the chat's surface.
        let session = match ev
            .message_id
            .and_then(|m| self.surface_of_message(ev.chat_id, ev.message_thread_id, MessageId(m)))
        {
            Some(sid) => sid.clone(),
            None => {
                let chat = Self::session_id(ev.chat_id, ev.message_thread_id);
                match self.latest.get(&chat) {
                    Some(sid) => sid.clone(),
                    None => chat,
                }
            }
        };
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
        if let Some(slot) = self.sessions.remove(session) {
            if let Some(mid) = slot.message_id {
                self.by_message
                    .remove(&(slot.chat_id, slot.message_thread_id, mid.0));
            }
        }
        // Drop the chat's "most recent surface" pointer if it pointed here.
        if let Some(chat) = Self::chat_session_of(session) {
            if self.latest.get(&chat) == Some(session) {
                self.latest.remove(&chat);
            }
        }
    }
}
