//! # The RUNTIME SHELL — what turns the library into a RUNNING bot.
//!
//! Everything below the [`crate::transport::HttpPost`] byte seam stays exactly as committed (pure
//! request builders, the injected transport, the [`TelegramHost`] router over the shared catalog).
//! This module adds the process around it, in the same testable split:
//!
//! - **[`BotApi`]** — the raw-method client for the calls a running bot needs beyond
//!   `sendMessage`: `getUpdates` (the LONG POLL), `answerCallbackQuery` (ack a press so the
//!   client's spinner stops), plain-text `sendMessage` replies, `getMe` (the startup token
//!   check). Same shape as [`crate::transport::RawBotApi`]: pure URL/body composition over an
//!   injected [`HttpPost`].
//! - **[`parse_updates`]** — the pure `Update[]` → [`BotEvent`] decoder (a button callback, a
//!   text command, a bounded-operation document, or a Mini App `web_app_data` round-trip), plus
//!   the next long-poll offset.
//!   Driven directly in the tests with the real Bot API JSON shapes — no network needed to
//!   prove the routing.
//! - **[`route_callback`] / [`route_text`]** — one press / one command → the ONE router
//!   ([`TelegramHost::press`] / [`TelegramHost::open`]), including the RESTART path: a press in a
//!   chat whose session was durably resumed but not yet rebound ([`TelegramHost::resume_chat`])
//!   re-presents the live surface and retries, so a stale button from before the restart still
//!   lands.
//! - **[`durable_telegram_host`]** — the full shared catalog over a
//!   [`FileResumeStore`](dreggnet_offerings::FileResumeStore) (the same durable-store idiom
//!   `dreggnet-web`'s `demo_host_over` mounts): every open + landed advance is written through as
//!   a move-log, and boot RESUMES every persisted session by replay — a tampered log refuses to
//!   reopen (fail-closed; the file is kept as evidence).
//! - **[`run_update_loop`]** — the forever loop the bin runs: long-poll → decode → route → ack.
//!
//! The bin (`src/bin/dreggnet-telegram-bot.rs`) wires token-from-env + the store + this loop; the
//! systemd unit under `deploy/telegram/` keeps it running. The only thing a test cannot drive is
//! the real `api.telegram.org` edge — that needs the ops-gated bot token.

use std::path::PathBuf;

use serde_json::{Value, json};

use dreggnet_catalog::{
    PlayerWorlds, PublicGameAttribution, PublicGameReceipt, PublicGameReceiptResult,
};
use dreggnet_offerings::player_turn_receipt::{PlayerReplaySurface, PlayerTurnReceipt};
use dreggnet_offerings::resume::SessionResumeStore;
use dreggnet_offerings::{FileResumeStore, OfferingHost, Outcome, VerifyReport};

use crate::api::{decode_callback, encode_callback};
use crate::audit::{self, Actor, AuditEvent, AuditOutcome, Input, Surface};
use crate::host::{
    HostPress, TURN_VERIFY, TelegramAppliedOperation, TelegramGameStatus, TelegramHost,
    TelegramSharedGameStatus, telegram_default_host,
};
use crate::transport::{HttpPost, Transport, TransportError};
use crate::{CallbackQuery, ChatId, ChatKind, TelegramFrontend, TelegramUserId};

/// How long the server holds a `getUpdates` long poll open (seconds). The Bot API allows up to
/// ~50; the HTTP client timeout ([`crate::reqwest_transport`]) sits above this.
pub const POLL_TIMEOUT_SECS: u64 = 50;

/// The Bot API cap on an `answerCallbackQuery` toast text.
const CALLBACK_ANSWER_MAX: usize = 200;

/// **The `/help` (and `/start`) text — GENERATED** from [`crate::commands::COMMANDS`], the same
/// registry [`route_text_decided`] resolves every command word through. A hand-maintained help
/// string rots the moment a command is added (this one had: `/menu`, `/webapp`, `/record` and
/// `/start` were dispatched and undocumented, while `/operation` was documented as a command
/// though it is a document caption). Generated, it cannot.
pub fn help_text() -> String {
    crate::commands::help_text()
}

// ─────────────────────────────────────────────────────────────────────────────
// The raw-method Bot API client (getUpdates / answerCallbackQuery / getMe / text replies)
// ─────────────────────────────────────────────────────────────────────────────

/// **The raw-method Bot API client** the update loop drives. Pure composition (URL + JSON body +
/// the `{ok, result}` envelope) over an injected [`HttpPost`] — the same split as
/// [`crate::transport::RawBotApi`], for the methods a RUNNING bot needs around the send path.
pub struct BotApi<H: HttpPost> {
    token: String,
    base_url: String,
    http: H,
}

impl<H: HttpPost> BotApi<H> {
    /// A client for `token`, POSTing through `http`, against the public Bot API host.
    pub fn new(token: impl Into<String>, http: H) -> Self {
        BotApi {
            token: token.into(),
            base_url: "https://api.telegram.org".to_string(),
            http,
        }
    }

    /// Override the Bot API host (a self-hosted Bot API server, or a test double).
    pub fn with_base_url(mut self, base_url: impl Into<String>) -> Self {
        self.base_url = base_url.into();
        self
    }

    /// Call `method` with the JSON `body`, unwrap the `{ok, result}` envelope, return `result`.
    pub fn call(&self, method: &str, body: &Value) -> Result<Value, TransportError> {
        let url = format!("{}/bot{}/{}", self.base_url, self.token, method);
        let resp = self
            .http
            .post_json(&url, &body.to_string())
            .map_err(TransportError)?;
        let v: Value = serde_json::from_str(&resp)
            .map_err(|e| TransportError(format!("decode {method} response: {e}")))?;
        if v.get("ok").and_then(Value::as_bool) != Some(true) {
            let desc = v
                .get("description")
                .and_then(Value::as_str)
                .unwrap_or("Bot API returned ok=false");
            return Err(TransportError(format!("{method}: {desc}")));
        }
        Ok(v.get("result").cloned().unwrap_or(Value::Null))
    }

    /// `getMe` — the startup token check. Returns the bot's username.
    pub fn get_me(&self) -> Result<String, TransportError> {
        let me = self.call("getMe", &json!({}))?;
        Ok(me
            .get("username")
            .and_then(Value::as_str)
            .unwrap_or("<unnamed bot>")
            .to_string())
    }

    /// **Register the client-side `/` menu** (`setMyCommands`) from the ONE command registry
    /// ([`crate::commands::bot_father_commands`]). Without this call `getMyCommands` returns `[]`
    /// and the Telegram client shows NO command list at all — the whole surface has to be
    /// guessed, which is exactly how a user ends up typing `/descent` and getting
    /// "unknown_command". Returns how many commands were registered.
    pub fn set_my_commands(&self) -> Result<usize, TransportError> {
        let commands: Vec<Value> = crate::commands::bot_father_commands()
            .into_iter()
            .map(|(command, description)| json!({ "command": command, "description": description }))
            .collect();
        let count = commands.len();
        self.call("setMyCommands", &json!({ "commands": commands }))?;
        Ok(count)
    }

    /// One `getUpdates` LONG POLL: block server-side up to [`POLL_TIMEOUT_SECS`] for new updates
    /// at/after `offset`. Returns the raw `result` array (decode with [`parse_updates`]).
    pub fn get_updates(&self, offset: Option<i64>) -> Result<Value, TransportError> {
        let mut body = json!({
            "timeout": POLL_TIMEOUT_SECS,
            "allowed_updates": ["message", "callback_query"],
        });
        if let Some(o) = offset {
            body["offset"] = json!(o);
        }
        self.call("getUpdates", &body)
    }

    /// Ack a button press (`answerCallbackQuery`) with a short toast — the client's loading
    /// spinner stops. Text is truncated to the Bot API's 200-char cap.
    pub fn answer_callback(&self, callback_id: &str, text: &str) -> Result<(), TransportError> {
        let toast: String = text.chars().take(CALLBACK_ANSWER_MAX).collect();
        self.call(
            "answerCallbackQuery",
            &json!({ "callback_query_id": callback_id, "text": toast }),
        )
        .map(|_| ())
    }

    /// Send a plain-text reply into a chat (command answers, verify reports) — distinct from the
    /// session's presented surface message, which the [`TelegramHost`]'s own transport owns.
    pub fn send_text(
        &self,
        chat_id: ChatId,
        topic: Option<i64>,
        text: &str,
    ) -> Result<(), TransportError> {
        let mut body = json!({ "chat_id": chat_id, "text": text });
        if let Some(t) = topic {
            body["message_thread_id"] = json!(t);
        }
        self.call("sendMessage", &body).map(|_| ())
    }

    /// Resolve a Telegram document with `getFile`, then read its body through
    /// the injected transport's hard byte ceiling. Neither the token-bearing
    /// URL nor the opaque body is included in an error string.
    pub fn download_document(
        &self,
        file_id: &str,
        declared_bytes: usize,
        maximum: usize,
    ) -> Result<Vec<u8>, TransportError> {
        let file = self.call("getFile", &json!({ "file_id": file_id }))?;
        if let Some(size) = file.get("file_size").and_then(Value::as_u64) {
            if size > maximum as u64 {
                return Err(TransportError(format!(
                    "getFile reports an object larger than the {maximum}-byte operation limit"
                )));
            }
            if size != declared_bytes as u64 {
                return Err(TransportError(format!(
                    "Telegram document metadata changed size ({declared_bytes} declared, {size} at getFile)"
                )));
            }
        }
        let path = file
            .get("file_path")
            .and_then(Value::as_str)
            .ok_or_else(|| TransportError("getFile response missing file_path".to_string()))?;
        if path.is_empty()
            || path.starts_with('/')
            || path.split('/').any(|part| part == "..")
            || path.contains("://")
        {
            return Err(TransportError(
                "getFile returned an invalid file_path".to_string(),
            ));
        }
        let url = format!("{}/file/bot{}/{}", self.base_url, self.token, path);
        self.http
            .get_bytes_bounded(&url, maximum)
            .map_err(TransportError)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Update decoding (pure — driven directly by the tests with real Bot API JSON)
// ─────────────────────────────────────────────────────────────────────────────

/// One decoded incoming update the shell routes — a button, text/service
/// message, or metadata-only document handle.
#[derive(Debug, Clone)]
pub enum BotEvent {
    /// An inline-button press (`callback_query`): the Bot API callback id (for the ack) plus the
    /// typed [`CallbackQuery`] the library routes.
    Callback {
        /// The `callback_query.id` — `answerCallbackQuery` needs it to stop the spinner.
        callback_id: String,
        /// The press, in the library's own event type.
        query: CallbackQuery,
    },
    /// A text message (`message.text`) — the command surface (`/offerings`, `/open`, …).
    Text {
        /// The chat the message was sent in.
        chat_id: ChatId,
        /// The forum-topic thread, if any.
        topic: Option<i64>,
        /// The sending Telegram user.
        uid: TelegramUserId,
        /// The message text.
        text: String,
    },
    /// Data a Mini App sent back through `Telegram.WebApp.sendData` (`message.web_app_data`) —
    /// a service message from a KEYBOARD-launched web-view. Routed by [`route_web_app_data`]:
    /// a payload in the ONE affordance codec routes as a synthetic press (the executor stays
    /// the sole referee); anything else is acknowledged, never trusted — a client string can
    /// never name an identity or bypass the presented-affordance gate.
    WebAppData {
        /// The chat the service message landed in.
        chat_id: ChatId,
        /// The forum-topic thread, if any.
        topic: Option<i64>,
        /// The Telegram user whose web-view sent the data.
        uid: TelegramUserId,
        /// The raw `web_app_data.data` payload (client-authored — untrusted).
        data: String,
        /// The `web_app_data.button_text` — the keyboard button's label, display only.
        button_text: Option<String>,
    },
    /// A player-attached opaque producer receipt. Metadata is parsed before
    /// any `getFile` call so the live descriptor can reject it cheaply.
    Document {
        /// The chat the document message landed in.
        chat_id: ChatId,
        /// The forum topic, if any.
        topic: Option<i64>,
        /// The sending Telegram user.
        uid: TelegramUserId,
        /// Telegram's opaque handle for the subsequent `getFile` call.
        file_id: String,
        /// Telegram's declared body length. An unrepresentable or absent
        /// length becomes `usize::MAX` and therefore fails preflight.
        declared_bytes: usize,
        /// Must be exactly `/operation <live-name>`.
        caption: String,
    },
}

/// **Decode a `getUpdates` `result` array** into the events the shell routes, plus the NEXT poll
/// offset (max `update_id` + 1 — confirming these updates consumed so the server drops them).
/// Unknown/partial update shapes are skipped, never a crash: the loop must survive whatever the
/// wire brings.
pub fn parse_updates(result: &Value) -> (Vec<BotEvent>, Option<i64>) {
    let mut events = Vec::new();
    let mut next: Option<i64> = None;
    let Some(arr) = result.as_array() else {
        return (events, next);
    };
    for u in arr {
        if let Some(id) = u.get("update_id").and_then(Value::as_i64) {
            next = Some(next.map_or(id + 1, |n| n.max(id + 1)));
        }
        if let Some(cb) = u.get("callback_query") {
            let (Some(callback_id), Some(uid), Some(msg), Some(data)) = (
                cb.get("id").and_then(Value::as_str),
                cb.get("from")
                    .and_then(|f| f.get("id"))
                    .and_then(Value::as_u64),
                cb.get("message"),
                cb.get("data").and_then(Value::as_str),
            ) else {
                continue;
            };
            let Some(chat_id) = msg
                .get("chat")
                .and_then(|c| c.get("id"))
                .and_then(Value::as_i64)
            else {
                continue;
            };
            events.push(BotEvent::Callback {
                callback_id: callback_id.to_string(),
                query: CallbackQuery {
                    chat_id,
                    message_thread_id: msg.get("message_thread_id").and_then(Value::as_i64),
                    // WHICH message the button lives on — with several offerings open in one
                    // chat this is what says which one the press addresses.
                    message_id: msg.get("message_id").and_then(Value::as_i64),
                    from_user_id: uid,
                    data: data.to_string(),
                },
            });
        } else if let Some(m) = u.get("message") {
            let (Some(chat_id), Some(uid)) = (
                m.get("chat")
                    .and_then(|c| c.get("id"))
                    .and_then(Value::as_i64),
                m.get("from")
                    .and_then(|f| f.get("id"))
                    .and_then(Value::as_u64),
            ) else {
                continue;
            };
            let topic = m.get("message_thread_id").and_then(Value::as_i64);
            // A Mini App's `sendData` round-trip arrives as a `web_app_data` service message
            // (no `text`), so it is checked FIRST — the same skip-not-crash posture for
            // anything partial.
            if let Some(wad) = m.get("web_app_data") {
                let Some(data) = wad.get("data").and_then(Value::as_str) else {
                    continue;
                };
                events.push(BotEvent::WebAppData {
                    chat_id,
                    topic,
                    uid,
                    data: data.to_string(),
                    button_text: wad
                        .get("button_text")
                        .and_then(Value::as_str)
                        .map(str::to_string),
                });
            } else if let Some(document) = m.get("document") {
                let Some(file_id) = document.get("file_id").and_then(Value::as_str) else {
                    continue;
                };
                let declared_bytes = document
                    .get("file_size")
                    .and_then(Value::as_u64)
                    .and_then(|size| usize::try_from(size).ok())
                    .unwrap_or(usize::MAX);
                events.push(BotEvent::Document {
                    chat_id,
                    topic,
                    uid,
                    file_id: file_id.to_string(),
                    declared_bytes,
                    caption: m
                        .get("caption")
                        .and_then(Value::as_str)
                        .unwrap_or_default()
                        .to_string(),
                });
            } else if let Some(text) = m.get("text").and_then(Value::as_str) {
                events.push(BotEvent::Text {
                    chat_id,
                    topic,
                    uid,
                    text: text.to_string(),
                });
            }
        }
    }
    (events, next)
}

/// Parse the exact caption that opts a document into operation ingress.
/// Arbitrary attachments and captions are never swallowed by an offering.
pub fn parse_operation_caption(caption: &str) -> Option<&str> {
    let mut fields = caption.split_whitespace();
    let command = fields.next()?.split('@').next()?;
    let operation = fields.next()?;
    if command == "/operation" && fields.next().is_none() {
        Some(operation)
    } else {
        None
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Routing (one event → the ONE TelegramHost router → a human ack)
// ─────────────────────────────────────────────────────────────────────────────

/// **The MACHINE account of a routed press** — what the audit envelope records (the human ack
/// stays [`describe_press`]'s). Extracted from the [`HostPress`] BEFORE it is consumed, so the
/// update loop emits [`AuditEvent`]s in the design's §3 taxonomy without re-deriving anything.
#[derive(Debug, Clone)]
pub enum PressDecision {
    /// A menu press opened the named offering.
    Opened(String),
    /// A turn landed — carries the executor's turn id for the audit record.
    Landed {
        /// The offering key the turn advanced.
        key: String,
        /// `hex(TurnReceipt.turn_hash)` — the committed turn id.  The player-facing
        /// acknowledgement separately publishes the complete receipt-chain join.
        turn_hash: String,
        /// Whether the session ended.
        ended: bool,
    },
    /// The executor refused the move (anti-ghost: nothing committed).
    ExecutorRefused {
        /// The offering key.
        key: String,
        /// The executor's own reason.
        why: String,
    },
    /// A [`TURN_VERIFY`](crate::host::TURN_VERIFY) press re-verified the chain.
    Verified {
        /// The offering key.
        key: String,
        /// The report verdict (`None` = the offering exposes no verifier).
        verified: Option<bool>,
        /// Turns replayed.
        turns: u64,
    },
    /// A press ARMED a free-text affordance ([`HostPress::TextArmed`]) — a deliberate selection,
    /// not a committed turn; the next plain-text message fills it.
    TextArmed {
        /// The offering key whose text slot was armed.
        key: String,
    },
    /// A menu press asked for a HIDDEN-INFORMATION offering in a shared chat and this surface
    /// refused to host it ([`HostPress::OpenRefused`]) — a privacy refusal BEFORE any render.
    OpenRefused {
        /// The offering that was not opened.
        key: String,
    },
    /// Frontend-level refusal BEFORE the substrate (stale keyboard / unknown affordance).
    NotOffered,
    /// Nothing open in the chat (post-resume-retry).
    NoSession,
    /// The restart-resume path found a persisted offering but could not reopen it.
    ReopenFailed(String),
}

impl PressDecision {
    /// Read the machine decision off a [`HostPress`] (borrow — the press is still yours to
    /// [`describe_press`]).
    pub fn of(press: &HostPress) -> PressDecision {
        match press {
            HostPress::Opened(key) => PressDecision::Opened(key.clone()),
            HostPress::Advanced {
                key,
                outcome: Outcome::Landed { receipt, ended },
            } => PressDecision::Landed {
                key: key.clone(),
                turn_hash: audit::hex32(&receipt.turn_hash),
                ended: *ended,
            },
            HostPress::Advanced {
                key,
                outcome: Outcome::Refused(why),
            } => PressDecision::ExecutorRefused {
                key: key.clone(),
                why: why.clone(),
            },
            HostPress::Verified { key, report } => PressDecision::Verified {
                key: key.clone(),
                verified: report.as_ref().map(|r| r.verified),
                turns: report.as_ref().map(|r| r.turns as u64).unwrap_or(0),
            },
            HostPress::TextArmed { key, .. } => PressDecision::TextArmed { key: key.clone() },
            HostPress::OpenRefused { key, .. } => PressDecision::OpenRefused { key: key.clone() },
            HostPress::NotOffered => PressDecision::NotOffered,
            HostPress::NoSession => PressDecision::NoSession,
        }
    }

    /// The §3 taxonomy mapping: `(decision.kind, decision.reason, outcome, offering)`.
    pub fn audit_parts(&self) -> (&'static str, String, AuditOutcome, Option<String>) {
        match self {
            PressDecision::Opened(key) => (
                "routed",
                String::new(),
                AuditOutcome::None,
                Some(key.clone()),
            ),
            PressDecision::Landed {
                key,
                turn_hash,
                ended,
            } => (
                "routed",
                String::new(),
                AuditOutcome::Landed {
                    turn_hash: turn_hash.clone(),
                    ended: *ended,
                },
                Some(key.clone()),
            ),
            PressDecision::ExecutorRefused { key, why } => (
                "routed", // the substrate WAS reached; the refusal is the executor's
                String::new(),
                AuditOutcome::Refused { why: why.clone() },
                Some(key.clone()),
            ),
            PressDecision::Verified {
                key,
                verified,
                turns,
            } => (
                "routed",
                String::new(),
                AuditOutcome::Verified {
                    verified: verified.unwrap_or(false),
                    turns: *turns,
                },
                Some(key.clone()),
            ),
            PressDecision::TextArmed { key } => (
                "routed",
                "text_armed".to_string(),
                AuditOutcome::None,
                Some(key.clone()),
            ),
            PressDecision::OpenRefused { key } => (
                "refused",
                "hidden_information_in_shared_chat".to_string(),
                AuditOutcome::None,
                Some(key.clone()),
            ),
            PressDecision::NotOffered => (
                "refused",
                "not_offered".to_string(),
                AuditOutcome::None,
                None,
            ),
            PressDecision::NoSession => (
                "refused",
                "no_session".to_string(),
                AuditOutcome::None,
                None,
            ),
            PressDecision::ReopenFailed(key) => (
                "error",
                "resume_reopen_failed".to_string(),
                AuditOutcome::None,
                Some(key.clone()),
            ),
        }
    }
}

/// **Route a button press through the host**, with the RESTART-RESUME path: if the chat answers
/// [`HostPress::NoSession`] (this process never presented there) but the chat's session was
/// durably RESUMED on boot, rebind it ([`TelegramHost::resume_chat`]), re-present the live
/// surface ([`TelegramHost::open`] — idempotent, the resumed state is kept), and retry the press
/// once against the fresh keyboard. Returns the human ack for `answerCallbackQuery`.
pub fn route_callback<T: Transport>(host: &mut TelegramHost<T>, query: CallbackQuery) -> String {
    route_callback_decided(host, query).0
}

/// [`route_callback`] plus the machine [`PressDecision`] — the audit-emitting caller's form
/// (design §9: `route_*` expose the structured decision alongside the human string).
pub fn route_callback_decided<T: Transport>(
    host: &mut TelegramHost<T>,
    query: CallbackQuery,
) -> (String, PressDecision) {
    // Whatever an EARLIER interaction failed to paint is not this press's news; the ack must
    // report only what this press did.
    let _ = host.take_paint_failure();
    match host.press(query.clone()) {
        HostPress::NoSession => {
            let sid = TelegramFrontend::<T>::session_id(query.chat_id, query.message_thread_id);
            // Resume EVERY offering this chat durably owns, not one arbitrary alphabetical
            // winner, and re-present each as a fresh live message. A chat with `craft` and `doc`
            // persisted used to rebind whichever sorted first no matter which message was
            // pressed, so half the chat's buttons routed into the wrong offering — and if the
            // winner was a session nothing could advance, the chat stayed pinned to it across
            // every restart.
            // The presser's identity is what makes an RPG session findable at all: it lives in
            // THAT user's own per-identity world, not the shared catalog host.
            let viewer = host.identity(query.from_user_id);
            let keys = host.resume_chat_all(&sid, Some(&viewer));
            let Some(primary) = keys.first().cloned() else {
                return (
                    "No session in this chat yet — send /offerings to pick one.".to_string(),
                    PressDecision::NoSession,
                );
            };
            let mut reopened = Vec::new();
            // A session that reopens but paints nothing is worse than one that refuses: the user
            // is told their game is back and sees no message. Name each one.
            let mut unpainted = Vec::new();
            for key in &keys {
                if host
                    .open(
                        key,
                        query.chat_id,
                        query.message_thread_id,
                        query.from_user_id,
                    )
                    .is_ok()
                {
                    match host.take_paint_failure() {
                        Some(why) => unpainted.push(format!("{key} ({why})")),
                        None => reopened.push(key.clone()),
                    }
                }
            }
            if reopened.is_empty() && !unpainted.is_empty() {
                return (
                    format!(
                        "Your session(s) resumed but could not be painted: {}. /cancel clears \
                         this chat; /close <key> discards one.",
                        unpainted.join(", ")
                    ),
                    PressDecision::ReopenFailed(primary),
                );
            }
            if reopened.is_empty() {
                return (
                    format!("Could not reopen {primary} — send /offerings."),
                    PressDecision::ReopenFailed(primary),
                );
            }
            let press = host.press(query);
            let decision = PressDecision::of(&press);
            // A press that STILL resolves nothing is a button from before the restart whose
            // message this process cannot map — say so, and point at the live surfaces just
            // reposted, instead of the bare "stale keyboard?" dead end.
            if matches!(decision, PressDecision::NotOffered) {
                return (
                    format!(
                        "That button is from before my last restart. I have reposted your live \
                         session(s) below: {}. Press there, or /cancel to start clean.",
                        reopened.join(", ")
                    ),
                    decision,
                );
            }
            (describe_press(press), decision)
        }
        press => {
            let decision = PressDecision::of(&press);
            (ack_for(host, press), decision)
        }
    }
}

/// [`describe_press`] plus the host's **paint failure**, if the press opened or advanced
/// something whose surface never went out. A press that lands a turn nobody can see is the same
/// silence `/open` used to answer with; the ack is the only place a presser would ever learn it.
fn ack_for<T: Transport>(host: &mut TelegramHost<T>, press: HostPress) -> String {
    let described = describe_press(press);
    match host.take_paint_failure() {
        None => described,
        Some(why) => format!(
            "{described} …but I could not paint the surface: {why}. /cancel clears this chat."
        ),
    }
}

/// **Route a text message** — the command surface. `None` means nothing to reply (ordinary
/// chatter is ignored; the offerings menu / opened surface are their own messages, sent through
/// the host's transport).
pub fn route_text<T: Transport>(
    host: &mut TelegramHost<T>,
    chat_id: ChatId,
    topic: Option<i64>,
    uid: TelegramUserId,
    text: &str,
) -> Option<String> {
    route_text_decided(host, chat_id, topic, uid, text).0
}

/// The machine account of a routed text message — the audit envelope's half of
/// [`route_text_decided`]. `Ignored` (ordinary chatter) is deliberately NOT audited by the
/// loop: no decision was made and group chatter is not an interaction with the bot.
#[derive(Debug, Clone)]
pub enum TextDecision {
    /// `/start` `/help` — the help text answered.
    Help,
    /// `/offerings` `/menu` — the offerings menu presented.
    Menu,
    /// `/play` — the Mini App launch menu; `why` is the honest refusal when unserved.
    PlayMenu {
        /// Whether the launch menu was actually sent.
        served: bool,
        /// The human reason when it was not.
        why: Option<String>,
    },
    /// `/open <key>` — `err` carries the host's refusal, if any.
    Open {
        /// The requested offering key.
        key: String,
        /// The open error, if the host refused.
        err: Option<String>,
    },
    /// `/status` inspected the active game through the shared game-session spine.
    GameStatus {
        /// Active game key, when one was resolved.
        key: Option<String>,
        /// Whether the live session was inspected and replay-verified.
        inspected: bool,
    },
    /// `/verify` / `/act` minted a synthetic press — the press's own decision.
    Press {
        /// Which command minted the press.
        cmd: String,
        /// The routed press's machine decision.
        press: PressDecision,
    },
    /// `/offerings` was asked for and the menu could NOT be sent — the transport's reason,
    /// answered to the user instead of silence.
    MenuFailed {
        /// The transport's own account of the failure.
        why: String,
    },
    /// `/cancel` — the always-available escape cleared this chat's presentation state.
    Cancelled {
        /// The offering keys whose surfaces were cleared (empty = nothing was open).
        cleared: Vec<String>,
    },
    /// `/close <key>` — a session was ended and its move-log discarded (or was not open).
    Closed {
        /// The offering key named.
        key: String,
        /// Whether a session was actually closed.
        closed: bool,
    },
    /// A recognized command with unusable arguments.
    Usage {
        /// The command whose usage was answered.
        cmd: String,
    },
    /// An unrecognized slash command.
    Unknown {
        /// The command word as typed.
        cmd: String,
    },
    /// **Plain text routed as a pending text affordance's input** — the chat had an open
    /// text-input offering (a document session soliciting an insert / title), so the message
    /// became that affordance's [`Action::text`](dreggnet_offerings::Action::text) payload and
    /// advanced one real turn. Carries the routed press's machine decision (the executor's
    /// verdict — a landed edit or a real refusal).
    TextInput {
        /// The routed press's machine decision.
        press: PressDecision,
    },
    /// Ordinary chatter — no decision, no reply, no audit event.
    Ignored,
}

/// [`route_text`] plus the machine [`TextDecision`] — the audit-emitting caller's form.
pub fn route_text_decided<T: Transport>(
    host: &mut TelegramHost<T>,
    chat_id: ChatId,
    topic: Option<i64>,
    uid: TelegramUserId,
    text: &str,
) -> (Option<String>, TextDecision) {
    let text = text.trim();
    let (cmd, rest) = match text.split_once(char::is_whitespace) {
        Some((c, r)) => (c, r.trim()),
        None => (text, ""),
    };
    // Whatever an EARLIER interaction failed to paint is not this command's news.
    let _ = host.take_paint_failure();
    // In a group, commands arrive suffixed with the bot's username: `/open@MyBot dungeon`.
    let typed = cmd.split('@').next().unwrap_or(cmd);
    // EVERY command word resolves through the ONE registry, which also folds aliases onto the
    // canonical name (`/menu` → `/offerings`, `/record` → `/status`, `/reset` → `/cancel`). A
    // word that is not registered cannot reach a handler — so a new command must be registered,
    // and being registered is exactly what puts it in `/help` and in Telegram's `/` menu.
    let cmd = match crate::commands::lookup(typed) {
        Some(command) => command.name,
        None if typed.starts_with('/') => {
            // Answer in a DM (a user who guessed a command deserves to be told, and told WHERE
            // the real list is — the live bot's own audit shows a real `/descent` met with
            // total silence). Stay quiet in a group: Telegram delivers every member's slash
            // word to the bot, and a collective chat does not want a bot correcting each one.
            let reply = (!ChatKind::classify(chat_id, topic).is_collective())
                .then(|| format!("{typed} is not a command. /help lists everything I answer to."));
            return (
                reply,
                TextDecision::Unknown {
                    cmd: typed.to_string(),
                },
            );
        }
        // Not a command at all — fall through to the free-text path below.
        None => "",
    };
    match cmd {
        "/help" => {
            // `/help <cmd>` renders one entry; an unrecognised argument says so and falls back to
            // the full list rather than silently showing everything.
            if rest.is_empty() {
                return (Some(help_text()), TextDecision::Help);
            }
            match crate::commands::command_help(rest) {
                Some(one) => (Some(one), TextDecision::Help),
                None => (
                    Some(format!("No command `{rest}`.\n\n{}", help_text())),
                    TextDecision::Help,
                ),
            }
        }
        "/cancel" => {
            // THE ESCAPE. It must work from every state, including no state at all — so it is
            // routed before anything that could refuse, needs no session, and cannot fail.
            let cleared = host.cancel_chat(chat_id, topic);
            host.present_offerings_menu(chat_id, topic);
            let what = if cleared.is_empty() {
                "Nothing was open here — you are clear.".to_string()
            } else {
                format!(
                    "Cleared this chat's surfaces ({}) and any pending text slot. Nothing \
                     committed was discarded — /open <key> brings a session back with its \
                     receipts intact.",
                    cleared.join(", ")
                )
            };
            (
                Some(format!("{what} Here is the menu again.")),
                TextDecision::Cancelled { cleared },
            )
        }
        "/close" => {
            if rest.is_empty() {
                return (
                    Some(
                        "Usage: /close <key> — ENDS that session and DISCARDS its move-log. \
                         /cancel is the non-destructive escape."
                            .to_string(),
                    ),
                    TextDecision::Usage {
                        cmd: cmd.to_string(),
                    },
                );
            }
            // A close that FAILED is not "nothing was open" — say which it was.
            let closed = match host.close_offering(rest, chat_id, topic, uid) {
                Ok(closed) => closed,
                Err(why) => {
                    return (
                        Some(format!(
                            "Could not close {rest}: {why}. /cancel clears this chat's surfaces \
                             without touching any move-log."
                        )),
                        TextDecision::Closed {
                            key: rest.to_string(),
                            closed: false,
                        },
                    );
                }
            };
            (
                Some(if closed {
                    format!(
                        "Closed {rest} in this chat and forgot its move-log. /open {rest} starts \
                         a fresh session."
                    )
                } else {
                    format!("No {rest} session is open in this chat.")
                }),
                TextDecision::Closed {
                    key: rest.to_string(),
                    closed,
                },
            )
        }
        "/offerings" => match host.present_offerings_menu_result(chat_id, topic) {
            // The menu message IS the reply.
            (_, None) => (None, TextDecision::Menu),
            // …unless it did not get sent, in which case SAY SO. Replying nothing to a failed
            // present is what made the bot read as dead.
            (_, Some(why)) => (
                Some(format!(
                    "I could not paint the offerings menu: {why}. /open <key> still opens one \
                     directly, and /cancel clears this chat."
                )),
                TextDecision::MenuFailed { why },
            ),
        },
        // The Mini App launch tier: a menu of `web_app` buttons opening the rich web surface,
        // one per offering. `Err` is the honest human reply (tier unarmed / group chat —
        // Telegram only honors `web_app` inline buttons in DMs / a transport failure).
        "/play" => match host.present_play_menu(chat_id, topic) {
            Ok(()) => (
                None, // the launch menu IS the reply
                TextDecision::PlayMenu {
                    served: true,
                    why: None,
                },
            ),
            Err(why) => (
                Some(why.clone()),
                TextDecision::PlayMenu {
                    served: false,
                    why: Some(why),
                },
            ),
        },
        "/link" => match host.present_link_menu(chat_id, topic) {
            Ok(()) => (
                None, // the link launch button IS the reply
                TextDecision::PlayMenu {
                    served: true,
                    why: None,
                },
            ),
            Err(why) => (
                Some(why.clone()),
                TextDecision::PlayMenu {
                    served: false,
                    why: Some(why),
                },
            ),
        },
        "/open" => {
            if rest.is_empty() {
                return (
                    Some("Usage: /open <key> — see /offerings for the catalog.".to_string()),
                    TextDecision::Usage {
                        cmd: cmd.to_string(),
                    },
                );
            }
            // In a DM an open REPOSTS, so the surface itself is the visible reply. A group /
            // forum topic deliberately keeps ONE shared message that every re-present edits in
            // place (the audience rule rests on it), so a re-open there paints nothing new and
            // wherever that message sits is where it stays — say so in words rather than
            // answering the command with silence.
            let repaint_in_place = ChatKind::classify(chat_id, topic).is_collective()
                && host.has_live_surface(chat_id, topic, rest);
            match host.open(rest, chat_id, topic, uid) {
                // An `Ok` open whose surface was never PAINTED is the silent failure this arm
                // used to answer with nothing at all — the session opens, the command replies
                // `None`, and the chat shows no message. Say what went wrong instead.
                Ok(_) => match host.take_paint_failure() {
                    Some(why) => (
                        Some(format!(
                            "I opened {rest}, but could not paint its surface: {why}. \
                             /cancel clears this chat; /close {rest} discards that session."
                        )),
                        TextDecision::Open {
                            key: rest.to_string(),
                            err: Some(why),
                        },
                    ),
                    None => (
                        // the opened surface IS the reply — unless it was an in-place repaint
                        repaint_in_place.then(|| {
                            format!(
                                "{rest} is already open in this chat — I refreshed its message \
                                 above (a group keeps ONE shared surface per game, so it stays \
                                 where it is). /cancel clears this chat."
                            )
                        }),
                        TextDecision::Open {
                            key: rest.to_string(),
                            err: None,
                        },
                    ),
                },
                Err(e) => (
                    // A shared-chat privacy refusal replies with its own redirect; a host failure
                    // keeps the "Cannot open <key>: …" shape.
                    Some(e.human(rest)),
                    TextDecision::Open {
                        key: rest.to_string(),
                        err: Some(e.to_string()),
                    },
                ),
            }
        }
        "/status" => {
            // Like `/verify`, status remains useful immediately after a process restart: bind the
            // durable session to this chat and repaint before inspecting the shared game spine.
            let sid = TelegramFrontend::<T>::session_id(chat_id, topic);
            if host.active_offering(&sid).is_none() {
                // Viewer-aware: an RPG session lives in the presser's OWN per-identity world,
                // so without the identity it is invisible to the resume path entirely.
                let viewer = host.identity(uid);
                for key in host.resume_chat_all(&sid, Some(&viewer)) {
                    let _ = host.open(&key, chat_id, topic, uid);
                }
            }
            let key = host.active_offering(&sid).map(str::to_string);
            match host.game_status(chat_id, topic, uid) {
                Ok(status) => (
                    Some(describe_game_status_for_chat(&status, chat_id, topic)),
                    TextDecision::GameStatus {
                        key: Some(status.key),
                        inspected: true,
                    },
                ),
                Err(error) => (
                    Some(format!("Game record unavailable: {error}")),
                    TextDecision::GameStatus {
                        key,
                        inspected: false,
                    },
                ),
            }
        }
        // `/verify` and `/act` mint the same synthetic press a pinned button would — the ONE
        // router (with the restart-resume path) handles both.
        "/verify" => {
            let (ack, press) = route_callback_decided(
                host,
                CallbackQuery {
                    chat_id,
                    message_thread_id: topic,
                    // A command-minted press names no message — it addresses the chat's most
                    // recent surface, which is what "this chat's session" means to the typist.
                    message_id: None,
                    from_user_id: uid,
                    data: encode_callback(TURN_VERIFY, 0),
                },
            );
            (
                Some(ack),
                TextDecision::Press {
                    cmd: cmd.to_string(),
                    press,
                },
            )
        }
        "/act" => {
            let usage = "Usage: /act <turn> <arg> — e.g. /act bid 500".to_string();
            let Some((turn, arg)) = rest.split_once(char::is_whitespace) else {
                return (
                    Some(usage),
                    TextDecision::Usage {
                        cmd: cmd.to_string(),
                    },
                );
            };
            let Ok(arg) = arg.trim().parse::<i64>() else {
                return (
                    Some(usage),
                    TextDecision::Usage {
                        cmd: cmd.to_string(),
                    },
                );
            };
            let (ack, press) = route_callback_decided(
                host,
                CallbackQuery {
                    chat_id,
                    message_thread_id: topic,
                    // A command-minted press names no message — it addresses the chat's most
                    // recent surface, which is what "this chat's session" means to the typist.
                    message_id: None,
                    from_user_id: uid,
                    data: encode_callback(turn, arg),
                },
            );
            (
                Some(ack),
                TextDecision::Press {
                    cmd: cmd.to_string(),
                    press,
                },
            )
        }
        // FREE TEXT (a non-command message). If — and ONLY if — the chat has ARMED a text
        // affordance (a deliberate press on a `wants_text` template, recorded per chat/session by
        // [`TelegramHost::press`]), route the whole message as that affordance's text input; the
        // executor referees what lands. Otherwise it is ordinary chatter and stays `Ignored`
        // (never swallow arbitrary group talk — text is claimed only when a slot is genuinely
        // armed for this chat's session).
        _ => {
            let sid = TelegramFrontend::<T>::session_id(chat_id, topic);
            // Restart-resume: after a restart this process never bound the chat's durably-resumed
            // session, so `active_offering` is empty and any subsequent text would fall through.
            // Rebind + re-present the live surface first (idempotent — the resumed state is kept),
            // so the chat is live again and the presented text buttons reappear for the user to
            // arm; without this a text-only user after a restart is stranded with no session.
            if host.active_offering(&sid).is_none() {
                // Viewer-aware: an RPG session lives in the presser's OWN per-identity world,
                // so without the identity it is invisible to the resume path entirely.
                let viewer = host.identity(uid);
                for key in host.resume_chat_all(&sid, Some(&viewer)) {
                    let _ = host.open(&key, chat_id, topic, uid);
                }
            }
            if host.pending_text_action(&sid).is_some() {
                let press = host.press_text(chat_id, topic, uid, text);
                let decision = PressDecision::of(&press);
                (
                    Some(describe_press(press)),
                    TextDecision::TextInput { press: decision },
                )
            } else {
                (None, TextDecision::Ignored)
            }
        }
    }
}

impl TextDecision {
    /// The §3 taxonomy mapping: `(decision.kind, reason, outcome, offering, input.kind)`.
    /// `None` = ordinary chatter — not an interaction, no audit event.
    pub fn audit_parts(
        &self,
    ) -> Option<(&'static str, String, AuditOutcome, Option<String>, String)> {
        match self {
            TextDecision::Help => Some((
                "routed",
                String::new(),
                AuditOutcome::None,
                None,
                "/help".to_string(),
            )),
            TextDecision::Menu => Some((
                "routed",
                String::new(),
                AuditOutcome::None,
                None,
                "/offerings".to_string(),
            )),
            TextDecision::PlayMenu { served, why } => Some((
                if *served { "routed" } else { "refused" },
                if *served {
                    String::new()
                } else {
                    format!(
                        "webapp_unavailable: {}",
                        why.as_deref().unwrap_or("unknown")
                    )
                },
                AuditOutcome::None,
                None,
                "/play".to_string(),
            )),
            TextDecision::Open { key, err } => Some((
                if err.is_none() { "routed" } else { "refused" },
                err.as_ref()
                    .map(|e| format!("open_failed: {e}"))
                    .unwrap_or_default(),
                AuditOutcome::None,
                Some(key.clone()),
                "/open".to_string(),
            )),
            TextDecision::GameStatus { key, inspected } => Some((
                if *inspected { "routed" } else { "refused" },
                if *inspected {
                    String::new()
                } else {
                    "game_status_unavailable".to_string()
                },
                AuditOutcome::None,
                key.clone(),
                "/status".to_string(),
            )),
            TextDecision::Press { cmd, press } => {
                let (kind, reason, outcome, offering) = press.audit_parts();
                Some((kind, reason, outcome, offering, cmd.clone()))
            }
            TextDecision::MenuFailed { why } => Some((
                "error",
                format!("menu_send_failed: {why}"),
                AuditOutcome::None,
                None,
                "/offerings".to_string(),
            )),
            TextDecision::Cancelled { cleared } => Some((
                "routed",
                format!("cancelled: {}", cleared.join(",")),
                AuditOutcome::None,
                None,
                "/cancel".to_string(),
            )),
            TextDecision::Closed { key, closed } => Some((
                if *closed { "routed" } else { "refused" },
                if *closed {
                    "closed_and_forgot_log".to_string()
                } else {
                    "no_such_session".to_string()
                },
                AuditOutcome::None,
                Some(key.clone()),
                "/close".to_string(),
            )),
            TextDecision::Usage { cmd } => Some((
                "refused",
                "usage".to_string(),
                AuditOutcome::None,
                None,
                cmd.clone(),
            )),
            TextDecision::Unknown { cmd } => Some((
                "refused",
                "unknown_command".to_string(),
                AuditOutcome::None,
                None,
                cmd.clone(),
            )),
            // Free text routed into a pending text affordance — the press's own decision, under
            // a `text` input kind (design §8: user free text IS the trail).
            TextDecision::TextInput { press } => {
                let (kind, reason, outcome, offering) = press.audit_parts();
                Some((kind, reason, outcome, offering, "text".to_string()))
            }
            TextDecision::Ignored => None,
        }
    }
}

/// **Route a `web_app_data` payload** — what a Mini App sent back via
/// `Telegram.WebApp.sendData`. The payload is CLIENT-AUTHORED and untrusted: it can never name
/// an identity (the acting identity derives from the Telegram `uid` the update itself
/// attributes, exactly as a button press) and never bypasses a gate. A payload in the ONE
/// affordance codec (`turn:arg` — [`decode_callback`]) is routed as a synthetic press through
/// [`route_callback`], so it faces the same presented-affordance check + the same executor
/// refereeing as any button; anything else is acknowledged honestly and dropped. Returns the
/// human reply.
pub fn route_web_app_data<T: Transport>(
    host: &mut TelegramHost<T>,
    chat_id: ChatId,
    topic: Option<i64>,
    uid: TelegramUserId,
    data: &str,
) -> String {
    route_web_app_data_decided(host, chat_id, topic, uid, data).0
}

/// The machine account of a routed `web_app_data` payload.
#[derive(Debug, Clone)]
pub enum WebAppDecision {
    /// The payload decoded in the ONE affordance codec and routed as a synthetic press.
    Press(PressDecision),
    /// The payload decoded as nothing — acknowledged-and-dropped (client-authored, untrusted).
    Dropped {
        /// The payload length (the payload itself is client-authored noise; the length is the
        /// honest record).
        len: usize,
    },
}

/// [`route_web_app_data`] plus the machine [`WebAppDecision`] — the audit-emitting caller's
/// form.
pub fn route_web_app_data_decided<T: Transport>(
    host: &mut TelegramHost<T>,
    chat_id: ChatId,
    topic: Option<i64>,
    uid: TelegramUserId,
    data: &str,
) -> (String, WebAppDecision) {
    if decode_callback(data).is_some() {
        let (ack, press) = route_callback_decided(
            host,
            CallbackQuery {
                chat_id,
                message_thread_id: topic,
                // A Mini App round-trip names no message — the chat's most recent surface.
                message_id: None,
                from_user_id: uid,
                data: data.to_string(),
            },
        );
        (ack, WebAppDecision::Press(press))
    } else {
        (
            format!(
                "Mini App sent {} byte(s) — no affordance decoded, nothing landed. State-changing \
                 turns land through the app's own verified channel.",
                data.len()
            ),
            WebAppDecision::Dropped { len: data.len() },
        )
    }
}

/// The human account of a routed press — what the presser's ack toast says.
pub fn describe_press(press: HostPress) -> String {
    match press {
        HostPress::Opened(key) => format!("Opened {key}."),
        HostPress::Advanced {
            outcome: Outcome::Landed { receipt, ended },
            ..
        } => format!(
            "Turn landed · {}",
            PlayerTurnReceipt::from_landed(&receipt, ended)
                .compact_text(PlayerReplaySurface::Telegram)
        ),
        HostPress::Advanced {
            outcome: Outcome::Refused(why),
            ..
        } => format!("Refused by the executor: {why}"),
        HostPress::Verified { key, report } => describe_verify(&key, report.as_ref()),
        HostPress::TextArmed { action, .. } => format!(
            "Selected \"{}\" — now send your text and I will fill it in.",
            action.label
        ),
        // The privacy redirect IS the ack (and, being long, the loop also lands it in the chat).
        HostPress::OpenRefused { why, .. } => why,
        HostPress::NotOffered => {
            // Name the way out. A refusal that only says "stale keyboard?" leaves the presser
            // with no next move, which is how a chat reads as broken rather than as refused.
            "That button is not on the current surface (a stale keyboard?). Send /offerings for \
             a fresh menu, or /cancel to clear this chat."
                .to_string()
        }
        HostPress::NoSession => "No session in this chat yet — send /offerings.".to_string(),
    }
}

/// Human rendering of a game-session view. Shared views first cross the typed no-viewer
/// projection; only a DM-private view may render the host-rich diagnostic fields.
pub fn describe_game_status(status: &TelegramGameStatus) -> String {
    if !status.private_projection {
        return match status.shared_projection() {
            Ok(shared) => describe_shared_game_status(&shared),
            Err(_) => {
                "Game record unavailable: the shared publication boundary refused this projection."
                    .to_string()
            }
        };
    }
    let audience = if status.private_projection {
        if status.hidden_information {
            "private single-reader projection (player-only state may appear in the game message)"
        } else {
            "private single-reader projection"
        }
    } else {
        "shared viewer-blind projection"
    };
    let operations = if status.proof_operations.is_empty() {
        "none currently advertised".to_string()
    } else {
        status.proof_operations.join(", ")
    };
    let artifacts = if status.artifacts.is_empty() {
        "none currently advertised".to_string()
    } else {
        status.artifacts.join(", ")
    };
    format!(
        "Game record · {} / {}\n\
         Session · {}\n\
         Audience · {}\n\
         Record · {} · {} verified turn(s) · {} landed step(s) · {}\n\
         Affordances · {} ordinary turn(s)\n\
         Proof operations · {}\n\
         Read-only artifacts · {}\n\
         Replay recipe · {} (process durability depends on the mounted session store)",
        status.key,
        status.kind,
        status.session.0,
        audience,
        if status.verified {
            "VERIFIED"
        } else {
            "FAILED"
        },
        status.verified_turns,
        status.landed_steps,
        status.verification_detail,
        status.turn_affordances,
        operations,
        artifacts,
        if status.replay_recipe {
            "complete"
        } else {
            "unavailable"
        },
    )
}

/// Render status under the actual Telegram readership classification.
///
/// The host normally derives `private_projection` from this same chat address. Rechecking it at
/// the final formatter means a future host regression cannot route a rich DM projection into a
/// group merely by setting the wrong flag on the returned object.
pub fn describe_game_status_for_chat(
    status: &TelegramGameStatus,
    chat_id: ChatId,
    topic: Option<i64>,
) -> String {
    if ChatKind::classify(chat_id, topic).is_collective() {
        return match status.shared_projection() {
            Ok(shared) => describe_shared_game_status(&shared),
            Err(_) => {
                "Game record unavailable: the shared publication boundary refused this projection."
                    .to_string()
            }
        };
    }
    describe_game_status(status)
}

/// Render the deliberately small grammar accepted in a group or forum topic.
///
/// Operation and artifact names, verification diagnostics, public-field values, raw session
/// routes, actors, heads, payloads, and concrete receipt internals are unrepresentable here. The
/// full receipt and publication commitments remain copyable audit joins.
pub fn describe_shared_game_status(status: &TelegramSharedGameStatus) -> String {
    let latest = match &status.latest_receipt {
        None => "Latest public receipt · none since this bot process started".to_string(),
        Some(receipt) if receipt.validate().is_err() || receipt.kind != status.kind => {
            "Latest public receipt · unavailable (viewer-blind binding refused)".to_string()
        }
        Some(receipt) => {
            let attribution = match receipt.attribution {
                PublicGameAttribution::Signed => "signed",
                PublicGameAttribution::Asserted => "adapter-asserted",
            };
            let result = match &receipt.result {
                PublicGameReceiptResult::Turn { ended } => {
                    if *ended {
                        "ordinary turn · session complete".to_string()
                    } else {
                        "ordinary turn · session continues".to_string()
                    }
                }
                PublicGameReceiptResult::Operation { fields } => format!(
                    "shielded/proven operation · {} audited public field(s) withheld from chat",
                    fields.len()
                ),
            };
            format!(
                "Latest public receipt · {result} · {attribution}\n\
                 Session route · {}\n\
                 Receipt · {}\n\
                 Publication · {}",
                audit::hex32(&receipt.session_route_id),
                audit::hex32(&receipt.receipt_id),
                audit::hex32(&receipt.publication_id),
            )
        }
    };
    format!(
        "Game record · {}\n\
         Audience · shared viewer-blind projection\n\
         Record · {} · {} verified turn(s) · {} landed step(s)\n\
         Affordances · {} ordinary turn(s) · {} shielded/proven operation(s) · {} read-only artifact(s)\n\
         Replay recipe · {} (process durability depends on the mounted session store)\n\
         {}",
        status.kind.as_str(),
        if status.verified {
            "VERIFIED"
        } else {
            "FAILED"
        },
        status.verified_turns,
        status.landed_steps,
        status.affordances.ordinary_turns,
        status.affordances.shielded_operations,
        status.affordances.read_only_artifacts,
        if status.replay_recipe {
            "complete"
        } else {
            "unavailable"
        },
        latest,
    )
}

/// Minimal immediate acknowledgement after a proven operation lands in a multi-reader chat.
/// Detailed result values remain available only to an explicitly private surface.
pub fn describe_shared_game_operation_landed(status: &TelegramSharedGameStatus) -> String {
    let Some(receipt) = status.latest_receipt.as_ref() else {
        return "Shielded/proven operation landed. /status inspects the viewer-blind record."
            .to_string();
    };
    if receipt.validate().is_err() || receipt.kind != status.kind {
        return "Shielded/proven operation landed. The viewer-blind receipt binding was refused."
            .to_string();
    }
    describe_shared_game_receipt_landed(receipt)
}

/// Immediate multi-reader acknowledgement from the exact viewer-blind receipt returned by the
/// host boundary. No rich status or direct operation receipt is accepted by this formatter.
pub fn describe_shared_game_receipt_landed(receipt: &PublicGameReceipt) -> String {
    if receipt.validate().is_err() {
        return "Shielded/proven operation landed. The viewer-blind receipt binding was refused."
            .to_string();
    }
    if !matches!(&receipt.result, PublicGameReceiptResult::Operation { .. }) {
        return "Shielded/proven operation landed. /status inspects the viewer-blind record."
            .to_string();
    }
    format!(
        "Shielded/proven operation landed · receipt {} · publication {}. /status inspects the viewer-blind record.",
        audit::hex32(&receipt.receipt_id),
        audit::hex32(&receipt.publication_id),
    )
}

/// The human account of a re-verification.
pub fn describe_verify(key: &str, report: Option<&VerifyReport>) -> String {
    match report {
        Some(r) if r.verified => format!(
            "{key}: {} turn(s) re-verified by replay — {}",
            r.turns, r.detail
        ),
        Some(r) => format!(
            "{key}: VERIFY FAILED after {} turn(s) — {}",
            r.turns, r.detail
        ),
        None => format!("{key} exposes no verifier."),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The durable host + the forever loop
// ─────────────────────────────────────────────────────────────────────────────

/// **The full shared catalog over a durable session store** — the host build the bin ships to
/// [`TelegramHost::with_host`]'s owning thread. With a `dir`: opens a
/// [`FileResumeStore`](dreggnet_offerings::FileResumeStore) there, attaches it (every session
/// open + landed advance + signed-replay floor is written through as a move-log), and
/// boot-resumes every persisted session by REPLAY — the identical committed state, or a
/// fail-closed refusal for a tampered log (logged; the file is kept as evidence). An unopenable
/// dir degrades to the in-memory host with a loud warning (the bot still boots; sessions are
/// ephemeral) — the same posture as `dreggnet-web`'s `demo_host_over`. The shipped bot uses
/// [`try_durable_telegram_host`] instead, because durable game state and durable routing epochs
/// must either boot together or not boot at all. `None` → in-memory.
pub fn durable_telegram_host(dir: Option<PathBuf>, council_members: Vec<[u8; 32]>) -> OfferingHost {
    let host = telegram_default_host(council_members);
    let Some(dir) = dir else {
        return host;
    };
    match attach_durable_telegram_store(host, &dir) {
        Ok(host) => host,
        Err((host, error)) => {
            eprintln!(
                "WARN: {error} — sessions stay IN-MEMORY (a restart \
                 drops them)",
            );
            host
        }
    }
}

/// Build the shared catalog over a required durable move-log store.
///
/// Unlike [`durable_telegram_host`], an unopenable store is returned as a boot
/// error. The production binary uses this constructor so it can never retain a
/// durable game-incarnation ledger while silently forgetting the concrete game
/// state that incarnation names.
pub fn try_durable_telegram_host(
    dir: PathBuf,
    council_members: Vec<[u8; 32]>,
) -> Result<OfferingHost, String> {
    attach_durable_telegram_store(telegram_default_host(council_members), &dir)
        .map_err(|(_, error)| error)
}

/// Required-durability production host with the explicitly configured private
/// Bazaar offering mounted before replay. Registering first is load-bearing:
/// persisted Enter moves can then reconstruct the hosted market/journey and
/// repopulate the deployment's fresh process-local worker registry.
#[cfg(feature = "private-bazaar-live")]
pub fn try_durable_telegram_host_with_private_bazaar(
    dir: PathBuf,
    council_members: Vec<[u8; 32]>,
    deployment: &dreggnet_catalog::PrivateBazaarLiveDeployment,
) -> Result<OfferingHost, String> {
    let host = dreggnet_catalog::full_catalog_host_with_private_bazaar(
        // Live day binding, as `telegram_default_host` — see `host::arm_todays_descent_day`.
        &dreggnet_catalog::CatalogConfig::live(council_members),
        deployment,
    )
    // Bounded session lifecycle, as `telegram_default_host` — armed BEFORE the store attaches
    // (so boot-resumed sessions get last-touched stamps) and never born unbounded.
    .with_policy(
        crate::host::resolve_telegram_policy(),
        dreggnet_offerings::SystemClock,
    );
    attach_durable_telegram_store(host, &dir).map_err(|(_, error)| error)
}

fn attach_durable_telegram_store(
    mut host: OfferingHost,
    dir: &std::path::Path,
) -> Result<OfferingHost, (OfferingHost, String)> {
    let store = match FileResumeStore::open(dir) {
        Ok(store) => store,
        Err(error) => {
            return Err((
                host,
                format!("cannot open session dir {}: {error}", dir.display()),
            ));
        }
    };
    host = host.with_resume_store(Box::new(store));
    let results = host.resume_all();
    let resumed = results.iter().filter(|(_, result)| result.is_ok()).count();
    let refused = results.len() - resumed;
    eprintln!(
        "session store {} attached: {resumed} session(s) resumed by move-log replay, \
         {refused} refused",
        dir.display()
    );
    for (log, outcome) in &results {
        if let Err(error) = outcome {
            eprintln!(
                "  REFUSED (fail-closed; file kept): {}/{}: {error}",
                log.key, log.id.0
            );
        }
        // The boot-resume decision, durably (design §2.2: today stderr-only) — one
        // `resume` event per persisted log, routed (resumed) or refused (fail-closed).
        let event = AuditEvent::new(
            "telegram",
            Actor::system("boot-resume"),
            Surface::Resume,
            Input::new("resume", json!({ "store": dir.display().to_string() })),
        )
        .in_session(Some(log.key.clone()), Some(log.id.0.clone()));
        audit::log().emit(match outcome {
            Ok(_) => event.decided("routed", ""),
            Err(error) => {
                event
                    .decided("refused", "resume_failed")
                    .with_outcome(AuditOutcome::Error {
                        what: error.to_string(),
                    })
            }
        });
    }
    Ok(host)
}

/// **The per-identity RPG worlds registry over a durable session store** — the per-player half of
/// the catalog (the eight `is_rpg_key` surfaces), the companion to [`durable_telegram_host`]. With
/// a `dir`: each identity's world attaches a durable [`FileResumeStore`] under a PER-IDENTITY
/// subdirectory (`<dir>/players/<blake3(identity)>`), so a player's forge / inventory / trade
/// survive a restart by move-log replay — the same durability the shared game sessions get, and the
/// same per-player scoping Discord's `SqliteRpgResumeStore` gives (there by SQL row, here by
/// directory). The subdirectory is the ONE thing the isolation guarantee rests on: no identity's
/// host ever sees another's logs. `None` (or an unopenable dir) → that world stays in memory.
pub fn durable_player_worlds(dir: Option<PathBuf>) -> PlayerWorlds {
    let Some(root) = dir else {
        return PlayerWorlds::new();
    };
    let players_root = root.join("players");
    PlayerWorlds::with_store(move |identity| {
        // A per-identity subdirectory, named by a hash of the identity so any identity string maps
        // to a safe, collision-resistant directory.
        let sub = players_root.join(blake3::hash(identity.as_bytes()).to_hex().as_str());
        match FileResumeStore::open(&sub) {
            Ok(store) => Some(Box::new(store) as Box<dyn SessionResumeStore>),
            Err(e) => {
                eprintln!(
                    "WARN: cannot open per-identity RPG world store {}: {e} — that world stays IN-MEMORY",
                    sub.display()
                );
                None
            }
        }
    })
}

/// **The forever loop**: long-poll `getUpdates`, decode, route every event through the ONE
/// router, ack. A transport error backs off 5s and re-polls (the loop must outlive flaky
/// networks); `persist_offset` is called with each new offset so a restart does not replay
/// already-routed updates (the bin writes it beside the session store).
pub fn run_update_loop<T: Transport, H: HttpPost>(
    host: &mut TelegramHost<T>,
    api: &BotApi<H>,
    mut offset: Option<i64>,
    mut persist_offset: impl FnMut(i64),
) {
    loop {
        let result = match api.get_updates(offset) {
            Ok(v) => v,
            Err(e) => {
                eprintln!("getUpdates failed: {e} — retrying in 5s");
                std::thread::sleep(std::time::Duration::from_secs(5));
                continue;
            }
        };
        let (events, next) = parse_updates(&result);
        if let Some(n) = next {
            offset = Some(n);
            persist_offset(n);
        }
        for ev in events {
            match ev {
                BotEvent::Callback { callback_id, query } => {
                    let (chat, topic) = (query.chat_id, query.message_thread_id);
                    // AUDIT EMIT (ingress + outcome, one stack frame): the press's envelope —
                    // who (custodial uid → derived identity), what (callback_data), the
                    // decision taxonomy, and the receipt-chain join on a landed turn.
                    let sid = TelegramFrontend::<T>::session_id(chat, topic);
                    let actor = Actor::custodial(
                        query.from_user_id.to_string(),
                        host.identity(query.from_user_id).0,
                    );
                    let data = query.data.clone();
                    let (ack, decision) = route_callback_decided(host, query);
                    let (kind, reason, outcome, offering) = decision.audit_parts();
                    audit::log().emit(
                        AuditEvent::new(
                            "telegram",
                            actor,
                            Surface::Callback,
                            Input::new("callback", json!({ "callback_data": data })),
                        )
                        .in_session(offering, Some(sid.0.clone()))
                        .decided(kind, reason)
                        .with_outcome(outcome),
                    );
                    if let Err(e) = api.answer_callback(&callback_id, &ack) {
                        eprintln!("answerCallbackQuery failed: {e}");
                    }
                    // A long ack (a verify report, an executor refusal with detail) does not fit
                    // a 200-char toast — also land it in the chat.
                    if ack.len() > 180 {
                        if let Err(e) = api.send_text(chat, topic, &ack) {
                            eprintln!("sendMessage (long ack) failed: {e}");
                        }
                    }
                }
                BotEvent::Text {
                    chat_id,
                    topic,
                    uid,
                    text,
                } => {
                    let sid = TelegramFrontend::<T>::session_id(chat_id, topic);
                    let actor = Actor::custodial(uid.to_string(), host.identity(uid).0);
                    let (reply, decision) = route_text_decided(host, chat_id, topic, uid, &text);
                    // AUDIT EMIT: every routed command (ordinary chatter maps to None — not an
                    // interaction). User free text IS the trail (§8); no /key-class command
                    // exists on this surface.
                    if let Some((kind, reason, outcome, offering, input_kind)) =
                        decision.audit_parts()
                    {
                        audit::log().emit(
                            AuditEvent::new(
                                "telegram",
                                actor,
                                Surface::Command,
                                Input::new(&*input_kind, json!({ "text": text })),
                            )
                            .in_session(offering, Some(sid.0.clone()))
                            .decided(kind, reason)
                            .with_outcome(outcome),
                        );
                    }
                    if let Some(reply) = reply {
                        if let Err(e) = api.send_text(chat_id, topic, &reply) {
                            eprintln!("sendMessage failed: {e}");
                        }
                    }
                }
                BotEvent::WebAppData {
                    chat_id,
                    topic,
                    uid,
                    data,
                    ..
                } => {
                    let sid = TelegramFrontend::<T>::session_id(chat_id, topic);
                    let actor = Actor::custodial(uid.to_string(), host.identity(uid).0);
                    let (reply, decision) =
                        route_web_app_data_decided(host, chat_id, topic, uid, &data);
                    // AUDIT EMIT: the Mini App sendData round-trip — routed as a synthetic
                    // press, or acknowledged-and-dropped (client-authored, untrusted).
                    let (kind, reason, outcome, offering) = match &decision {
                        WebAppDecision::Press(p) => p.audit_parts(),
                        WebAppDecision::Dropped { .. } => (
                            "refused",
                            "no_affordance_decoded".to_string(),
                            AuditOutcome::None,
                            None,
                        ),
                    };
                    audit::log().emit(
                        AuditEvent::new(
                            "telegram",
                            actor,
                            Surface::WebAppData,
                            Input::new("web_app_data", json!({ "data": data, "len": data.len() })),
                        )
                        .in_session(offering, Some(sid.0.clone()))
                        .decided(kind, reason)
                        .with_outcome(outcome),
                    );
                    if let Err(e) = api.send_text(chat_id, topic, &reply) {
                        eprintln!("sendMessage (web_app_data reply) failed: {e}");
                    }
                }
                BotEvent::Document {
                    chat_id,
                    topic,
                    uid,
                    file_id,
                    declared_bytes,
                    caption,
                } => {
                    let sid = TelegramFrontend::<T>::session_id(chat_id, topic);
                    let actor = Actor::custodial(uid.to_string(), host.identity(uid).0);
                    let (reply, decision, offering) = match parse_operation_caption(&caption) {
                        None => (
                            "To apply a canonical producer receipt, attach it with the exact caption `/operation <name>` shown in the proof-operation guide. Most operations require a private chat; the guide names any exact shared-session exception. No file was downloaded."
                                .to_string(),
                            ("refused", "operation_caption_missing"),
                            None,
                        ),
                        Some(name) => match host.preflight_operation(
                            chat_id,
                            topic,
                            uid,
                            name,
                            declared_bytes,
                        ) {
                            Err(error) => (
                                format!("Receipt not accepted: {error}. No file was downloaded."),
                                ("refused", "operation_preflight_refused"),
                                None,
                            ),
                            Ok(route) => {
                                let key = route.key.clone();
                                match api.download_document(
                                    &file_id,
                                    route.policy.declared_bytes,
                                    route.policy.transport_max_bytes,
                                ) {
                                    Err(error) => (
                                        format!("Receipt transport failed: {error}"),
                                        ("error", "operation_download_failed"),
                                        Some(key),
                                    ),
                                    Ok(payload) => match host.apply_operation(route, payload) {
                                        Err(error) => (
                                            format!(
                                                "The operation verifier refused the receipt: {error}"
                                            ),
                                            ("refused", "operation_refused"),
                                            Some(key),
                                        ),
                                        Ok(applied) => match applied {
                                            TelegramAppliedOperation::SharedGame(receipt) => (
                                                describe_shared_game_receipt_landed(&receipt),
                                                ("routed", ""),
                                                Some(key),
                                            ),
                                            TelegramAppliedOperation::SharedGameUnpublished => (
                                                "Shielded/proven operation landed. The shared publication is temporarily unavailable; /status will retry the viewer-blind record."
                                                    .to_string(),
                                                ("routed", ""),
                                                Some(key),
                                            ),
                                            TelegramAppliedOperation::Direct(_)
                                                if ChatKind::classify(chat_id, topic)
                                                    .is_collective() =>
                                            {
                                                (
                                                    "The operation landed, but Telegram refused a direct receipt at the shared-chat boundary. /status will retry the viewer-blind record."
                                                        .to_string(),
                                                    ("error", "shared_operation_direct_receipt"),
                                                    Some(key),
                                                )
                                            }
                                            TelegramAppliedOperation::Direct(receipt) => {
                                                let fields = receipt
                                                    .public_fields
                                                    .iter()
                                                    .map(|(name, value)| {
                                                        format!("{name}={value}")
                                                    })
                                                    .collect::<Vec<_>>()
                                                    .join(" · ");
                                                (
                                                    format!(
                                                        "Applied `{}` · receipt {}{}",
                                                        receipt.operation,
                                                        audit::hex32(&receipt.receipt_id),
                                                        if fields.is_empty() {
                                                            String::new()
                                                        } else {
                                                            format!(" · {fields}")
                                                        }
                                                    ),
                                                    ("routed", ""),
                                                    Some(key),
                                                )
                                            }
                                        },
                                    },
                                }
                            }
                        },
                    };
                    audit::log().emit(
                        AuditEvent::new(
                            "telegram",
                            actor,
                            Surface::Command,
                            Input::new(
                                "operation_attachment",
                                json!({
                                    "declared_bytes": declared_bytes,
                                    "caption_valid": parse_operation_caption(&caption).is_some(),
                                }),
                            ),
                        )
                        .in_session(offering, Some(sid.0.clone()))
                        .decided(decision.0, decision.1),
                    );
                    if let Err(e) = api.send_text(chat_id, topic, &reply) {
                        eprintln!("sendMessage (operation reply) failed: {e}");
                    }
                }
            }
        }
    }
}
