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
//!   text command, or a Mini App `web_app_data` round-trip), plus the next long-poll offset.
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

use dreggnet_offerings::{FileResumeStore, OfferingHost, Outcome, VerifyReport};

use crate::api::{decode_callback, encode_callback};
use crate::host::{HostPress, TURN_VERIFY, TelegramHost, telegram_default_host};
use crate::transport::{HttpPost, Transport, TransportError};
use crate::{CallbackQuery, ChatId, TelegramFrontend, TelegramUserId};

/// How long the server holds a `getUpdates` long poll open (seconds). The Bot API allows up to
/// ~50; the HTTP client timeout ([`crate::reqwest_transport`]) sits above this.
pub const POLL_TIMEOUT_SECS: u64 = 50;

/// The Bot API cap on an `answerCallbackQuery` toast text.
const CALLBACK_ANSWER_MAX: usize = 200;

/// The `/help` (and `/start`) text — the shell's whole command surface, honestly enumerated.
pub const HELP_TEXT: &str = "DreggNet Cloud — every move is a real, verifiable executor turn.\n\
    /offerings — list the catalog (press a button to open one)\n\
    /open <key> — open an offering in this chat (e.g. /open dungeon)\n\
    /play — Mini App launch buttons: the rich web surface, per offering (DMs only)\n\
    /verify — re-verify this chat's committed chain by replay\n\
    /act <turn> <arg> — fire a value-taking turn (e.g. /act bid 500)\n\
    /help — this text\n\
    A group chat plays as a collective; a DM plays solo. Sessions survive bot restarts.";

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
}

// ─────────────────────────────────────────────────────────────────────────────
// Update decoding (pure — driven directly by the tests with real Bot API JSON)
// ─────────────────────────────────────────────────────────────────────────────

/// One decoded incoming update the shell routes — a button press or a text message.
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

// ─────────────────────────────────────────────────────────────────────────────
// Routing (one event → the ONE TelegramHost router → a human ack)
// ─────────────────────────────────────────────────────────────────────────────

/// **Route a button press through the host**, with the RESTART-RESUME path: if the chat answers
/// [`HostPress::NoSession`] (this process never presented there) but the chat's session was
/// durably RESUMED on boot, rebind it ([`TelegramHost::resume_chat`]), re-present the live
/// surface ([`TelegramHost::open`] — idempotent, the resumed state is kept), and retry the press
/// once against the fresh keyboard. Returns the human ack for `answerCallbackQuery`.
pub fn route_callback<T: Transport>(host: &mut TelegramHost<T>, query: CallbackQuery) -> String {
    match host.press(query.clone()) {
        HostPress::NoSession => {
            let sid = TelegramFrontend::<T>::session_id(query.chat_id, query.message_thread_id);
            let Some(key) = host.resume_chat(&sid) else {
                return "No session in this chat yet — send /offerings to pick one.".to_string();
            };
            if host
                .open(
                    &key,
                    query.chat_id,
                    query.message_thread_id,
                    query.from_user_id,
                )
                .is_err()
            {
                return format!("Could not reopen {key} — send /offerings.");
            }
            describe_press(host.press(query))
        }
        press => describe_press(press),
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
    let text = text.trim();
    let (cmd, rest) = match text.split_once(char::is_whitespace) {
        Some((c, r)) => (c, r.trim()),
        None => (text, ""),
    };
    // In a group, commands arrive suffixed with the bot's username: `/open@MyBot dungeon`.
    let cmd = cmd.split('@').next().unwrap_or(cmd);
    match cmd {
        "/start" | "/help" => Some(HELP_TEXT.to_string()),
        "/offerings" | "/menu" => {
            host.present_offerings_menu(chat_id, topic);
            None
        }
        // The Mini App launch tier: a menu of `web_app` buttons opening the rich web surface,
        // one per offering. `Err` is the honest human reply (tier unarmed / group chat —
        // Telegram only honors `web_app` inline buttons in DMs / a transport failure).
        "/play" | "/webapp" => match host.present_play_menu(chat_id, topic) {
            Ok(()) => None, // the launch menu IS the reply
            Err(why) => Some(why),
        },
        "/open" => {
            if rest.is_empty() {
                return Some("Usage: /open <key> — see /offerings for the catalog.".to_string());
            }
            match host.open(rest, chat_id, topic, uid) {
                Ok(_) => None, // the opened surface IS the reply
                Err(e) => Some(format!("Cannot open {rest}: {e}")),
            }
        }
        // `/verify` and `/act` mint the same synthetic press a pinned button would — the ONE
        // router (with the restart-resume path) handles both.
        "/verify" => Some(route_callback(
            host,
            CallbackQuery {
                chat_id,
                message_thread_id: topic,
                from_user_id: uid,
                data: encode_callback(TURN_VERIFY, 0),
            },
        )),
        "/act" => {
            let usage = "Usage: /act <turn> <arg> — e.g. /act bid 500".to_string();
            let Some((turn, arg)) = rest.split_once(char::is_whitespace) else {
                return Some(usage);
            };
            let Ok(arg) = arg.trim().parse::<i64>() else {
                return Some(usage);
            };
            Some(route_callback(
                host,
                CallbackQuery {
                    chat_id,
                    message_thread_id: topic,
                    from_user_id: uid,
                    data: encode_callback(turn, arg),
                },
            ))
        }
        _ => None,
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
    if decode_callback(data).is_some() {
        route_callback(
            host,
            CallbackQuery {
                chat_id,
                message_thread_id: topic,
                from_user_id: uid,
                data: data.to_string(),
            },
        )
    } else {
        format!(
            "Mini App sent {} byte(s) — no affordance decoded, nothing landed. State-changing \
             turns land through the app's own verified channel.",
            data.len()
        )
    }
}

/// The human account of a routed press — what the presser's ack toast says.
pub fn describe_press(press: HostPress) -> String {
    match press {
        HostPress::Opened(key) => format!("Opened {key}."),
        HostPress::Advanced {
            outcome: Outcome::Landed { ended, .. },
            ..
        } => {
            if ended {
                "Turn landed — session complete. /verify replays the whole chain.".to_string()
            } else {
                "Turn landed — one real verified receipt.".to_string()
            }
        }
        HostPress::Advanced {
            outcome: Outcome::Refused(why),
            ..
        } => format!("Refused by the executor: {why}"),
        HostPress::Verified { key, report } => describe_verify(&key, report.as_ref()),
        HostPress::NotOffered => {
            "That button is not on the current surface (a stale keyboard?).".to_string()
        }
        HostPress::NoSession => "No session in this chat yet — send /offerings.".to_string(),
    }
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
/// ephemeral) — the same posture as `dreggnet-web`'s `demo_host_over`. `None` → in-memory.
pub fn durable_telegram_host(dir: Option<PathBuf>, council_members: Vec<[u8; 32]>) -> OfferingHost {
    let mut host = telegram_default_host(council_members);
    let Some(dir) = dir else {
        return host;
    };
    match FileResumeStore::open(&dir) {
        Ok(store) => {
            host = host.with_resume_store(Box::new(store));
            let results = host.resume_all();
            let resumed = results.iter().filter(|(_, r)| r.is_ok()).count();
            let refused = results.len() - resumed;
            eprintln!(
                "session store {} attached: {resumed} session(s) resumed by move-log replay, \
                 {refused} refused",
                dir.display()
            );
            for (log, outcome) in &results {
                if let Err(e) = outcome {
                    eprintln!(
                        "  REFUSED (fail-closed; file kept): {}/{}: {e}",
                        log.key, log.id.0
                    );
                }
            }
        }
        Err(e) => {
            eprintln!(
                "WARN: cannot open session dir {}: {e} — sessions stay IN-MEMORY (a restart \
                 drops them)",
                dir.display()
            );
        }
    }
    host
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
                    let ack = route_callback(host, query);
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
                    if let Some(reply) = route_text(host, chat_id, topic, uid, &text) {
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
                    let reply = route_web_app_data(host, chat_id, topic, uid, &data);
                    if let Err(e) = api.send_text(chat_id, topic, &reply) {
                        eprintln!("sendMessage (web_app_data reply) failed: {e}");
                    }
                }
            }
        }
    }
}
