//! **The Mini App LAUNCH tier** — pure composition of the `web_app` inline buttons that open the
//! rich web surface (`dreggnet-web`'s `/tg` Mini App routes, docs/TELEGRAM-MINIAPP-DESIGN.md)
//! for an offering/session, beside the existing inline-button tier (which stays the lightweight
//! fallback — every offering remains fully playable without the web-view).
//!
//! Everything here is PURE (no env reads except the one named resolver, no network): the URL a
//! Play button carries is `{TELEGRAM_WEBAPP_BASE}/tg/offerings/{key}/session/{sid}` — the funnel
//! base plus the design's pinned Mini App deep path, so tapping it opens the web surface for
//! THAT offering + the SAME chat-scoped session id this bot names its sessions by.
//!
//! **Telegram's rule, honored not fought:** `web_app` INLINE buttons only work in PRIVATE chats
//! (a group/supergroup send with one is refused by the Bot API). [`web_app_allowed`] is the one
//! gate; a group gets the honest text fallback instead of a broken send.
//!
//! **Identity note (why the launch button carries NO identity):** the Mini App page derives the
//! trusted Telegram identity from the HMAC-validated `initData` Telegram itself injects into the
//! web-view — the URL never carries a uid, and nothing a client could edit in it is trusted
//! (the design's hard rule).

use dreggnet_offerings::{OfferingInfo, SessionId};

use crate::ChatId;
use crate::api::{InlineKeyboardButton, InlineKeyboardMarkup, SendMessageRequest};

/// The env var naming the public HTTPS base the Mini App is served from (the tailscale funnel).
pub const WEBAPP_BASE_ENV: &str = "TELEGRAM_WEBAPP_BASE";

/// The default Mini App base — the hbox funnel the web catalog is already public on.
pub const DEFAULT_WEBAPP_BASE: &str = "https://hbox-dregg.skunk-emperor.ts.net";

/// The label on a session surface's "open this in the rich web surface" launch button.
pub const PLAY_IN_APP_LABEL: &str = "🕹 Play in the app";

/// Resolve the Mini App base URL: [`WEBAPP_BASE_ENV`] (trimmed, trailing `/` stripped) when set
/// and non-empty, else [`DEFAULT_WEBAPP_BASE`]. The bin calls this once at startup.
pub fn webapp_base_from_env() -> String {
    std::env::var(WEBAPP_BASE_ENV)
        .ok()
        .map(|s| s.trim().trim_end_matches('/').to_string())
        .filter(|s| !s.is_empty())
        .unwrap_or_else(|| DEFAULT_WEBAPP_BASE.to_string())
}

/// Whether Telegram will accept a `web_app` INLINE button in this chat: PRIVATE chats only
/// (a positive chat id, no forum topic). Groups get the text fallback — an inline `web_app`
/// button in a group is refused by the Bot API itself.
pub fn web_app_allowed(chat_id: ChatId, topic: Option<i64>) -> bool {
    chat_id > 0 && topic.is_none()
}

/// The Mini App deep URL for `(key, session)` — the funnel `base` + the design-pinned
/// `/tg/offerings/{key}/session/{id}` path the web lane serves. The session id is the SAME
/// chat-scoped id this bot names the session by (`tg:{chat_id}`), so the web surface names the
/// same logical session.
pub fn play_url(base: &str, key: &str, session: &SessionId) -> String {
    format!(
        "{}/tg/offerings/{}/session/{}",
        base.trim_end_matches('/'),
        key,
        session.0
    )
}

/// The per-offering **Play launch button** — a [`InlineKeyboardButton::web_app`] carrying
/// [`play_url`]. Appended (by the host) as a trailing row under an offering's presented
/// affordances in a DM; never an offering [`Action`](dreggnet_offerings::Action), so it is never
/// matched by `collect` and never reaches the executor.
pub fn play_button(base: &str, key: &str, session: &SessionId) -> InlineKeyboardButton {
    InlineKeyboardButton::web_app(PLAY_IN_APP_LABEL, play_url(base, key, session))
}

/// **Build the `/play` control message** — one `web_app` launch button per registered offering,
/// each deep-linking the rich web surface for that offering at this chat's session id. A control
/// message like the `/offerings` menu, but its buttons LAUNCH (no callbacks), so it needs no
/// session-slot bookkeeping. Pure; the caller has already gated on [`web_app_allowed`].
pub fn build_play_menu_request(
    chat_id: ChatId,
    topic: Option<i64>,
    base: &str,
    session: &SessionId,
    offerings: &[OfferingInfo],
) -> SendMessageRequest {
    let rows = offerings
        .iter()
        .map(|o| {
            vec![InlineKeyboardButton::web_app(
                format!("🕹 {}", o.title),
                play_url(base, &o.key, session),
            )]
        })
        .collect();
    SendMessageRequest {
        chat_id,
        text: "DreggNet Cloud — the rich web surface. Each button opens the Mini App for that \
               offering; every move there is the same real, verifiable executor turn (signed \
               attribution via the app's validated Telegram identity). The inline buttons here \
               in chat keep working as the lightweight tier."
            .to_string(),
        reply_markup: Some(InlineKeyboardMarkup {
            inline_keyboard: rows,
        }),
        message_thread_id: topic,
    }
}
