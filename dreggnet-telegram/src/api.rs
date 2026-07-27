//! **The PURE Telegram Bot API layer** — request-building with NO transport, NO token, NO
//! network. Mirrors the discord-bot's `build_*_request` split (a pure request builder separate
//! from the live `Http` call): here [`build_present_request`] turns an offering [`Surface`] +
//! its cap-gated [`Action`]s into a [`SendMessageRequest`] whose serde encoding IS the real Bot
//! API `sendMessage` JSON wire body. A test that asserts the request shape asserts the wire
//! shape; a [`crate::transport::Transport`] is the only thing that ever touches the network.
//!
//! ## Surface → inline keyboard (the affordance mapping)
//! An offering's [`Surface`] is a deos [`deos_view::ViewNode`]; its [`Action`]s are cap-gated
//! `{turn, arg}` affordances. Telegram renders them as an **inline keyboard**: one button per
//! affordance, packed into rows by label width and BOUNDED
//! ([`TELEGRAM_KEYBOARD_MAX_ROWS`] / [`TELEGRAM_KEYBOARD_MAX_LOCKED`]), the button's
//! `callback_data` carrying the `{turn, arg}` (see [`encode_callback`] / [`decode_callback`]) so a
//! press round-trips back to the same [`Action`]. A `!enabled` affordance is the **cap tooth
//! shown, not hidden**: rendered with a dim lock glyph but still pressable — the executor is the
//! sole referee, so firing it lands a real [`dreggnet_offerings::Outcome::Refused`] (anti-ghost),
//! exactly as on Discord. What the bound leaves off is COUNTED in a trailing line of the message,
//! and stays reachable through `/act` (the session records every action as presented).
//!
//! The message carries [`TELEGRAM_PARSE_MODE`], because the board needs a monospace fence to be a
//! board at all — which makes escaping load-bearing for every other line (see
//! [`crate::render::render_surface_html`]).

use deos_view::AffordanceTransport;
use dreggnet_offerings::{Action, Surface};
use serde::{Deserialize, Serialize};

use crate::render::render_surface_html;

/// Telegram's documented text ceiling for `sendMessage` / `editMessageText`, in Unicode
/// characters after entity parsing. The adapter paginates non-interactive companion guides and
/// refuses an oversized interactive surface before the live Bot API can reject it ambiguously.
pub const TELEGRAM_TEXT_LIMIT: usize = 4096;

/// **The `parse_mode` every INTERACTIVE surface is sent with** — `HTML`.
///
/// ⚑ It is here because of the BOARD. `deos_view::coordgrid_text` builds a grid out of
/// fixed-3-character cells; a `sendMessage` with NO parse mode is laid out by the client in a
/// PROPORTIONAL font, in which equal character counts are not equal widths and the rows do not line
/// up into columns. The board is wrapped in `<pre>` — Telegram's monospace guarantee — by
/// [`render_surface_html`], and that wrapper only means anything with this set.
///
/// ⚑ Setting it makes ESCAPING LOAD-BEARING for the whole message: a parse mode is per-message, so
/// every other line becomes text the parser reads and one raw `<` is a `can't parse entities`
/// refusal of the entire send. That is why the escape and the fence are one decision inside the
/// shared walk ([`deos_view::ChatTextStyle`]) rather than something a caller applies. HTML rather
/// than MarkdownV2 because its escape surface is three characters instead of eighteen.
///
/// Button labels are NOT parsed (the Bot API takes them as literal text), and the non-interactive
/// companion pages set no parse mode at all, so neither needs escaping.
pub const TELEGRAM_PARSE_MODE: &str = "HTML";

/// **The most buttons put in ONE keyboard row** — a row of short labels reads as a row; a row of
/// sentences reads as mush, so `row_capacity` only reaches this for genuinely short labels.
pub const TELEGRAM_KEYBOARD_MAX_PER_ROW: usize = 3;

/// **THE BOUND: the most affordance ROWS one keyboard paints.**
///
/// ⚑ There was no bound at all. Every [`Action`] became its own row, so a fresh 11×11 automatafl
/// position painted 36 separate `Select (x,y)` rows and a sealed seat painted the whole ~50-row list
/// lock-prefixed — a keyboard that fills a phone several times over and buries the two buttons that
/// matter. (A comment in `dregg-automatafl` asserted for months that the Telegram renderer "paints
/// the first ≤25 actions as buttons and silently drops the rest"; it was simply false, and the claim
/// is exactly why nobody looked.) 16 is the native Descent's own bound, arrived at by the same
/// reasoning about the same tall keyboard — one screen of controls, scrollable but not endless.
///
/// Rows are the unit because rows are what makes a keyboard tall: with `row_capacity` packing
/// short labels three-up, 36 `Select (x,y)` buttons are 12 rows, not 36.
pub const TELEGRAM_KEYBOARD_MAX_ROWS: usize = 16;

/// **The most LOCKED (`!enabled`) buttons one keyboard paints** — the row cap, because a locked
/// affordance may FILL the keyboard but must never be the reason it is taller than the bound.
///
/// The cap tooth is shown, not hidden — a `!enabled` affordance stays pressable so firing it lands
/// the executor's real refusal instead of vanishing. That is right for a handful and absurd for
/// fifty: a sealed automatafl seat has nothing live and ~58 dead affordances, and painting them all
/// turns "the tooth is visible" into "the bot is broken". Spending the budget ROUND-ROBIN across
/// distinct `turn`s (see [`build_present_request_with_callback_data`]) keeps a real sample of every
/// verb rather than sixteen squares of one, so that seat's reveal and resolve survive beside a
/// sample of its dead selects — about six rows, from fifty-eight.
///
/// Deriving it from [`TELEGRAM_KEYBOARD_MAX_ROWS`] rather than picking a smaller number is
/// deliberate: the native Descent's complete action vocabulary is 16 affordances of which most are
/// legitimately locked at any moment, and its own comment says to keep them (their executor
/// refusals are the useful part). A tighter budget would have silently amputated the flagship's
/// catalogue to solve automatafl's problem.
pub const TELEGRAM_KEYBOARD_MAX_LOCKED: usize = TELEGRAM_KEYBOARD_MAX_ROWS;

/// How many buttons a row of this label may hold. Widths are in CHARACTERS of the final label
/// (lock glyph included): a Telegram button does not wrap, it ellipsizes, so three long labels
/// side by side is three unreadable buttons.
fn row_capacity(label: &str) -> usize {
    match label.chars().count() {
        0..=12 => TELEGRAM_KEYBOARD_MAX_PER_ROW,
        13..=20 => 2,
        _ => 1,
    }
}

/// Encode an affordance `{turn, arg}` into Telegram `callback_data` (`"<turn>:<arg>"`). The
/// inverse of [`decode_callback`]. Deterministic and byte-bounded (≤ 64 bytes for any real
/// affordance). The Telegram binding of the ONE `deos_view::affordance` codec.
pub fn encode_callback(turn: &str, arg: i64) -> String {
    deos_view::affordance_id(turn, arg, AffordanceTransport::Telegram)
}

/// Decode Telegram `callback_data` back into `(turn, arg)` — the inverse of [`encode_callback`].
/// Splits on the LAST separator so `turn` may (in principle) contain earlier ones. `None` if the
/// data is malformed (no separator, or a non-integer arg) — a press the frontend never minted. The
/// Telegram binding of the ONE `deos_view::affordance` codec.
pub fn decode_callback(data: &str) -> Option<(String, i64)> {
    deos_view::affordance::parse_affordance_id(data, AffordanceTransport::Telegram)
}

/// The dim lock glyph prefixing a `!enabled` (ineligible) affordance's button label — the cap
/// tooth shown, not hidden. The button is still pressable; the executor refuses it on `advance`.
pub const LOCK_GLYPH: &str = "🔒 ";

/// A **Mini App launch descriptor** — the Bot API `WebAppInfo`: the HTTPS URL Telegram opens in
/// its in-app web-view when the carrying button is pressed. The Telegram wire type behind the
/// "Play in the app" tier ([`crate::webapp`]) — the rich web surface beside the inline-button
/// fallback, both driving the SAME offering substrate.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct WebAppInfo {
    /// The HTTPS URL of the Mini App page (the funnel base + the `/tg` offering/session path).
    pub url: String,
}

/// One **inline keyboard button** — the Bot API `InlineKeyboardButton` (the fields we use).
/// Exactly ONE of the optional actions is set per button (Telegram's own rule): a
/// `callback_data` press button carries the affordance `{turn, arg}` and delivers it back
/// verbatim in a `CallbackQuery`; a `web_app` launch button opens a Mini App instead (and never
/// produces a callback). An empty `callback_data` is OMITTED from the wire, so a
/// [`web_app`](Self::web_app) button serializes with only its `web_app` field — the shape the
/// Bot API accepts.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct InlineKeyboardButton {
    /// The button label (the affordance's human text; a `!enabled` one is [`LOCK_GLYPH`]-prefixed).
    pub text: String,
    /// The affordance `{turn, arg}`, [`encode_callback`]-encoded — echoed back on a press. Empty
    /// (and omitted on the wire) for a [`web_app`](Self::web_app) launch button.
    #[serde(skip_serializing_if = "String::is_empty", default)]
    pub callback_data: String,
    /// The Mini App this button launches instead of a callback press (`None` for an ordinary
    /// press button). Telegram only honors `web_app` inline buttons in PRIVATE chats — the
    /// caller gates on that ([`crate::webapp::web_app_allowed`]).
    #[serde(skip_serializing_if = "Option::is_none", default)]
    pub web_app: Option<WebAppInfo>,
}

impl InlineKeyboardButton {
    /// An ordinary **press button**: `callback_data` echoed back in a `CallbackQuery`.
    pub fn callback(text: impl Into<String>, callback_data: impl Into<String>) -> Self {
        InlineKeyboardButton {
            text: text.into(),
            callback_data: callback_data.into(),
            web_app: None,
        }
    }

    /// A **Mini App launch button**: pressing it opens `url` in Telegram's in-app web-view
    /// (no callback is ever produced). Private chats only — Telegram's rule for `web_app`
    /// inline buttons.
    pub fn web_app(text: impl Into<String>, url: impl Into<String>) -> Self {
        InlineKeyboardButton {
            text: text.into(),
            callback_data: String::new(),
            web_app: Some(WebAppInfo { url: url.into() }),
        }
    }
}

/// An **inline keyboard** — the Bot API `InlineKeyboardMarkup`: a grid of [`InlineKeyboardButton`]
/// rows. Rows are packed by label width (`row_capacity`) and bounded
/// ([`TELEGRAM_KEYBOARD_MAX_ROWS`]); a sentence-long label still gets a row to itself, which is
/// what makes the dungeon's vertical `Menu` read as a menu.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct InlineKeyboardMarkup {
    /// Rows of buttons (each inner `Vec` is one keyboard row).
    pub inline_keyboard: Vec<Vec<InlineKeyboardButton>>,
}

/// A **`sendMessage` request** — the Bot API `sendMessage` body, verbatim. Its serde encoding is
/// exactly the JSON wire body a live bot POSTs to `https://api.telegram.org/bot<token>/sendMessage`
/// (a test asserting this struct's shape asserts the real wire shape). Built purely by
/// [`build_present_request`]; sent by a [`crate::transport::Transport`].
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SendMessageRequest {
    /// The target chat (a Telegram chat id — negative for groups/supergroups, positive for DMs).
    pub chat_id: i64,
    /// The message text (the offering's rendered room prose + party state + verified-turn count).
    pub text: String,
    /// The affordance controls — an inline keyboard of the cap-gated actions. `None` when the
    /// surface offers no moves (a terminal room).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reply_markup: Option<InlineKeyboardMarkup>,
    /// For a forum-topic session, the topic thread this message posts under. `None` for a plain
    /// chat/DM. (The Bot API `message_thread_id`.)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub message_thread_id: Option<i64>,
    /// **How Telegram should parse [`text`](Self::text)** — [`TELEGRAM_PARSE_MODE`] for an
    /// interactive surface (the board needs a `<pre>` fence to be laid out in a monospace font),
    /// `None` for a plain-text control message (a companion guide page, a consent prompt), which is
    /// then never entity-parsed and needs no escaping.
    ///
    /// ⚑ Set this ONLY on text produced by [`render_surface_html`]: the two halves are one
    /// decision, and a parse mode over unescaped prose is a `can't parse entities` refusal of the
    /// whole message.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub parse_mode: Option<String>,
}

/// **Build the `sendMessage` request that presents `surface` + `actions` in `chat_id`** — the
/// pure Surface→(text + inline keyboard) mapping. The text is the deos view-tree walked into
/// Telegram-flavored prose ([`render_surface_html`]); the keyboard is the BOUNDED affordance grid
/// ([`TELEGRAM_KEYBOARD_MAX_ROWS`]), each button's `callback_data` carrying its `{turn, arg}` so a
/// press round-trips back to the [`Action`]. A `!enabled` affordance is rendered dimmed
/// ([`LOCK_GLYPH`]) but still pressable — the cap tooth shown, not hidden (the executor refuses it
/// on `advance`). `message_thread_id` scopes the message to a forum topic when the session is a
/// topic-per-session.
pub fn build_present_request(
    chat_id: i64,
    message_thread_id: Option<i64>,
    surface: &Surface,
    actions: &[Action],
) -> SendMessageRequest {
    let callback_data: Vec<String> = actions
        .iter()
        .map(|action| encode_callback(&action.turn, action.arg))
        .collect();
    build_present_request_with_callback_data(
        chat_id,
        message_thread_id,
        surface,
        actions,
        &callback_data,
    )
    .expect("one callback was derived for every action")
}

/// Build an interactive surface with caller-supplied callback data for each
/// action. This is used by the multi-offering game host to carry an opaque
/// digest of the complete bound action reference; generic frontend callers
/// continue to use [`build_present_request`]'s `{turn, arg}` wire.
///
/// ⚑ **THE KEYBOARD IS BOUNDED HERE, and the message says when the bound bit.** Three rules, in
/// order, all of them presentation-only — no action identity changes, and the session still records
/// EVERY action as presented, so `/act <turn> <arg>` and any pinned callback still reach an
/// affordance that did not fit:
///
/// 1. **Live before locked.** A stable sort puts `enabled` affordances first, preserving each
///    offering's authored order within the two bands (automatafl's "seal targets before selects",
///    the native descent's "FLEE after the other live moves"). This is what the two frontends'
///    ordering comments have always ASSUMED and what nothing enforced.
/// 2. **A locked BUDGET** ([`TELEGRAM_KEYBOARD_MAX_LOCKED`]). Under the budget, nothing is spent and
///    the authored order is kept exactly. Over it, the budget is spent ROUND-ROBIN over distinct
///    `turn`s so a sample of every verb survives rather than sixteen squares of one. That is the
///    collapse a sealed automatafl seat needed: nothing live, ~58 dead, and a keyboard that should
///    be six short rows and a sentence instead of fifty-eight lock-prefixed rows.
/// 3. **A ROW CAP** ([`TELEGRAM_KEYBOARD_MAX_ROWS`]) over rows packed by label width
///    (`row_capacity`).
///
/// Whatever rules 2 and 3 leave off is COUNTED and named in a trailing line of the message text —
/// the bound is a stated constraint, never a silent drop.
pub fn build_present_request_with_callback_data(
    chat_id: i64,
    message_thread_id: Option<i64>,
    surface: &Surface,
    actions: &[Action],
    callback_data: &[String],
) -> Result<SendMessageRequest, String> {
    if actions.len() != callback_data.len() {
        return Err(format!(
            "callback/action count mismatch: {} callbacks for {} actions",
            callback_data.len(),
            actions.len()
        ));
    }
    if let Some(data) = callback_data
        .iter()
        .find(|data| data.is_empty() || data.len() > 64)
    {
        return Err(format!(
            "Telegram callback_data must contain 1..=64 bytes, found {}",
            data.len()
        ));
    }
    let mut text = render_surface_html(surface);

    // ── Rule 1: live before locked, stable, so each offering's authored order survives. ──
    let mut buttons: Vec<(bool, &str, InlineKeyboardButton)> = actions
        .iter()
        .zip(callback_data)
        .map(|(a, callback_data)| {
            let label = if a.enabled {
                a.label.clone()
            } else {
                format!("{LOCK_GLYPH}{}", a.label)
            };
            (
                a.enabled,
                a.turn.as_str(),
                InlineKeyboardButton::callback(label, callback_data),
            )
        })
        .collect();
    buttons.sort_by_key(|(enabled, _, _)| !*enabled);
    let live_count = buttons.iter().filter(|(enabled, _, _)| *enabled).count();

    // ── Rule 2: the locked budget. ──
    let locked_total = buttons.len() - live_count;
    let mut kept: Vec<InlineKeyboardButton> = Vec::with_capacity(buttons.len());
    let mut dropped_locked = 0usize;
    if locked_total <= TELEGRAM_KEYBOARD_MAX_LOCKED {
        // No shortage, so nothing to spend and no reordering to justify: every offering's authored
        // order is kept exactly. This is the ordinary case (the native Descent's whole 16-affordance
        // vocabulary lands here), and it matters that it is byte-for-byte the authored list.
        kept.extend(buttons.iter().map(|(_, _, button)| button.clone()));
    } else {
        kept.extend(
            buttons
                .iter()
                .filter(|(enabled, _, _)| *enabled)
                .map(|(_, _, button)| button.clone()),
        );
        // Queues in first-appearance order of `turn`, each holding that turn's locked buttons in
        // authored order. Draining one button per queue per pass spends the budget on VERBS first,
        // so a sealed automatafl seat keeps its reveal and its resolve rather than sixteen dead
        // squares of one verb.
        let mut turns: Vec<&str> = Vec::new();
        let mut queues: Vec<Vec<InlineKeyboardButton>> = Vec::new();
        for (enabled, turn, button) in &buttons {
            if *enabled {
                continue;
            }
            let turn: &str = turn;
            match turns.iter().position(|t| *t == turn) {
                Some(at) => queues[at].push(button.clone()),
                None => {
                    turns.push(turn);
                    queues.push(vec![button.clone()]);
                }
            }
        }
        let mut taken = 0usize;
        let mut round = 0usize;
        while taken < TELEGRAM_KEYBOARD_MAX_LOCKED {
            let mut progressed = false;
            for queue in &queues {
                if let Some(button) = queue.get(round) {
                    kept.push(button.clone());
                    taken += 1;
                    progressed = true;
                    if taken == TELEGRAM_KEYBOARD_MAX_LOCKED {
                        break;
                    }
                }
            }
            if !progressed {
                break;
            }
            round += 1;
        }
        dropped_locked = locked_total - taken;
    }

    // ── Rule 3: pack by label width, then cap the rows. ──
    let mut rows: Vec<Vec<InlineKeyboardButton>> = Vec::new();
    let mut i = 0;
    while i < kept.len() {
        let capacity = row_capacity(&kept[i].text);
        let mut row = vec![kept[i].clone()];
        i += 1;
        while row.len() < capacity && i < kept.len() && row_capacity(&kept[i].text) >= capacity {
            row.push(kept[i].clone());
            i += 1;
        }
        rows.push(row);
    }
    let mut dropped_live = 0usize;
    if rows.len() > TELEGRAM_KEYBOARD_MAX_ROWS {
        for row in rows.drain(TELEGRAM_KEYBOARD_MAX_ROWS..) {
            // Everything past the cap is at the tail, i.e. the locked band first only if the live
            // band already filled the keyboard; count each honestly by its lock glyph.
            for button in row {
                if button.text.starts_with(LOCK_GLYPH) {
                    dropped_locked += 1;
                } else {
                    dropped_live += 1;
                }
            }
        }
    }
    if let Some(note) = keyboard_bound_note(live_count, dropped_live, dropped_locked) {
        // Escaped like every other content line: the message carries a live parse mode.
        if !text.is_empty() {
            text.push('\n');
        }
        text.push_str(&deos_view::escape_telegram_html(&note));
    }
    let reply_markup = (!rows.is_empty()).then_some(InlineKeyboardMarkup {
        inline_keyboard: rows,
    });
    Ok(SendMessageRequest {
        chat_id,
        text,
        reply_markup,
        message_thread_id,
        parse_mode: Some(TELEGRAM_PARSE_MODE.to_string()),
    })
}

/// **What the message says when the keyboard bound bit** — `None` when everything fit, which is the
/// normal case for every offering whose action list is already a screenful.
///
/// It names the count, WHY, that the omitted affordances are still real, and the one gesture that
/// reaches them. The "nothing here is yours right now" sentence is the honest reading of a surface
/// with zero live affordances — a sealed seat waiting on its opponent, a locked seat between
/// rounds — which used to be painted as fifty identical lock-prefixed rows.
fn keyboard_bound_note(
    live_count: usize,
    dropped_live: usize,
    dropped_locked: usize,
) -> Option<String> {
    let dropped = dropped_live + dropped_locked;
    if dropped == 0 {
        return None;
    }
    let mut note = String::new();
    if live_count == 0 {
        note.push_str("Nothing on this surface is yours to press right now. ");
    }
    note.push_str(&format!(
        "{dropped} more affordance{} not on the keyboard ({dropped_live} you could take now, \
         {dropped_locked} locked): a keyboard past {TELEGRAM_KEYBOARD_MAX_ROWS} rows stops being \
         readable, so the live moves come first. They are still offered: /act <turn> <arg> \
         reaches any of them, and /status shows the whole record.",
        if dropped == 1 { " is" } else { "s are" }
    ));
    Some(note)
}
