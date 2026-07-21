//! Viewer-blind Telegram adapters for explicit Chutes consent and public receipt provenance.
//!
//! A group message is shared by every member. The callback payload therefore carries only the
//! exact versioned affirmative consent; Telegram supplies the pressing user's identity separately
//! in the authenticated callback envelope. No actor, balance, prompt, tool input, private result,
//! narration source, or token count enters message text or `callback_data`.

use dreggnet_offerings::chutes_consent::{
    CHUTES_CONSENT_WIRE, ChutesReplaySurface, ViewerBlindChutesConsent, ViewerBlindChutesReceipt,
};

use crate::api::{InlineKeyboardButton, InlineKeyboardMarkup, SendMessageRequest};

/// Build one public consent message with one exact callback. It is valid in a DM, group, or forum
/// topic; the eventual callback's `from.id`, not this shared wire, identifies the consenting user.
pub fn build_chutes_consent_request(
    chat_id: i64,
    message_thread_id: Option<i64>,
    disclosure: &ViewerBlindChutesConsent,
) -> SendMessageRequest {
    SendMessageRequest {
        chat_id,
        text: disclosure.compact_text(),
        reply_markup: Some(InlineKeyboardMarkup {
            inline_keyboard: vec![vec![InlineKeyboardButton::callback(
                disclosure.button_label(),
                CHUTES_CONSENT_WIRE,
            )]],
        }),
        message_thread_id,
    }
}

/// Build the viewer-blind public receipt record. Replay uses the surface's ordinary Verify action;
/// no private/player account fact is embedded in the message.
pub fn build_chutes_receipt_request(
    chat_id: i64,
    message_thread_id: Option<i64>,
    disclosure: &ViewerBlindChutesReceipt,
) -> SendMessageRequest {
    SendMessageRequest {
        chat_id,
        text: disclosure.compact_text(ChutesReplaySurface::Telegram),
        reply_markup: None,
        message_thread_id,
    }
}
