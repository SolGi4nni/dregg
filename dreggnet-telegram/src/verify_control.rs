//! Telegram's standing, read-only offering verifier control.
//!
//! Web play surfaces expose replay verification and Discord appends a verify button to every
//! offering. Telegram already routed the same operation through `TelegramHost::press`, but only
//! slash-command callers could discover it. This module owns the one canonical callback shape
//! used by both the rendered button and the router.

use crate::api::{InlineKeyboardButton, encode_callback};

/// The reserved host-level verb for replaying an offering's committed chain.
pub const TURN_VERIFY: &str = "verifychain";
/// The only admitted argument for [`TURN_VERIFY`].
pub const VERIFY_ARG: i64 = 0;
/// The human label shared by every Telegram offering surface.
pub const VERIFY_LABEL: &str = "⛓ re-verify chain";

/// Mint the canonical callback button. It is a host control, never an offering `Action`, so it
/// cannot reach an offering executor or become part of the committed move log.
pub fn button() -> InlineKeyboardButton {
    InlineKeyboardButton::callback(VERIFY_LABEL, encode_callback(TURN_VERIFY, VERIFY_ARG))
}

/// Admit only the exact host-control wire. A forged non-zero argument falls through to the
/// ordinary offered-action check and is refused because this control is never in that list.
pub fn is_verify_callback(turn: &str, arg: i64) -> bool {
    turn == TURN_VERIFY && arg == VERIFY_ARG
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::api::decode_callback;

    #[test]
    fn button_and_router_share_one_canonical_wire() {
        let button = button();
        assert_eq!(button.text, VERIFY_LABEL);
        assert_eq!(
            decode_callback(&button.callback_data),
            Some((TURN_VERIFY.to_string(), VERIFY_ARG))
        );
        assert!(is_verify_callback(TURN_VERIFY, VERIFY_ARG));
        assert!(!is_verify_callback(TURN_VERIFY, 1));
        assert!(!is_verify_callback("verify", VERIFY_ARG));
    }
}
