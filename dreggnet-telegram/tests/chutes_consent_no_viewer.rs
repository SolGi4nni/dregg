//! Hostile Telegram group/DM checks for the viewer-blind Chutes affordance.

use dreggnet_offerings::chutes_consent::{
    CHUTES_CONSENT_WIRE, ViewerBlindChutesConsent, ViewerBlindChutesReceipt, admits_chutes_consent,
};
use dreggnet_telegram::chutes_consent::{
    build_chutes_consent_request, build_chutes_receipt_request,
};

#[test]
fn group_consent_callback_contains_no_viewer_identity_or_private_input() {
    let disclosure = ViewerBlindChutesConsent::new("deepseek-ai/DeepSeek-V3", 50_000).unwrap();
    let request = build_chutes_consent_request(-100_700, Some(44), &disclosure);
    let wire = serde_json::to_string(&request).unwrap();
    let keyboard = request.reply_markup.unwrap();
    let button = &keyboard.inline_keyboard[0][0];

    assert_eq!(button.callback_data, CHUTES_CONSENT_WIRE);
    assert!(admits_chutes_consent(&button.callback_data));
    assert!(button.callback_data.len() <= 64, "Telegram callback bound");
    assert!(button.text.contains("1 credit"));
    assert!(
        request
            .text
            .contains("only after a provenance-bound executor receipt lands")
    );
    assert!(request.text.contains("No private input"));
    assert_eq!(request.chat_id, -100_700);
    assert_eq!(request.message_thread_id, Some(44));

    for forbidden in [
        "from_user_id",
        "private-actor-42",
        "balance=9",
        "secret prompt",
        "sealed_card",
        "input_tokens",
        "output_tokens",
    ] {
        assert!(
            !wire.contains(forbidden),
            "Telegram wire leaked `{forbidden}`"
        );
    }
}

#[test]
fn callback_lookalikes_never_count_as_consent() {
    for hostile in [
        "chutes-consent-v1 ",
        "chutes-consent-v1:4242",
        "{{chutes-consent-v1}}",
        "approve",
        "yes",
        "1",
        "",
    ] {
        assert!(!admits_chutes_consent(hostile), "refuse `{hostile}`");
    }
}

#[test]
fn public_receipt_has_full_replay_handle_but_no_account_or_prompt_side_channel() {
    let disclosure =
        ViewerBlindChutesReceipt::new("deepseek-ai/DeepSeek-V3", "press_on", [0xefu8; 32], 20_001)
            .unwrap();
    let request = build_chutes_receipt_request(700, None, &disclosure);
    let wire = serde_json::to_string(&request).unwrap();
    assert!(request.reply_markup.is_none());
    assert!(request.text.contains(&"ef".repeat(32)));
    assert!(request.text.contains("Use the Verify action"));
    assert!(request.text.contains("operator spend $0.020001"));
    assert!(request.text.contains("player charge 1 run credit"));
    for forbidden in [
        "remaining credits",
        "player-identity-hex",
        "private route",
        "tool_input",
        "token usage",
    ] {
        assert!(
            !wire.contains(forbidden),
            "public receipt leaked `{forbidden}`"
        );
    }
}
