//! Hostile tests for the viewer-blind Chutes disclosure boundary.

use dreggnet_offerings::chutes_consent::{
    CHUTES_CONSENT_WIRE, CHUTES_DISCLOSURE_MAX_CHARS, ChutesReplaySurface,
    ViewerBlindChutesConsent, ViewerBlindChutesReceipt, admits_chutes_consent,
};

const PRIVATE_ACTOR: &str = "private-actor-7f83";
const PRIVATE_BALANCE: &str = "balance=41";
const PRIVATE_PROMPT: &str = "secret route: left-left-right";
const PRIVATE_TOOL_INPUT: &str = "sealed_card=ace-of-embers";

fn assert_viewer_blind(rendered: &str) {
    for secret in [
        PRIVATE_ACTOR,
        PRIVATE_BALANCE,
        PRIVATE_PROMPT,
        PRIVATE_TOOL_INPUT,
    ] {
        assert!(
            !rendered.contains(secret),
            "shared Chutes disclosure leaked private material: {secret}"
        );
    }
    assert!(
        rendered.chars().count() <= CHUTES_DISCLOSURE_MAX_CHARS,
        "cross-surface disclosure remains bounded"
    );
}

#[test]
fn consent_is_exact_bounded_and_contains_the_charge_condition_before_any_call() {
    let disclosure = ViewerBlindChutesConsent::new("deepseek-ai/DeepSeek-V3", 50_000).unwrap();
    let rendered = disclosure.compact_text();
    assert!(rendered.contains("Chutes/Bittensor"));
    assert!(rendered.contains("gets only the current public room"));
    assert!(
        rendered.contains("No private input, player identity, balance, or account data is sent")
    );
    assert!(rendered.contains("exactly 1 run credit"));
    assert!(rendered.contains("only after a provenance-bound executor receipt lands"));
    assert!(rendered.contains("costs 0 player credits"));
    assert!(rendered.contains("$0.050000"));
    assert!(rendered.contains("No private input"));
    assert_viewer_blind(&rendered);

    assert!(admits_chutes_consent(CHUTES_CONSENT_WIRE));
    for hostile in [
        "chutes-consent-v1 ",
        " chutes-consent-v1",
        "chutes-consent-v1:admin",
        "{{chutes-consent-v1}}",
        "yes",
        "true",
        "1",
        "",
    ] {
        assert!(!admits_chutes_consent(hostile), "refuse `{hostile}`");
    }
}

#[test]
fn public_receipt_has_full_verification_handle_but_no_viewer_or_prompt_side_channel() {
    let receipt =
        ViewerBlindChutesReceipt::new("deepseek-ai/DeepSeek-V3", "press_on", [0xabu8; 32], 12_345)
            .unwrap();
    let rendered = receipt.compact_text(ChutesReplaySurface::Discord);
    assert!(
        rendered.contains(&"ab".repeat(32)),
        "full receipt is public"
    );
    assert!(rendered.contains("`/dungeon verify`"));
    assert!(rendered.contains("player charge 1 run credit"));
    assert!(rendered.contains("operator spend $0.012345"));
    assert!(rendered.contains("no player identity"));
    assert!(rendered.contains("token count"));
    assert_viewer_blind(&rendered);
}

#[test]
fn operator_metadata_cannot_become_a_format_or_injection_carrier() {
    for model in [
        "",
        "model with spaces",
        "model`spoof",
        "<script>alert(1)</script>",
        "model\nprivate-input",
        "a-model/{{system}}",
    ] {
        assert!(
            ViewerBlindChutesConsent::new(model, 50_000).is_err(),
            "unsafe model refused: {model:?}"
        );
    }
    for command in ["", "press on", "`press_on`", "{{press_on}}", "x/y"] {
        assert!(
            ViewerBlindChutesReceipt::new("safe/model", command, [1u8; 32], 1).is_err(),
            "unsafe command refused: {command:?}"
        );
    }
    assert!(
        ViewerBlindChutesConsent::new("m".repeat(129), 50_000).is_err(),
        "overlong model refused"
    );
    assert!(
        ViewerBlindChutesReceipt::new("safe/model", "c".repeat(65), [1u8; 32], 1).is_err(),
        "overlong command refused"
    );

    let maximal = ViewerBlindChutesConsent::new("m".repeat(128), u64::MAX).unwrap();
    let rendered = maximal.compact_text();
    assert_viewer_blind(&rendered);
    assert!(
        rendered.ends_with("token counts."),
        "even maximal safe metadata leaves every disclosure clause visible"
    );
}
