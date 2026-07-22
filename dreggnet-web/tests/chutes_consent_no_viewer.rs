//! Hostile no-viewer checks for the web Chutes consent/provenance fragments.

use dreggnet_offerings::chutes_consent::{
    CHUTES_CONSENT_WIRE, ViewerBlindChutesConsent, ViewerBlindChutesReceipt,
};
use dreggnet_web::chutes_consent::{
    ChutesPublicPath, render_chutes_consent, render_chutes_receipt,
};

#[test]
fn shared_consent_form_submits_only_exact_consent_and_no_viewer_material() {
    let disclosure = ViewerBlindChutesConsent::new("deepseek-ai/DeepSeek-V3", 50_000).unwrap();
    let action = ChutesPublicPath::new("/offerings/dungeon/session/public-7/chutes").unwrap();
    let html = render_chutes_consent(&disclosure, &action);

    assert!(html.contains("data-audience=\"viewer-blind\""));
    assert!(html.contains("Chutes/Bittensor"));
    assert!(html.contains("1 run credit"));
    assert!(html.contains("only after a provenance-bound executor receipt lands"));
    assert!(html.contains(&format!("name=\"consent\" value=\"{CHUTES_CONSENT_WIRE}\"")));
    assert_eq!(html.matches("<input").count(), 1, "one exact consent value");
    for forbidden in [
        "name=\"user\"",
        "name=\"actor\"",
        "name=\"balance\"",
        "name=\"prompt\"",
        "name=\"tool_input\"",
        "private-route-left",
        "sealed-card-ace",
    ] {
        assert!(
            !html.contains(forbidden),
            "shared form leaked `{forbidden}`"
        );
    }
}

#[test]
fn public_receipt_renders_full_hash_and_replay_link_without_account_side_channels() {
    let disclosure =
        ViewerBlindChutesReceipt::new("deepseek-ai/DeepSeek-V3", "press_on", [0xcdu8; 32], 9_876)
            .unwrap();
    let verify = ChutesPublicPath::new("/offerings/dungeon/session/public-7/verify").unwrap();
    let html = render_chutes_receipt(&disclosure, &verify);
    assert!(html.contains(&"cd".repeat(32)));
    assert!(html.contains("Replay-verify this session"));
    assert!(html.contains("operator spend $0.009876"));
    assert!(html.contains("player charge 1 run credit"));
    for forbidden in [
        "remaining credits",
        "input_tokens",
        "output_tokens",
        "private-actor",
        "secret prompt",
        "sealed_card",
    ] {
        assert!(
            !html.contains(forbidden),
            "public receipt leaked `{forbidden}`"
        );
    }
}

#[test]
fn route_metadata_cannot_smuggle_query_fragment_or_markup_into_shared_html() {
    for hostile in [
        "https://evil.example/steal",
        "//evil.example/steal",
        "/chutes?user=private-actor",
        "/chutes#private-prompt",
        "/chutes/../private",
        "/chutes/./approve",
        "/chutes/<script>",
        "/chutes/\" autofocus",
        "relative/chutes",
        "",
    ] {
        assert!(
            ChutesPublicPath::new(hostile).is_err(),
            "route carrier refused: {hostile:?}"
        );
    }
    assert!(
        ChutesPublicPath::new(format!("/{}", "a".repeat(256))).is_err(),
        "overlong local route refused"
    );
}
