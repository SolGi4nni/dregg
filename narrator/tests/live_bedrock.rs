//! A LIVE Bedrock smoke test — one real Converse call against the default hosted model.
//!
//! Guarded by `DREGG_NARRATOR_LIVE=1` so CI/offline runs skip it (it costs ~$0.001 on Haiku,
//! ~$0.00002 on Nova). It asserts the narration is non-empty AND that the ledger's spend
//! increased by EXACTLY the usage-priced amount computed from the response's real token counts —
//! the true-up is real, not a fixture.
//!
//! Run: `DREGG_NARRATOR_LIVE=1 AWS_PROFILE=commonquant-ember cargo test -p dregg-narrator --test
//! live_bedrock -- --nocapture`. Override the model with `DREGG_NARRATOR_MODEL`.

use dregg_narrator::{
    metered_converse, BedrockClient, BudgetLedger, ConverseRequest, ModelRegistry, DEFAULT_MODEL,
};

#[test]
#[ignore = "LIVE + PAID: one real Bedrock Converse call (~$0.001 on Haiku). Needs \
           DREGG_NARRATOR_LIVE=1 and AWS creds — run `DREGG_NARRATOR_LIVE=1 \
           AWS_PROFILE=… cargo test -p dregg-narrator --test live_bedrock -- --ignored \
           --nocapture`. It used to `return` on the unset var and report `ok`, which is \
           the same word cargo prints for a run that actually billed a token."]
fn live_bedrock_converse_meters_exact_usage() {
    assert_eq!(
        std::env::var("DREGG_NARRATOR_LIVE").ok().as_deref(),
        Some("1"),
        "the #[ignore] above is the gate now; under --ignored without DREGG_NARRATOR_LIVE=1 \
         this must fail loudly rather than print `ok` for a call it never made"
    );

    let tmp = tempfile::tempdir().unwrap();
    let ledger = BudgetLedger::new(tmp.path().join("live-ledger.json"), 20.00);
    let registry = ModelRegistry::builtin();
    let client = BedrockClient::from_env().expect("build Bedrock client");
    let model = std::env::var("DREGG_NARRATOR_MODEL").unwrap_or_else(|_| DEFAULT_MODEL.to_string());
    let pricing = registry
        .pricing_for(&model)
        .expect("the model must be priced");

    let before = ledger.spent_usd().unwrap();
    assert_eq!(before, 0.0, "fresh ledger starts at $0.00");

    let req = ConverseRequest::plain(
        &model,
        "You are the dungeon master of a drowned dark-fantasy vault. Narrate vividly in 1-2 sentences.",
        "I raise the lantern and step into the flooded antechamber.",
        256,
    );
    let resp = metered_converse(&ledger, &registry, &client, &req).expect("live converse");

    assert!(!resp.text.trim().is_empty(), "the model narrated something");

    let expected = pricing.actual_cost(resp.input_tokens, resp.output_tokens);
    let after = ledger.spent_usd().unwrap();
    let delta = after - before;

    eprintln!("── LIVE BEDROCK SMOKE ──────────────────────────────────────────");
    eprintln!("model        : {model}");
    eprintln!("stopReason   : {}", resp.stop_reason);
    eprintln!(
        "usage        : {} in + {} out tokens",
        resp.input_tokens, resp.output_tokens
    );
    eprintln!("narration    : {}", resp.text.trim());
    eprintln!(
        "price/1k     : ${:.5} in / ${:.5} out ({})",
        pricing.input_per_1k,
        pricing.output_per_1k,
        pricing.source.tag()
    );
    eprintln!("computed cost: ${expected:.8}");
    eprintln!("ledger delta : ${delta:.8}  (before ${before:.8} -> after ${after:.8})");
    eprintln!("ledger file  : {}", ledger.path().display());
    eprintln!("────────────────────────────────────────────────────────────────");

    assert!(
        (delta - expected).abs() < 1e-9,
        "the ledger delta ${delta:.8} must equal the exact usage-priced cost ${expected:.8}"
    );
    assert!(delta > 0.0, "a real call spends a positive amount");
}
