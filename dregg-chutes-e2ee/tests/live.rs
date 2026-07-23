//! LIVE acceptance test — GATED (`#[ignore]`). Runs the full attested round trip against a
//! real Chutes `-TEE` instance: resolve model → chute_id, discover, fetch evidence with a
//! fresh nonce, DCAP-verify, encrypt to the attested ML-KEM key, POST `/e2e/invoke`, decrypt.
//!
//! Requires (none of which the offline suite needs):
//!   - `CHUTES_API_KEY`         — a `cpk_...` key.
//!   - `CHUTES_TEE_MODEL`       — a TEE-enabled model id (default below); list with
//!                                `GET https://llm.chutes.ai/v1/models` and pick a `-TEE` one.
//!   - `CHUTES_MEASUREMENTS_JSON` — path to the Chutes measurements registry JSON
//!                                (from `GET https://api.chutes.ai/servers/tee/measurements`).
//!   - DCAP collateral: either build with `--features collateral-fetch` (fetches per-quote
//!     from Phala PCCS, override base with `CHUTES_PCCS_URL`), or set
//!     `CHUTES_COLLATERAL_JSON` to a pre-fetched `QuoteCollateralV3` JSON file.
//!
//! Run (once a key is available):
//!   CHUTES_API_KEY=cpk_... \
//!   CHUTES_TEE_MODEL='deepseek-ai/DeepSeek-R1-TEE' \
//!   CHUTES_MEASUREMENTS_JSON=/path/chutes_measurements.json \
//!   CARGO_TARGET_DIR=/tmp/e2e-target \
//!   cargo test -p dregg-chutes-e2ee --features collateral-fetch \
//!       --test live -- --ignored --nocapture attested_chat_against_real_tee_instance

use dregg_chutes_e2ee::{attested_chat_completion, CollateralSource, VerifierConfig};
use serde_json::json;

fn measurements_json() -> String {
    let path = std::env::var("CHUTES_MEASUREMENTS_JSON")
        .expect("set CHUTES_MEASUREMENTS_JSON to the registry JSON path");
    std::fs::read_to_string(&path).expect("read measurements JSON")
}

fn collateral_source() -> CollateralSource {
    if let Ok(path) = std::env::var("CHUTES_COLLATERAL_JSON") {
        return CollateralSource::PrefetchedJson(
            std::fs::read_to_string(&path).expect("read collateral JSON"),
        );
    }
    #[cfg(feature = "collateral-fetch")]
    {
        let url = std::env::var("CHUTES_PCCS_URL")
            .unwrap_or_else(|_| "https://pccs.phala.network".to_string());
        return CollateralSource::Pccs(url);
    }
    #[cfg(not(feature = "collateral-fetch"))]
    panic!(
        "no collateral source: set CHUTES_COLLATERAL_JSON or build with --features collateral-fetch"
    );
}

#[test]
#[ignore = "LIVE: requires CHUTES_API_KEY + network + a -TEE model; run explicitly with --ignored"]
fn attested_chat_against_real_tee_instance() {
    let cpk = std::env::var("CHUTES_API_KEY").expect("set CHUTES_API_KEY (cpk_...)");
    let model = std::env::var("CHUTES_TEE_MODEL")
        .unwrap_or_else(|_| "deepseek-ai/DeepSeek-R1-TEE".to_string());

    let mut cfg = VerifierConfig::new(String::new(), measurements_json());
    cfg.collateral = collateral_source();
    // Widen only if the operator explicitly chooses to (default is STRICT UpToDate).
    if let Ok(extra) = std::env::var("CHUTES_ACCEPTED_STATUSES") {
        cfg.accepted_statuses = extra.split(',').map(|s| s.trim().to_string()).collect();
    }

    let request = json!({
        "model": model,
        "messages": [{"role": "user", "content": "Say 'hello world' and nothing else."}],
        "max_tokens": 32,
        "temperature": 0.0
    });

    let (response, record) =
        attested_chat_completion(&model, &request, &cpk, &cfg).expect("attested chat completion");

    println!(
        "ATTESTED by instance {} | measurement {} | tcb {} | quote {} bytes",
        record.instance_id,
        hex::encode(record.measurement),
        record.tcb_status,
        record.quote_bytes.len()
    );
    println!(
        "response: {}",
        serde_json::to_string_pretty(&response).unwrap()
    );

    assert!(
        response.get("choices").and_then(|c| c.as_array()).is_some(),
        "decrypted OpenAI response must carry a choices array"
    );
    assert_eq!(record.tcb_status, "UpToDate");
}
