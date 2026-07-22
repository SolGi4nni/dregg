//! **Phase-E LIVE spike — a REAL MPC-TLS 2PC attestation of a live AWS Bedrock Claude call.**
//!
//! Ignored by default (real network + paid Bedrock call + heavy 2PC). Run:
//! ```text
//! export AWS_ACCESS_KEY_ID=$(aws configure get aws_access_key_id --profile commonquant-ember)
//! export AWS_SECRET_ACCESS_KEY=$(aws configure get aws_secret_access_key --profile commonquant-ember)
//! cargo test -p dregg-zkoracle-prove --features tlsn-live --test bedrock_mpctls_live -- --ignored --nocapture
//! ```
//!
//! On success it PRINTS the disclosed body — Claude's genuine in-session completion, attested by
//! a real `presentation.verify()`, with the SigV4 `Authorization` credential hidden. That is the
//! Phase-E hole closed: the attested body is what Bedrock actually returned, not a passed-in
//! string.

#![cfg(feature = "tlsn-live")]

use std::time::{SystemTime, UNIX_EPOCH};

use dregg_zkoracle_prove::notary_server::{
    generate_notary_key, load_notary_key, load_or_generate_notary_key, verifying_key_of,
};
use dregg_zkoracle_prove::sigv4::AwsCredentials;
use dregg_zkoracle_prove::tlsn_bedrock::{
    BedrockExchange, authorization_hidden, run_bedrock_roundtrip_blocking,
    run_bedrock_roundtrip_with_durable_notary, verify_bedrock_presentation,
};

fn amz_date(unix: u64) -> String {
    let days = (unix / 86_400) as i64;
    let sod = unix % 86_400;
    let (h, mi, s) = (sod / 3600, (sod % 3600) / 60, sod % 60);
    let z = days + 719_468;
    let era = if z >= 0 { z } else { z - 146_096 } / 146_097;
    let doe = z - era * 146_097;
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    let y = if m <= 2 { y + 1 } else { y };
    format!("{y:04}{m:02}{d:02}T{h:02}{mi:02}{s:02}Z")
}

#[test]
#[ignore = "live: real network + paid Bedrock call + heavy MPC-TLS 2PC"]
fn bedrock_mpctls_attests_real_claude_output() {
    let creds = AwsCredentials {
        access_key_id: std::env::var("AWS_ACCESS_KEY_ID").expect("AWS_ACCESS_KEY_ID"),
        secret_access_key: std::env::var("AWS_SECRET_ACCESS_KEY").expect("AWS_SECRET_ACCESS_KEY"),
    };
    let now = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_secs();

    let host = "bedrock-runtime.us-east-1.amazonaws.com".to_string();
    // Keep maxTokens small so the response fits MAX_RECV_DATA and the 2PC stays cheap.
    let body = r#"{"messages":[{"role":"user","content":[{"text":"I raise the lantern and step into the flooded antechamber. Narrate in one vivid sentence."}]}],"system":[{"text":"You are the dungeon master of a drowned dark-fantasy vault."}],"inferenceConfig":{"maxTokens":64}}"#;

    let ex = BedrockExchange {
        host: host.clone(),
        region: "us-east-1".to_string(),
        model_id: "us.anthropic.claude-haiku-4-5-20251001-v1:0".to_string(),
        request_body: body.to_string(),
        creds,
        amz_date: amz_date(now),
    };

    let rt = run_bedrock_roundtrip_blocking(&ex).expect("real Bedrock MPC-TLS roundtrip");

    let disclosed = String::from_utf8_lossy(&rt.verified.response_body);
    eprintln!("── PHASE-E: REAL MPC-TLS ATTESTATION OF LIVE BEDROCK ────────────");
    eprintln!("pinned server : {}", rt.verified.server_name);
    eprintln!("session time  : {}", rt.verified.connection_time);
    eprintln!(
        "auth hidden   : {}",
        authorization_hidden(&rt.verified.sent_redacted)
    );
    eprintln!("presentation  : {} bytes", rt.presentation_bytes.len());
    eprintln!("── DISCLOSED BODY (Claude's genuine in-session output) ──────────");
    eprintln!("{disclosed}");
    eprintln!("────────────────────────────────────────────────────────────────");

    assert_eq!(rt.verified.server_name, host, "server pinned to Bedrock");
    assert!(
        authorization_hidden(&rt.verified.sent_redacted),
        "the SigV4 Authorization credential must be hidden by selective disclosure"
    );
    assert!(
        disclosed.contains("\"output\"") || disclosed.contains("\"message\""),
        "the disclosed body is a genuine Bedrock converse response"
    );
}

/// Parse `usage.outputTokens` out of a Bedrock `converse` response body.
fn output_tokens(body: &[u8]) -> Option<u64> {
    let v: serde_json::Value = serde_json::from_slice(body).ok()?;
    v.get("usage")?.get("outputTokens")?.as_u64()
}

/// **The Phase-E gap closed, DRIVEN.** The prover runs a REAL Bedrock MPC-TLS session against a
/// SEPARATE notary party (a distinct task on a real localhost socket, owning a key the prover
/// never sees). The presentation verifies ONLY under the notary's PINNED verifying key — a
/// wrong key is rejected (non-vacuous) — and the disclosed body is a FULL-LENGTH (>64-token)
/// genuine Claude completion with the SigV4 credential hidden.
#[test]
#[ignore = "live: real network + paid Bedrock call + heavy MPC-TLS 2PC against a separate notary"]
fn bedrock_attested_by_separate_pinned_notary() {
    let creds = AwsCredentials {
        access_key_id: std::env::var("AWS_ACCESS_KEY_ID").expect("AWS_ACCESS_KEY_ID"),
        secret_access_key: std::env::var("AWS_SECRET_ACCESS_KEY").expect("AWS_SECRET_ACCESS_KEY"),
    };
    let now = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_secs();

    let host = "bedrock-runtime.us-east-1.amazonaws.com".to_string();
    // A FULL-LENGTH narration: maxTokens far above the old 64-token cap. Fits the raised
    // MAX_RECV_DATA (64 KiB) with headroom.
    let body = r#"{"messages":[{"role":"user","content":[{"text":"I raise the lantern and wade deeper into the drowned vault. Narrate the next four rooms I discover in rich, vivid detail — the water, the ruined shrines, what glints beneath the surface, and the thing that stirs in the dark."}]}],"system":[{"text":"You are the dungeon master of a drowned dark-fantasy vault. Narrate immersively."}],"inferenceConfig":{"maxTokens":768}}"#;

    let ex = BedrockExchange {
        host: host.clone(),
        region: "us-east-1".to_string(),
        model_id: "us.anthropic.claude-haiku-4-5-20251001-v1:0".to_string(),
        request_body: body.to_string(),
        creds,
        amz_date: amz_date(now),
    };

    // Runs the prover against a SEPARATE hosted notary party; verifies under its PINNED key.
    let rt = run_bedrock_roundtrip_blocking(&ex)
        .expect("real Bedrock MPC-TLS roundtrip via a separate pinned notary");

    let disclosed = String::from_utf8_lossy(&rt.verified.response_body);
    let tokens = output_tokens(&rt.verified.response_body);

    eprintln!("── PHASE-E: SEPARATE PINNED NOTARY ATTESTS LIVE BEDROCK ─────────");
    eprintln!("separate-notary : {}", rt.separate_notary);
    eprintln!("notary socket   : {}", rt.notary_pin.addr);
    eprintln!("pinned-key (fp) : {}", rt.notary_pin.key_fingerprint());
    eprintln!("pinned server   : {}", rt.verified.server_name);
    eprintln!("session time    : {}", rt.verified.connection_time);
    eprintln!(
        "auth hidden     : {}",
        authorization_hidden(&rt.verified.sent_redacted)
    );
    eprintln!("presentation    : {} bytes", rt.presentation_bytes.len());
    eprintln!("output tokens   : {tokens:?}");
    eprintln!("── DISCLOSED BODY (Claude's genuine in-session output) ──────────");
    eprintln!("{disclosed}");
    eprintln!("────────────────────────────────────────────────────────────────");

    // 1. The notary is a SEPARATE party.
    assert!(rt.separate_notary, "notary must be a separate hosted party");

    // 2. The presentation verifies under the PINNED notary key.
    let ok = verify_bedrock_presentation(
        &rt.presentation_bytes,
        &host,
        &rt.model_id,
        &rt.notary_pin.verifying_key,
    );
    assert!(
        ok.is_ok(),
        "presentation must verify under the PINNED notary key: {ok:?}"
    );

    // 3. A WRONG notary key is REJECTED (non-vacuous pin — an independent key must fail).
    let wrong_key =
        verifying_key_of(&generate_notary_key().expect("wrong key")).expect("wrong verifying key");
    assert_ne!(
        wrong_key, rt.notary_pin.verifying_key,
        "the wrong key must differ from the pin"
    );
    let rejected =
        verify_bedrock_presentation(&rt.presentation_bytes, &host, &rt.model_id, &wrong_key);
    assert!(
        rejected.is_err(),
        "a presentation signed by the trusted notary must be REJECTED under a wrong/unpinned key"
    );
    eprintln!(
        "wrong-key rejected: true  (err = {})",
        rejected.unwrap_err()
    );

    // 4. Server pinned to Bedrock; SigV4 credential hidden.
    assert_eq!(rt.verified.server_name, host, "server pinned to Bedrock");
    assert!(
        authorization_hidden(&rt.verified.sent_redacted),
        "the SigV4 Authorization credential must be hidden by selective disclosure"
    );

    // 5. A genuine converse response, and a FULL-LENGTH (>64-token) completion.
    assert!(
        disclosed.contains("\"output\"") || disclosed.contains("\"message\""),
        "the disclosed body is a genuine Bedrock converse response"
    );
    assert!(
        tokens.map(|t| t > 64).unwrap_or(false),
        "a full-length completion (>64 output tokens) must be attested; got {tokens:?}"
    );
}

/// **The DURABLE trust root, DRIVEN live.** The notary key is PERSISTED to a file
/// (provisioned once as an operator would), and its public pin is read OUT OF BAND — the value
/// a verifier holds independently of any single run. The Bedrock roundtrip runs under that
/// durable notary, and a verifier holding the KNOWN durable key (loaded from config, not
/// handed out by the run) ACCEPTS the attestation, while a wrong key is REJECTED (non-vacuous).
///
/// Cross-RUN stability of the persisted key is proven hermetically (no paid call) by
/// `tests/notary_durable_key.rs`; this test keeps to a single Bedrock call and proves the live
/// attestation verifies under the independently-loaded durable pin.
#[test]
#[ignore = "live: real network + paid Bedrock call + heavy MPC-TLS 2PC under a DURABLE pinned notary"]
fn bedrock_attested_under_durable_pinned_notary() {
    let creds = AwsCredentials {
        access_key_id: std::env::var("AWS_ACCESS_KEY_ID").expect("AWS_ACCESS_KEY_ID"),
        secret_access_key: std::env::var("AWS_SECRET_ACCESS_KEY").expect("AWS_SECRET_ACCESS_KEY"),
    };
    let now = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_secs();

    let host = "bedrock-runtime.us-east-1.amazonaws.com".to_string();
    let body = r#"{"messages":[{"role":"user","content":[{"text":"I raise the lantern and step into the flooded antechamber. Narrate in one vivid sentence."}]}],"system":[{"text":"You are the dungeon master of a drowned dark-fantasy vault."}],"inferenceConfig":{"maxTokens":64}}"#;

    let ex = BedrockExchange {
        host: host.clone(),
        region: "us-east-1".to_string(),
        model_id: "us.anthropic.claude-haiku-4-5-20251001-v1:0".to_string(),
        request_body: body.to_string(),
        creds,
        amz_date: amz_date(now),
    };

    // Provision the DURABLE notary key at an operator-controlled path (once), and record its
    // public pin OUT OF BAND — this is the anchor a verifier holds, independent of any run.
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let dir = std::env::temp_dir().join(format!("zkoracle-notary-live-{nanos}"));
    let key_path = dir.join("notary.key");
    let durable_pin = verifying_key_of(&load_or_generate_notary_key(&key_path).expect("provision"))
        .expect("durable pin");

    // Run the live Bedrock roundtrip under the DURABLE notary.
    let rt = run_bedrock_roundtrip_with_durable_notary(&ex, &key_path)
        .expect("real Bedrock MPC-TLS roundtrip under a durable pinned notary");

    let disclosed = String::from_utf8_lossy(&rt.verified.response_body);
    eprintln!("── PHASE-E: DURABLE PINNED NOTARY ATTESTS LIVE BEDROCK ──────────");
    eprintln!("durable key file: {}", key_path.display());
    eprintln!("pinned-key (fp) : {}", rt.notary_pin.key_fingerprint());
    eprintln!("pinned server   : {}", rt.verified.server_name);
    eprintln!("── DISCLOSED BODY (Claude's genuine in-session output) ──────────");
    eprintln!("{disclosed}");
    eprintln!("────────────────────────────────────────────────────────────────");

    // The run used the durable key: its pin equals the anchor we recorded out of band.
    assert_eq!(
        rt.notary_pin.verifying_key, durable_pin,
        "the live run must have used the DURABLE persisted key"
    );

    // A verifier holding the KNOWN durable key (loaded from config, NOT from the run) ACCEPTS.
    let known_durable = verifying_key_of(&load_notary_key(&key_path).expect("reload")).expect("vk");
    assert_eq!(
        known_durable, durable_pin,
        "reloaded key matches the anchor"
    );
    let accepted =
        verify_bedrock_presentation(&rt.presentation_bytes, &host, &rt.model_id, &known_durable);
    assert!(
        accepted.is_ok(),
        "a verifier holding the loaded DURABLE pin must ACCEPT: {accepted:?}"
    );

    // A WRONG key is REJECTED (non-vacuous pin).
    let wrong = verifying_key_of(&generate_notary_key().expect("wrong")).expect("wrong vk");
    assert_ne!(
        wrong, durable_pin,
        "the wrong key must differ from the durable pin"
    );
    let rejected = verify_bedrock_presentation(&rt.presentation_bytes, &host, &rt.model_id, &wrong);
    assert!(
        rejected.is_err(),
        "an attestation under the durable notary must be REJECTED under a wrong key"
    );
    eprintln!(
        "wrong-key rejected: true  (err = {})",
        rejected.unwrap_err()
    );

    assert_eq!(rt.verified.server_name, host, "server pinned to Bedrock");
    assert!(
        authorization_hidden(&rt.verified.sent_redacted),
        "the SigV4 Authorization credential must be hidden by selective disclosure"
    );

    let _ = std::fs::remove_dir_all(&dir);
}
