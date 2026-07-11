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

use dregg_zkoracle_prove::sigv4::AwsCredentials;
use dregg_zkoracle_prove::tlsn_bedrock::{
    BedrockExchange, authorization_hidden, run_bedrock_roundtrip_blocking,
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
