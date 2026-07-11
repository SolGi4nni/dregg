//! **Phase-E SigV4 spike — prove the hand-rolled signer is accepted by REAL Bedrock.**
//!
//! Signs a Bedrock `converse` POST with [`dregg_zkoracle_prove::sigv4`] using live creds + the
//! current UTC minute, then POSTs the request through `curl` with the EXACT signed headers
//! (curl `-H`, no `--aws-sigv4`, so curl does NOT re-sign — it sends our bytes verbatim). If
//! Bedrock returns a genuine Claude completion, the Rust signer produces a wire-correct SigV4
//! request — the same bytes the MPC-TLS prover would feed the 2PC.
//!
//! Run:
//! ```text
//! export AWS_ACCESS_KEY_ID=$(aws configure get aws_access_key_id --profile commonquant-ember)
//! export AWS_SECRET_ACCESS_KEY=$(aws configure get aws_secret_access_key --profile commonquant-ember)
//! cargo run -p dregg-zkoracle-prove --example sign_bedrock_live
//! ```

use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use dregg_zkoracle_prove::sigv4::{AwsCredentials, SignRequest, sign};

const HOST: &str = "bedrock-runtime.us-east-1.amazonaws.com";
const REGION: &str = "us-east-1";
// SigV4 subtlety: AWS canonicalizes the RECEIVED path by URI-encoding it, so the wire path uses
// the RAW `:` and the SIGNED canonical path uses `%3A` (AWS re-encodes the raw `:` to `%3A` and
// matches). Sending `%3A` on the wire makes AWS canonicalize it to `%253A` → signature mismatch.
const MODEL_RAW: &str = "us.anthropic.claude-haiku-4-5-20251001-v1:0"; // wire
const MODEL_ENC: &str = "us.anthropic.claude-haiku-4-5-20251001-v1%3A0"; // signed canonical

/// Format a unix time as SigV4 basic-ISO8601 `YYYYMMDDTHHMMSSZ` (UTC), no chrono dep.
fn amz_date(unix: u64) -> String {
    // days since epoch → civil date (Howard Hinnant's algorithm).
    let days = (unix / 86_400) as i64;
    let secs_of_day = unix % 86_400;
    let (h, mi, s) = (
        secs_of_day / 3600,
        (secs_of_day % 3600) / 60,
        secs_of_day % 60,
    );
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

fn main() {
    let creds = AwsCredentials {
        access_key_id: std::env::var("AWS_ACCESS_KEY_ID")
            .expect("set AWS_ACCESS_KEY_ID (see the doc header)"),
        secret_access_key: std::env::var("AWS_SECRET_ACCESS_KEY")
            .expect("set AWS_SECRET_ACCESS_KEY (see the doc header)"),
    };
    let now = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_secs();
    let date = amz_date(now);

    let body = br#"{"messages":[{"role":"user","content":[{"text":"I raise the lantern and step into the flooded antechamber. Narrate in one vivid sentence."}]}],"system":[{"text":"You are the dungeon master of a drowned dark-fantasy vault."}],"inferenceConfig":{"maxTokens":128}}"#;
    let signed_uri = format!("/model/{MODEL_ENC}/converse"); // `%3A` — what we SIGN
    let wire_uri = format!("/model/{MODEL_RAW}/converse"); // raw `:` — what we SEND

    let signed = sign(
        &SignRequest {
            method: "POST",
            host: HOST,
            canonical_uri: &signed_uri,
            content_type: "application/json",
            body,
            region: REGION,
            service: "bedrock",
            amz_date: &date,
        },
        &creds,
    );

    eprintln!("── PHASE-E SIGV4 SPIKE: Rust-signed request → REAL Bedrock ──────");
    eprintln!("wire path    : {wire_uri}   (signed canonical: {signed_uri})");
    eprintln!("X-Amz-Date   : {}", signed.amz_date);
    // The Authorization value is the SECRET the MPC-TLS selective disclosure HIDES.
    eprintln!("Authorization: {}", signed.authorization);
    eprintln!("────────────────────────────────────────────────────────────────");

    // POST the pre-signed request via curl (NO --aws-sigv4 → curl does not re-sign). Send the
    // RAW-`:` wire path; `--path-as-is` stops curl from touching it.
    let url = format!("https://{HOST}{wire_uri}");
    let out = Command::new("curl")
        .args([
            "-sS",
            "--path-as-is",
            "-X",
            "POST",
            &url,
            "-H",
            &format!("Host: {HOST}"),
            "-H",
            &format!("X-Amz-Date: {}", signed.amz_date),
            "-H",
            &format!("Authorization: {}", signed.authorization),
            "-H",
            "content-type: application/json",
            "--data-binary",
            std::str::from_utf8(body).unwrap(),
        ])
        .output()
        .expect("curl runs");
    println!("--- REAL BEDROCK RESPONSE (genuine in-session Claude output) ---");
    println!("{}", String::from_utf8_lossy(&out.stdout));
    if !out.stderr.is_empty() {
        eprintln!("[curl stderr] {}", String::from_utf8_lossy(&out.stderr));
    }
}
