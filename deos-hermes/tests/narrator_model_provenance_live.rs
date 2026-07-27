//! **THE NARRATOR'S MODEL PROVENANCE, LIVE — the one un-driven rung, named exactly.**
//!
//! Everything else in the provenance ladder is driven in CI:
//!   * the provenance GATE (a self-signed fixture refused on the live path) —
//!     `zkoracle-prove/tests/provenance_gate.rs`, light build;
//!   * REAL TRANSPORT provenance (a genuine MPC-TLS 2PC session, a separate notary that sees
//!     no plaintext, a real `presentation.verify()`, fused into the authentic leg) —
//!     `zkoracle-prove/tests/model_provenance_fused.rs` + `attested-dm/tests/dm_model_provenance.rs`.
//!
//! What those CANNOT show is **MODEL** provenance: their endpoint is a local test server that
//! echoes a reply the prover handed it, so the 2PC is real and the model is not. THIS test is
//! the rung that closes that — [`attest_turn_bedrock`] drives the 2PC prover against LIVE
//! `bedrock-runtime.<region>.amazonaws.com` over a real socket, verifies Amazon's genuine cert
//! chain against the Mozilla roots, SigV4-signs the request, hides the credential by selective
//! disclosure, and binds **the completion Claude actually returned in-session** — under a
//! SEPARATE durable notary whose key the verifier pins out-of-band.
//!
//! ⚑ **IT IS `#[ignore]`d BECAUSE IT NEEDS LIVE NETWORK + AWS CREDENTIALS + A PAID BEDROCK
//! CALL** — not because it is unfinished. It is wired end-to-end. Drive it with:
//!
//! ```text
//! export AWS_ACCESS_KEY_ID=$(aws configure get aws_access_key_id --profile commonquant-ember)
//! export AWS_SECRET_ACCESS_KEY=$(aws configure get aws_secret_access_key --profile commonquant-ember)
//! cd deos-hermes && cargo test --features zk-live --test narrator_model_provenance_live -- --ignored --nocapture
//! ```
#![cfg(feature = "zk-live")]

use std::time::{SystemTime, UNIX_EPOCH};

use deos_hermes::attest::{AttestationCarrier, attest_turn_bedrock, attestation_commitment};
use dregg_zkoracle_live::tlsn_bedrock::BedrockExchange;
use dregg_zkoracle_live::verify_zkoracle_live_host;
use dregg_zkoracle_prove::sigv4::AwsCredentials;
use dregg_zkoracle_prove::{AuthenticProvenance, authentic_provenance};

/// `YYYYMMDDTHHMMSSZ` from unix seconds (UTC), within AWS's 5-minute skew window.
fn amz_date(unix: u64) -> String {
    let days = (unix / 86_400) as i64;
    let sod = unix % 86_400;
    // Civil-from-days (Howard Hinnant's algorithm).
    let z = days + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z.rem_euclid(146_097);
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    let y = if m <= 2 { y + 1 } else { y };
    format!(
        "{:04}{:02}{:02}T{:02}{:02}{:02}Z",
        y,
        m,
        d,
        sod / 3600,
        (sod % 3600) / 60,
        sod % 60
    )
}

/// **THE NARRATOR'S TURN, PROVABLY FROM THE MODEL.** A live Bedrock Claude narration whose
/// attestation's authentic leg IS the real MPC-TLS presentation of that session — so
/// "provably came from the model" is literally true, not a self-signed fixture.
#[test]
#[ignore = "live: real network + AWS credentials + a paid Bedrock call + heavy MPC-TLS 2PC"]
fn narrator_turn_is_provably_from_the_live_model() {
    let creds = AwsCredentials {
        access_key_id: std::env::var("AWS_ACCESS_KEY_ID").expect("AWS_ACCESS_KEY_ID"),
        secret_access_key: std::env::var("AWS_SECRET_ACCESS_KEY").expect("AWS_SECRET_ACCESS_KEY"),
    };
    let now = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_secs();

    let host = "bedrock-runtime.us-east-1.amazonaws.com".to_string();
    // Small maxTokens so the response fits MAX_RECV_DATA and the 2PC stays cheap.
    let request_body = r#"{"messages":[{"role":"user","content":[{"text":"I raise the lantern and step into the flooded antechamber. Narrate in one vivid sentence."}]}],"system":[{"text":"You are the dungeon master of a drowned dark-fantasy vault."}],"inferenceConfig":{"maxTokens":64}}"#;

    let exchange = BedrockExchange {
        host: host.clone(),
        region: "us-east-1".to_string(),
        model_id: "us.anthropic.claude-haiku-4-5-20251001-v1:0".to_string(),
        request_body: request_body.to_string(),
        creds,
        amz_date: amz_date(now),
    };

    // A DURABLE notary key: provisioned once, reused on every run, so a verifier can pin the
    // SAME verifying key out-of-band forever after.
    let key_path = std::env::temp_dir().join("dregg-narrator-bedrock-notary.key");

    let carrier = AttestationCarrier::default();
    let turn = attest_turn_bedrock(&carrier, &exchange, &key_path)
        .expect("a live Bedrock MPC-TLS narration attests");

    eprintln!("── THE NARRATOR'S TURN, PROVABLY FROM THE LIVE MODEL ────────────");
    eprintln!("pinned host  : {}", turn.pinned_host);
    eprintln!("notary pin   : {:?}", turn.notary_pin.addr);
    eprintln!(
        "presentation : {} bytes",
        turn.attestation
            .tlsn_presentation
            .as_ref()
            .map(|b| b.len())
            .unwrap_or(0)
    );
    eprintln!(
        "commitment   : {}",
        hex(&attestation_commitment(&turn.attestation))
    );
    eprintln!("── CLAUDE'S GENUINE IN-SESSION NARRATION (the bound field) ─────");
    eprintln!("{}", String::from_utf8_lossy(&turn.field));
    eprintln!("────────────────────────────────────────────────────────────────");

    // (1) THE AUTHENTIC LEG IS THE REAL MPC-TLS PRESENTATION — not a fixture.
    assert_eq!(
        authentic_provenance(&turn.attestation),
        AuthenticProvenance::MpcTls,
        "the narration's authentic leg must be the real Bedrock session"
    );
    assert_eq!(turn.pinned_host, host, "server pinned to live Bedrock");

    // (2) IT VERIFIES under the PINNED separate notary + Amazon's real cert chain. This is
    //     the whole claim: a genuine `presentation.verify()` over a session with the real
    //     model endpoint vouches for these bytes.
    let out = verify_zkoracle_live_host(&turn.attestation, &host, &turn.notary_pin.verifying_key)
        .expect("the live Bedrock presentation authenticates the narration");
    assert_eq!(out.provenance, AuthenticProvenance::MpcTls);

    // (3) The bound field is Claude's ACTUAL words, a committed substring of the body the
    //     REAL session authenticated.
    let body = String::from_utf8_lossy(&out.session.response_body);
    assert!(
        body.contains("\"output\"") || body.contains("\"message\""),
        "the authenticated body is a genuine Bedrock converse response"
    );
    let field = String::from_utf8_lossy(&turn.field);
    assert!(
        body.contains(field.as_ref()),
        "the bound narration is a committed substring of the authenticated body"
    );
    assert!(!field.is_empty(), "Claude actually narrated something");

    // (4) The in-circuit prose tooth rides the live model turn too.
    assert!(
        turn.attestation.zk_injection.is_some(),
        "the Bedrock narrator path attaches the in-circuit STARK injection leg"
    );

    // (5) A WRONG notary pin is refused — so the accept above really rested on the pin.
    let fresh = dregg_zkoracle_live::notary_server::generate_notary_key().expect("a fresh key");
    let other = dregg_zkoracle_live::notary_server::verifying_key_of(&fresh)
        .expect("the fresh key has a verifying key");
    assert!(
        verify_zkoracle_live_host(&turn.attestation, &host, &other).is_err(),
        "an unpinned notary must not authenticate the narration"
    );
}

fn hex(b: &[u8; 32]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}
