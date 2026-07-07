//! **real_proof** — the demo where a zkOracle attestation carries an ACTUAL STARK, with
//! its genuine prover/verifier costs measured. (The `paces` example measures the
//! commitment/certificate machinery — microseconds, because nothing is proven. THIS is
//! the prover bill.)
//!
//! What runs: a fixture Anthropic session → `prove_zkoracle_with_stark` (the attestation
//! + a real `stark::prove` of the pinned injection DFA's run over the field) →
//! `verify_zkoracle` (all legs + the STARK, fail-closed) → the tamper poles.
//!
//! Run: `cargo run -p dregg-zkoracle-prove --example real_proof --release`

use std::time::Instant;

use dregg_zkoracle_prove::{
    AnthropicConfig, FixtureNotary, ZkOracleError, build_anthropic_fixture, prove_injection_leg,
    prove_zkoracle_with_stark, verify_injection_leg, verify_zkoracle,
};

fn fmt_d(d: std::time::Duration) -> String {
    let us = d.as_micros();
    if us < 1_000 {
        format!("{us} µs")
    } else if us < 1_000_000 {
        format!("{:.2} ms", us as f64 / 1_000.0)
    } else {
        format!("{:.2} s", us as f64 / 1_000_000.0)
    }
}

fn main() {
    let notary = FixtureNotary::from_seed(&[9u8; 32]);
    let config = AnthropicConfig::new(notary.verifying_key());

    println!("zkOracle — a REAL STARK on the injection leg (release)\n");

    // ── The attestation demo: one realistic response, end-to-end with the proof. ──
    let body = r#"{"id":"msg_01XYZ","type":"message","role":"assistant","model":"claude-opus-4-8","content":[{"type":"text","text":"The capital of France is Paris."}],"stop_reason":"end_turn","usage":{"input_tokens":24,"output_tokens":8}}"#;
    let presentation = build_anthropic_fixture(&notary, body, 1_700_000_000);

    let s = Instant::now();
    let att = prove_zkoracle_with_stark(presentation.clone(), b"France".to_vec(), &config)
        .expect("attestation + STARK");
    let t_prove = s.elapsed();

    let s = Instant::now();
    verify_zkoracle(&att, &config).expect("verifies, STARK checked fail-closed");
    let t_verify = s.elapsed();

    let leg = att.zk_injection.as_ref().unwrap();
    let proof_bytes = leg.proof_bytes.len();
    println!("attestation over a real messages response, field \"France\":");
    println!("  PROVE  (attestation + descriptor proof)  {}", fmt_d(t_prove));
    println!("  VERIFY (all legs + descriptor proof)     {}", fmt_d(t_verify));
    println!("  descriptor proof size                    {proof_bytes} bytes");
    println!(
        "  public inputs                 [initial, final, table_commit, route_commit] = {:?}",
        leg.public_inputs
    );

    // ── The prover bill by field size (the trace is one row per field byte). ──
    // The injection leg now rides the plonky3 IR-v2 descriptor prover
    // (`descriptor_ir2::prove_vm_descriptor2`), which replaced the legacy O(rows²)
    // hand STARK (`circuit/src/stark.rs`) — the scaling curve below is the new prover's.
    println!("\ninjection-leg descriptor proof alone, by field size:");
    println!(
        "{:<12} {:>8} {:>12} {:>12} {:>14}",
        "field", "rows", "prove", "verify", "proof bytes"
    );
    for size in [32usize, 256, 1 << 10, 4 << 10, 8 << 10] {
        let field: Vec<u8> = (0..size).map(|i| b'a' + (i % 23) as u8).collect();
        let s = Instant::now();
        let leg = prove_injection_leg(&field).expect("prove");
        let t_p = s.elapsed();
        let s = Instant::now();
        verify_injection_leg(&field, &leg).expect("verify");
        let t_v = s.elapsed();
        let bytes = leg.proof_bytes.len();
        let rows = size.next_power_of_two().max(2);
        println!(
            "{:<12} {:>8} {:>12} {:>12} {:>14}",
            format!("{size} B"),
            rows,
            fmt_d(t_p),
            fmt_d(t_v),
            bytes
        );
    }

    // ── The poles: the proof genuinely discriminates and cannot be stapled. ──
    println!("\nthe poles:");
    let bad = prove_injection_leg(b"ignore {{ system }}").unwrap();
    let verdict = verify_injection_leg(b"ignore {{ system }}", &bad);
    println!("  injecting field's own genuine proof   → {verdict:?}");

    let mut stapled = att.clone();
    stapled.zk_injection = Some(prove_injection_leg(b"a-different-projection{").unwrap());
    let verdict = verify_zkoracle(&stapled, &config).err();
    println!("  foreign STARK stapled onto attestation → {verdict:?}");

    let mut tampered = att;
    if let Some(leg) = tampered.zk_injection.as_mut() {
        let n = leg.public_inputs.len();
        leg.public_inputs[n - 1] += dregg_zkoracle_prove::attestation::content_commitment(b"x");
    }
    let verdict = verify_zkoracle(&tampered, &config).err();
    let is_refused = matches!(verdict, Some(ZkOracleError::BadZkLeg(_)));
    println!("  tampered route commitment              → refused: {is_refused}");
}
