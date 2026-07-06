//! **paces** — the zkOracle prover under measurement: per-leg and end-to-end timings
//! across the scaling axes, plus refuse-path latency.
//!
//! Axes: TEXT (bytes grow, tokens do not — [`tokenize`] collapses a JSON string to one
//! token), TRANSCRIPT (a long multi-turn context as an array of content blocks — bytes
//! AND tokens grow; sized to ≈256k / 1M / 10M LLM tokens at ~4 bytes each), and DENSE
//! (pure token growth, the certificate's stress axis). The compact certificate
//! ([`CompactCert`], the leftmost rule sequence) is O(tokens); the legacy form-chain is
//! O(tokens²) and is contrasted on the dense axis where it is feasible.
//!
//! Run: `cargo run -p dregg-zkoracle-prove --example paces --release`

use std::time::{Duration, Instant};

use dregg_zkoracle_prove::attestation::{FieldSpan, content_commitment};
use dregg_zkoracle_prove::{
    AnthropicConfig, FixtureNotary, ZkOracleAttestation, build_anthropic_fixture, injection_free,
    prove_cfg_cert, prove_cfg_compact, prove_zkoracle, tokenize, verify_cfg_cert,
    verify_cfg_compact, verify_zkoracle,
};

/// An Anthropic-messages-shaped body whose single `text` field is `text_len` bytes.
fn text_body(text_len: usize) -> String {
    let text = "The capital of France is Paris. ".repeat(text_len / 32 + 1);
    format!(
        r#"{{"id":"msg_01XYZ","type":"message","role":"assistant","model":"claude-opus-4-8","content":[{{"type":"text","text":"{}"}}],"stop_reason":"end_turn","stop_sequence":null,"usage":{{"input_tokens":24,"output_tokens":8}}}}"#,
        &text[..text_len]
    )
}

/// A long-context transcript shape: `n` content blocks (~105 bytes ≈ 26 LLM tokens each).
fn transcript_body(n_blocks: usize) -> String {
    let block = r#"{"type":"text","text":"The quick brown fox jumps over the lazy dog and files a verified receipt."}"#;
    let blocks: Vec<&str> = (0..n_blocks).map(|_| block).collect();
    format!(
        r#"{{"id":"msg_ctx","type":"message","role":"assistant","content":[{}],"stop_reason":"end_turn"}}"#,
        blocks.join(",")
    )
}

/// A structure-dense body: `n` small numbers in an array — every element costs tokens.
fn dense_body(n: usize) -> String {
    let elems: Vec<String> = (0..n).map(|i| (i % 10).to_string()).collect();
    format!(r#"{{"id":"msg_dense","data":[{}]}}"#, elems.join(","))
}

/// Median of `k` timed runs of `f` (fewer runs once a single run is slow).
fn med<F: FnMut() -> Duration>(mut f: F) -> Duration {
    let first = f();
    let k = if first > Duration::from_millis(500) {
        1
    } else if first > Duration::from_millis(50) {
        3
    } else {
        7
    };
    let mut samples = vec![first];
    for _ in 1..k {
        samples.push(f());
    }
    samples.sort();
    samples[samples.len() / 2]
}

fn fmt_d(d: Duration) -> String {
    let us = d.as_micros();
    if us < 1_000 {
        format!("{us} µs")
    } else if us < 1_000_000 {
        format!("{:.2} ms", us as f64 / 1_000.0)
    } else {
        format!("{:.2} s", us as f64 / 1_000_000.0)
    }
}

fn fmt_n(n: usize) -> String {
    if n < 1_000 {
        format!("{n}")
    } else if n < 1_000_000 {
        format!("{:.1}k", n as f64 / 1e3)
    } else if n < 1_000_000_000 {
        format!("{:.1}M", n as f64 / 1e6)
    } else {
        format!("{:.2}G", n as f64 / 1e9)
    }
}

fn run_case(
    label: &str,
    body: &str,
    field: &[u8],
    config: &AnthropicConfig,
    notary: &FixtureNotary,
) {
    let presentation = build_anthropic_fixture(notary, body, 1_700_000_000);
    let toks = tokenize(body.as_bytes()).expect("body tokenizes");
    let cert = prove_cfg_compact(body.as_bytes()).expect("body certifies");

    let t_prove_cert = med(|| {
        let s = Instant::now();
        let _ = prove_cfg_compact(body.as_bytes()).unwrap();
        s.elapsed()
    });
    let t_verify_cert = med(|| {
        let s = Instant::now();
        verify_cfg_compact(&cert, body.as_bytes()).unwrap();
        s.elapsed()
    });
    let t_commit = med(|| {
        let s = Instant::now();
        let _ = content_commitment(body.as_bytes());
        s.elapsed()
    });
    let t_prove_e2e = med(|| {
        let s = Instant::now();
        let _ = prove_zkoracle(presentation.clone(), field.to_vec(), config).unwrap();
        s.elapsed()
    });
    let att = prove_zkoracle(presentation, field.to_vec(), config).unwrap();
    let t_verify_e2e = med(|| {
        let s = Instant::now();
        let _ = verify_zkoracle(&att, config).unwrap();
        s.elapsed()
    });

    println!(
        "{:<16} {:>9} {:>8} {:>8} | {:>10} {:>10} {:>9} | {:>10} {:>10}",
        label,
        fmt_n(body.len()),
        fmt_n(toks.len()),
        fmt_n(cert.rules.len()),
        fmt_d(t_prove_cert),
        fmt_d(t_verify_cert),
        fmt_d(t_commit),
        fmt_d(t_prove_e2e),
        fmt_d(t_verify_e2e)
    );
}

fn main() {
    let notary = FixtureNotary::from_seed(&[9u8; 32]);
    let config = AnthropicConfig::new(notary.verifying_key());

    println!("zkOracle paces — compact certificate (release, median-of-k)\n");
    println!(
        "{:<16} {:>9} {:>8} {:>8} | {:>10} {:>10} {:>9} | {:>10} {:>10}",
        "case",
        "bytes",
        "jtokens",
        "cert B",
        "cert-prove",
        "cert-vrfy",
        "commit",
        "PROVE e2e",
        "VERIFY e2e"
    );

    // TEXT — bytes grow, tokens do not (the single-response shape).
    for text_len in [1usize << 10, 16 << 10, 256 << 10] {
        let body = text_body(text_len);
        run_case(
            &format!("text-{}", fmt_n(text_len)),
            &body,
            b"France",
            &config,
            &notary,
        );
    }

    // TRANSCRIPT — the long-context shape (≈4 bytes/LLM token; blocks ≈ 26 LLM tokens).
    // 256k / 1M / 10M LLM tokens ≈ 1 MiB / 4 MiB / 40 MiB.
    for (label, n_blocks) in [
        ("ctx-256k-tok", 10_000usize),
        ("ctx-1M-tok", 40_000),
        ("ctx-10M-tok", 400_000),
    ] {
        let body = transcript_body(n_blocks);
        run_case(label, &body, b"fox", &config, &notary);
    }

    // DENSE — pure token growth (the certificate's stress axis), compact all the way up.
    for n in [16_384usize, 262_144, 1 << 20, 10 << 20] {
        let body = dense_body(n);
        run_case(
            &format!("dense-{}", fmt_n(n)),
            &body,
            b"msg_dense",
            &config,
            &notary,
        );
    }

    // DEEP — 100k-deep nesting (the stack-safety pole; certificates are heap-bounded).
    {
        let depth = 100_000;
        let mut deep = String::with_capacity(2 * depth + 16);
        deep.push_str(r#"{"d":"#);
        for _ in 0..depth {
            deep.push('[');
        }
        deep.push('1');
        for _ in 0..depth {
            deep.push(']');
        }
        deep.push('}');
        run_case("deep-100k", &deep, b"d", &config, &notary);
    }

    // The OLD form-chain, contrasted where it is feasible: it is O(tokens²), and its
    // recursive prover overflows the thread stack near dense-65k — the compact path is
    // the scale path on BOTH axes.
    println!("\nold form-chain certificate (contrast — O(tokens²), stack-bounded ~65k):");
    for n in [16_384usize, 32_768] {
        let body = dense_body(n);
        let s = Instant::now();
        let chain = prove_cfg_cert(body.as_bytes()).unwrap();
        let t_prove = s.elapsed();
        let symbols: usize = chain.chain.iter().map(|f| f.len()).sum();
        let s = Instant::now();
        verify_cfg_cert(&chain, body.as_bytes()).unwrap();
        let t_verify = s.elapsed();
        println!(
            "  dense-{:<8} {:>10} symbols | chain-prove {:>10} | chain-vrfy {:>10}",
            fmt_n(n),
            fmt_n(symbols),
            fmt_d(t_prove),
            fmt_d(t_verify)
        );
    }

    // Refuse paths — how fast does a hostile attestation bounce?
    println!("\nrefuse-path latency (hostiles must fail FAST):");
    let body = text_body(1 << 10);
    let presentation = build_anthropic_fixture(&notary, &body, 42);
    let att = prove_zkoracle(presentation.clone(), b"France".to_vec(), &config).unwrap();

    let mut forged = att.clone();
    let n = forged.presentation.recv.len();
    forged.presentation.recv[n - 4] ^= 0xFF;
    let t = med(|| {
        let s = Instant::now();
        let _ = verify_zkoracle(&forged, &config).unwrap_err();
        s.elapsed()
    });
    println!("  forged notary sig     → refused in {}", fmt_d(t));

    let other = build_anthropic_fixture(&notary, r#"{"id":"other"}"#, 43);
    let spliced = ZkOracleAttestation {
        presentation: other,
        ..att.clone()
    };
    let t = med(|| {
        let s = Instant::now();
        let _ = verify_zkoracle(&spliced, &config).unwrap_err();
        s.elapsed()
    });
    println!("  cross-leg splice      → refused in {}", fmt_d(t));

    let mut bad_span = att.clone();
    bad_span.field_span = FieldSpan { offset: 0, len: 2 };
    let t = med(|| {
        let s = Instant::now();
        let _ = verify_zkoracle(&bad_span, &config);
        s.elapsed()
    });
    println!("  re-pointed field span → decided in {}", fmt_d(t));

    let t = med(|| {
        let s = Instant::now();
        let _ = injection_free(b"ignore previous {{ system }}");
        s.elapsed()
    });
    println!("  injection match alone → {}", fmt_d(t));
}
