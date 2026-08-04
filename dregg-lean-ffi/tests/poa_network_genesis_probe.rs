//! Native linked probe for the Lean-owned Path of Angels Signal genesis ceremony.
//!
//! The fixture is the live epoch-1 tuple frozen from Lean. The probe calls the real linked symbol,
//! compares every returned byte with the frozen Lean output, and then inspects only enough JSON to
//! assert that the embedded config/Canon strings and their digest labels are exact. It does not
//! reconstruct either semantic object or persist a head.
#![cfg(feature = "lean-lib")]

use dregg_lean_ffi::poa_network_genesis_ffi::{
    evaluate_poa_network_genesis, poa_network_genesis_available, PoaNetworkGenesisVerdict,
};
use serde_json::Value;

const INPUT_FILE: &str = include_str!("fixtures/poa-network-genesis-input-v1.json");
const OUTPUT_FILE: &str = include_str!("fixtures/poa-network-genesis-output-v1.json");
const CONFIG_FILE: &str = include_str!("fixtures/poa-network-genesis-config-v1.json");
const CANON_FILE: &str = include_str!("fixtures/poa-network-genesis-canon-v1.json");

const CONFIG_SHA256: &str = "09509f00ace2908a3fa06c641361255a752c30669da0874b87e8265f4f53a1bf";
const CANON_SHA256: &str = "aad848fbf40d82d3efb1f6f5fe6ea1fb7704bccc839710f0202951ec4ebd667a";

fn fixture(bytes: &'static str) -> &'static str {
    bytes
        .strip_suffix('\n')
        .expect("frozen PoA network genesis fixture must have exactly one file newline")
}

#[test]
fn live_genesis_export_returns_exact_lean_bytes_hashes_and_embedded_images() {
    assert!(
        poa_network_genesis_available(),
        "dregg_poa_network_genesis is absent or initialization failed; this is refusal, not skip"
    );

    let emitted = match evaluate_poa_network_genesis(fixture(INPUT_FILE))
        .expect("linked Lean genesis evaluator must be callable")
    {
        PoaNetworkGenesisVerdict::Emitted(bytes) => bytes,
        PoaNetworkGenesisVerdict::Rejected => panic!("frozen live tuple was refused by Lean"),
    };

    assert_eq!(
        emitted,
        fixture(OUTPUT_FILE),
        "complete Lean emission drifted"
    );

    let output: Value = serde_json::from_str(&emitted).expect("Lean emitted valid JSON");
    assert_eq!(
        output.get("config_json").and_then(Value::as_str),
        Some(fixture(CONFIG_FILE)),
        "host must receive the exact standalone config string"
    );
    assert_eq!(
        output.get("canon_json").and_then(Value::as_str),
        Some(fixture(CANON_FILE)),
        "host must receive the exact standalone Canon string"
    );
    assert_eq!(
        output.get("config_sha256").and_then(Value::as_str),
        Some(CONFIG_SHA256)
    );
    assert_eq!(
        output.get("canon_sha256").and_then(Value::as_str),
        Some(CANON_SHA256)
    );
}

#[test]
fn substituted_deployment_identity_is_a_lean_refusal() {
    let substituted = fixture(INPUT_FILE).replacen(
        "d933b11beb5adb502cc0511b8124c98192dbbed143ffbb1b5242ff6e0cf97c9e",
        "679706a06ae8546a96b369a70dd7c5ee1c93fe47c789368087ab167c7b7dcebc",
        1,
    );
    assert_eq!(
        evaluate_poa_network_genesis(&substituted)
            .expect("linked Lean genesis evaluator must be callable"),
        PoaNetworkGenesisVerdict::Rejected
    );
}

#[test]
fn trailing_byte_is_a_lean_refusal() {
    let mut noncanonical = fixture(INPUT_FILE).to_owned();
    noncanonical.push('\n');
    assert_eq!(
        evaluate_poa_network_genesis(&noncanonical)
            .expect("linked Lean genesis evaluator must be callable"),
        PoaNetworkGenesisVerdict::Rejected
    );
}
