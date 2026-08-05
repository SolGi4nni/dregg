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

const CONFIG_SHA256: &str = "31ba37b4bebba44252b2b4da96c4d13a411e75b6d2b106f5459cb2b9ebca7b17";
const CANON_SHA256: &str = "f770d6bd6fd3fe09ec7c2fe882b74aa655c4ce6687f1a01e02e4faa468ba6181";

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

/// ⚑ The substitution must actually SUBSTITUTE.
///
/// This falsifier mutated the fixture by `replacen` of a hard-coded deployment id. When
/// `poa/deployments/epoch-1/` was re-pointed at the live solo federation on 2026-08-05 and
/// the fixture was re-emitted, that string stopped being present — so `replacen` replaced
/// NOTHING, the "substituted" input was the untouched valid one, and Lean correctly emitted.
/// It failed loudly here only because the expected verdict is an exact `Rejected`; had it
/// asserted merely "not the frozen bytes" it would have gone green while testing nothing.
///
/// A mutation-based falsifier is only a falsifier if the mutation happened, so that is now
/// asserted first and the id is read out of the fixture instead of typed twice.
#[test]
fn substituted_deployment_identity_is_a_lean_refusal() {
    const LIVE_DEPLOYMENT_ID: &str =
        "4db835cc36cd0d3b722e742334dc1dde9557601fe1334c7499ab023de4d6d45d";
    let original = fixture(INPUT_FILE);
    assert!(
        original.contains(LIVE_DEPLOYMENT_ID),
        "the fixture no longer carries the deployment id this probe substitutes; re-point it \
         rather than letting the mutation become a no-op"
    );
    let substituted = original.replacen(
        LIVE_DEPLOYMENT_ID,
        "679706a06ae8546a96b369a70dd7c5ee1c93fe47c789368087ab167c7b7dcebc",
        1,
    );
    assert_ne!(substituted, original, "the substitution changed nothing");
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
