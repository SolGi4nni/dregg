//! The documented operator key command must install the verified PQ keygen core
//! in its own process. Genesis doing so is insufficient: each CLI invocation has
//! fresh process-global install state.

use std::process::Command;

const NODE_BIN: &str = env!("CARGO_BIN_EXE_dregg-node");

#[test]
fn gen_validator_key_uses_the_verified_keygen_process_path() {
    let data_dir = tempfile::tempdir().expect("temporary validator data dir");
    let output = Command::new(NODE_BIN)
        .arg("gen-validator-key")
        .arg("--data-dir")
        .arg(data_dir.path())
        .arg("--json")
        .env("DREGG_REQUIRE_LEAN", "1")
        .env_remove("DREGG_ALLOW_UNAUDITED_PQ")
        .output()
        .expect("run dregg-node gen-validator-key");

    assert!(
        output.status.success(),
        "gen-validator-key must not fall through to unaudited ML-DSA keygen:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    let response: serde_json::Value =
        serde_json::from_slice(&output.stdout).expect("strict JSON command output");
    assert_eq!(
        response["public_key"].as_str().map(str::len),
        Some(64),
        "Ed25519 public key is exactly 32-byte hex",
    );
    assert_eq!(
        response["ml_dsa_public_key"].as_str().map(str::len),
        Some(1_952 * 2),
        "ML-DSA-65 public key is exactly 1952-byte hex",
    );
    assert_eq!(
        std::fs::read(data_dir.path().join("node.key"))
            .expect("generated validator seed")
            .len(),
        32,
    );
}
