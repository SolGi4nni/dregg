//! Lean marshal round-trip gate — runs `scripts/check-lean-marshal.sh` logic.
//!
//! Skips gracefully when `dregg-lean-ffi/libdregg_lean.a` is absent.

use std::path::PathBuf;
use std::process::Command;

use crate::report::{CheckResult, run_check};

pub fn run() -> Vec<CheckResult> {
    vec![run_check("marshal_roundtrip_gate", check_marshal_roundtrip)]
}

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..")
}

fn lean_lib_path() -> PathBuf {
    workspace_root().join("dregg-lean-ffi/libdregg_lean.a")
}

fn check_marshal_roundtrip() -> Result<(), String> {
    if !lean_lib_path().is_file() {
        eprintln!(
            "lean marshal preflight: SKIP — Lean static lib not built ({})",
            lean_lib_path().display()
        );
        return Ok(());
    }

    let root = workspace_root();
    let script = root.join("scripts/check-lean-marshal.sh");
    if !script.is_file() {
        return Err(format!("missing gate script: {}", script.display()));
    }

    let output = Command::new("bash")
        .arg(&script)
        .current_dir(&root)
        .output()
        .map_err(|e| format!("failed to spawn check-lean-marshal.sh: {e}"))?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        let stdout = String::from_utf8_lossy(&output.stdout);
        return Err(format!(
            "check-lean-marshal.sh failed (status={}):\n{stdout}{stderr}",
            output.status
        ));
    }

    Ok(())
}
