//! Lean marshal round-trip gate — runs `scripts/check-lean-marshal.sh` ARMED.
//!
//! Green-or-bust, same as [`crate::checks::demo_agent`]: a skipped check is a failing
//! check. This subsystem is the ONLY thing standing between "Ready for testnet
//! promotion." and an undetected Lean<->Rust executor divergence, so it must be
//! structurally capable of being red. It previously returned `Ok(())` — indistinguishable
//! from a real pass in `PreflightReport` — whenever `libdregg_lean.a` was absent, i.e. it
//! reported the same green whether the executors agree or whether nobody looked.
//!
//! The script already implements the honest failure: `DREGG_REQUIRE_LEAN_GATE=1` turns an
//! absent Lean archive into a nonzero exit naming exactly what is missing. We arm it here
//! rather than pre-empting it with our own skip, so the script stays the single source of
//! truth for what "the Lean gate passed" means.

use std::path::PathBuf;
use std::process::Command;

use crate::report::{CheckResult, run_check};

pub fn run() -> Vec<CheckResult> {
    vec![run_check("marshal_roundtrip_gate", check_marshal_roundtrip)]
}

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..")
}

fn check_marshal_roundtrip() -> Result<(), String> {
    let root = workspace_root();
    let script = root.join("scripts/check-lean-marshal.sh");
    if !script.is_file() {
        return Err(format!("missing gate script: {}", script.display()));
    }

    // ARMED: absent Lean archive => the script exits nonzero => this check goes RED.
    // Without this the gate cannot fail, and a green would assert nothing.
    let output = Command::new("bash")
        .arg(&script)
        .current_dir(&root)
        .env("DREGG_REQUIRE_LEAN_GATE", "1")
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
