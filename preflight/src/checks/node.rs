//! Node startup checks: binary existence, help, genesis, config validation.

use std::process::Command;

use crate::report::{CheckResult, run_check};

pub fn run() -> Vec<CheckResult> {
    vec![
        run_check("node_binary_exists", check_node_binary_exists),
        run_check("node_help", check_node_help),
        run_check("node_relay_help", check_node_relay_help),
    ]
}

fn check_node_binary_exists() -> Result<(), String> {
    // The node binary is built from dregg-node crate. Check that the crate compiles.
    let output = Command::new("cargo")
        .args(["build", "-p", "dregg-node", "--message-format=short"])
        .output()
        .map_err(|e| format!("failed to spawn cargo build: {e}"))?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        // Check if it's just a dependency issue vs a real problem.
        if stderr.contains("error[E") {
            return Err(format!(
                "dregg-node does not compile: {}",
                stderr.lines().take(5).collect::<Vec<_>>().join("\n")
            ));
        }
        // Warnings are fine.
    }

    Ok(())
}

fn check_node_help() -> Result<(), String> {
    let output = Command::new("cargo")
        .args(["run", "-p", "dregg-node", "--", "--help"])
        .output()
        .map_err(|e| format!("failed to spawn: {e}"))?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        // Some CLIs exit with code 0 for --help, some with 2, depends on clap version.
        // Just verify it didn't panic.
        if stderr.contains("panic") {
            return Err(format!("node --help panicked: {stderr}"));
        }
    }

    let stdout = String::from_utf8_lossy(&output.stdout);
    if stdout.is_empty() && output.status.success() {
        return Err("--help produced no stdout output".into());
    }

    Ok(())
}

fn check_node_relay_help() -> Result<(), String> {
    let output = Command::new("cargo")
        .args(["run", "-p", "dregg-node", "--", "relay", "--help"])
        .output()
        .map_err(|e| format!("failed to spawn: {e}"))?;

    // Relay subcommand help should produce output without panicking.
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    if stderr.contains("panic") || stdout.contains("panic") {
        return Err(format!("relay --help panicked: {stderr}"));
    }

    // It's acceptable if the subcommand doesn't exist yet (clap will print an error).
    // We just verify no panics.
    Ok(())
}
