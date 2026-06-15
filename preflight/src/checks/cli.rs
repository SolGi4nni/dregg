//! CLI functionality checks: spawn the dregg CLI binary as a subprocess.
//!
//! Every check here asserts something REAL about the CLI's offline surface
//! (green-or-bust): exact version string, the config-show report, the
//! doctor report shape, the hermetic `config init`, and a well-formed zsh
//! completion script. `config init` honors `DREGG_HOME`, so preflight runs it
//! against a throwaway temp root (asserting it writes there + exits 0) without
//! ever touching the operator's real `~/.dregg`.

use std::process::Command;

use crate::report::{CheckResult, run_check};

/// Number of health checks the `dregg doctor` report runs (mirrors
/// `cli/src/commands/doctor.rs`). Like the demo-agent EXAMPLES registry,
/// updating this is a conscious act when a doctor check is added/retired.
const DOCTOR_CHECK_COUNT: usize = 8;

pub fn run() -> Vec<CheckResult> {
    vec![
        run_check("cli_version", check_cli_version),
        run_check("cli_config_show", check_cli_config_show),
        run_check("cli_config_init", check_cli_config_init),
        run_check("cli_doctor", check_cli_doctor),
        run_check("cli_completions", check_cli_completions),
    ]
}

/// Helper: run a cargo command for dregg-cli with given args.
/// Returns Ok((stdout, stderr)) on exit 0, Err on non-zero exit or spawn failure.
fn run_cli(args: &[&str]) -> Result<(String, String), String> {
    let mut cmd_args = vec!["run", "-p", "dregg-cli", "--"];
    cmd_args.extend_from_slice(args);

    let output = Command::new("cargo")
        .args(&cmd_args)
        .output()
        .map_err(|e| format!("failed to spawn cargo: {e}"))?;

    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();

    if output.status.success() {
        Ok((stdout, stderr))
    } else {
        Err(format!(
            "exit code {:?}\nstdout: {}\nstderr: {}",
            output.status.code(),
            stdout,
            stderr
        ))
    }
}

/// `dregg version` exits 0 and reports EXACTLY the workspace version
/// (dregg-cli shares `version.workspace`, so `env!("CARGO_PKG_VERSION")`
/// here is the same value the CLI must print).
fn check_cli_version() -> Result<(), String> {
    let (stdout, stderr) = run_cli(&["version"])?;
    let version = env!("CARGO_PKG_VERSION");

    // Human mode prints `dregg {version}` to stderr; JSON mode prints
    // {"name":"dregg","version":...} to stdout. Both must carry the
    // exact workspace version and the binary name.
    let combined = format!("{stdout}\n{stderr}");
    if !combined.contains(version) || !combined.contains("dregg") {
        return Err(format!(
            "version output must report dregg + the workspace version {version:?}; \
             got stdout={stdout:?} stderr={stderr:?}"
        ));
    }
    Ok(())
}

/// `dregg config show` (read-only) exits 0 and reports the config path and
/// the effective node URL — the two facts every other CLI command depends on.
fn check_cli_config_show() -> Result<(), String> {
    let (stdout, stderr) = run_cli(&["config", "show"])?;
    let combined = format!("{stdout}\n{stderr}");

    for needle in ["Configuration", "Node URL"] {
        if !combined.contains(needle) {
            return Err(format!(
                "config show must report {needle:?}; got stdout={stdout:?} stderr={stderr:?}"
            ));
        }
    }
    Ok(())
}

/// `dregg config init` is HERMETIC: it honors `DREGG_HOME` (cli/src/config.rs
/// `config_path`), so preflight runs it against a throwaway temp root and
/// asserts it writes `$DREGG_HOME/config.toml` and exits 0 — WITHOUT touching
/// the operator's real `~/.dregg` (the path-injectable follow-up, now closed).
fn check_cli_config_init() -> Result<(), String> {
    let dir = std::env::temp_dir().join(format!("dregg-preflight-cfg-{}", std::process::id()));
    let cfg = dir.join("config.toml");
    let _ = std::fs::remove_dir_all(&dir);

    let output = Command::new("cargo")
        .args(["run", "-p", "dregg-cli", "--", "config", "init"])
        .env("DREGG_HOME", &dir)
        .output()
        .map_err(|e| format!("failed to spawn cargo: {e}"))?;
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();

    if !output.status.success() {
        let _ = std::fs::remove_dir_all(&dir);
        return Err(format!(
            "config init (DREGG_HOME-hermetic) must exit 0; got {:?}\nstdout={stdout}\nstderr={stderr}",
            output.status.code()
        ));
    }
    let wrote = cfg.exists();
    let _ = std::fs::remove_dir_all(&dir);
    if !wrote {
        return Err(format!(
            "config init must write $DREGG_HOME/config.toml ({}); stdout={stdout} stderr={stderr}",
            cfg.display()
        ));
    }
    Ok(())
}

/// `dregg doctor` exits 0 (its report carries the diagnosis; the command
/// itself must not error), runs EXACTLY the registered number of health
/// checks, and prints the pass/fail summary line. No node is required:
/// node-dependent checks may report ✗, but they must all RUN and be
/// reported.
fn check_cli_doctor() -> Result<(), String> {
    let (stdout, stderr) = run_cli(&["doctor"])?;
    let combined = format!("{stdout}\n{stderr}");

    // Each health check renders as an indicator line "  ✓ ..." / "  ✗ ...".
    let check_lines = combined
        .lines()
        .filter(|l| {
            let t = l.trim_start();
            t.starts_with('\u{2713}') || t.starts_with('\u{2717}')
        })
        .count();
    if check_lines != DOCTOR_CHECK_COUNT {
        return Err(format!(
            "doctor must report exactly {DOCTOR_CHECK_COUNT} health checks \
             (the registered count), found {check_lines} indicator lines:\n{combined}"
        ));
    }

    // The summary line: "All N checks passed." or "N passed, M failed."
    if !combined.contains("passed") {
        return Err(format!(
            "doctor must print a pass/fail summary:\n{combined}"
        ));
    }

    Ok(())
}

/// `dregg completions zsh` exits 0 and emits a structurally valid zsh
/// completion script for the `dregg` binary (clap_complete always opens
/// with `#compdef` and defines the `_dregg` function).
fn check_cli_completions() -> Result<(), String> {
    let (stdout, _stderr) = run_cli(&["completions", "zsh"])?;

    if !stdout.contains("#compdef dregg") {
        return Err("zsh completions must start with `#compdef dregg`".into());
    }
    if !stdout.contains("_dregg") {
        return Err("zsh completions must define the `_dregg` function".into());
    }
    Ok(())
}
