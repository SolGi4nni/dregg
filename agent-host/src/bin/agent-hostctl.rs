//! `agent-hostctl` — enrol SSH keys into hosted agent sessions and emit
//! the OpenSSH `authorized_keys` the edge serves.
//!
//! ```text
//!   agent-hostctl --registry reg.json enroll \
//!       --account dga1_alice --budget 500 --caps fs,http:api.github.com \
//!       --key "ssh-ed25519 AAAA… alice@laptop" [--brain nemotron]
//!   agent-hostctl --registry reg.json revoke --key "ssh-ed25519 AAAA…"
//!   agent-hostctl --registry reg.json list
//!   agent-hostctl --registry reg.json authorized-keys [--attach-bin /usr/local/bin/dregg-agent]
//! ```
//!
//! The `authorized-keys` output is what you drop at the host agent-user's
//! `~/.ssh/authorized_keys` (or serve from an `AuthorizedKeysCommand`). Each line
//! drops the connecting key into its OWN confined `dregg-agent attach` session.
//!
//! HOSTED CONFINEMENT: the enrol path ALWAYS REFUSES a raw `shell` cap (a hosted
//! shell can read the operator's keys past the in-process env-scrub, and the
//! per-tenant OS jail that would make it safe is not yet wired into any run path).
//! Grant the lexically-confined tools only (`fs`, `http:HOST`, `git:HOST`,
//! `pay:VENDOR`, `provision:PROVIDER`, `cell:/path`).

use std::process::ExitCode;

use agent_host::AgentHostRegistry;

fn flag<'a>(args: &'a [String], name: &str) -> Option<&'a str> {
    args.iter()
        .position(|a| a == name)
        .and_then(|i| args.get(i + 1))
        .map(String::as_str)
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let registry_path = flag(&args, "--registry").unwrap_or("agent-host-registry.json");

    let mut reg = match AgentHostRegistry::load(registry_path) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("cannot load registry {registry_path}: {e}");
            return ExitCode::FAILURE;
        }
    };
    if let Some(bin) = flag(&args, "--attach-bin") {
        reg = reg.with_attach_bin(bin);
    }
    // NOTE: `--os-isolation` is intentionally NOT accepted. It used to re-grant a raw
    // `shell` on the operator-key-holding host on the mere assertion of a per-tenant
    // OS jail, but that jail (`isolation.rs`) is not wired into any run path — the flag
    // confined nothing. A hosted session is always shell-disabled until the jail is
    // genuinely wired (`dregg-agent` itself hard-errors on the flag).
    if args.iter().any(|a| a == "--os-isolation") {
        eprintln!(
            "--os-isolation is not supported: per-tenant OS isolation is not yet wired, so a \
             hosted session cannot safely grant a raw shell. Enrolments stay shell-disabled. \
             See the isolation module docs."
        );
        return ExitCode::FAILURE;
    }

    // The subcommand is the first recognized verb (positional order-independent of
    // the `--registry` / `--attach-bin` flag values, which are also non-`--` tokens).
    let cmd = args
        .iter()
        .map(String::as_str)
        .find(|a| matches!(*a, "enroll" | "revoke" | "list" | "authorized-keys"));
    match cmd {
        Some("enroll") => {
            let account = flag(&args, "--account").unwrap_or("");
            let key = flag(&args, "--key").unwrap_or("");
            let caps = flag(&args, "--caps").unwrap_or(agent_host::DEFAULT_HOSTED_CAPS);
            let brain = flag(&args, "--brain").unwrap_or("");
            let budget: i64 = flag(&args, "--budget")
                .and_then(|s| s.parse().ok())
                .unwrap_or(500);
            match reg.enroll_with_brain(account, key, budget, caps, brain) {
                Ok(r) => {
                    println!(
                        "enrolled {} (budget {}¢, caps {}) for key …{}",
                        r.account,
                        r.budget_cents,
                        r.caps,
                        key.split_whitespace().last().unwrap_or("")
                    );
                }
                Err(e) => {
                    eprintln!("enroll failed: {e}");
                    return ExitCode::FAILURE;
                }
            }
        }
        Some("revoke") => {
            let key = flag(&args, "--key").unwrap_or("");
            match reg.revoke(key) {
                Some(r) => println!("revoked {}", r.account),
                None => {
                    eprintln!("no account enrolled for that key");
                    return ExitCode::FAILURE;
                }
            }
        }
        Some("list") => {
            if reg.records().is_empty() {
                println!("(no accounts enrolled)");
            }
            for r in reg.records() {
                println!(
                    "{}  budget {}¢  caps {}  brain {}",
                    r.account,
                    r.budget_cents,
                    r.caps,
                    if r.brain.is_empty() {
                        "(default)"
                    } else {
                        &r.brain
                    }
                );
            }
        }
        Some("authorized-keys") => {
            print!("{}", reg.authorized_keys());
            return ExitCode::SUCCESS; // no save needed (read-only)
        }
        _ => {
            eprintln!(
                "usage: agent-hostctl --registry FILE \
                 (enroll|revoke|list|authorized-keys) [flags]"
            );
            return ExitCode::FAILURE;
        }
    }

    if let Err(e) = reg.save(registry_path) {
        eprintln!("cannot save registry {registry_path}: {e}");
        return ExitCode::FAILURE;
    }
    ExitCode::SUCCESS
}
