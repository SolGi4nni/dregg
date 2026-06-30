//! `dregg-agent` — the **flexible, live, bounded operator agent** CLI.
//!
//! ```text
//!   dregg-agent run --goal "<natural-language goal>" [--budget N] [--caps …]
//!                   [--workdir DIR] [--model M] [--base URL] [--step-cap N]
//!                   [--out run.json] [--record resp.json | --replay resp.json] [--no-scale]
//!   dregg-agent verify <run.json> [--tamper]
//! ```
//!
//! `run` gives a live model an arbitrary goal + a budget + a cap bundle, and runs
//! a real reason → act → observe loop: the model decides the next tool call, the
//! run loop **cap-gates + meters + receipts** it, runs it for REAL (a real shell /
//! fs / http / git, or a budget-gated spend), feeds the result back, and repeats
//! until the model finishes or the budget / step-cap bounds it. Hand it a
//! *different* `--goal` and it genuinely adapts — that is the proof it is not
//! scripted. It writes `run.json`; `verify` re-witnesses the whole run offline
//! (chain + bound), host untrusted; `--tamper` flips one line and it is caught
//! (`BadSignature`). The default model is a confirmed-live NVIDIA Nemotron.

use std::process::ExitCode;

use dregg_agent::live::{LiveRun, verify_live};

/// The default live model: confirmed to do native OpenAI `tool_calls` on the
/// NVIDIA NIM endpoint for this account (Ultra/70b are listed but 404 on
/// inference here; super-49b is the working agentic model).
#[cfg(feature = "live-brain")]
const DEFAULT_MODEL: &str = "nvidia/llama-3.3-nemotron-super-49b-v1";
/// The NVIDIA NIM OpenAI-compatible base.
#[cfg(feature = "live-brain")]
const DEFAULT_BASE: &str = "https://integrate.api.nvidia.com/v1";

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.first().map(String::as_str) {
        Some("run") => cmd_run(&args[1..]),
        Some("verify") => cmd_verify(&args[1..]),
        Some("-h") | Some("--help") | None => {
            usage();
            ExitCode::SUCCESS
        }
        Some(other) => {
            eprintln!("unknown command `{other}`\n");
            usage();
            ExitCode::FAILURE
        }
    }
}

fn usage() {
    println!(
        "dregg-agent — a flexible, live, bounded operator agent\n\n\
         USAGE:\n\
         \x20 dregg-agent run --goal \"<goal>\" [--budget N] [--caps a,b,…] [--workdir DIR]\n\
         \x20                 [--model M] [--base URL] [--step-cap N] [--out run.json]\n\
         \x20                 [--record resp.json | --replay resp.json] [--no-scale]\n\
         \x20 dregg-agent verify <run.json> [--tamper]\n\n\
         CAPS (comma-separated): shell, fs, git:HOST, http:HOST, spend, run_tests,\n\
         \x20                     cell:/path  (each is a per-tool/per-resource grant)\n\n\
         The agent runs a real reason→act→observe loop on a live model; every tool\n\
         call is cap-gated + metered + receipted. verify re-witnesses run.json\n\
         offline; --tamper flips a line and it is caught (BadSignature)."
    );
}

#[cfg(feature = "live-brain")]
fn flag<'a>(args: &'a [String], name: &str) -> Option<&'a str> {
    args.iter()
        .position(|a| a == name)
        .and_then(|i| args.get(i + 1))
        .map(String::as_str)
}

fn has(args: &[String], name: &str) -> bool {
    args.iter().any(|a| a == name)
}

// ─────────────────────────────── verify (std-only) ───────────────────────────

fn cmd_verify(args: &[String]) -> ExitCode {
    let Some(path) = args.iter().find(|a| !a.starts_with("--")) else {
        eprintln!("usage: dregg-agent verify <run.json> [--tamper]");
        return ExitCode::FAILURE;
    };
    let tamper = has(args, "--tamper");
    let raw = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("cannot read {path}: {e}");
            return ExitCode::FAILURE;
        }
    };
    let mut run: LiveRun = match serde_json::from_str(&raw) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("cannot parse {path}: {e}");
            return ExitCode::FAILURE;
        }
    };

    rule();
    if tamper {
        println!("  THE TEETH — flip one receipted line; the audit catches it");
    } else {
        println!("  PROVE — re-witness the whole run offline, trusting no host");
    }
    rule();
    println!();

    if tamper {
        // Prefer a spend receipt (the "I barely paid" forgery); else any receipt.
        let idx = run
            .run
            .receipts
            .iter()
            .position(|r| r.action.starts_with("spend:"))
            .or(if run.run.receipts.is_empty() {
                None
            } else {
                Some(0)
            });
        match idx {
            Some(i) => {
                let r = &mut run.run.receipts[i];
                let was = r.cost;
                // Guaranteed-different value (so the body hash actually moves).
                r.cost = if was == 1 { 999 } else { 1 };
                println!(
                    "[tamper] flipped {} cost: {was}¢ → {}¢ (\"it barely spent anything\")\n",
                    r.action, r.cost
                );
            }
            None => println!("[tamper] no receipt to flip (the model committed nothing)\n"),
        }
    }

    match verify_live(&run) {
        Ok(v) => {
            println!("   GOAL: {}", run.goal);
            println!(
                "   ✓ chain    {} action(s), signed + unbroken + tamper-evident",
                v.actions
            );
            println!(
                "   ✓ bound    consumed {}¢ ≤ ceiling {}¢; headroom {}¢",
                v.consumed, v.budget, v.headroom
            );
            if run.subagent_run.is_some() {
                println!(
                    "   ✓ scale    sub-agent chain re-witnessed — {} action(s)",
                    v.subagent_actions
                );
            }
            println!("\n   VERDICT: ✓ the live agent run re-verifies offline.\n");
            ExitCode::SUCCESS
        }
        Err(e) => {
            println!("   ✗ REJECTED: {e}");
            println!("\n   VERDICT: ✗ the audit caught it — the proof does not lie.\n");
            // A caught tamper is the INTENDED outcome of --tamper.
            if tamper {
                ExitCode::SUCCESS
            } else {
                ExitCode::FAILURE
            }
        }
    }
}

fn rule() {
    println!("════════════════════════════════════════════════════════════════════");
}

// ─────────────────────────────── run (needs live-brain) ──────────────────────

#[cfg(not(feature = "live-brain"))]
fn cmd_run(_args: &[String]) -> ExitCode {
    eprintln!(
        "`run` drives a LIVE model + real http and needs the `live-brain` feature.\n\
         Rebuild:  cargo build -p dregg-agent --bin dregg-agent --features live-brain"
    );
    ExitCode::FAILURE
}

#[cfg(feature = "live-brain")]
fn cmd_run(args: &[String]) -> ExitCode {
    live::run(args)
}

#[cfg(feature = "live-brain")]
mod live {
    use super::*;
    use std::path::{Path, PathBuf};
    use std::process::{Command, Stdio};
    use std::sync::mpsc;
    use std::time::Duration;

    use dregg_agent::agent::{AgentAction, AgentCloud, AgentSpec, PlannedBrain, ToolCall, op};
    use dregg_agent::brain::{
        LiveOpenAICompatCaller, OpenAICompatBrain, OpenAICompatCaller, ProviderKey,
    };
    use dregg_agent::live::{LiveRun, transcript_of};
    use dregg_agent::toolkit::Toolkit;
    use dregg_agent::tools::{HttpResp, OperatorTools, ShellOut};
    use serde_json::Value;

    /// A real, default-demoable goal that exercises git + shell + fs + http +
    /// the budget-gated spend — all real, ~30-60s, network-light.
    const DEFAULT_GOAL: &str = "Clone the small repo https://github.com/octocat/Hello-World \
        into your workdir, list the files you cloned and read the README, then GET \
        https://api.github.com/repos/octocat/Hello-World and report the repo's description. \
        Finally pay 12 cents to the vendor 'compute' via stripe_pay for the work you did. \
        Stay under budget and call finish with a one-line summary of what you found.";

    const DEFAULT_CAPS: &str = "shell,fs,git:github.com,http:api.github.com,spend";

    pub fn run(args: &[String]) -> ExitCode {
        let goal = flag(args, "--goal").unwrap_or(DEFAULT_GOAL).to_string();
        let budget: i64 = flag(args, "--budget")
            .and_then(|s| s.parse().ok())
            .unwrap_or(500);
        let caps_str = flag(args, "--caps").unwrap_or(DEFAULT_CAPS).to_string();
        let model = flag(args, "--model").unwrap_or(DEFAULT_MODEL).to_string();
        let base = flag(args, "--base").unwrap_or(DEFAULT_BASE).to_string();
        let step_cap: u64 = flag(args, "--step-cap")
            .and_then(|s| s.parse().ok())
            .unwrap_or(16);
        let out = flag(args, "--out").unwrap_or("run.json").to_string();
        let scale = !has(args, "--no-scale");

        // For a FAITHFUL film replay, reuse the recorded run's workdir by default
        // (the model's tool calls may carry absolute paths tied to it; a different
        // workdir would correctly cap-refuse them). An explicit --workdir overrides.
        let replay_arg = flag(args, "--replay").map(String::from);
        let recorded_workdir = replay_arg
            .as_deref()
            .and_then(|p| load_record(p).ok())
            .map(|r| r.workdir);
        let workdir = flag(args, "--workdir")
            .map(PathBuf::from)
            .or_else(|| {
                recorded_workdir
                    .filter(|s| !s.is_empty())
                    .map(PathBuf::from)
            })
            .unwrap_or_else(|| {
                std::env::temp_dir().join(format!("dregg-agent-wd-{}", std::process::id()))
            });
        if let Err(e) = std::fs::create_dir_all(&workdir) {
            eprintln!("cannot create workdir {}: {e}", workdir.display());
            return ExitCode::FAILURE;
        }
        let workdir = workdir.canonicalize().unwrap_or(workdir);
        let workdir_s = workdir.to_string_lossy().to_string();

        // Build the cap bundle + the advertised tool lists from --caps.
        let Bundle {
            mut spec,
            services,
            op_tools,
            cells,
        } = match parse_caps(&caps_str, "agent:operator", budget, &workdir_s) {
            Ok(b) => b,
            Err(e) => {
                eprintln!("bad --caps: {e}");
                return ExitCode::FAILURE;
            }
        };
        // The budget is denominated in cents; one op costs 1¢, a spend costs its amount.
        spec.asset = "USD-CENTS".into();

        let cloud = AgentCloud::new();
        let handle = match cloud.deploy(&spec) {
            Ok(h) => h,
            Err(e) => {
                eprintln!("deploy failed: {e}");
                return ExitCode::FAILURE;
            }
        };

        rule();
        println!("  dregg-agent — a flexible, live, bounded operator agent");
        rule();
        println!();
        println!("  GOAL    {goal}");
        println!("  MODEL   {model} @ {base}");
        println!("  BUDGET  {budget}¢   STEP-CAP {step_cap}   WORKDIR {workdir_s}");
        println!("  CAPS    {}", handle.caps.join("  ·  "));

        // Funding (honest): a real Stripe test PaymentIntent if a test key is
        // present; otherwise a real budget-ledger allowance, labeled as such.
        let stripe_key = stripe_test_key();
        let funding = match &stripe_key {
            Some(_) => format!("Stripe test-mode PaymentIntent for {budget}¢ (live money leg)"),
            None => format!(
                "operator allowance of {budget}¢ (REAL budget-ledger ceiling; set ~/.stripekey \
                 or STRIPE_API_KEY for a live Stripe test PaymentIntent money leg)"
            ),
        };
        println!("  FUNDING {funding}");
        println!();

        // The real operator toolkit: real shell (timeout + cwd), real http
        // (reqwest), real fs (std, workdir-confined), git via the shell runner,
        // plus a budget-gated stripe_pay spend (real Stripe test call if a key is set).
        let timeout = Duration::from_secs(60);
        let inner = build_inner_toolkit(stripe_key);
        let toolkit = OperatorTools::new(inner, &workdir)
            .with_shell(move |cmd, cwd| real_shell(cmd, cwd, timeout))
            .with_http(real_http);

        // The brain: a live model over native tool_calls (confirmed), driving the
        // reason→act→observe loop. Replay re-feeds a recorded transcript.
        let replay = replay_arg;
        let record = flag(args, "--record").map(String::from);

        println!(
            "──[ reason → act → observe ]── (live; each step is cap-gated · metered · receipted)\n"
        );

        let report = if let Some(rp) = &replay {
            let responses = match load_record(rp) {
                Ok(r) => r.responses,
                Err(e) => {
                    eprintln!("cannot load replay {rp}: {e}");
                    return ExitCode::FAILURE;
                }
            };
            println!(
                "  [mode] REPLAY of a recorded brain ({} responses) — tools execute for real\n",
                responses.len()
            );
            let caller = dregg_agent::brain::RecordedOpenAICaller::new(responses);
            let mut brain = make_brain(
                &goal,
                &services,
                &cells,
                &op_tools,
                ProviderKey::unauthenticated(),
                &base,
                &model,
                caller,
                step_cap,
            );
            cloud.run_with_toolkit(&handle, &mut brain, &toolkit)
        } else {
            let key = match nvidia_key() {
                Some(k) => k,
                None => {
                    eprintln!(
                        "no model key: put it in ~/.nvidiakey or set NVIDIA_API_KEY \
                         (or use --replay <resp.json>)"
                    );
                    return ExitCode::FAILURE;
                }
            };
            let caller = TeeCaller::new(LiveOpenAICompatCaller::new());
            let mut brain = make_brain(
                &goal, &services, &cells, &op_tools, key, &base, &model, caller, step_cap,
            );
            let report = cloud.run_with_toolkit(&handle, &mut brain, &toolkit);
            if let Some(rec) = &record {
                let responses = brain.caller().recorded();
                match save_record(rec, &workdir_s, &responses) {
                    Ok(()) => println!(
                        "\n  [record] saved {} model responses to {rec} (replay with --replay)",
                        responses.len()
                    ),
                    Err(e) => eprintln!("\n  [record] failed to save {rec}: {e}"),
                }
            }
            report
        };

        // Narrate the real transcript (every line traces to a receipt / refusal).
        let transcript = transcript_of(&report);
        for s in &transcript {
            let mark = if s.outcome == "admitted" {
                "✓"
            } else {
                "✗"
            };
            println!("  {mark} step {:>2}  {}", s.n, s.action);
            println!("           {}", s.outcome);
            if let Some(sum) = &s.tool_summary {
                for line in indent(sum, "           │ ").lines() {
                    println!("{line}");
                }
            }
        }
        if transcript.is_empty() {
            println!("  (the model committed no admitted action)");
        }
        println!();
        println!(
            "  → {} admitted · {} cap-refused · {} budget-refused · consumed {}¢ · headroom {}¢",
            report.admitted,
            report.cap_refused,
            report.budget_refused,
            report.consumed,
            report.headroom
        );
        println!();

        // SCALE: fork a sub-agent with a NARROWER bundle it provably cannot exceed.
        let subagent_run = if scale {
            Some(run_scale_demo(&cloud, &handle, &toolkit))
        } else {
            None
        };

        let live_run = LiveRun {
            goal,
            model,
            endpoint: base,
            funding,
            budget_cents: budget,
            caps: handle.caps.clone(),
            workdir: workdir_s,
            transcript,
            run: report,
            subagent_run,
        };

        let json = serde_json::to_string_pretty(&live_run).expect("run serializes");
        if let Err(e) = std::fs::write(&out, json) {
            eprintln!("failed to write {out}: {e}");
            return ExitCode::FAILURE;
        }
        println!("  → wrote the receipt to {out}");
        println!("  → audit it yourself:  dregg-agent verify {out}\n");
        ExitCode::SUCCESS
    }

    // ── the SCALE / attenuation demo (deterministic, real tools) ──────────────

    fn run_scale_demo(
        cloud: &AgentCloud,
        parent: &dregg_agent::agent::AgentHandle,
        toolkit: &OperatorTools,
    ) -> dregg_agent::agent::AgentRunReport {
        println!("──[ SCALE ]── fork a sub-agent with a NARROWER cap bundle (no-amplify)\n");
        // The child keeps shell ONLY (drops http / spend / fs if the parent had them).
        let child_spec = AgentSpec::new("agent:operator/burst", parent.budget.min(50)).with_shell();
        let child = match cloud.deploy_subagent(parent, &child_spec) {
            Ok(c) => c,
            Err(e) => {
                println!("   (sub-agent not forked: {e})\n");
                // Return an empty, still-verifiable report by running an empty plan.
                return cloud.run_with_toolkit(parent, &mut PlannedBrain::new(vec![]), toolkit);
            }
        };
        println!(
            "   ✓ sub-agent deployed (shell only, budget {}¢) — provably narrower",
            child.budget
        );
        // One in-bundle op + two it CANNOT reach (no http grant, no spend grant).
        let plan = vec![
            AgentAction::Op(ToolCall::new(
                "shell",
                [("cmd".into(), "echo 'sub-agent at work'".into())],
            )),
            AgentAction::Op(ToolCall::new(
                "http_get",
                [("url".into(), "https://api.github.com/zen".into())],
            )),
            AgentAction::Spend {
                service: "stripe_pay".into(),
                amount_cents: 5,
            },
        ];
        let report = cloud.run_with_toolkit(&child, &mut PlannedBrain::new(plan), toolkit);
        for s in transcript_of(&report) {
            let mark = if s.outcome == "admitted" {
                "✓"
            } else {
                "✗"
            };
            println!("   {mark} {:<28} {}", s.action, s.outcome);
        }
        println!();
        report
    }

    // ── caps parsing ──────────────────────────────────────────────────────────

    struct Bundle {
        spec: AgentSpec,
        services: Vec<String>,
        op_tools: Vec<String>,
        cells: Vec<String>,
    }

    fn parse_caps(caps: &str, id: &str, budget: i64, workdir: &str) -> Result<Bundle, String> {
        let mut spec = AgentSpec::new(id, budget);
        let mut services = Vec::new();
        let mut op_tools = Vec::new();
        let mut cells = Vec::new();
        for tok in caps.split(',').map(str::trim).filter(|t| !t.is_empty()) {
            match tok {
                "shell" => {
                    spec = spec.with_shell();
                    op_tools.push(op::SHELL.to_string());
                }
                "fs" => {
                    spec = spec.with_workdir_fs(workdir);
                    for t in [op::FS_READ, op::FS_WRITE, op::LIST_DIR, op::MKDIR] {
                        op_tools.push(t.to_string());
                    }
                }
                "spend" => {
                    spec = spec.with_service("stripe_pay");
                    services.push("stripe_pay".to_string());
                }
                t if t.starts_with("http:") => {
                    let host = &t["http:".len()..];
                    spec = spec.with_http_host(host);
                    op_tools.push(op::HTTP_GET.to_string());
                }
                t if t.starts_with("git:") => {
                    let host = &t["git:".len()..];
                    spec = spec.with_http_host(host);
                    op_tools.push(op::GIT_CLONE.to_string());
                }
                t if t.starts_with("cell:") => {
                    let path = &t["cell:".len()..];
                    spec = spec.with_cell(path);
                    cells.push(path.to_string());
                }
                // A bare token is a flat invoke service (e.g. run_tests).
                other => {
                    spec = spec.with_service(other);
                    services.push(other.to_string());
                }
            }
        }
        op_tools.sort();
        op_tools.dedup();
        Ok(Bundle {
            spec,
            services,
            op_tools,
            cells,
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn make_brain<C: OpenAICompatCaller>(
        goal: &str,
        services: &[String],
        cells: &[String],
        op_tools: &[String],
        key: ProviderKey,
        base: &str,
        model: &str,
        caller: C,
        step_cap: u64,
    ) -> OpenAICompatBrain<C> {
        OpenAICompatBrain::with_base(goal, services.to_vec(), cells.to_vec(), key, base, model, caller)
            .with_op_tools(op_tools.to_vec())
            .with_system_note("Work step by step using ONE tool call per turn. Keep reasoning brief. Call finish when the goal is met.")
            .with_step_cap(step_cap)
    }

    // ── the flat/priced inner toolkit (run_tests + the spend rail) ────────────

    fn build_inner_toolkit(stripe_key: Option<String>) -> Toolkit {
        Toolkit::new().with_stripe_pay("stripe_pay", move |amount_cents| match &stripe_key {
            Some(key) => real_stripe_payment_intent(key, amount_cents),
            None => Ok(format!(
                "ledger-{amount_cents}c (budget enforced; Stripe live leg needs a test key)"
            )),
        })
    }

    // ── real runners ───────────────────────────────────────────────────────────

    /// A real shell command: `bash -c` in `cwd`, captured stdout/stderr/exit, with
    /// a timeout (a SIGKILL on overrun → exit 124) and **cd persistence** (a `cd`
    /// inside the command sticks to the next call via a trailing pwd marker).
    fn real_shell(cmd: &str, cwd: &Path, timeout: Duration) -> Result<ShellOut, String> {
        const MARKER: &str = "__DREGG_CWD__";
        let wrapped =
            format!("{cmd}\n__dregg_ec=$?\nprintf '\\n{MARKER}%s' \"$(pwd)\"\nexit $__dregg_ec");
        let child = Command::new("bash")
            .arg("-c")
            .arg(&wrapped)
            .current_dir(cwd)
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|e| format!("spawn bash: {e}"))?;
        let pid = child.id();
        let (tx, rx) = mpsc::channel();
        std::thread::spawn(move || {
            let _ = tx.send(child.wait_with_output());
        });
        match rx.recv_timeout(timeout) {
            Ok(Ok(out)) => {
                let mut stdout = String::from_utf8_lossy(&out.stdout).into_owned();
                let stderr = String::from_utf8_lossy(&out.stderr).into_owned();
                let mut new_cwd = None;
                if let Some(pos) = stdout.rfind(MARKER) {
                    let cwd_str = stdout[pos + MARKER.len()..].trim().to_string();
                    stdout.truncate(pos);
                    stdout = stdout.trim_end().to_string();
                    if !cwd_str.is_empty() {
                        new_cwd = Some(PathBuf::from(cwd_str));
                    }
                }
                Ok(ShellOut {
                    exit: out.status.code().unwrap_or(-1) as i64,
                    stdout,
                    stderr,
                    new_cwd,
                })
            }
            Ok(Err(e)) => Err(format!("wait: {e}")),
            Err(_) => {
                let _ = Command::new("kill").arg("-9").arg(pid.to_string()).status();
                Ok(ShellOut {
                    exit: 124,
                    stdout: String::new(),
                    stderr: format!("timed out after {}s (killed)", timeout.as_secs()),
                    new_cwd: None,
                })
            }
        }
    }

    /// A real HTTP GET via reqwest blocking (bounded body), off any async runtime.
    fn real_http(url: &str) -> Result<HttpResp, String> {
        let url = url.to_string();
        let handle = std::thread::spawn(move || -> Result<HttpResp, String> {
            let client = reqwest::blocking::Client::builder()
                .timeout(Duration::from_secs(30))
                .user_agent("dregg-agent/0.1")
                .build()
                .map_err(|e| format!("client: {e}"))?;
            let resp = client.get(&url).send().map_err(|e| format!("get: {e}"))?;
            let status = resp.status().as_u16() as i64;
            let mut body = resp.text().map_err(|e| format!("body: {e}"))?;
            if body.len() > 4096 {
                body.truncate(4096);
            }
            Ok(HttpResp { status, body })
        });
        handle
            .join()
            .map_err(|_| "http thread panicked".to_string())?
    }

    /// A REAL Stripe **test-mode** PaymentIntent (only with an `sk_test_` key). The
    /// genuine money leg: POST /v1/payment_intents (amount, usd, automatic methods,
    /// confirm with the `pm_card_visa` test method). Returns the PaymentIntent id.
    fn real_stripe_payment_intent(key: &str, amount_cents: i64) -> Result<String, String> {
        if !key.starts_with("sk_test_") {
            return Err("refusing a non-test Stripe key (demo is test-mode only)".into());
        }
        let key = key.to_string();
        let handle = std::thread::spawn(move || -> Result<String, String> {
            let client = reqwest::blocking::Client::builder()
                .timeout(Duration::from_secs(30))
                .build()
                .map_err(|e| format!("client: {e}"))?;
            let resp = client
                .post("https://api.stripe.com/v1/payment_intents")
                .basic_auth(&key, Some(""))
                .form(&[
                    ("amount", amount_cents.to_string()),
                    ("currency", "usd".to_string()),
                    ("payment_method", "pm_card_visa".to_string()),
                    ("confirm", "true".to_string()),
                    ("automatic_payment_methods[enabled]", "true".to_string()),
                    (
                        "automatic_payment_methods[allow_redirects]",
                        "never".to_string(),
                    ),
                ])
                .send()
                .map_err(|e| format!("stripe send: {e}"))?;
            let v: Value = resp.json().map_err(|e| format!("stripe decode: {e}"))?;
            if let Some(id) = v.get("id").and_then(|i| i.as_str()) {
                Ok(id.to_string())
            } else {
                Err(format!(
                    "stripe error: {}",
                    v.get("error")
                        .and_then(|e| e.get("message"))
                        .and_then(|m| m.as_str())
                        .unwrap_or("unknown")
                ))
            }
        });
        handle
            .join()
            .map_err(|_| "stripe thread panicked".to_string())?
    }

    // ── keys + record/replay ────────────────────────────────────────────────────

    fn nvidia_key() -> Option<ProviderKey> {
        ProviderKey::from_env("nvidia", "NVIDIA_API_KEY").or_else(|| {
            std::env::var_os("HOME")
                .map(|h| Path::new(&h).join(".nvidiakey"))
                .and_then(|p| ProviderKey::from_file("nvidia", p))
        })
    }

    fn stripe_test_key() -> Option<String> {
        if let Ok(k) = std::env::var("STRIPE_API_KEY")
            && !k.is_empty()
        {
            return Some(k);
        }
        std::env::var_os("HOME")
            .map(|h| Path::new(&h).join(".stripekey"))
            .and_then(|p| std::fs::read_to_string(p).ok())
            .map(|s| s.trim().to_string())
            .filter(|s| !s.is_empty())
    }

    /// The capture format: the recorded model responses plus the workdir they ran
    /// against (so a replay reuses it and the recorded tool calls resolve).
    #[derive(serde::Serialize, serde::Deserialize)]
    struct Record {
        workdir: String,
        responses: Vec<Value>,
    }

    fn save_record(path: &str, workdir: &str, responses: &[Value]) -> Result<(), String> {
        let rec = Record {
            workdir: workdir.to_string(),
            responses: responses.to_vec(),
        };
        let json = serde_json::to_string_pretty(&rec).map_err(|e| e.to_string())?;
        std::fs::write(path, json).map_err(|e| e.to_string())
    }

    fn load_record(path: &str) -> Result<Record, String> {
        let raw = std::fs::read_to_string(path).map_err(|e| e.to_string())?;
        // Accept either the {workdir, responses} record or a bare responses array.
        if let Ok(rec) = serde_json::from_str::<Record>(&raw) {
            return Ok(rec);
        }
        let responses: Vec<Value> = serde_json::from_str(&raw).map_err(|e| e.to_string())?;
        Ok(Record {
            workdir: String::new(),
            responses,
        })
    }

    fn indent(s: &str, prefix: &str) -> String {
        s.lines()
            .map(|l| format!("{prefix}{l}"))
            .collect::<Vec<_>>()
            .join("\n")
    }

    /// A recording wrapper around the live caller: tees every provider response so
    /// a good real run can be saved (`--record`) and later replayed (`--replay`).
    /// The key still rides ONLY in the inner caller's auth header.
    pub struct TeeCaller<C: OpenAICompatCaller> {
        inner: C,
        recorded: std::cell::RefCell<Vec<Value>>,
    }

    impl<C: OpenAICompatCaller> TeeCaller<C> {
        pub fn new(inner: C) -> TeeCaller<C> {
            TeeCaller {
                inner,
                recorded: std::cell::RefCell::new(Vec::new()),
            }
        }
        pub fn recorded(&self) -> Vec<Value> {
            self.recorded.borrow().clone()
        }
    }

    impl<C: OpenAICompatCaller> OpenAICompatCaller for TeeCaller<C> {
        fn complete(
            &mut self,
            endpoint: &str,
            api_key: &str,
            request: &Value,
        ) -> Result<Value, String> {
            let resp = self.inner.complete(endpoint, api_key, request)?;
            self.recorded.borrow_mut().push(resp.clone());
            Ok(resp)
        }
    }
}
