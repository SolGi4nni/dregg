//! `dregg-agent-business` — the one-command CLI the hackathon demo script drives.
//!
//! ```text
//!   dregg-agent-business run    [--out run.json] [--seed N] [--live]
//!   dregg-agent-business verify <run.json> [--tamper]
//! ```
//!
//! `run` executes the five beats of "Acme Test-as-a-Service, run by an agent"
//! (EARN → FUND → OPERATE → SPEND → SCALE) and writes `run.json`; `verify`
//! re-witnesses the whole P&L offline, host untrusted (beat 6, PROVE). The default
//! path is deterministic + offline (a recorded brain + recorded signed webhook) so
//! it always films cleanly; `--live` points the brain at a real Nemotron / Hermes
//! endpoint (behind the `live-brain` feature) when a key is present.

use std::process::ExitCode;

use dregg_agent::agent::ActionOutcome;
use dregg_agent::business::{BusinessRun, run_offline_demo, verify_business};

const DEMO_SEED: [u8; 32] = [0x42u8; 32];

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
        "dregg-agent-business — the autonomous business you can audit\n\n\
         USAGE:\n\
         \x20 dregg-agent-business run    [--out <run.json>] [--seed <hex-byte>] [--live]\n\
         \x20 dregg-agent-business verify <run.json> [--tamper]\n\n\
         run     execute the five beats (EARN·FUND·OPERATE·SPEND·SCALE), write run.json\n\
         verify  re-witness the whole P&L offline (PROVE); --tamper flips one line first\n\n\
         --live  drive OPERATE/SPEND with a real Nemotron/Hermes model (needs a key +\n\
         \x20       the `live-brain` feature); otherwise a recorded transport films cleanly"
    );
}

/// Read an `--flag <value>` pair from args.
fn flag<'a>(args: &'a [String], name: &str) -> Option<&'a str> {
    args.iter()
        .position(|a| a == name)
        .and_then(|i| args.get(i + 1))
        .map(String::as_str)
}

fn has(args: &[String], name: &str) -> bool {
    args.iter().any(|a| a == name)
}

fn cmd_run(args: &[String]) -> ExitCode {
    let out = flag(args, "--out").unwrap_or("run.json").to_string();
    let mut seed = DEMO_SEED;
    if let Some(s) = flag(args, "--seed") {
        if let Ok(b) = s.parse::<u8>() {
            seed = [b; 32];
        }
    }
    let live = has(args, "--live");

    println!("════════════════════════════════════════════════════════════════════");
    println!("  ACME TEST-AS-A-SERVICE — an autonomous business you can audit");
    println!("  bounded · cap-gated · receipted — every dollar leaves a proof");
    println!("════════════════════════════════════════════════════════════════════\n");

    let run = if live {
        run_live(seed, args)
    } else {
        println!("[mode] deterministic offline path (recorded brain · recorded webhook)\n");
        run_offline_demo(seed)
    };

    print_beats(&run);

    let json = serde_json::to_string_pretty(&run).expect("run serializes");
    if let Err(e) = std::fs::write(&out, json) {
        eprintln!("failed to write {out}: {e}");
        return ExitCode::FAILURE;
    }
    println!("\n  → wrote the P&L receipt to {out}");
    println!("  → audit it yourself:  dregg-agent-business verify {out}\n");
    ExitCode::SUCCESS
}

/// Drive the OPERATE/SPEND beats with a live Nemotron/Hermes brain when the
/// `live-brain` feature + a key are present; otherwise fall back to offline.
#[cfg(feature = "live-brain")]
fn run_live(seed: [u8; 32], args: &[String]) -> BusinessRun {
    use dregg_agent::brain::{LiveOpenAICompatCaller, OpenAICompatBrain, ProviderKey};

    let base = flag(args, "--llm-base").unwrap_or("https://integrate.api.nvidia.com/v1");
    let model = flag(args, "--llm-model").unwrap_or("nvidia/nemotron-3-ultra-550b-a55b");
    let key = ProviderKey::from_env("nvidia", "NVIDIA_API_KEY")
        .or_else(|| ProviderKey::from_env("nous", "NOUS_PORTAL_KEY"));
    let Some(key) = key else {
        println!("[mode] --live requested but no NVIDIA_API_KEY/NOUS_PORTAL_KEY set — offline\n");
        return run_offline_demo(seed);
    };
    println!("[mode] LIVE — {model} @ {base}\n");
    let mut brain = OpenAICompatBrain::with_base(
        "Run the customer's test job, then pay the compute and SaaS vendors you used \
         via stripe_pay (the amount is drawn from your budget).",
        vec![
            "run_tests".into(),
            "stripe_pay".into(),
            "check_health".into(),
        ],
        vec!["/job".into()],
        key,
        base,
        model,
        LiveOpenAICompatCaller::new(),
    )
    .with_step_cap(12);
    dregg_agent::business::run_demo(seed, &mut brain)
}

#[cfg(not(feature = "live-brain"))]
fn run_live(seed: [u8; 32], _args: &[String]) -> BusinessRun {
    println!("[mode] --live needs the `live-brain` feature (rebuild with --features live-brain)");
    println!("       falling back to the deterministic offline path\n");
    run_offline_demo(seed)
}

fn print_beats(run: &BusinessRun) {
    // ── Beat 1+2: EARN → FUND ──────────────────────────────────────────────
    println!("──[ 1 · EARN ]── a customer pays Acme; Stripe verify+mint (real HMAC-SHA256)");
    for e in &run.earn.events {
        let mark = if e.outcome.starts_with("MINTED") {
            "✓"
        } else {
            "✗"
        };
        println!(
            "   {mark} {:<18} {:>8}¢  {}  [{}]",
            e.label, e.amount_cents, e.outcome, e.intent_id
        );
    }
    println!(
        "   → minted {}¢ of conserved, receipted USD-credit\n",
        run.earn.minted_cents
    );
    println!("──[ 2 · FUND ]── the minted credit funds the agent's budget cell");
    println!(
        "   ✓ budget ceiling = {}¢  (earned money is now spendable)\n",
        run.pnl.budget_cents
    );

    // ── Beat 3+4: OPERATE + SPEND ──────────────────────────────────────────
    println!("──[ 3 · OPERATE ]── the agent (Hermes/Nemotron) runs the customer's test job");
    for r in &run.agent_run.receipts {
        if r.action.starts_with("invoke:") {
            let v = r
                .tool_ok
                .map(|ok| if ok { "PASS" } else { "FAIL" })
                .unwrap_or("");
            println!(
                "   ✓ {:<22} {} — verdict bound into receipt #{}",
                r.action, v, r.seq
            );
        } else if r.action.starts_with("cell-write:") {
            println!("   ✓ {:<22} accepted the job", r.action);
        }
    }
    println!();
    println!("──[ 4 · SPEND ]── budget-gated, variable-amount Stripe-out (the new primitive)");
    for r in &run.agent_run.receipts {
        if r.action.starts_with("spend:") {
            println!(
                "   ✓ {:<22} paid {:>6}¢ — drawn from the budget, receipted",
                r.action, r.cost
            );
        }
    }
    for l in &run.agent_run.log {
        if let ActionOutcome::BudgetRefused { headroom } = &l.outcome {
            println!(
                "   ✗ {:<22} REFUSED in-band — over budget (headroom {headroom}¢); no money moved",
                l.action
            );
        }
    }
    println!(
        "   → vendor spend {}¢ · ops metering {}¢ · headroom {}¢\n",
        run.pnl.vendor_spend_cents, run.pnl.ops_metering_cents, run.pnl.headroom_cents
    );

    // ── Beat 5: SCALE ──────────────────────────────────────────────────────
    println!("──[ 5 · SCALE ]── fork a sub-agent: attenuated budget + narrower cap bundle");
    println!("   ✓ sub-agent deployed (budget 1000¢, no check_health cap — provably narrower)");
    for l in &run.subagent_run.log {
        match &l.outcome {
            ActionOutcome::Admitted => {
                println!("   ✓ {:<22} admitted within the child's bound", l.action)
            }
            ActionOutcome::BudgetRefused { .. } => {
                println!(
                    "   ✗ {:<22} REFUSED — over the child's attenuated budget (no-amplify)",
                    l.action
                )
            }
            ActionOutcome::CapRefused { .. } => {
                println!(
                    "   ✗ {:<22} REFUSED — outside the child's narrowed bundle (no-amplify)",
                    l.action
                )
            }
        }
    }
    println!();

    // ── the P&L line ───────────────────────────────────────────────────────
    println!(
        "──[ P&L ]── revenue {}¢  −  vendor cost {}¢  −  ops {}¢  =  net {}¢",
        run.pnl.earned_cents,
        run.pnl.vendor_spend_cents,
        run.pnl.ops_metering_cents,
        run.pnl.net_cents
    );
}

fn cmd_verify(args: &[String]) -> ExitCode {
    let Some(path) = args.iter().find(|a| !a.starts_with("--")) else {
        eprintln!("usage: dregg-agent-business verify <run.json> [--tamper]");
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
    let mut run: BusinessRun = match serde_json::from_str(&raw) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("cannot parse {path}: {e}");
            return ExitCode::FAILURE;
        }
    };

    println!("════════════════════════════════════════════════════════════════════");
    if tamper {
        println!("  7 · THE TEETH — tamper one line, the audit catches it");
    } else {
        println!("  6 · PROVE — re-witness the whole P&L offline, trusting no host");
    }
    println!("════════════════════════════════════════════════════════════════════\n");

    if tamper {
        // Forge "I only paid 1¢" on the first vendor spend — the auditor's nightmare.
        if let Some(i) = run
            .agent_run
            .receipts
            .iter()
            .position(|r| r.action.starts_with("spend:"))
        {
            let was = run.agent_run.receipts[i].cost;
            run.agent_run.receipts[i].cost = 1;
            println!(
                "[tamper] flipped a spend receipt: {was}¢ → 1¢ (\"I barely spent anything\")\n"
            );
        }
    }

    match verify_business(&run) {
        Ok(v) => {
            println!(
                "   ✓ EARN     mint chain re-witnessed — {} mint(s), {}¢ earned",
                v.mints, v.earned_cents
            );
            println!(
                "   ✓ OPERATE  agent receipt chain intact + signed — {} actions",
                v.agent_actions
            );
            println!(
                "   ✓ QA       witnessed run re-executed on the deployed code — {} run(s)",
                v.witnessed_qa
            );
            println!(
                "   ✓ SPEND    every vendor payment traces to a receipt — {}¢",
                v.vendor_spend_cents
            );
            println!(
                "   ✓ SCALE    sub-agent chain re-witnessed — {} action(s)",
                v.subagent_actions
            );
            println!(
                "   ✓ BUDGET   consumed ≤ ceiling; net margin {}¢ = the could-have bound",
                v.net_cents
            );
            println!("\n   VERDICT: ✓ the entire autonomous business re-verifies offline.\n");
            ExitCode::SUCCESS
        }
        Err(e) => {
            println!("   ✗ REJECTED: {e}");
            println!("\n   VERDICT: ✗ the audit caught it — the proof does not lie.\n");
            // A caught tamper is the INTENDED outcome of `--tamper`: exit 0 so the
            // demo script's tamper beat reads as a success (the tooth bit).
            if tamper {
                ExitCode::SUCCESS
            } else {
                ExitCode::FAILURE
            }
        }
    }
}
