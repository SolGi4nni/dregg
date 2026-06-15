//! `dregg-deploy` — the DreggDL CLI.
//!
//! ```text
//!   dregg-deploy check <file.dregg.toml>     parse → lower → static assurance verdict
//!   dregg-deploy check --ring <file>         also run the ring-balance check
//!   dregg-deploy check --json <file>         emit the assurance as JSON
//!   dregg-deploy apply <file.dregg.toml>     GATE on the check, then emit the per-root
//!                                            turn sequence + receipt-chain shape
//!   dregg-deploy apply --json <file>         emit the planned turn sequence as JSON
//!   dregg-deploy lower <file.dregg.toml>     emit the lowered CallForest as JSON
//!                                            (feed it to `dregg-uverify`)
//!   dregg-deploy fmt   <file.dregg.toml>     round-trip: parse and re-serialize canonical TOML
//! ```
//!
//! `check`/`apply` exit 0 on a passing assurance, 1 on findings / a refused
//! deployment, 2 on input/parse error — so they compose into CI / pre-submit
//! hooks. `apply` is the gate: it refuses to emit a turn sequence for a
//! non-conserving / amplifying spec.

use std::process::ExitCode;

use dregg_deploy::{
    ApplyError, Lowered, check, explain_assurance, parse_toml, plan_apply, serialize_toml,
};

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let cmd = args.first().map(String::as_str);

    match cmd {
        Some("check") => run_check(&args[1..]),
        Some("apply") => run_apply(&args[1..]),
        Some("lower") => run_lower(&args[1..]),
        Some("fmt") => run_fmt(&args[1..]),
        Some("-h") | Some("--help") | None => {
            print_help();
            ExitCode::SUCCESS
        }
        Some(other) => {
            eprintln!("unknown subcommand `{other}`\n");
            print_help();
            ExitCode::from(2)
        }
    }
}

fn print_help() {
    eprintln!(
        "dregg-deploy — DreggDL, a checkable deployment spec (CapDL for dregg)\n\n\
         USAGE:\n  \
           dregg-deploy check [--ring] [--json] <file.dregg.toml>\n      \
               parse → lower → run the static assurance over the whole authority layout\n  \
           dregg-deploy apply [--ring] [--json] <file.dregg.toml>\n      \
               GATE on the static check, then emit the per-root turn sequence + receipt chain\n  \
           dregg-deploy lower <file.dregg.toml>\n      \
               emit the lowered dregg_turn::CallForest as JSON (pipe to dregg-uverify)\n  \
           dregg-deploy fmt   <file.dregg.toml>\n      \
               round-trip: parse and re-emit canonical TOML\n\n\
         EXIT (check/apply): 0 = Pass, 1 = findings / refused, 2 = input/parse error."
    );
}

fn read_file(args: &[String]) -> Result<String, ExitCode> {
    let file = args.iter().find(|a| !a.starts_with("--"));
    match file {
        Some(path) => std::fs::read_to_string(path).map_err(|e| {
            eprintln!("error reading `{path}`: {e}");
            ExitCode::from(2)
        }),
        None => {
            eprintln!("error: expected a <file.dregg.toml> argument");
            Err(ExitCode::from(2))
        }
    }
}

fn run_check(args: &[String]) -> ExitCode {
    let as_ring = args.iter().any(|a| a == "--ring");
    let as_json = args.iter().any(|a| a == "--json");
    let text = match read_file(args) {
        Ok(t) => t,
        Err(c) => return c,
    };
    let verdict = match check(&text, as_ring) {
        Ok(v) => v,
        Err(e) => {
            eprintln!("error: {e}");
            return ExitCode::from(2);
        }
    };

    if as_json {
        // Emit the underlying assurance object (the Verdict types are
        // serde-serializable in dregg-userspace-verify).
        match serde_json::to_string_pretty(&verdict.assurance) {
            Ok(j) => println!("{j}"),
            Err(e) => {
                eprintln!("error serializing verdict: {e}");
                return ExitCode::from(2);
            }
        }
    } else {
        print_human(&verdict, &text);
    }

    if verdict.pass() {
        ExitCode::SUCCESS
    } else {
        ExitCode::from(1)
    }
}

fn print_human(v: &dregg_deploy::DeployVerdict, text: &str) {
    println!("dregg-deploy: resolved deployment");
    println!("  federation turns (effect-groups): {}", v.turn_count);
    if !v.factories.is_empty() {
        println!("  factories:");
        for (name, vk) in &v.factories {
            println!("    {name:<16} factory_vk b3:{}…", &vk[..16]);
        }
    }
    if !v.cells.is_empty() {
        println!("  cells:");
        for (name, id) in &v.cells {
            println!("    {name:<16} cell      {}…", &id[..16]);
        }
    }
    println!();

    let a = &v.assurance;
    let line = |name: &str, vd: &dregg_userspace_verify::Verdict| {
        if vd.is_pass() {
            println!("  [PASS] {name}");
        } else {
            println!("  [FAIL] {name}");
            for f in vd.findings() {
                println!("         @ {}  —  {}", f.locus, f.message);
            }
        }
    };
    println!("static assurance over the declared authority layout:");
    line(
        "B  conservation      (funding transfers net to zero)",
        &a.conservation,
    );
    line(
        "A  no-amplification  (grant edges are attenuations)  ",
        &a.no_amplification,
    );
    line(
        "   well-formedness   (structural shape)              ",
        &a.wellformed,
    );
    line(
        "   ring balance                                      ",
        &a.ring_balance,
    );
    println!();
    // On a FAIL, print the ENRICHED diagnostics: a no-amplification finding named
    // by spec name + human facet + the parent cap it exceeded (not a hex prefix).
    if !v.pass() {
        if let Ok(dep) = parse_toml(text) {
            if let Ok(lowered) = Lowered::from_deployment(&dep) {
                let diag = explain_assurance(&lowered, &a);
                if !diag.is_clean() {
                    println!("why (named):");
                    for l in diag.lines() {
                        println!("  • {l}");
                    }
                    println!();
                }
            }
        }
    }
    if v.pass() {
        println!(
            "VERDICT: PASS (static). The whole declared cap layout conserves and \
             does not amplify. NOTE: a Pass is necessary, not sufficient — the \
             executor still checks holding, balances, credentials, freshness, and \
             the state commitment at submit time."
        );
    } else {
        println!(
            "VERDICT: FAIL — fix the findings above; this deployment would be \
             rejected by the executor (you'd pay gas to be rejected)."
        );
    }
}

fn run_apply(args: &[String]) -> ExitCode {
    let as_ring = args.iter().any(|a| a == "--ring");
    let as_json = args.iter().any(|a| a == "--json");
    let text = match read_file(args) {
        Ok(t) => t,
        Err(c) => return c,
    };
    let dep = match parse_toml(&text) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("error: {e}");
            return ExitCode::from(2);
        }
    };
    // THE GATE: plan_apply runs the static check first and refuses to emit a
    // turn sequence for a non-conserving / amplifying spec.
    let plan = match plan_apply(&dep, as_ring) {
        Ok(p) => p,
        Err(ApplyError::Refused { assurance }) => {
            eprintln!(
                "REFUSED: the static pre-submission check rejected this deployment — \
                 NO turn sequence emitted (you'd pay gas to be rejected). Findings:"
            );
            // Enriched diagnostics: re-lower so a no-amplification finding names
            // the over-granting edge by spec name + human facet, not a hex prefix
            // + `Some(17)`. (Re-lowering cannot fail — plan_apply already lowered.)
            match Lowered::from_deployment(&dep) {
                Ok(lowered) => {
                    let diag = explain_assurance(&lowered, &assurance);
                    for line in diag.lines() {
                        eprintln!("  • {line}");
                    }
                }
                Err(_) => {
                    for f in assurance.all_findings() {
                        eprintln!("  @ {}  —  {}", f.locus, f.message);
                    }
                }
            }
            return ExitCode::from(1);
        }
        Err(e) => {
            eprintln!("error: {e}");
            return ExitCode::from(2);
        }
    };

    if as_json {
        // Emit the planned turn sequence (the Turn type is serde-serializable).
        let turns: Vec<&dregg_turn::turn::Turn> = plan.turns.iter().map(|t| &t.turn).collect();
        match serde_json::to_string_pretty(&turns) {
            Ok(j) => println!("{j}"),
            Err(e) => {
                eprintln!("error serializing plan: {e}");
                return ExitCode::from(2);
            }
        }
    } else {
        print_apply(&plan);
    }
    ExitCode::SUCCESS
}

fn print_apply(plan: &dregg_deploy::AppliedPlan) {
    println!("dregg-deploy apply: the static check PASSED — emitting the turn sequence.");
    println!(
        "  {} turn(s), one per root effect-group (births → funds → grants), receipt-chained:",
        plan.len()
    );
    let hexn = |b: &[u8; 32], n: usize| -> String {
        b.iter().take(n).map(|x| format!("{x:02x}")).collect()
    };
    for (i, pt) in plan.turns.iter().enumerate() {
        let prev = pt
            .turn
            .previous_receipt_hash
            .map(|h| format!("⟵ {}…", hexn(&h, 6)))
            .unwrap_or_else(|| "(chain root)".to_string());
        println!(
            "    [{i}] {:<6} agent {}…  turn {}…  receipt {}…  {prev}",
            pt.phase,
            hexn(pt.agent.as_bytes(), 6),
            hexn(&pt.turn_hash, 6),
            hexn(&pt.projected_receipt_hash, 6),
        );
    }
    println!();
    println!(
        "The chain is the deployment's causal strand (each turn's \
         previous_receipt_hash = the prior turn's projected receipt). Submit in \
         order, re-signed with the operator key. NOTE: a Pass + a projected chain \
         is the SHAPE — the executor fills the real state commitments, signatures, \
         and computrons at submit time."
    );
}

fn run_lower(args: &[String]) -> ExitCode {
    let text = match read_file(args) {
        Ok(t) => t,
        Err(c) => return c,
    };
    let dep = match parse_toml(&text) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("error: {e}");
            return ExitCode::from(2);
        }
    };
    let lowered = match Lowered::from_deployment(&dep) {
        Ok(l) => l,
        Err(e) => {
            eprintln!("error: {e}");
            return ExitCode::from(2);
        }
    };
    match serde_json::to_string_pretty(&lowered.forest) {
        Ok(j) => {
            println!("{j}");
            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("error serializing forest: {e}");
            ExitCode::from(2)
        }
    }
}

fn run_fmt(args: &[String]) -> ExitCode {
    let text = match read_file(args) {
        Ok(t) => t,
        Err(c) => return c,
    };
    let dep = match parse_toml(&text) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("error: {e}");
            return ExitCode::from(2);
        }
    };
    match serialize_toml(&dep) {
        Ok(t) => {
            print!("{t}");
            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("error serializing: {e}");
            ExitCode::from(2)
        }
    }
}
