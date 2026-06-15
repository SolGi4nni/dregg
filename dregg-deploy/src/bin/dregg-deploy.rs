//! `dregg-deploy` — the DreggDL CLI.
//!
//! ```text
//!   dregg-deploy check <file.dregg.toml>     parse → lower → static assurance verdict
//!   dregg-deploy check --ring <file>         also run the ring-balance check
//!   dregg-deploy check --json <file>         emit the assurance as JSON
//!   dregg-deploy apply <file.dregg.toml>     GATE on the check, then emit the per-root
//!                                            turn sequence + receipt-chain shape
//!   dregg-deploy apply --json <file>         emit the planned turn sequence as JSON
//!   dregg-deploy refine <old> <new>          BEHAVIORAL safe-upgrade gate: does NEW
//!                                            refine the running OLD (new ≤ᶠ old)?
//!   dregg-deploy refine --intent <i> <plan>  intent-conformance: does PLAN refine the
//!                                            declared intent flow (lowered ≤ᶠ intent)?
//!   dregg-deploy refine --json …             emit the refinement verdict as JSON
//!   dregg-deploy lower <file.dregg.toml>     emit the lowered CallForest as JSON
//!                                            (feed it to `dregg-uverify`)
//!   dregg-deploy fmt   <file.dregg.toml>     round-trip: parse and re-serialize canonical TOML
//! ```
//!
//! `check`/`apply`/`refine` exit 0 on a passing verdict, 1 on findings / a
//! refused deployment / a non-refining upgrade, 2 on input/parse error — so they
//! compose into CI / pre-submit hooks. `apply` is the static gate (refuses a
//! non-conserving / amplifying spec); `refine` is the BEHAVIORAL gate (refuses a
//! widening upgrade, or a lowering that exceeds its declared intent) — a
//! DIFFERENT property neither subsumes the other (see `dregg_deploy::refine`).

use std::process::ExitCode;

use dregg_deploy::{
    AppliedPlan, ApplyError, FlowSpec, IntentEffect, Lowered, RefineVerdict, check,
    explain_assurance, parse_toml, plan_apply, plan_apply_toml, plan_from_lowered, refines_intent,
    refines_upgrade, serialize_toml,
};

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let cmd = args.first().map(String::as_str);

    match cmd {
        Some("check") => run_check(&args[1..]),
        Some("apply") => run_apply(&args[1..]),
        Some("refine") => run_refine(&args[1..]),
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
           dregg-deploy refine [--json] <old.dregg.toml> <new.dregg.toml>\n      \
               BEHAVIORAL safe-upgrade gate: is NEW a refinement of the running OLD (new ≤ᶠ old)?\n      \
               A widening (a new effect / wider capability) is REFUSED with the divergence named.\n  \
           dregg-deploy refine --intent [--json] <intent.dregg.toml> <plan.dregg.toml>\n      \
               intent-conformance: does PLAN refine the declared intent flow (lowered ≤ᶠ intent)?\n      \
               The intent's effect-set is the authorized envelope; a lowering that does MORE is REFUSED.\n  \
           dregg-deploy lower <file.dregg.toml>\n      \
               emit the lowered dregg_turn::CallForest as JSON (pipe to dregg-uverify)\n  \
           dregg-deploy fmt   <file.dregg.toml>\n      \
               round-trip: parse and re-emit canonical TOML\n\n\
         EXIT (check/apply/refine): 0 = Pass/Refines, 1 = findings / refused / non-refining, \
         2 = input/parse error."
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

/// Build an [`AppliedPlan`] from a DreggDL file for the refinement gate.
///
/// Prefers the GATED constructor ([`plan_apply_toml`]): a deployment that
/// conserves + does not amplify yields a plan straight off. If the static gate
/// REFUSES the spec (it is non-conserving / amplifying), we still build the plan
/// leniently ([`plan_from_lowered`]) so the *behavioral* refinement question can
/// be answered — and we NOTE the failing static verdict on stderr, because the
/// two gates are independent (a spec can fail safety yet be a legitimate side of
/// the refinement comparison). Only a genuine lower/parse error is fatal here.
fn build_plan_for_refine(path: &str, label: &str) -> Result<AppliedPlan, ExitCode> {
    let text = std::fs::read_to_string(path).map_err(|e| {
        eprintln!("error reading {label} `{path}`: {e}");
        ExitCode::from(2)
    })?;
    match plan_apply_toml(&text, false) {
        Ok(plan) => Ok(plan),
        Err(dregg_deploy::DeployError::Apply(ApplyError::Refused { .. })) => {
            // The static gate refused this side. The behavioral refinement check
            // is orthogonal, so lower leniently and proceed — but say so.
            let dep = parse_toml(&text).map_err(|e| {
                eprintln!("error parsing {label} `{path}`: {e}");
                ExitCode::from(2)
            })?;
            let lowered = Lowered::from_deployment(&dep).map_err(|e| {
                eprintln!("error lowering {label} `{path}`: {e}");
                ExitCode::from(2)
            })?;
            eprintln!(
                "NOTE: {label} `{path}` does NOT pass the static no-amplification/conservation \
                 gate; the BEHAVIORAL refinement check below is independent of that and is \
                 computed over the lowered flow regardless. (Run `dregg-deploy check {path}` for \
                 the static findings.)"
            );
            Ok(plan_from_lowered(&lowered))
        }
        Err(e) => {
            eprintln!("error in {label} `{path}`: {e}");
            Err(ExitCode::from(2))
        }
    }
}

/// `refine`: the BEHAVIORAL gate, in two modes — default `refine <old> <new>`
/// is safe-upgrade (decides `new ≤ᶠ old`), and `--intent` `refine --intent
/// <intent> <plan>` is intent-conformance (decides `lowered(plan) ≤ᶠ
/// intent(intent-file's effect-set)`).
///
/// Exit 0 iff the refinement holds, 1 on a divergence (with the reason), 2 on
/// input/parse error.
fn run_refine(args: &[String]) -> ExitCode {
    let as_json = args.iter().any(|a| a == "--json");
    let as_intent = args.iter().any(|a| a == "--intent");
    let positionals: Vec<&String> = args.iter().filter(|a| !a.starts_with("--")).collect();
    if positionals.len() != 2 {
        eprintln!(
            "error: `refine` needs exactly two files.\n  \
             safe-upgrade:        dregg-deploy refine [--json] <old.dregg.toml> <new.dregg.toml>\n  \
             intent-conformance:  dregg-deploy refine --intent [--json] <intent.dregg.toml> \
             <plan.dregg.toml>"
        );
        return ExitCode::from(2);
    }

    if as_intent {
        // refine --intent <intent-file> <plan-file>: does the plan's lowered flow
        // refine the intent declared by the intent-file's effect-set?
        let intent_plan = match build_plan_for_refine(positionals[0], "intent") {
            Ok(p) => p,
            Err(c) => return c,
        };
        let plan = match build_plan_for_refine(positionals[1], "plan") {
            Ok(p) => p,
            Err(c) => return c,
        };
        // The intent is the menu of effect-shapes the intent-file authorizes: its
        // own effect-set (`from_plan_envelope`). Equivalently, every concrete
        // effect of the intent file wrapped as `IntentEffect::Exact`.
        let mut intents: Vec<IntentEffect> = Vec::new();
        for pt in &intent_plan.turns {
            for root in &pt.turn.call_forest.roots {
                for eff in root.all_effects() {
                    intents.push(IntentEffect::Exact(eff.clone()));
                }
            }
        }
        let intent = FlowSpec::from_intent(&intents);
        let verdict = refines_intent(&plan, &intent);
        report_refine(
            &verdict,
            as_json,
            "intent-conformance",
            &format!(
                "PLAN `{}` ≤ᶠ INTENT `{}`",
                positionals[1], positionals[0]
            ),
            "the lowered deployment stays within the declared intent envelope (it fires only \
             effects the intent authorized)",
            "the lowered deployment EXCEEDS its declared intent — it fires an effect the intent \
             did not authorize",
        )
    } else {
        // refine <old> <new>: does NEW refine the running OLD (new ≤ᶠ old)?
        let old_plan = match build_plan_for_refine(positionals[0], "old") {
            Ok(p) => p,
            Err(c) => return c,
        };
        let new_plan = match build_plan_for_refine(positionals[1], "new") {
            Ok(p) => p,
            Err(c) => return c,
        };
        let verdict = refines_upgrade(&new_plan, &old_plan);
        report_refine(
            &verdict,
            as_json,
            "safe-upgrade",
            &format!(
                "NEW `{}` ≤ᶠ OLD `{}`",
                positionals[1], positionals[0]
            ),
            "the new deployment only NARROWS (or matches) the running one — every effect it can \
             perform, the running deployment already could; safe to roll forward",
            "the new deployment WIDENS the running one — it introduces behavior the running \
             deployment never authorized; NOT safe to roll forward as-is",
        )
    }
}

/// Render a [`RefineVerdict`] (human or JSON) and map it to an exit code:
/// 0 on `Refines`, 1 on `Diverges`.
fn report_refine(
    verdict: &RefineVerdict,
    as_json: bool,
    check_name: &str,
    relation: &str,
    pass_summary: &str,
    fail_summary: &str,
) -> ExitCode {
    if as_json {
        // A self-describing JSON object: the verdict, the relation decided, and
        // the located findings (each finding's fields are public on RefineFinding).
        let findings: Vec<serde_json::Value> = verdict
            .findings()
            .iter()
            .map(|f| {
                serde_json::json!({
                    "check": f.check,
                    "message": f.message,
                    "diverging_letter": f.diverging_letter.map(|l| format!("{l:#018x}")),
                    "diverging_effect": f.diverging_effect_label,
                })
            })
            .collect();
        let obj = serde_json::json!({
            "check": check_name,
            "relation": relation,
            "refines": verdict.is_refine(),
            "verdict": if verdict.is_refine() { "Refines" } else { "Diverges" },
            "findings": findings,
        });
        match serde_json::to_string_pretty(&obj) {
            Ok(j) => println!("{j}"),
            Err(e) => {
                eprintln!("error serializing refinement verdict: {e}");
                return ExitCode::from(2);
            }
        }
    } else {
        println!("dregg-deploy refine — behavioral {check_name} gate (online simulation order ≤ᶠ)");
        println!("  deciding:  {relation}");
        println!();
        if verdict.is_refine() {
            println!("  [REFINES]  {pass_summary}.");
            println!();
            println!(
                "VERDICT: REFINES. {}. NOTE: this is the BEHAVIORAL relation only; it is \
                 independent of the static no-amplification/conservation gate (`dregg-deploy \
                 check`) and of the live executor's holding/balance/freshness checks.",
                cap_first(pass_summary)
            );
        } else {
            println!("  [REFUSED]  {fail_summary}.");
            for f in verdict.findings() {
                println!();
                println!("  divergence ({}):", f.check);
                println!("    {}", f.message);
                if let Some(label) = &f.diverging_effect_label {
                    println!("    diverging effect:  {label}");
                }
                if let Some(l) = f.diverging_letter {
                    println!("    diverging letter:  {l:#018x}");
                }
            }
            println!();
            println!(
                "VERDICT: REFUSED — {}. Drop or narrow the diverging effect above to make the \
                 relation hold.",
                fail_summary
            );
        }
    }
    if verdict.is_refine() {
        ExitCode::SUCCESS
    } else {
        ExitCode::from(1)
    }
}

/// Capitalize the first letter of a summary for the VERDICT sentence.
fn cap_first(s: &str) -> String {
    let mut c = s.chars();
    match c.next() {
        Some(f) => f.to_uppercase().collect::<String>() + c.as_str(),
        None => String::new(),
    }
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
