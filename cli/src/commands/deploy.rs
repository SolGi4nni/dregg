//! `dregg deploy` — DreggDL, the checkable deployment spec, surfaced in the ONE
//! CLI.
//!
//! DreggDL (the `dregg-deploy` crate) lets an operator write a capability layout
//! ONCE, declaratively (TOML), and lower it to the exact `dregg_turn::CallForest`
//! the SDKs instantiate and `dregg-userspace-verify` checks — CapDL's "audit the
//! whole authority structure off one file" property, made executable for dregg.
//! Until now it lived only in a SECOND binary (`dregg-deploy`) a stranger never
//! discovers; these subcommands put it under the primary `dregg` CLI.
//!
//! - `dregg deploy check <spec.dregg.toml>` — parse → lower → run the four static
//!   checks (conservation B, non-amplification A, well-formedness, optional ring)
//!   over the WHOLE declared authority layout, before any gas. The check IS the
//!   gate: an over-grant — a re-delegation that WIDENS a capability the chain
//!   handed the grantor — surfaces as a `no_amplification` finding that names the
//!   exact offending edge (`from → to over target`, granted facet vs held facet).
//! - `dregg deploy apply <spec.dregg.toml>` — the same static gate, then the
//!   per-root **turn sequence** + the receipt-chain SHAPE an operator submits
//!   (births → funds → grants, chained). An amplifying / non-conserving spec is
//!   REFUSED before a single turn is produced.
//!
//! ## Exit codes (the deploy/lint convention)
//!
//! - **0** — the spec passed (clean layout / a submittable plan was emitted).
//! - **2** — the spec PARSED and lowered, but the static check REFUSED it: an
//!   in-forest capability amplification (over-grant), non-conservation, or
//!   ill-formedness. The diagnostic names the precise locus. This is the
//!   "policy violation" code a CI gate keys on.
//! - **1** — a usage / IO / parse error (file missing, malformed TOML, an unknown
//!   name the lowering could not resolve). Flows through the top-level error
//!   handler.

use std::path::PathBuf;

use clap::Subcommand;

use dregg_deploy::{ApplyError, DeployError, Lowered, explain_assurance, plan_apply};

use crate::config::Config;
use crate::output::Context;

/// Exit code: the static check refused the (well-formed, lowered) deployment —
/// an over-grant / non-conservation / ill-formedness. Distinct from a usage
/// error (1) so a CI gate can tell "your spec is unsafe" from "I couldn't read
/// your spec".
const EXIT_REFUSED: i32 = 2;

#[derive(Subcommand)]
pub enum DeployCommand {
    /// Statically check a DreggDL deployment spec (the whole authority layout).
    ///
    /// Parses the spec, lowers it to the checkable call-forest, and runs the four
    /// static assurance checks (conservation, non-amplification, well-formedness,
    /// optional ring balance) over the ENTIRE declared cap graph — before any
    /// turn is built or any gas spent. Exit 0 on a clean layout; exit 2 if the
    /// check refuses it (e.g. an over-grant), naming the offending edge.
    Check {
        /// Path to the `.dregg.toml` deployment spec.
        spec: PathBuf,

        /// Also run the ring-balance check (for a deployment that declares a
        /// settlement ring as bare funding transfers).
        #[arg(long)]
        ring: bool,
    },

    /// Plan the apply: the static gate, then the per-root turn sequence.
    ///
    /// Runs the same static check as the GATE, then (on a pass) emits the ordered
    /// turn sequence an operator submits — births → funds → grants — linked into
    /// a receipt-chain shape. An amplifying / non-conserving spec is REFUSED
    /// (exit 2) before a single turn is produced; the plan you get back (exit 0)
    /// is exactly the plan that passed the check.
    Apply {
        /// Path to the `.dregg.toml` deployment spec.
        spec: PathBuf,

        /// Also gate on the ring-balance check.
        #[arg(long)]
        ring: bool,
    },
}

pub async fn run(
    cmd: DeployCommand,
    cfg: &Config,
    ctx: &Context,
) -> Result<(), Box<dyn std::error::Error>> {
    match cmd {
        DeployCommand::Check { spec, ring } => check(cfg, ctx, &spec, ring),
        DeployCommand::Apply { spec, ring } => apply(cfg, ctx, &spec, ring),
    }
}

/// Read the spec file, surfacing a legible IO error (exit 1 via the caller).
fn read_spec(path: &std::path::Path) -> Result<String, Box<dyn std::error::Error>> {
    std::fs::read_to_string(path).map_err(|e| {
        format!(
            "cannot read deployment spec `{}`: {e}",
            path.display()
        )
        .into()
    })
}

/// Parse + lower in one place so BOTH commands share the `Lowered` the rich
/// diagnostics (`explain_assurance`) need to name edges by their spec names.
/// A parse / name-resolution failure is a usage error (returned `Err` → exit 1),
/// NOT a policy refusal (exit 2).
fn parse_and_lower(text: &str) -> Result<(dregg_deploy::Deployment, Lowered), DeployError> {
    let dep = dregg_deploy::parse_toml(text)?;
    let lowered = Lowered::from_deployment(&dep)?;
    Ok((dep, lowered))
}

fn check(
    cfg: &Config,
    ctx: &Context,
    spec: &std::path::Path,
    ring: bool,
) -> Result<(), Box<dyn std::error::Error>> {
    let text = read_spec(spec)?;
    // Parse + lower ourselves so we keep the `Lowered` for diagnostics; a failure
    // here is a usage error (exit 1), surfaced with the file context.
    let (_dep, lowered) = parse_and_lower(&text)
        .map_err(|e| -> Box<dyn std::error::Error> {
            format!("{}: {e}", spec.display()).into()
        })?;

    // THE STATIC CHECK over the whole declared authority layout. `check` re-lowers
    // internally; we reuse our `lowered` only to enrich the (same) findings.
    let verdict = dregg_deploy::check(&text, ring)?;
    let assurance = &verdict.assurance;

    if cfg.is_json() {
        let diag = explain_assurance(&lowered, assurance);
        ctx.json_stdout(&serde_json::json!({
            "command": "deploy check",
            "spec": spec.display().to_string(),
            "pass": verdict.pass(),
            "turn_count": verdict.turn_count,
            "factories": verdict.factories,
            "cells": verdict.cells,
            "findings": diag.lines(),
            "exit_code": if verdict.pass() { 0 } else { EXIT_REFUSED },
        }));
        if !verdict.pass() {
            std::process::exit(EXIT_REFUSED);
        }
        return Ok(());
    }

    ctx.header("DreggDL — static deployment check");
    ctx.kv("Spec", &spec.display().to_string());
    ctx.kv("Cells", &verdict.cells.len().to_string());
    ctx.kv("Factories", &verdict.factories.len().to_string());
    ctx.kv("Effect groups", &verdict.turn_count.to_string());

    if verdict.pass() {
        ctx.success(
            "Static check PASSED — conservation · non-amplification · well-formedness hold over \
             the whole declared authority layout.",
        );
        ctx.info("  (The static audit is artifact-decidable; the live executor still checks held \
                  caps, balances, signatures, and freshness.)");
        return Ok(());
    }

    // REFUSED: name the precise loci. The enriched explanation turns an
    // amplification into the human OVER-GRANT diagnostic (named edge + facets).
    report_refusal(ctx, explain_assurance(&lowered, assurance));
    std::process::exit(EXIT_REFUSED);
}

fn apply(
    cfg: &Config,
    ctx: &Context,
    spec: &std::path::Path,
    ring: bool,
) -> Result<(), Box<dyn std::error::Error>> {
    let text = read_spec(spec)?;
    let (dep, lowered) = parse_and_lower(&text)
        .map_err(|e| -> Box<dyn std::error::Error> {
            format!("{}: {e}", spec.display()).into()
        })?;

    // THE GATE then the plan. `plan_apply` runs the static check FIRST and refuses
    // to emit any turn if it fails — an over-grant never reaches a submittable
    // sequence through this path.
    match plan_apply(&dep, ring) {
        Ok(plan) => {
            if cfg.is_json() {
                let phases: Vec<serde_json::Value> = plan
                    .turns
                    .iter()
                    .map(|t| {
                        serde_json::json!({
                            "phase": t.phase,
                            "agent": hex::encode(t.agent.0),
                            "turn_hash": hex::encode(t.turn_hash),
                            "projected_receipt_hash": hex::encode(t.projected_receipt_hash),
                        })
                    })
                    .collect();
                ctx.json_stdout(&serde_json::json!({
                    "command": "deploy apply",
                    "spec": spec.display().to_string(),
                    "pass": true,
                    "federation_id": hex::encode(plan.federation_id.0),
                    "turn_count": plan.turns.len(),
                    "chain_is_linked": plan.chain_is_linked(),
                    "receipts_are_planned_shape": plan.receipts_are_planned_shape(),
                    "turns": phases,
                    "exit_code": 0,
                }));
                return Ok(());
            }

            ctx.header("DreggDL — apply plan (static gate PASSED)");
            ctx.kv("Spec", &spec.display().to_string());
            ctx.kv("Federation", &hex::encode(plan.federation_id.0));
            ctx.kv("Turns", &plan.turns.len().to_string());
            ctx.success(
                "Static gate PASSED — emitting the per-root turn sequence (births → funds → \
                 grants), chained into a receipt-chain SHAPE.",
            );
            for (i, t) in plan.turns.iter().enumerate() {
                ctx.kv_dim(
                    &format!("  turn[{i}] {}", t.phase),
                    &format!(
                        "agent {} · turn {} · receipt {}",
                        crate::output::abbrev_hex(&hex::encode(t.agent.0), 8, 4),
                        crate::output::abbrev_hex(&hex::encode(t.turn_hash), 8, 4),
                        crate::output::abbrev_hex(&hex::encode(t.projected_receipt_hash), 8, 4),
                    ),
                );
            }
            ctx.info(
                "  These turns are a SHAPE: the SDK re-signs each action with the live key and \
                 fills the executor-deferred receipt fields at submit time.",
            );
            Ok(())
        }

        // REFUSED by the gate — an in-forest amplification / non-conservation /
        // ill-formedness. NO turn was produced. Exit 2.
        Err(ApplyError::Refused { assurance }) => {
            if cfg.is_json() {
                let diag = explain_assurance(&lowered, &assurance);
                ctx.json_stdout(&serde_json::json!({
                    "command": "deploy apply",
                    "spec": spec.display().to_string(),
                    "pass": false,
                    "refused": true,
                    "findings": diag.lines(),
                    "exit_code": EXIT_REFUSED,
                }));
                std::process::exit(EXIT_REFUSED);
            }
            ctx.header("DreggDL — apply REFUSED by the static gate");
            ctx.kv("Spec", &spec.display().to_string());
            ctx.warn("No turn was produced — the gate refuses an unsafe deployment up front.");
            report_refusal(ctx, explain_assurance(&lowered, &assurance));
            std::process::exit(EXIT_REFUSED);
        }

        // Lowering failed on the `plan_apply` path (we already lowered above so
        // this is unlikely, but it is a usage error either way): exit 1.
        Err(e @ ApplyError::Lower(_)) => {
            Err(format!("{}: {e}", spec.display()).into())
        }
    }
}

/// Print every finding with the enriched, spec-named explanation — for an
/// amplification this is the human OVER-GRANT diagnostic (named edge + held vs
/// granted facet). Shared by `check` and `apply`. Takes the already-enriched
/// [`dregg_deploy::DeployDiagnostics`] so this module never has to name the
/// (non-re-exported) `Assurance` type.
fn report_refusal(ctx: &Context, diag: dregg_deploy::DeployDiagnostics) {
    ctx.error(&format!(
        "Static check REFUSED the deployment ({} finding(s) over the declared authority layout):",
        diag.findings.len()
    ));
    for line in diag.lines() {
        ctx.info(&format!("  • {line}"));
    }
}
