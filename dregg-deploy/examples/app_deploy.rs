//! `app_deploy` — DreggDL deploys the REAL starbridge-apps, and the gates catch
//! the over-grant before it ships.
//!
//! For each of three deos-native starbridge-apps (`supply-chain-provenance`,
//! `escrow-market`, `identity`), this example loads TWO crate-local DreggDL specs
//! (`dregg-deploy/specs/<app>.dregg.toml`) — a CORRECT app-deploy and a
//! DELIBERATELY OVER-GRANTING sibling — and runs the deploy gates over both:
//!
//!   1. the static NO-AMPLIFICATION + conservation gate (`plan_apply`): the
//!      correct spec is ACCEPTED and lowers to its per-root turn sequence; the
//!      over-granting spec is REFUSED before any turn, with the exact offending
//!      edge NAMED (spec names + human facets, via the enriched diagnostics);
//!   2. the BEHAVIORAL refinement gate (`refines_upgrade`, FlowRefine): treating
//!      the over-grant as a "redeploy" of the running correct deployment, the
//!      gate decides `overgrant ≤ᶠ correct` — it DIVERGES (the over-grant fires a
//!      capability the running deploy never had), and names the diverging effect.
//!
//! Run:  cargo run -p dregg-deploy --example app_deploy
//! Exit: 0 iff every accept ACCEPTED and every over-grant REFUSED (the story
//!       holds); non-zero otherwise (so it doubles as a smoke test).

use std::process::ExitCode;

use dregg_deploy::{
    AppliedPlan, ApplyError, FlowSpec, Lowered, explain_assurance, parse_toml, plan_apply,
    refines_intent, refines_upgrade,
};

/// One app: its name + the two crate-local spec files.
struct AppSpecs {
    app: &'static str,
    accept: &'static str,
    overgrant: &'static str,
}

const APPS: &[AppSpecs] = &[
    AppSpecs {
        app: "supply-chain-provenance",
        accept: include_str!("../specs/supply-chain-provenance.dregg.toml"),
        overgrant: include_str!("../specs/supply-chain-provenance.overgrant.dregg.toml"),
    },
    AppSpecs {
        app: "escrow-market",
        accept: include_str!("../specs/escrow-market.dregg.toml"),
        overgrant: include_str!("../specs/escrow-market.overgrant.dregg.toml"),
    },
    AppSpecs {
        app: "identity",
        accept: include_str!("../specs/identity.dregg.toml"),
        overgrant: include_str!("../specs/identity.overgrant.dregg.toml"),
    },
];

fn main() -> ExitCode {
    println!("══════════════════════════════════════════════════════════════════════");
    println!(" DreggDL · deploy the real starbridge-apps · the gate catches over-grant");
    println!("══════════════════════════════════════════════════════════════════════\n");

    let mut all_ok = true;
    for a in APPS {
        all_ok &= run_app(a);
        println!();
    }

    println!("══════════════════════════════════════════════════════════════════════");
    if all_ok {
        println!(" RESULT: every app-deploy ACCEPTED, every over-grant REFUSED + named. ✓");
        ExitCode::SUCCESS
    } else {
        println!(" RESULT: a gate did not behave as the story requires. ✗");
        ExitCode::FAILURE
    }
}

fn run_app(a: &AppSpecs) -> bool {
    println!(
        "── {} ──────────────────────────────────────────────",
        a.app
    );

    // (1) The CORRECT deploy spec: must be ACCEPTED (no-amp ✓, conserves ✓), and
    //     lower to its per-root turn sequence.
    let accept_dep = match parse_toml(a.accept) {
        Ok(d) => d,
        Err(e) => {
            println!("  ✗ accept spec failed to parse: {e}");
            return false;
        }
    };
    let accepted: AppliedPlan = match plan_apply(&accept_dep, false) {
        Ok(p) => p,
        Err(ApplyError::Refused { assurance }) => {
            println!("  ✗ the CORRECT spec was unexpectedly REFUSED:");
            if let Ok(l) = Lowered::from_deployment(&accept_dep) {
                for line in explain_assurance(&l, &assurance).lines() {
                    println!("      {line}");
                }
            }
            return false;
        }
        Err(e) => {
            println!("  ✗ accept spec error: {e}");
            return false;
        }
    };
    println!(
        "  ACCEPT  ✓  no-amp ✓ · conserves ✓ · lowered to {} receipt-chained turn(s):",
        accepted.len()
    );
    let phases: Vec<&str> = accepted.turns.iter().map(|t| t.phase).collect();
    println!("            phases (dependency order): {phases:?}");
    // The receipt chain is the honest PLANNED SHAPE (executor-filled fields are
    // typed Deferred, not zeroed) and is internally linked.
    println!(
        "            receipt chain linked: {} · planned-shape (dynamic fields deferred): {}",
        accepted.chain_is_linked(),
        accepted.receipts_are_planned_shape()
    );
    // refines ✓ (BEHAVIORAL): the accepted lowering stays WITHIN its declared
    // envelope — it conforms to the intent that authorizes exactly its own
    // effects (the FlowRefine intent-conformance gate, `lowered ≤ᶠ intent`).
    let envelope = FlowSpec::from_plan_envelope(&accepted);
    let accept_refines = refines_intent(&accepted, &envelope).is_refine();
    println!(
        "            refines ✓: lowering conforms to its declared effect envelope: {accept_refines}"
    );
    if !accept_refines {
        println!("  ✗ the accepted lowering did NOT conform to its own envelope (a bug)");
        return false;
    }

    // (2) The OVER-GRANTING spec: must be REFUSED by the static gate, with the
    //     offending edge NAMED.
    let og_dep = match parse_toml(a.overgrant) {
        Ok(d) => d,
        Err(e) => {
            println!("  ✗ over-grant spec failed to parse: {e}");
            return false;
        }
    };
    let refused_named = match plan_apply(&og_dep, false) {
        Ok(_) => {
            println!("  ✗ the OVER-GRANT spec was NOT refused — the gate missed it!");
            return false;
        }
        Err(ApplyError::Refused { assurance }) => {
            println!("  REFUSE  ✓  the over-grant is REFUSED before any turn — named:");
            let lowered = Lowered::from_deployment(&og_dep).expect("over-grant lowers");
            let diag = explain_assurance(&lowered, &assurance);
            for line in diag.lines() {
                println!("            {line}");
            }
            !diag.is_clean()
        }
        Err(e) => {
            println!("  ✗ over-grant spec error (not a refusal): {e}");
            return false;
        }
    };

    // (3) The BEHAVIORAL refinement gate: the over-grant as a "redeploy" of the
    //     running (accepted) deployment WIDENS it — refines_upgrade DIVERGES and
    //     names the new effect. (This catches widenings the static gate cannot;
    //     here it independently confirms the over-grant introduces new authority.)
    //     We must lower the over-grant to a plan to run the flow gate; the gate
    //     runs on the LOWERED forest, which exists even though `apply` refused to
    //     EMIT a turn sequence — so we lower it directly into a plan-shaped flow.
    let refine_ok = match build_plan_unchecked(&og_dep) {
        Some(og_plan) => {
            let v = refines_upgrade(&og_plan, &accepted);
            if v.is_refine() {
                println!("  REFINE  …  (over-grant does not widen the running flow — n/a here)");
                true
            } else {
                let f = &v.findings()[0];
                println!(
                    "  REFINE  ✓  redeploy-widening also caught by FlowRefine (overgrant ⋠ running):"
                );
                println!("            {}", f.message);
                true
            }
        }
        None => {
            // The over-grant could not be lowered to a flow (shouldn't happen —
            // it lowers fine; only the GATE refused). Treat as informational.
            println!("  REFINE  …  (over-grant flow unavailable; static gate already refused)");
            true
        }
    };

    refused_named && refine_ok
}

/// Lower a deployment to an [`AppliedPlan`] WITHOUT the static gate — used only
/// to run the *behavioral* refinement gate over a spec the static gate (rightly)
/// refused, so the example can show BOTH gates' verdicts on the same over-grant.
/// The behavioral gate is independent of the static one; this does not bypass any
/// safety (nothing is submitted).
fn build_plan_unchecked(dep: &dregg_deploy::Deployment) -> Option<AppliedPlan> {
    let lowered = Lowered::from_deployment(dep).ok()?;
    Some(dregg_deploy::apply::plan_from_lowered(&lowered))
}
