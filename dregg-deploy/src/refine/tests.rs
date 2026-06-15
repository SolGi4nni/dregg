//! Refinement-gate tests: the σ-free `decide_refines` mirror agrees with
//! `FlowRefine.lean` on its own counterexample (both polarities), and the two
//! deploy-side gates work — a safe (narrowing) upgrade is ACCEPTED, an unsafe
//! widening is REJECTED with the divergence named.

use super::*;
use crate::apply::plan_apply_toml;

// ════════════════════════════════════════════════════════════════════════════
//  §A — The mirror agrees with FlowRefine.lean (non-vacuity, both polarities).
//
//  FlowRefine §5 pins `decideRefines` against FlowAlgebra's headline
//  counterexample: early = (P⋆R) ⊔ (Q⋆R), late = (P⊔Q) ⋆ R, with P=fire 1,
//  Q=fire 2, R=run 0 (output letter 0). The HALF holds (early ≤ late = true);
//  the RIGHT-SKEW fails (late ≤ early = false). We rebuild those exact `Proc`s
//  in the Rust mirror and assert the SAME verdicts — so the mirror is faithful
//  on the very example the Lean proof distinguishes.
// ════════════════════════════════════════════════════════════════════════════

/// `R = run 0 …` projects (σ-free) to `Emit 0` — fire output letter 0, halt.
fn rr() -> Proc {
    Proc::Emit(0)
}
fn pf() -> Proc {
    Proc::Emit(1)
}
fn qf() -> Proc {
    Proc::Emit(2)
}
/// `P ⋆ R` = `Seqp(P, R)` (R runs first).
fn seq(p: Proc, r: Proc) -> Proc {
    Proc::Seqp(Box::new(p), Box::new(r))
}
fn ch(a: Proc, b: Proc) -> Proc {
    Proc::Ch(Box::new(a), Box::new(b))
}

fn early_ex() -> Proc {
    // (P ⋆ R) ⊔ (Q ⋆ R)
    ch(seq(pf(), rr()), seq(qf(), rr()))
}
fn late_ex() -> Proc {
    // (P ⊔ Q) ⋆ R
    seq(ch(pf(), qf()), rr())
}

#[test]
fn mirror_agrees_with_flowrefine_half_holds() {
    // FlowRefine #guard: decideRefines earlyEx lateEx == true (the half).
    assert!(
        decide_refines(&early_ex(), &late_ex()),
        "the half must hold: (P⋆R) ⊔ (Q⋆R) ≤ᶠ (P⊔Q) ⋆ R (FlowRefine.decideRefines_half)"
    );
}

#[test]
fn mirror_agrees_with_flowrefine_rightskew_fails() {
    // FlowRefine #guard: decideRefines lateEx earlyEx == false (the right-skew).
    assert!(
        !decide_refines(&late_ex(), &early_ex()),
        "the right-skew must fail: (P⊔Q) ⋆ R ⋠ (P⋆R) ⊔ (Q⋆R) (FlowRefine.decideRefines_rightskew)"
    );
}

#[test]
fn mirror_reflexive_and_distinct_letters() {
    // FlowRefine #guard: a flow refines itself; distinct single letters do not.
    assert!(
        decide_refines(&early_ex(), &early_ex()),
        "reflexive: a flow refines itself"
    );
    assert!(
        !decide_refines(&Proc::Emit(1), &Proc::Emit(2)),
        "distinct letters: fire 1 ⋠ fire 2"
    );
    // A strict narrowing: a single branch refines the choice that offers it.
    assert!(
        decide_refines(&Proc::Emit(1), &ch(Proc::Emit(1), Proc::Emit(2))),
        "fire 1 ≤ᶠ (fire 1 ⊔ fire 2): the choice offers the 1-move"
    );
    // …but the choice does NOT refine a single branch (it can fire 2, which the
    // branch cannot match) — the no-widening direction.
    assert!(
        !decide_refines(&ch(Proc::Emit(1), Proc::Emit(2)), &Proc::Emit(1)),
        "(fire 1 ⊔ fire 2) ⋠ fire 1: the choice widens"
    );
}

// ════════════════════════════════════════════════════════════════════════════
//  §B — The deploy flow mapping: a linear deploy lowers to a fireable chain.
// ════════════════════════════════════════════════════════════════════════════

const BASE: &str = r#"
[federation]
id = "auto"

[[factory]]
ref = "f"

[[cell]]
name = "deal"
factory = "f"
[[cell]]
name = "operator"
factory = "f"
[[cell]]
name = "bank"
factory = "f"

[[fund]]
from = "bank"
to   = "deal"
amount = 1000

[[grant]]
from        = "deal"
to          = "operator"
permissions = "signature"
target      = "deal"
"#;

#[test]
fn a_deploy_plan_lowers_to_a_nonempty_fireable_flow() {
    let plan = plan_apply_toml(BASE, false).expect("base applies");
    let flow = flow_of_plan(&plan);
    // The flow is non-vacuous: it has at least one move (a vacuous refinement
    // that held because the graph is dead would be a BUG — the FlowAlgebra
    // non-vacuity discipline).
    assert!(
        !moves(&flow).is_empty(),
        "the deploy flow actually fires effects"
    );
    // It refines itself (the gate's reflexive sanity — every plan is a safe
    // upgrade of itself).
    assert!(decide_refines(&flow, &flow), "a plan's flow refines itself");
}

// ════════════════════════════════════════════════════════════════════════════
//  §C — THE DELIVERABLE: safe (narrowing) upgrade ACCEPTED.
//
//  NARROWED drops BASE's grant: it performs a strict SUBSET of BASE's effects.
//  So every effect-sequence NARROWED fires, BASE can match → narrowed ≤ᶠ base.
// ════════════════════════════════════════════════════════════════════════════

const NARROWED: &str = r#"
[federation]
id = "auto"

[[factory]]
ref = "f"

[[cell]]
name = "deal"
factory = "f"
[[cell]]
name = "operator"
factory = "f"
[[cell]]
name = "bank"
factory = "f"

[[fund]]
from = "bank"
to   = "deal"
amount = 1000
"#;

#[test]
fn safe_narrowing_upgrade_is_accepted() {
    let base = plan_apply_toml(BASE, false).expect("base applies");
    let narrowed = plan_apply_toml(NARROWED, false).expect("narrowed applies");
    // NARROWED drops the grant — it does strictly LESS. A safe upgrade:
    // narrowed ≤ᶠ base.
    let v = refines_upgrade(&narrowed, &base);
    assert!(
        v.is_refine(),
        "dropping an effect is a narrowing — the upgrade must be ACCEPTED; got: {:?}",
        v.findings()
    );
}

#[test]
fn an_identical_redeploy_is_a_safe_upgrade() {
    // Re-deploying the SAME spec is the reflexive safe upgrade (base ≤ᶠ base).
    let base = plan_apply_toml(BASE, false).unwrap();
    let base2 = plan_apply_toml(BASE, false).unwrap();
    assert!(
        refines_upgrade(&base2, &base).is_refine(),
        "an identical redeploy refines the running deployment"
    );
}

// ════════════════════════════════════════════════════════════════════════════
//  §D — THE DELIVERABLE: unsafe WIDENING upgrade REJECTED, divergence named.
//
//  WIDENED is BASE plus an EXTRA grant (deal → bank). That extra grant is a new
//  observable effect-letter BASE never had — so WIDENED can fire a move BASE
//  cannot match → widened ⋠ base, and the finding names the diverging letter.
// ════════════════════════════════════════════════════════════════════════════

const WIDENED: &str = r#"
[federation]
id = "auto"

[[factory]]
ref = "f"

[[cell]]
name = "deal"
factory = "f"
[[cell]]
name = "operator"
factory = "f"
[[cell]]
name = "bank"
factory = "f"

[[fund]]
from = "bank"
to   = "deal"
amount = 1000

[[grant]]
from        = "deal"
to          = "operator"
permissions = "signature"
target      = "deal"

# THE WIDENING: an extra grant the running (BASE) deployment never had —
# deal hands `bank` a fresh signature cap. A new reachable authority edge.
[[grant]]
from        = "deal"
to          = "bank"
permissions = "signature"
target      = "deal"
"#;

#[test]
fn unsafe_widening_upgrade_is_rejected_with_the_divergence_named() {
    let base = plan_apply_toml(BASE, false).expect("base applies");
    let widened = plan_apply_toml(WIDENED, false).expect("widened applies (it is well-formed)");

    // NOTE the boundary this test pins: WIDENED still PASSES the static
    // no-amplification check (its grant graph is flat — each grant is a fresh
    // signature cap, none re-delegates beyond what it holds). So the existing
    // safety gate does NOT catch it.
    assert!(
        widened.assurance.pass(),
        "the widening passes the STATIC no-amplification check — it is a flat, \
         conserving grant graph; only the BEHAVIORAL refinement check catches it"
    );

    // The refinement gate DOES catch it: widened ⋠ base.
    let v = refines_upgrade(&widened, &base);
    assert!(
        !v.is_refine(),
        "adding a new grant WIDENS the running deployment — the upgrade must be REJECTED"
    );
    let findings = v.findings();
    assert_eq!(findings.len(), 1, "one located divergence finding");
    assert_eq!(findings[0].check, "safe-upgrade");
    assert!(
        findings[0].message.contains("WIDENS") || findings[0].message.contains("not a refinement"),
        "the finding names the widening; got: {}",
        findings[0].message
    );
    assert!(
        findings[0].diverging_letter.is_some(),
        "the finding isolates the diverging effect-letter (the new grant)"
    );
}

#[test]
fn the_divergence_finding_names_the_widening_effect_in_words() {
    // The enriched refinement diagnostic: the rejected widening is named as a
    // CONCRETE effect (a GrantCapability over a target with a human facet), not
    // just an opaque letter — the "surface the diverging letter well" deliverable.
    let base = plan_apply_toml(BASE, false).unwrap();
    let widened = plan_apply_toml(WIDENED, false).unwrap();
    let v = refines_upgrade(&widened, &base);
    let f = &v.findings()[0];
    let label = f
        .diverging_effect_label
        .as_deref()
        .expect("the divergence is resolved to a concrete effect");
    // It is the extra grant: a GrantCapability effect, with a facet description.
    assert!(
        label.contains("GrantCapability"),
        "names the effect kind: {label}"
    );
    assert!(label.contains("facet"), "describes the cap facet: {label}");
    // The human message embeds the same concrete description.
    assert!(
        f.message.contains("GrantCapability"),
        "the message names the widening effect: {}",
        f.message
    );
}

#[test]
fn the_two_checks_are_independent_widening_passes_safety_but_fails_refinement() {
    // The honest-boundary claim of the module, as an executable test: the
    // no-amplification (SAFETY) check and the safe-upgrade (REFINEMENT) check
    // are DIFFERENT properties. WIDENED passes safety, fails refinement.
    let base = plan_apply_toml(BASE, false).unwrap();
    let widened = plan_apply_toml(WIDENED, false).unwrap();
    assert!(
        widened.assurance.no_amplification.is_pass(),
        "SAFETY: passes"
    );
    assert!(
        !refines_upgrade(&widened, &base).is_refine(),
        "REFINEMENT: fails"
    );
}

// ════════════════════════════════════════════════════════════════════════════
//  §E — intent-conformance: lowered ≤ᶠ declared intent.
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn lowered_conforms_to_an_intent_that_lists_its_effects() {
    // The intent that authorizes exactly what BASE does (its own envelope): BASE
    // conforms to it.
    let base = plan_apply_toml(BASE, false).unwrap();
    let intent = FlowSpec::from_plan_envelope(&base);
    let v = refines_intent(&base, &intent);
    assert!(
        v.is_refine(),
        "BASE conforms to the intent listing exactly its effects; got: {:?}",
        v.findings()
    );
}

#[test]
fn lowering_that_exceeds_the_intent_envelope_is_rejected() {
    // Declare the intent as exactly NARROWED's effect-set (fund only, no grant),
    // then check the WIDER plan (BASE, which also grants) against it. BASE fires
    // the grant effect, which the intent never authorized → lowered ⋠ intent.
    let narrowed = plan_apply_toml(NARROWED, false).unwrap();
    let base = plan_apply_toml(BASE, false).unwrap();
    let intent = FlowSpec::from_plan_envelope(&narrowed); // fund-only envelope
    let v = refines_intent(&base, &intent);
    assert!(
        !v.is_refine(),
        "BASE grants, which the fund-only intent did not authorize — must be REJECTED"
    );
    let findings = v.findings();
    assert_eq!(findings[0].check, "intent-conformance");
    assert!(
        findings[0].diverging_letter.is_some(),
        "the finding names the out-of-envelope effect (the grant)"
    );
    assert!(
        findings[0]
            .message
            .contains("MORE than the declared intent")
            || findings[0].message.contains("exceeds"),
        "the finding explains the envelope breach; got: {}",
        findings[0].message
    );
}

#[test]
fn intent_built_from_explicit_effects_authorizes_a_matching_lowering() {
    // Build an intent from EXPLICIT IntentEffect::Exact entries mirroring BASE's
    // effects, and confirm BASE conforms — exercising the IntentEffect surface.
    let base = plan_apply_toml(BASE, false).unwrap();
    // Gather BASE's concrete effects and wrap each as an Exact intent.
    let mut intents: Vec<IntentEffect> = Vec::new();
    for pt in &base.turns {
        for root in &pt.turn.call_forest.roots {
            for eff in root.all_effects() {
                intents.push(IntentEffect::Exact(eff.clone()));
            }
        }
    }
    let intent = FlowSpec::from_intent(&intents);
    assert!(
        refines_intent(&base, &intent).is_refine(),
        "an intent listing BASE's exact effects authorizes BASE"
    );
}

#[test]
fn intent_trace_decision_agrees_with_the_decide_refines_game() {
    // The honest-equivalence pin (BOTH polarities): the fast `allows_trace`
    // decision the intent gate uses MUST agree with actually running the
    // `decide_refines` simulation game on the materialized repeat-menu `μ`.
    // This is what licenses replacing the (exponential) game on the menu with
    // the (linear) membership check.
    let base = plan_apply_toml(BASE, false).unwrap();
    let lowered = super::flow_of_plan(&base);
    let trace = super::trace_of(&lowered);
    let depth = trace.len() + 1; // enough to outlast the linear lowered side

    // (a) An intent that ALLOWS every BASE letter: both the trace-check and the
    // game on μ say REFINES.
    let allow_all = FlowSpec::from_plan_envelope(&base);
    let menu_all = allow_all.to_menu_proc(depth);
    assert!(
        allow_all.allows_trace(&trace).is_ok(),
        "trace-check: all allowed → refines"
    );
    assert!(
        decide_refines(&lowered, &menu_all),
        "the decide_refines GAME on μ agrees: lowered ≤ᶠ μ(all-allowed)"
    );

    // (b) An intent MISSING one of BASE's letters (drop the last = the grant):
    // both the trace-check and the game say does-NOT-refine.
    let mut short: Vec<u64> = trace.clone();
    short.pop(); // remove one real letter from the allowed alphabet
    let allow_partial = FlowSpec {
        allowed: {
            let mut a = short.clone();
            a.sort_unstable();
            a.dedup();
            a
        },
    };
    // (only valid if the dropped letter is genuinely absent from the kept set)
    let dropped = *trace.last().unwrap();
    if !short.contains(&dropped) {
        let menu_partial = allow_partial.to_menu_proc(depth);
        assert!(
            allow_partial.allows_trace(&trace).is_err(),
            "trace-check: a missing letter → does not refine"
        );
        assert!(
            !decide_refines(&lowered, &menu_partial),
            "the decide_refines GAME on μ agrees: lowered ⋠ μ(missing a letter)"
        );
    }
}
