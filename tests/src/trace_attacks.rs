//! Trace tampering tests.
//!
//! These tests verify that the Datalog trace verifier correctly rejects:
//! - Swapped body facts
//! - Skipped derivation steps
//! - Injected unauthorized facts
//! - Reordered derivation steps
//! - References to nonexistent rules

use dregg_trace::policy::minimal_policy;
use dregg_trace::types::*;
use dregg_trace::{Evaluator, standard_policy, symbol_from_str, verify_trace};

// =============================================================================
// Helper: create a valid trace we can then tamper with
// =============================================================================

fn valid_app_access_trace() -> (Vec<Fact>, Vec<Rule>, AuthorizationTrace) {
    let rules = minimal_policy();
    let facts = vec![Fact::new(
        symbol_from_str("app"),
        vec![
            Term::Const(symbol_from_str("dashboard")),
            Term::Const(symbol_from_str("read,write")),
        ],
    )];

    let eval = Evaluator::new(facts.clone(), rules.clone());
    let request = AuthorizationRequest {
        app_id: Some(symbol_from_str("dashboard")),
        service: None,
        action: Some(symbol_from_str("read")),
        features: vec![],
        user_id: None,
        now: 1000,
    };

    let trace = eval.evaluate(&request);
    assert_eq!(trace.conclusion, Conclusion::Allow { policy_rule_id: 1 });
    (facts, rules, trace)
}

fn two_step_trace() -> (Vec<Fact>, Vec<Rule>, AuthorizationTrace) {
    // A derivation that requires two steps:
    // 1. intermediate($user) :- user($user), active($user)
    // 2. allow() :- intermediate($user), request_user($user)
    let rules = vec![
        Rule {
            id: 100,
            head: Atom {
                predicate: symbol_from_str("intermediate"),
                terms: vec![Term::Var(0)],
            },
            body: vec![
                Atom {
                    predicate: symbol_from_str("user"),
                    terms: vec![Term::Var(0)],
                },
                Atom {
                    predicate: symbol_from_str("active"),
                    terms: vec![Term::Var(0)],
                },
            ],
            checks: vec![],
        },
        Rule {
            id: 101,
            head: Atom {
                predicate: symbol_from_str("allow"),
                terms: vec![],
            },
            body: vec![
                Atom {
                    predicate: symbol_from_str("intermediate"),
                    terms: vec![Term::Var(0)],
                },
                Atom {
                    predicate: symbol_from_str("request_user"),
                    terms: vec![Term::Var(0)],
                },
            ],
            checks: vec![],
        },
    ];

    let facts = vec![
        Fact::new(
            symbol_from_str("user"),
            vec![Term::Const(symbol_from_str("alice"))],
        ),
        Fact::new(
            symbol_from_str("active"),
            vec![Term::Const(symbol_from_str("alice"))],
        ),
    ];

    let eval = Evaluator::new(facts.clone(), rules.clone());
    let request = AuthorizationRequest {
        app_id: None,
        service: None,
        action: None,
        features: vec![],
        user_id: Some(symbol_from_str("alice")),
        now: 1000,
    };

    let trace = eval.evaluate(&request);
    assert_eq!(
        trace.conclusion,
        Conclusion::Allow {
            policy_rule_id: 101
        }
    );
    assert_eq!(trace.steps.len(), 2);
    (facts, rules, trace)
}

// =============================================================================
// 1. Swap body facts (use fact from wrong rule)
// =============================================================================

#[test]
fn swap_body_fact_index_to_wrong_fact() {
    let (facts, rules, mut trace) = valid_app_access_trace();

    // Change the body_fact_indices to point to a different fact
    if let Some(step) = trace.steps.first_mut() {
        // Point to an index that either doesn't exist or is a different fact
        step.body_fact_indices = vec![999, 0, 1]; // index 999 is invalid
    }

    assert!(
        !verify_trace(&facts, &rules, &trace),
        "Trace with invalid fact index must fail verification"
    );
}

#[test]
fn swap_body_fact_to_unrelated_fact() {
    let (facts, rules, mut trace) = valid_app_access_trace();

    // The trace has body_fact_indices pointing to specific facts.
    // Swap them so the wrong fact is used for unification.
    if let Some(step) = trace.steps.first_mut() {
        if step.body_fact_indices.len() >= 2 {
            // Swap first two indices
            step.body_fact_indices.swap(0, 1);
        }
    }

    assert!(
        !verify_trace(&facts, &rules, &trace),
        "Trace with swapped body fact indices must fail"
    );
}

// =============================================================================
// 2. Skip derivation steps
// =============================================================================

#[test]
fn skip_middle_derivation_step() {
    let (facts, rules, mut trace) = two_step_trace();

    // Remove the first step (intermediate derivation)
    // This means the second step references a fact that doesn't exist yet
    trace.steps.remove(0);

    assert!(
        !verify_trace(&facts, &rules, &trace),
        "Trace with skipped prerequisite step must fail"
    );
}

#[test]
fn skip_final_step_but_claim_allow() {
    let (facts, rules, mut trace) = two_step_trace();

    // Remove the last step but keep the conclusion as Allow
    trace.steps.pop();
    // Conclusion still says Allow but the allow fact was never derived
    assert_eq!(
        trace.conclusion,
        Conclusion::Allow {
            policy_rule_id: 101
        }
    );

    assert!(
        !verify_trace(&facts, &rules, &trace),
        "Claiming Allow without deriving allow fact must fail"
    );
}

// =============================================================================
// 3. Inject unauthorized facts
// =============================================================================

#[test]
fn inject_fake_allow_fact() {
    let rules = minimal_policy();
    let facts = vec![Fact::new(
        symbol_from_str("app"),
        vec![
            Term::Const(symbol_from_str("dashboard")),
            Term::Const(symbol_from_str("read")),
        ],
    )];

    // Request for "delete" which should be denied
    let request = AuthorizationRequest {
        app_id: Some(symbol_from_str("dashboard")),
        service: None,
        action: Some(symbol_from_str("delete")),
        features: vec![],
        user_id: None,
        now: 1000,
    };

    // Create a fraudulent trace that claims allow
    let fake_trace = AuthorizationTrace {
        request: request.clone(),
        steps: vec![DerivationStep {
            rule_id: 1,
            substitution: Substitution::empty()
                .extend(0, Term::Const(symbol_from_str("dashboard")))
                .unwrap()
                .extend(1, Term::Const(symbol_from_str("read")))
                .unwrap()
                .extend(2, Term::Const(symbol_from_str("delete")))
                .unwrap(),
            body_fact_indices: vec![0, 1, 2], // indices into fact set after request injection
            derived_fact: Fact::new(symbol_from_str("allow"), vec![]),
        }],
        conclusion: Conclusion::Allow { policy_rule_id: 1 },
    };

    assert!(
        !verify_trace(&facts, &rules, &fake_trace),
        "Fraudulent trace claiming unauthorized action must fail"
    );
}

#[test]
fn inject_extra_fact_into_derivation() {
    let (facts, rules, mut trace) = two_step_trace();

    // Inject an extra derivation step that derives an unauthorized fact
    let extra_step = DerivationStep {
        rule_id: 100, // reuse existing rule
        substitution: Substitution::empty()
            .extend(0, Term::Const(symbol_from_str("evil")))
            .unwrap(),
        body_fact_indices: vec![0, 1], // try to reference existing facts
        derived_fact: Fact::new(
            symbol_from_str("intermediate"),
            vec![Term::Const(symbol_from_str("evil"))],
        ),
    };

    // Insert before the existing steps
    trace.steps.insert(0, extra_step);

    // This should fail because "evil" isn't in the user or active facts
    assert!(
        !verify_trace(&facts, &rules, &trace),
        "Injected step with non-matching facts must fail"
    );
}

// =============================================================================
// 4. Reorder derivation steps
// =============================================================================

#[test]
fn reorder_valid_if_deps_satisfied() {
    // If a step doesn't depend on a prior step's output, reordering might be valid.
    // We test that the verifier correctly handles this.
    let rules = vec![
        Rule {
            id: 10,
            head: Atom {
                predicate: symbol_from_str("derived_a"),
                terms: vec![],
            },
            body: vec![Atom {
                predicate: symbol_from_str("base_a"),
                terms: vec![],
            }],
            checks: vec![],
        },
        Rule {
            id: 11,
            head: Atom {
                predicate: symbol_from_str("derived_b"),
                terms: vec![],
            },
            body: vec![Atom {
                predicate: symbol_from_str("base_b"),
                terms: vec![],
            }],
            checks: vec![],
        },
        Rule {
            id: 12,
            head: Atom {
                predicate: symbol_from_str("allow"),
                terms: vec![],
            },
            body: vec![
                Atom {
                    predicate: symbol_from_str("derived_a"),
                    terms: vec![],
                },
                Atom {
                    predicate: symbol_from_str("derived_b"),
                    terms: vec![],
                },
            ],
            checks: vec![],
        },
    ];

    let facts = vec![
        Fact::new(symbol_from_str("base_a"), vec![]),
        Fact::new(symbol_from_str("base_b"), vec![]),
    ];

    let eval = Evaluator::new(facts.clone(), rules.clone());
    let request = AuthorizationRequest {
        app_id: None,
        service: None,
        action: None,
        features: vec![],
        user_id: None,
        now: 1000,
    };

    let trace = eval.evaluate(&request);
    assert_eq!(trace.conclusion, Conclusion::Allow { policy_rule_id: 12 });
    assert!(verify_trace(&facts, &rules, &trace));
}

#[test]
fn reorder_invalid_when_deps_unsatisfied() {
    let (facts, rules, mut trace) = two_step_trace();

    // Reverse the steps: step 1 (allow) comes before step 0 (intermediate)
    // This means the allow step references a fact that hasn't been derived yet
    trace.steps.reverse();

    // We also need to fix the body_fact_indices since they're absolute
    // The reversed trace will try to reference "intermediate" which doesn't exist yet
    assert!(
        !verify_trace(&facts, &rules, &trace),
        "Reordered trace with unsatisfied deps must fail"
    );
}

// =============================================================================
// 5. Nonexistent rule references
// =============================================================================

#[test]
fn reference_nonexistent_rule_id() {
    let (facts, rules, mut trace) = valid_app_access_trace();

    // Change the rule_id to one that doesn't exist
    if let Some(step) = trace.steps.first_mut() {
        step.rule_id = 9999; // no such rule
    }

    assert!(
        !verify_trace(&facts, &rules, &trace),
        "Reference to nonexistent rule must fail"
    );
}

#[test]
fn reference_rule_with_wrong_body_arity() {
    let (facts, rules, mut trace) = valid_app_access_trace();

    // Provide wrong number of body fact indices
    if let Some(step) = trace.steps.first_mut() {
        step.body_fact_indices = vec![0]; // too few
    }

    assert!(
        !verify_trace(&facts, &rules, &trace),
        "Wrong number of body facts must fail"
    );
}

#[test]
fn reference_rule_with_extra_body_facts() {
    let (facts, rules, mut trace) = valid_app_access_trace();

    // Provide too many body fact indices
    if let Some(step) = trace.steps.first_mut() {
        step.body_fact_indices.push(0);
        step.body_fact_indices.push(0);
        step.body_fact_indices.push(0);
    }

    assert!(
        !verify_trace(&facts, &rules, &trace),
        "Too many body fact indices must fail"
    );
}

// =============================================================================
// 6. Substitution tampering
// =============================================================================

#[test]
fn substitution_inconsistent_with_derived_fact() {
    let (facts, rules, mut trace) = valid_app_access_trace();

    // Tamper with the derived fact to claim a different conclusion
    if let Some(step) = trace.steps.first_mut() {
        step.derived_fact = Fact::new(
            symbol_from_str("deny"), // changed from allow to deny
            vec![],
        );
    }

    assert!(
        !verify_trace(&facts, &rules, &trace),
        "Derived fact inconsistent with rule head must fail"
    );
}

#[test]
fn substitution_has_wrong_variable_binding() {
    let (facts, rules, mut trace) = valid_app_access_trace();

    // Change a variable binding in the substitution
    if let Some(step) = trace.steps.first_mut() {
        step.substitution = Substitution::empty()
            .extend(0, Term::Const(symbol_from_str("WRONG_APP")))
            .unwrap();
    }

    assert!(
        !verify_trace(&facts, &rules, &trace),
        "Wrong variable binding must fail unification"
    );
}

// =============================================================================
// 7. Conclusion tampering
// =============================================================================

#[test]
fn claim_allow_when_deny_is_correct() {
    let rules = minimal_policy();
    let facts = vec![]; // no facts at all

    let request = AuthorizationRequest {
        app_id: Some(symbol_from_str("anything")),
        service: None,
        action: Some(symbol_from_str("read")),
        features: vec![],
        user_id: None,
        now: 1000,
    };

    // Create a trace that falsely claims Allow
    let fake_trace = AuthorizationTrace {
        request,
        steps: vec![], // no derivation steps
        conclusion: Conclusion::Allow { policy_rule_id: 1 },
    };

    assert!(
        !verify_trace(&facts, &rules, &fake_trace),
        "Claiming Allow with no derivation must fail"
    );
}

#[test]
fn claim_deny_when_allow_was_derived() {
    let (facts, rules, mut trace) = valid_app_access_trace();

    // The real conclusion is Allow, but we claim Deny
    trace.conclusion = Conclusion::Deny;

    assert!(
        !verify_trace(&facts, &rules, &trace),
        "Claiming Deny when allow was derived must fail"
    );
}

#[test]
fn claim_wrong_policy_rule_id() {
    let (facts, rules, mut trace) = valid_app_access_trace();

    // Change the policy_rule_id to a different one
    trace.conclusion = Conclusion::Allow {
        policy_rule_id: 999,
    };

    assert!(
        !verify_trace(&facts, &rules, &trace),
        "Wrong policy rule ID in conclusion must fail"
    );
}
