//! Standalone trace verification.
//!
//! Verifies that a derivation trace is valid WITHOUT re-running evaluation.
//! This is the function that a ZK verifier circuit would replicate.

use std::collections::HashSet;

use crate::check;
use crate::eval::{Evaluator, predicates};
use crate::types::*;

/// Maximum number of trace steps allowed (prevents memory DoS).
const MAX_TRACE_STEPS: usize = 10_000;

/// Verify that an authorization trace is valid given the base facts, rules,
/// and an expected request.
///
/// The `expected_request` parameter allows the caller to verify that the trace's
/// embedded request matches the actual authorization query being verified. This
/// prevents a malicious prover from substituting a different request that would
/// produce an Allow conclusion.
///
/// Checks performed:
/// 1. Request authentication: trace.request must match expected_request.
/// 2. Base fact groundness: all base facts must be ground (no variables).
/// 3. Trace size: rejects traces exceeding MAX_TRACE_STEPS.
/// 4. Per-step verification (rule, unification, checks, derived fact).
/// 5. Conclusion consistency with derived facts.
/// 6. Deny completeness: verifies no derivable deny facts were omitted.
/// 7. Policy rule ID attribution: the claimed rule must be the one that derived allow.
pub fn verify_trace_with_request(
    facts: &[Fact],
    rules: &[Rule],
    trace: &AuthorizationTrace,
    expected_request: &AuthorizationRequest,
) -> bool {
    // Issue #9: Verify the trace's request matches the expected request.
    // A malicious prover could embed a different request that produces Allow.
    if trace.request != *expected_request {
        return false;
    }

    verify_trace(facts, rules, trace)
}

/// Verify that an authorization trace is valid given the base facts and rules.
///
/// Checks performed for each derivation step:
/// 1. The rule ID references a valid rule.
/// 2. The substitution unifies with each body atom against the referenced fact.
/// 3. Each referenced body fact exists in the fact set at that point.
/// 4. All constraint checks pass under the substitution.
/// 5. The derived fact matches the rule head under the substitution.
/// 6. The final conclusion is consistent with the derived facts.
/// 7. Deny completeness: re-derives deny facts to catch omissions.
///
/// IMPORTANT: Callers MUST verify that `trace.request` matches the actual
/// authorization query being evaluated. The trace's embedded request is
/// prover-controlled and not authenticated by this function. Use
/// `verify_trace_with_request` for the full check, or manually compare
/// `trace.request` against the expected request before calling this function.
pub fn verify_trace(facts: &[Fact], rules: &[Rule], trace: &AuthorizationTrace) -> bool {
    let allow_pred = predicates::allow();
    let deny_pred = predicates::deny();

    // Issue #8: Reject traces exceeding maximum step count (memory DoS prevention).
    if trace.steps.len() > MAX_TRACE_STEPS {
        return false;
    }

    // Issue #3: Validate all base facts are ground (no variables).
    // A non-ground base fact like `app(Var(999))` could unify with any rule body
    // trivially, enabling a malicious prover to forge derivations.
    for fact in facts {
        if fact.terms.iter().any(|t| matches!(t, Term::Var(_))) {
            return false;
        }
    }

    // SECURITY: Reject traces where allow/deny conclusions appear in base facts.
    // Base facts should only contain input facts (capabilities, request properties, etc.),
    // never conclusions. A malicious prover could inject allow(...) as a base fact to
    // bypass all policy rules.
    for fact in facts {
        if fact.predicate == allow_pred || fact.predicate == deny_pred {
            return false;
        }
    }

    // SECURITY: Fail-closed revocation check.
    // If any `revocable(T)` fact appears in base facts, there MUST be a corresponding
    // `not_revoked(T)` fact. Without this, a malicious prover can omit `revoked(T)` to
    // silently bypass revocation. The verifier MUST also independently check revocation
    // status outside the trace (via RevocationChannelSet), but this provides defense-in-depth.
    let revocable_pred = crate::symbol_from_str("revocable");
    let not_revoked_pred = crate::symbol_from_str("not_revoked");
    for fact in facts {
        if fact.predicate == revocable_pred {
            // For each revocable(T), require not_revoked(T) in base facts
            let token_term = &fact.terms;
            let has_not_revoked = facts
                .iter()
                .any(|f| f.predicate == not_revoked_pred && f.terms == *token_term);
            if !has_not_revoked {
                return false;
            }
        }
    }

    // Build up the fact set as we verify each step
    let mut known_facts: Vec<Fact> = facts.to_vec();

    // Inject request facts (same as the evaluator does)
    Evaluator::inject_request_facts(&mut known_facts, &trace.request);

    // Verify each derivation step, tracking which rule actually derived allow
    let mut allow_deriving_rule: Option<u32> = None;
    for step in &trace.steps {
        if !verify_step(step, &known_facts, rules) {
            return false;
        }
        // Track which rule derived the allow conclusion
        if step.derived_fact.predicate == allow_pred {
            allow_deriving_rule = Some(step.rule_id);
        }
        // Add the derived fact to our known set
        known_facts.push(step.derived_fact.clone());
    }

    // Issue #7: Verify policy_rule_id attribution.
    // If conclusion is Allow, the claimed policy_rule_id must match the rule
    // that actually derived the allow fact.
    if let Conclusion::Allow { policy_rule_id } = &trace.conclusion {
        match allow_deriving_rule {
            Some(actual_rule_id) if actual_rule_id != *policy_rule_id => {
                return false;
            }
            None if *policy_rule_id != 0 => {
                // No rule derived allow, but a non-zero rule is claimed
                // (policy_rule_id == 0 is allowed for base-fact allow, checked below)
                if !known_facts.iter().any(|f| f.predicate == allow_pred) {
                    return false;
                }
            }
            _ => {}
        }
    }

    // Issue #2: Deny completeness check.
    // A malicious prover can omit deny derivation steps. After verifying all
    // provided steps, we re-derive using deny-relevant rules to check if any
    // deny fact is derivable but missing from the trace.
    if matches!(trace.conclusion, Conclusion::Allow { .. }) {
        if has_derivable_deny(&known_facts, rules) {
            return false;
        }
    }

    // Verify the conclusion is consistent
    verify_conclusion(&known_facts, &trace.steps, &trace.conclusion)
}

/// Check if any deny fact is derivable from the current fact set and rules.
///
/// This implements the "completeness check" for Issue #2: a malicious prover
/// cannot omit deny derivation steps (BUDGET_DENY, REVOCATION_DENY, NOT_BEFORE_DENY)
/// to claim Allow when Deny should be the conclusion.
fn has_derivable_deny(known_facts: &[Fact], rules: &[Rule]) -> bool {
    let deny_pred = predicates::deny();

    // Check if deny already exists in known facts
    if known_facts.iter().any(|f| f.predicate == deny_pred) {
        return true;
    }

    // Filter to only deny-producing rules (optimization)
    let deny_rules: Vec<&Rule> = rules
        .iter()
        .filter(|r| r.head.predicate == deny_pred)
        .collect();

    if deny_rules.is_empty() {
        return false;
    }

    // Build fact set for O(1) membership check
    let fact_set: HashSet<Fact> = known_facts.iter().cloned().collect();

    // Try to derive deny facts using the deny rules
    let deny_rules_owned: Vec<Rule> = deny_rules.into_iter().cloned().collect();
    let new_steps = Evaluator::derive_one_round(&deny_rules_owned, known_facts, &fact_set);

    // If any deny fact would be derived, the trace is incomplete
    new_steps
        .iter()
        .any(|step| step.derived_fact.predicate == deny_pred)
}

/// Verify a single derivation step.
fn verify_step(step: &DerivationStep, known_facts: &[Fact], rules: &[Rule]) -> bool {
    // 1. Find the rule
    let Some(rule) = rules.iter().find(|r| r.id == step.rule_id) else {
        return false;
    };

    // 2. Check body atom count matches indices count
    if step.body_fact_indices.len() != rule.body.len() {
        return false;
    }

    // 3. For each body atom, verify the referenced fact exists and unifies
    let mut reconstructed_subst = Substitution::empty();

    for (body_atom, &fact_idx) in rule.body.iter().zip(step.body_fact_indices.iter()) {
        // Check the fact index is valid
        if fact_idx >= known_facts.len() {
            return false;
        }

        let fact = &known_facts[fact_idx];

        // Try to unify this body atom with the fact
        let Some(new_subst) =
            Evaluator::unify_atom_with_fact(body_atom, fact, &reconstructed_subst)
        else {
            return false;
        };
        reconstructed_subst = new_subst;
    }

    // 4. Verify the claimed substitution is consistent with what we reconstructed.
    if !substitutions_consistent(&step.substitution, &reconstructed_subst) {
        return false;
    }

    // 5. Check constraints pass
    if !rule
        .checks
        .iter()
        .all(|c| check::eval_check(c, &step.substitution))
    {
        return false;
    }

    // 6. Verify the derived fact matches the head under substitution
    let expected_atom = step.substitution.apply_atom(&rule.head);
    if expected_atom.predicate != step.derived_fact.predicate {
        return false;
    }
    if expected_atom.terms != step.derived_fact.terms {
        return false;
    }

    // 7. Verify the derived fact is ground
    if step
        .derived_fact
        .terms
        .iter()
        .any(|t| matches!(t, Term::Var(_)))
    {
        return false;
    }

    true
}

/// Check that two substitutions are consistent (no conflicting bindings)
/// and the claimed substitution does not contain extra unbound variables
/// that don't appear in the rule's body or head.
fn substitutions_consistent(claimed: &Substitution, reconstructed: &Substitution) -> bool {
    // All reconstructed bindings must match claimed bindings
    for (var, term) in &reconstructed.bindings {
        if let Some(claimed_term) = claimed.get(*var) {
            if claimed_term != term {
                return false;
            }
        }
    }
    // Reject extra variables in claimed substitution that were never bound
    // during reconstruction (i.e., variables not referenced by any body atom).
    for (var, _) in &claimed.bindings {
        if reconstructed.get(*var).is_none() {
            return false;
        }
    }
    true
}

/// Verify the conclusion is consistent with the derived facts.
///
/// A Deny conclusion is valid if:
/// - An explicit `deny` fact was derived (deny overrides allow), OR
/// - No `allow` fact exists in facts or steps.
///
/// An Allow conclusion is valid if:
/// - No `deny` fact was derived (deny always wins), AND
/// - An `allow` fact exists derived by the claimed rule.
/// - The claimed policy_rule_id matches the rule that actually derived allow (Issue #7).
fn verify_conclusion(facts: &[Fact], steps: &[DerivationStep], conclusion: &Conclusion) -> bool {
    let allow_pred = predicates::allow();
    let deny_pred = predicates::deny();

    // Check if any deny fact was derived or exists in known facts
    let has_deny = steps.iter().any(|s| s.derived_fact.predicate == deny_pred)
        || facts.iter().any(|f| f.predicate == deny_pred);

    match conclusion {
        Conclusion::Allow { policy_rule_id } => {
            // Deny always overrides allow — an Allow conclusion is invalid if deny exists
            if has_deny {
                return false;
            }
            // There must be an allow fact derived by the claimed rule.
            // Issue #7: The policy_rule_id must match the ACTUAL rule that derived allow.
            let has_allow_in_steps = steps
                .iter()
                .any(|s| s.derived_fact.predicate == allow_pred && s.rule_id == *policy_rule_id);
            let has_allow_in_base =
                facts.iter().any(|f| f.predicate == allow_pred) && *policy_rule_id == 0;
            has_allow_in_steps || has_allow_in_base
        }
        Conclusion::Deny => {
            // Deny is valid if: explicit deny was derived, OR no allow exists
            if has_deny {
                return true;
            }
            let no_allow_in_facts = !facts.iter().any(|f| f.predicate == allow_pred);
            let no_allow_in_steps = !steps.iter().any(|s| s.derived_fact.predicate == allow_pred);
            no_allow_in_facts && no_allow_in_steps
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbol_from_str;

    #[test]
    fn test_verify_empty_trace_deny() {
        let facts = vec![Fact::new(
            symbol_from_str("user"),
            vec![Term::Const(symbol_from_str("alice"))],
        )];
        let rules = vec![];
        let trace = AuthorizationTrace {
            request: AuthorizationRequest {
                app_id: None,
                service: None,
                action: Some(symbol_from_str("read")),
                features: vec![],
                user_id: Some(symbol_from_str("alice")),
                now: 1000,
            },
            steps: vec![],
            conclusion: Conclusion::Deny,
        };

        assert!(verify_trace(&facts, &rules, &trace));
    }

    #[test]
    fn test_verify_invalid_allow_conclusion() {
        let facts = vec![];
        let rules = vec![];
        // Claim allow but no allow fact exists
        let trace = AuthorizationTrace {
            request: AuthorizationRequest {
                app_id: None,
                service: None,
                action: Some(symbol_from_str("read")),
                features: vec![],
                user_id: None,
                now: 1000,
            },
            steps: vec![],
            conclusion: Conclusion::Allow { policy_rule_id: 1 },
        };

        assert!(!verify_trace(&facts, &rules, &trace));
    }

    #[test]
    fn test_verify_invalid_fact_index() {
        let rules = vec![Rule {
            id: 1,
            head: Atom {
                predicate: symbol_from_str("allow"),
                terms: vec![],
            },
            body: vec![Atom {
                predicate: symbol_from_str("app"),
                terms: vec![Term::Var(0)],
            }],
            checks: vec![],
        }];

        let trace = AuthorizationTrace {
            request: AuthorizationRequest {
                app_id: None,
                service: None,
                action: None,
                features: vec![],
                user_id: None,
                now: 1000,
            },
            steps: vec![DerivationStep {
                rule_id: 1,
                substitution: Substitution::empty()
                    .extend(0, Term::Const(symbol_from_str("myapp")))
                    .unwrap(),
                body_fact_indices: vec![999], // invalid index
                derived_fact: Fact::new(symbol_from_str("allow"), vec![]),
            }],
            conclusion: Conclusion::Allow { policy_rule_id: 1 },
        };

        assert!(!verify_trace(&[], &rules, &trace));
    }
}
