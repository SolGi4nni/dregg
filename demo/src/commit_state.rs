//! Token state commitment using the REAL `dregg_commit` crate.
//!
//! This module bridges the demo's `token::Fact` (rich, human-readable facts)
//! with `dregg_commit::TokenState` (algebraic field-element-based Merkle commitment).
//!
//! The demo's authorization logic stays in `token.rs`, but we compute a REAL
//! Merkle commitment and fold delta using `dregg-commit` in parallel.

use dregg_commit::{
    Fact as CommitFact, FoldDelta as CommitFoldDelta, FoldVerification,
    TokenState as CommitTokenState,
};

use crate::token::{Fact, FactKind};

/// Convert a demo `Fact` into a `dregg_commit::Fact` (field-element-based).
///
/// Uses `Fact::from_symbols` which hashes the kind+resource+actions into
/// a predicate and terms via BLAKE3.
pub fn demo_fact_to_commit_fact(fact: &Fact) -> CommitFact {
    let kind_str = match fact.kind {
        FactKind::App => "app",
        FactKind::Service => "service",
        FactKind::Feature => "feature",
        FactKind::Organization => "organization",
        FactKind::User => "user",
    };

    if fact.actions.is_empty() {
        // Unary fact: predicate(resource)
        CommitFact::from_symbols(kind_str, &[&fact.resource])
    } else {
        // Binary fact: predicate(resource, actions)
        CommitFact::from_symbols(kind_str, &[&fact.resource, &fact.actions])
    }
}

/// Build a `dregg_commit::TokenState` from a slice of demo facts and rules.
pub fn build_commit_state(facts: &[Fact], rules: &[crate::token::Rule]) -> CommitTokenState {
    let mut state = CommitTokenState::new();

    // Add facts.
    for fact in facts {
        state.add_fact(demo_fact_to_commit_fact(fact));
    }

    // Add rules as rule-facts.
    for rule in rules {
        let rule_fact = CommitTokenState::make_rule(&rule.description, &[]);
        state.add_rule_fact(rule_fact);
    }

    state
}

/// Compute a real fold delta between two demo token states using `dregg-commit`.
///
/// Returns the `FoldDelta` and a bool indicating whether it verifies.
pub fn compute_real_fold_delta(
    old_facts: &[Fact],
    old_rules: &[crate::token::Rule],
    new_facts: &[Fact],
    new_rules: &[crate::token::Rule],
    removed_facts: &[Fact],
    added_checks: &[&str],
) -> Option<(CommitFoldDelta, bool)> {
    let mut old_state = build_commit_state(old_facts, old_rules);

    // Build the new state by starting from old and applying changes.
    let mut new_state = CommitTokenState::new();
    for fact in new_facts {
        new_state.add_fact(demo_fact_to_commit_fact(fact));
    }
    for rule in new_rules {
        let rule_fact = CommitTokenState::make_rule(&rule.description, &[]);
        new_state.add_rule_fact(rule_fact);
    }
    // Add the checks.
    for check_desc in added_checks {
        let check_fact = CommitTokenState::make_rule(check_desc, &[]);
        new_state.add_rule_fact(check_fact);
    }

    // Convert removed facts to commit facts.
    let removed_commit_facts: Vec<CommitFact> = removed_facts
        .iter()
        .map(|f| demo_fact_to_commit_fact(f))
        .collect();

    // Convert added checks to commit facts.
    let added_check_facts: Vec<CommitFact> = added_checks
        .iter()
        .map(|desc| CommitTokenState::make_rule(desc, &[]))
        .collect();

    // Compute the fold delta.
    let delta = dregg_commit::FoldDelta::compute(
        &mut old_state,
        &mut new_state,
        removed_commit_facts,
        added_check_facts,
    )?;

    let verification = delta.verify();
    let valid = verification == FoldVerification::Valid;

    Some((delta, valid))
}

/// Compute the Merkle root of a set of demo facts + rules using the real crate.
pub fn compute_merkle_root(facts: &[Fact], rules: &[crate::token::Rule]) -> [u8; 32] {
    let mut state = build_commit_state(facts, rules);
    state.root()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::token::{Fact, Rule};

    #[test]
    fn test_build_commit_state() {
        let facts = vec![
            Fact::app("frontend", "rw"),
            Fact::service("http", "rw"),
            Fact::feature("ai-assist"),
        ];
        let rules = vec![Rule::allow_app(), Rule::deny_default()];
        let mut state = build_commit_state(&facts, &rules);

        // Should have 3 facts + 2 rules = 5 items.
        assert_eq!(state.len(), 5);
        assert_ne!(state.root(), [0u8; 32]);
    }

    #[test]
    fn test_merkle_root_deterministic() {
        let facts = vec![Fact::app("frontend", "rw"), Fact::app("backend", "rw")];
        let rules = vec![Rule::allow_app()];

        let root1 = compute_merkle_root(&facts, &rules);
        let root2 = compute_merkle_root(&facts, &rules);
        assert_eq!(root1, root2);
    }

    #[test]
    fn test_fold_delta_computation() {
        let old_facts = vec![
            Fact::app("frontend", "rw"),
            Fact::app("backend", "rw"),
            Fact::service("http", "rw"),
        ];
        let rules = vec![Rule::allow_app(), Rule::deny_default()];
        let removed = vec![Fact::app("backend", "rw")];
        let new_facts = vec![Fact::app("frontend", "rw"), Fact::service("http", "rw")];
        let checks = vec!["read_only"];

        let result =
            compute_real_fold_delta(&old_facts, &rules, &new_facts, &rules, &removed, &checks);

        assert!(result.is_some());
        let (delta, valid) = result.unwrap();
        assert!(valid, "fold delta should verify");
        assert_eq!(delta.num_removed(), 1);
        assert_eq!(delta.num_added_checks(), 1);
    }
}
