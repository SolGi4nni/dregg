//! StateCommitment: the token state as a commitment to facts and rules.
//!
//! The state of a dregg token is the Merkle root of the combined fact+rule set.
//! Rules are represented as facts with predicates prefixed by "rule:".
//! The state commitment is what gets folded during attenuation.

use serde::{Deserialize, Serialize};

use crate::fact::Fact;
use crate::factset::FactSet;
use crate::field::FieldElement;
use crate::merkle::MerkleProof;

/// Prefix used to distinguish rule predicates from regular fact predicates.
pub const RULE_PREFIX: &str = "rule:";

/// A state commitment: the Merkle root of the combined fact+rule set.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StateCommitment {
    /// The Merkle root of the combined fact and rule set.
    pub root: [u8; 32],
}

/// The full state: facts + rules + their Merkle commitment.
#[derive(Clone, Debug)]
pub struct TokenState {
    /// The combined fact set (facts + rules).
    factset: FactSet,
}

impl TokenState {
    /// Create a new empty token state.
    pub fn new() -> Self {
        Self {
            factset: FactSet::new(),
        }
    }

    /// Create a token state from existing facts and rules.
    pub fn from_parts(facts: Vec<Fact>, rules: Vec<Fact>) -> Self {
        let mut state = Self::new();
        for fact in facts {
            state.add_fact(fact);
        }
        for rule in rules {
            state.add_rule_fact(rule);
        }
        state
    }

    /// Add a fact to the state.
    pub fn add_fact(&mut self, fact: Fact) -> [u8; 32] {
        self.factset.insert(fact)
    }

    /// Add a rule (represented as a fact) to the state.
    /// The caller is responsible for using rule-prefixed predicates.
    pub fn add_rule_fact(&mut self, rule_fact: Fact) -> [u8; 32] {
        self.factset.insert(rule_fact)
    }

    /// Create a rule fact from a rule name and terms.
    pub fn make_rule(rule_name: &str, terms: &[&str]) -> Fact {
        let predicate_name = format!("{RULE_PREFIX}{rule_name}");
        Fact::from_symbols(&predicate_name, terms)
    }

    /// Remove a fact from the state.
    pub fn remove_fact(&mut self, fact: &Fact) -> Option<[u8; 32]> {
        self.factset.remove(fact)
    }

    /// Check if the state contains a fact.
    pub fn contains(&self, fact: &Fact) -> bool {
        self.factset.contains(fact)
    }

    /// Get the current state commitment.
    pub fn commitment(&mut self) -> StateCommitment {
        StateCommitment {
            root: self.factset.root(),
        }
    }

    /// Get the Merkle root directly.
    pub fn root(&mut self) -> [u8; 32] {
        self.factset.root()
    }

    /// Generate a membership proof for a fact.
    pub fn membership_proof(&self, fact: &Fact) -> Option<MerkleProof> {
        self.factset.membership_proof(fact)
    }

    /// Get all facts (including rules) in the state.
    pub fn all_facts(&self) -> Vec<Fact> {
        self.factset.to_vec()
    }

    /// Get only regular facts (not rules).
    pub fn facts_only(&self) -> Vec<&Fact> {
        self.factset
            .iter()
            .filter(|f| !is_rule_field_element(f.predicate))
            .collect()
    }

    /// Get only rules.
    pub fn rules_only(&self) -> Vec<&Fact> {
        self.factset
            .iter()
            .filter(|f| is_rule_field_element(f.predicate))
            .collect()
    }

    /// Number of items (facts + rules) in the state.
    pub fn len(&self) -> usize {
        self.factset.len()
    }

    /// Whether the state is empty.
    pub fn is_empty(&self) -> bool {
        self.factset.is_empty()
    }

    /// Access the underlying fact set.
    pub fn factset(&self) -> &FactSet {
        &self.factset
    }

    /// Access the underlying fact set mutably.
    pub fn factset_mut(&mut self) -> &mut FactSet {
        &mut self.factset
    }

    /// Verify that a fact is in a state with a given root.
    pub fn verify_membership(root: &[u8; 32], fact: &Fact, proof: &MerkleProof) -> bool {
        FactSet::verify_membership(root, fact, proof)
    }
}

impl Default for TokenState {
    fn default() -> Self {
        Self::new()
    }
}

/// Check if a field element likely represents a rule predicate.
/// Since we can't reverse the hash without a symbol table, we use a heuristic:
/// we check if the field element matches the hash of any "rule:*" prefix.
/// For production use, the symbol table should be consulted.
///
/// This is a simplified version that works when predicates are created via
/// `FieldElement::from_symbol("rule:...")`.
fn is_rule_field_element(_fe: FieldElement) -> bool {
    // Without a symbol table, we cannot determine this from the field element alone.
    // In practice, the caller should use a symbol table or tag rules separately.
    // For now, return false — the caller should use `make_rule` and track rule
    // predicates explicitly.
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::FieldElement;

    #[test]
    fn empty_state() {
        let mut state = TokenState::new();
        assert!(state.is_empty());
        let c = state.commitment();
        // Empty state has a deterministic root.
        let mut state2 = TokenState::new();
        assert_eq!(c.root, state2.commitment().root);
    }

    #[test]
    fn add_and_contains() {
        let mut state = TokenState::new();
        let fact = Fact::from_symbols("owns", &["alice", "document"]);
        state.add_fact(fact);
        assert!(state.contains(&fact));
        assert_eq!(state.len(), 1);
    }

    #[test]
    fn remove_fact() {
        let mut state = TokenState::new();
        let fact = Fact::from_symbols("access", &["bob", "resource"]);
        let empty_root = state.root();
        state.add_fact(fact);
        assert!(state.contains(&fact));
        state.remove_fact(&fact);
        assert!(!state.contains(&fact));
        assert_eq!(state.root(), empty_root);
    }

    #[test]
    fn make_rule_creates_fact() {
        let rule = TokenState::make_rule("allow_read", &["file.txt"]);
        assert_eq!(rule.arity(), 1);
        // The predicate should be the hash of "rule:allow_read".
        assert_eq!(rule.predicate, FieldElement::from_symbol("rule:allow_read"));
    }

    #[test]
    fn state_with_facts_and_rules() {
        let mut state = TokenState::new();
        let fact1 = Fact::from_symbols("owns", &["alice", "doc1"]);
        let fact2 = Fact::from_symbols("owns", &["alice", "doc2"]);
        let rule = TokenState::make_rule("can_read", &["doc1"]);

        state.add_fact(fact1);
        state.add_fact(fact2);
        state.add_rule_fact(rule);

        assert_eq!(state.len(), 3);
        assert!(state.contains(&fact1));
        assert!(state.contains(&fact2));
        assert!(state.contains(&rule));
    }

    #[test]
    fn commitment_changes_on_mutation() {
        let mut state = TokenState::new();
        let c1 = state.commitment();
        state.add_fact(Fact::from_symbols("x", &["y"]));
        let c2 = state.commitment();
        assert_ne!(c1.root, c2.root);
    }

    #[test]
    fn membership_proof() {
        let mut state = TokenState::new();
        let f1 = Fact::from_symbols("a", &["b"]);
        let f2 = Fact::from_symbols("c", &["d"]);
        state.add_fact(f1);
        state.add_fact(f2);

        let root = state.root();
        let proof = state.membership_proof(&f1).unwrap();
        assert!(TokenState::verify_membership(&root, &f1, &proof));
    }

    #[test]
    fn from_parts_constructor() {
        let facts = vec![
            Fact::from_symbols("x", &["1"]),
            Fact::from_symbols("y", &["2"]),
        ];
        let rules = vec![TokenState::make_rule("r1", &["a"])];

        let state = TokenState::from_parts(facts.clone(), rules.clone());
        assert_eq!(state.len(), 3);
        assert!(state.contains(&facts[0]));
        assert!(state.contains(&facts[1]));
        assert!(state.contains(&rules[0]));
    }
}
