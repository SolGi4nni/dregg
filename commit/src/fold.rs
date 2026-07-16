//! FoldDelta: represents an attenuation step in the dregg token system.
//!
//! Attenuation is the process of narrowing a token's capabilities. A FoldDelta
//! captures the difference between two states: what was removed, what checks
//! were added, and a witness that everything else survived unchanged.
//!
//! The key invariant: a valid attenuation can only REMOVE facts or ADD restriction
//! checks. It cannot add new capabilities.

use serde::{Deserialize, Serialize};

use crate::fact::Fact;
use crate::field::FieldElement;
use crate::hash::hash_leaf;
use crate::merkle::{MerkleProof, MerkleTree, SurvivalWitness};
use crate::state::{RULE_PREFIX, TokenState};

/// What a verifier is willing to accept as an added *restriction* check.
///
/// A `FoldDelta`'s `added_checks` are facts that get INSERTED into the new state.
/// Insertion is only a narrowing if the inserted fact is a rule-prefixed check
/// rather than a capability — an "added check" of `owns(alice, everything)` WIDENS
/// the token. A predicate is a BLAKE3 hash (`FieldElement::from_symbol`), so it
/// cannot be reversed; the verifier must therefore supply the rule names it is
/// willing to admit, and we re-derive the expected predicate hash from each.
///
/// Finding a `Fact` that is not a rule but whose predicate equals
/// `from_symbol("rule:<name>")` requires a BLAKE3 preimage collision.
pub enum CheckPolicy<'a> {
    /// The verifier has no rule allowlist, so it cannot tell a restriction from a
    /// capability. Fail-closed: any delta that adds checks is REFUSED. Removal-only
    /// deltas still verify (removal is unconditionally a narrowing).
    NoAddedChecks,
    /// Accept an added check only if its predicate is the hash of `rule:<name>`
    /// (or `rule:<name>_<index>`, the form emitted by `initial_attenuation_delta`)
    /// for some `<name>` in this allowlist.
    RuleNames(&'a [&'a str]),
}

impl CheckPolicy<'_> {
    /// Whether `predicate`, appearing at `index` in `added_checks`, is an admissible
    /// restriction under this policy.
    fn admits(&self, predicate: FieldElement, index: usize) -> bool {
        match self {
            CheckPolicy::NoAddedChecks => false,
            CheckPolicy::RuleNames(names) => names.iter().any(|name| {
                predicate == FieldElement::from_symbol(&format!("{RULE_PREFIX}{name}"))
                    || predicate
                        == FieldElement::from_symbol(&format!("{RULE_PREFIX}{name}_{index}"))
            }),
        }
    }
}

/// A fold delta: the difference between two token states during attenuation.
///
/// This captures:
/// - Which facts were removed (narrowing permissions).
/// - Which restriction checks were added (new constraints).
/// - A witness that all other facts survived unchanged.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct FoldDelta {
    /// The root of the state before attenuation.
    pub old_root: [u8; 32],
    /// The root of the state after attenuation.
    pub new_root: [u8; 32],
    /// Facts that were removed (with their membership proofs in the old tree).
    pub removed: Vec<(Fact, MerkleProof)>,
    /// New restriction checks added (facts with rule-prefixed predicates).
    pub added_checks: Vec<Fact>,
    /// Witness that all non-removed facts survived.
    pub surviving_proof: SurvivalWitness,
}

/// The result of attempting to apply a fold delta.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FoldVerification {
    /// The delta is valid: it represents a legitimate attenuation.
    Valid,
    /// A removed fact's membership proof doesn't verify against old_root.
    InvalidRemovalProof { index: usize },
    /// An added check is not a valid restriction (not rule-prefixed).
    InvalidCheck { index: usize },
    /// The survival witness doesn't check out.
    InvalidSurvivalWitness,
    /// `old_root` is not the root of the old state the verifier supplied. The delta
    /// describes a transition out of some OTHER state than the one being folded.
    OldRootMismatch,
    /// The new root doesn't match what we compute. Recomputing
    /// `old_state - removed + added_checks` did not yield `new_root`: the claimed
    /// post-state is not the one these operations produce.
    RootMismatch,
    /// The delta is empty (no changes).
    EmptyDelta,
}

impl FoldDelta {
    /// Create a fold delta by computing the difference between two states.
    ///
    /// `old_state`: the state before attenuation.
    /// `new_state`: the state after attenuation.
    /// `removed_facts`: facts that were explicitly removed.
    /// `added_checks`: restriction checks that were added.
    ///
    /// Returns None if the states don't represent a valid attenuation.
    pub fn compute(
        old_state: &mut TokenState,
        new_state: &mut TokenState,
        removed_facts: Vec<Fact>,
        added_checks: Vec<Fact>,
    ) -> Option<Self> {
        let old_root = old_state.root();
        let new_root = new_state.root();

        // Get membership proofs for each removed fact in the old tree.
        let mut removed_with_proofs = Vec::with_capacity(removed_facts.len());
        for fact in &removed_facts {
            let proof = old_state.membership_proof(fact)?;
            removed_with_proofs.push((*fact, proof));
        }

        // Compute the survival witness.
        let removed_hashes: Vec<[u8; 32]> = removed_facts
            .iter()
            .map(|f| hash_leaf(&f.to_bytes()))
            .collect();

        let surviving_proof = old_state
            .factset_mut()
            .tree_mut()
            .survival_witness(new_state.factset_mut().tree_mut(), &removed_hashes);

        Some(Self {
            old_root,
            new_root,
            removed: removed_with_proofs,
            added_checks,
            surviving_proof,
        })
    }

    /// Verify that this fold delta represents a valid attenuation OUT OF `old_state`.
    ///
    /// `old_state` is the verifier's own copy of the pre-state — it is what makes this
    /// check sound. Every root in a `FoldDelta` is a field the delta's author chose;
    /// comparing those fields to each other proves nothing. Binding them to a state the
    /// verifier independently holds is what turns them into evidence.
    ///
    /// Checks:
    /// 1. `old_root` is the actual root of `old_state` (`OldRootMismatch` otherwise).
    /// 2. Each removed fact was genuinely in the old state (membership proofs verify).
    /// 3. Each added check is an admissible restriction under `policy` — NOT a
    ///    capability smuggled in as a "check".
    /// 4. The survival witness is well-formed.
    /// 5. **`new_root` is recomputed** from `old_state - removed + added_checks` and
    ///    must equal the claimed `new_root` (`RootMismatch` otherwise).
    ///
    /// Check 5 is the load-bearing one: without it `new_root` is unconstrained, and a
    /// delta claiming a post-state with MORE capabilities than the pre-state verifies.
    pub fn verify(&self, old_state: &TokenState, policy: &CheckPolicy<'_>) -> FoldVerification {
        // Must have at least one change.
        if self.removed.is_empty() && self.added_checks.is_empty() {
            return FoldVerification::EmptyDelta;
        }

        // Bind old_root to the state the verifier actually holds. Without this the
        // removal proofs below would only be checked against a root of the delta
        // author's choosing.
        if old_state.root_immutable() != self.old_root {
            return FoldVerification::OldRootMismatch;
        }

        // Verify each removed fact's proof against the old root.
        for (i, (fact, proof)) in self.removed.iter().enumerate() {
            let expected_leaf = hash_leaf(&fact.to_bytes());
            if proof.leaf_hash != expected_leaf {
                return FoldVerification::InvalidRemovalProof { index: i };
            }
            if !MerkleTree::verify_membership(&self.old_root, proof) {
                return FoldVerification::InvalidRemovalProof { index: i };
            }
        }

        // Added checks are INSERTED into the new state, so an added check that is not
        // a rule-prefixed restriction is a capability grant. Re-derive the expected
        // `rule:`-prefixed predicate hash from the verifier's allowlist.
        for (i, check) in self.added_checks.iter().enumerate() {
            if check.predicate.is_zero() || !policy.admits(check.predicate, i) {
                return FoldVerification::InvalidCheck { index: i };
            }
        }

        // Verify survival witness roots match.
        if self.surviving_proof.old_root != self.old_root {
            return FoldVerification::InvalidSurvivalWitness;
        }
        if self.surviving_proof.new_root != self.new_root {
            return FoldVerification::InvalidSurvivalWitness;
        }

        // The unchanged subtrees must be structurally well-formed: consistent
        // depth/path, in-range indices, no zero hash at a populated depth, and no
        // duplicate paths (claiming the same subtree twice).
        let mut seen_paths: std::collections::HashSet<&[u8]> = std::collections::HashSet::new();
        for subtree in &self.surviving_proof.unchanged_subtrees {
            // Path length must match the declared depth.
            if subtree.path.len() != subtree.depth {
                return FoldVerification::InvalidSurvivalWitness;
            }
            // Each path index must be valid (0..3 for 4-ary tree).
            for &idx in &subtree.path {
                if idx >= 4 {
                    return FoldVerification::InvalidSurvivalWitness;
                }
            }
            if subtree.hash == [0u8; 32] && subtree.depth > 0 {
                return FoldVerification::InvalidSurvivalWitness;
            }
            if !seen_paths.insert(subtree.path.as_slice()) {
                return FoldVerification::InvalidSurvivalWitness;
            }
        }

        // THE TOOTH: independently recompute the post-state root from the verifier's
        // own `old_state` and the delta's declared operations. This is what binds
        // `new_root` to `removed`/`added_checks` instead of letting the author name it.
        if self.reconstruct_new_state(old_state).is_none() {
            return FoldVerification::RootMismatch;
        }

        FoldVerification::Valid
    }

    /// Apply the fold delta and verify it in one step against `old_state`.
    /// Returns true if the delta is a valid narrowing out of that state.
    pub fn apply_and_verify(&self, old_state: &TokenState, policy: &CheckPolicy<'_>) -> bool {
        self.verify(old_state, policy) == FoldVerification::Valid
    }

    /// Get the number of facts removed.
    pub fn num_removed(&self) -> usize {
        self.removed.len()
    }

    /// Get the number of checks added.
    pub fn num_added_checks(&self) -> usize {
        self.added_checks.len()
    }

    /// Reconstruct the new state from the old state and this delta.
    /// This is useful for the verifier to check correctness.
    pub fn reconstruct_new_state(&self, old_state: &TokenState) -> Option<TokenState> {
        let mut new_state = TokenState::from_parts(old_state.all_facts(), vec![]);

        // Remove the removed facts.
        for (fact, _) in &self.removed {
            new_state.remove_fact(fact)?;
        }

        // Add the new checks.
        for check in &self.added_checks {
            new_state.add_rule_fact(*check);
        }

        // Verify the root matches.
        if new_state.root() == self.new_root {
            Some(new_state)
        } else {
            None
        }
    }
}

/// Builder for constructing fold deltas step by step.
pub struct FoldDeltaBuilder {
    old_state: TokenState,
    removed: Vec<Fact>,
    added_checks: Vec<Fact>,
}

impl FoldDeltaBuilder {
    /// Start building a fold delta from an initial state.
    pub fn new(old_state: TokenState) -> Self {
        Self {
            old_state,
            removed: Vec::new(),
            added_checks: Vec::new(),
        }
    }

    /// Mark a fact for removal (narrowing).
    pub fn remove_fact(mut self, fact: Fact) -> Self {
        self.removed.push(fact);
        self
    }

    /// Add a restriction check.
    pub fn add_check(mut self, check: Fact) -> Self {
        self.added_checks.push(check);
        self
    }

    /// Add a restriction check by name and terms.
    pub fn add_named_check(mut self, rule_name: &str, terms: &[&str]) -> Self {
        let check = TokenState::make_rule(rule_name, terms);
        self.added_checks.push(check);
        self
    }

    /// Build the fold delta.
    /// Returns None if the delta is invalid (e.g., removing a fact not in the state).
    pub fn build(self) -> Option<FoldDelta> {
        let mut old_state = self.old_state.clone();
        let mut new_state = self.old_state;

        // Apply removals.
        for fact in &self.removed {
            new_state.remove_fact(fact)?;
        }

        // Apply additions.
        for check in &self.added_checks {
            new_state.add_rule_fact(*check);
        }

        FoldDelta::compute(
            &mut old_state,
            &mut new_state,
            self.removed,
            self.added_checks,
        )
    }
}

/// Verify a chain of fold deltas (a sequence of attenuations) starting from `genesis`.
///
/// `genesis` is the verifier's own copy of the pre-state of `deltas[0]`. The chain is
/// walked forward: each delta is verified against the state RECONSTRUCTED from the
/// previous one, so every intermediate root is recomputed rather than taken on the
/// author's word. Chain continuity falls out of that reconstruction — a delta whose
/// `old_root` does not match the reconstructed predecessor fails `OldRootMismatch`.
pub fn verify_fold_chain(
    genesis: &TokenState,
    deltas: &[FoldDelta],
    policy: &CheckPolicy<'_>,
) -> bool {
    let mut current = genesis.clone();

    for delta in deltas {
        if !delta.apply_and_verify(&current, policy) {
            return false;
        }
        // Advance to the state the delta actually produces. `verify` already proved
        // this reconstructs to `delta.new_root`.
        match delta.reconstruct_new_state(&current) {
            Some(next) => current = next,
            None => return false,
        }
    }

    true
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The rule names the tests below legitimately attenuate with.
    const TEST_RULES: &[&str] = &["max_reads", "expire_at"];

    fn policy() -> CheckPolicy<'static> {
        CheckPolicy::RuleNames(TEST_RULES)
    }

    fn sample_state() -> TokenState {
        let mut state = TokenState::new();
        state.add_fact(Fact::from_symbols("owns", &["alice", "file1"]));
        state.add_fact(Fact::from_symbols("owns", &["alice", "file2"]));
        state.add_fact(Fact::from_symbols("owns", &["alice", "file3"]));
        state.add_fact(Fact::from_symbols("can_read", &["alice", "file1"]));
        state.add_fact(Fact::from_symbols("can_read", &["alice", "file2"]));
        state.add_fact(Fact::from_symbols("can_read", &["alice", "file3"]));
        state
    }

    #[test]
    fn fold_delta_removal_only() {
        let old_state = sample_state();
        let fact_to_remove = Fact::from_symbols("owns", &["alice", "file3"]);

        let delta = FoldDeltaBuilder::new(old_state.clone())
            .remove_fact(fact_to_remove)
            .build()
            .unwrap();

        assert_eq!(delta.num_removed(), 1);
        assert_eq!(delta.num_added_checks(), 0);
        assert!(delta.apply_and_verify(&old_state, &policy()));
    }

    #[test]
    fn fold_delta_with_added_check() {
        let old_state = sample_state();
        let fact_to_remove = Fact::from_symbols("can_read", &["alice", "file3"]);

        let delta = FoldDeltaBuilder::new(old_state.clone())
            .remove_fact(fact_to_remove)
            .add_named_check("max_reads", &["2"])
            .build()
            .unwrap();

        assert_eq!(delta.num_removed(), 1);
        assert_eq!(delta.num_added_checks(), 1);
        assert!(delta.apply_and_verify(&old_state, &policy()));
    }

    #[test]
    fn fold_delta_multiple_removals() {
        let old_state = sample_state();
        let r1 = Fact::from_symbols("owns", &["alice", "file2"]);
        let r2 = Fact::from_symbols("owns", &["alice", "file3"]);
        let r3 = Fact::from_symbols("can_read", &["alice", "file2"]);
        let r4 = Fact::from_symbols("can_read", &["alice", "file3"]);

        let delta = FoldDeltaBuilder::new(old_state.clone())
            .remove_fact(r1)
            .remove_fact(r2)
            .remove_fact(r3)
            .remove_fact(r4)
            .build()
            .unwrap();

        assert_eq!(delta.num_removed(), 4);
        assert!(delta.apply_and_verify(&old_state, &policy()));
    }

    #[test]
    fn fold_delta_removing_absent_fact_fails() {
        let old_state = sample_state();
        let absent = Fact::from_symbols("nonexistent", &["x"]);

        let result = FoldDeltaBuilder::new(old_state).remove_fact(absent).build();

        assert!(result.is_none());
    }

    #[test]
    fn fold_delta_reconstruct_new_state() {
        let old_state = sample_state();
        let fact_to_remove = Fact::from_symbols("owns", &["alice", "file2"]);

        let delta = FoldDeltaBuilder::new(old_state.clone())
            .remove_fact(fact_to_remove)
            .build()
            .unwrap();

        let reconstructed = delta.reconstruct_new_state(&old_state).unwrap();
        assert!(!reconstructed.contains(&fact_to_remove));
        assert!(reconstructed.contains(&Fact::from_symbols("owns", &["alice", "file1"])));
    }

    #[test]
    fn fold_chain_valid() {
        let state0 = sample_state();
        let r1 = Fact::from_symbols("owns", &["alice", "file3"]);
        let r2 = Fact::from_symbols("can_read", &["alice", "file3"]);

        // First attenuation: remove file3 ownership.
        let delta1 = FoldDeltaBuilder::new(state0.clone())
            .remove_fact(r1)
            .build()
            .unwrap();

        // Build state1 from delta1.
        let state1 = delta1.reconstruct_new_state(&state0).unwrap();

        // Second attenuation: remove file3 read access.
        let delta2 = FoldDeltaBuilder::new(state1)
            .remove_fact(r2)
            .build()
            .unwrap();

        assert!(verify_fold_chain(&state0, &[delta1, delta2], &policy()));
    }

    #[test]
    fn fold_chain_broken_continuity() {
        let state0 = sample_state();
        let state0_copy = sample_state();
        let r1 = Fact::from_symbols("owns", &["alice", "file3"]);

        let delta1 = FoldDeltaBuilder::new(state0.clone())
            .remove_fact(r1)
            .build()
            .unwrap();

        // Create a second delta that doesn't chain from delta1.
        let r2 = Fact::from_symbols("owns", &["alice", "file2"]);
        let delta2 = FoldDeltaBuilder::new(state0)
            .remove_fact(r2)
            .build()
            .unwrap();

        // These don't chain correctly.
        assert!(!verify_fold_chain(
            &state0_copy,
            &[delta1, delta2],
            &policy()
        ));
    }

    #[test]
    fn empty_fold_chain_is_valid() {
        assert!(verify_fold_chain(&sample_state(), &[], &policy()));
    }

    #[test]
    fn fold_delta_check_only() {
        let old_state = sample_state();

        let delta = FoldDeltaBuilder::new(old_state.clone())
            .add_named_check("expire_at", &["2025-01-01"])
            .build()
            .unwrap();

        assert_eq!(delta.num_removed(), 0);
        assert_eq!(delta.num_added_checks(), 1);
        assert!(delta.apply_and_verify(&old_state, &policy()));
    }

    #[test]
    fn fold_delta_verify_tampered_proof() {
        let old_state = sample_state();
        let fact_to_remove = Fact::from_symbols("owns", &["alice", "file3"]);

        let mut delta = FoldDeltaBuilder::new(old_state.clone())
            .remove_fact(fact_to_remove)
            .build()
            .unwrap();

        // Tamper with the proof.
        if let Some((_, proof)) = delta.removed.first_mut() {
            proof.leaf_hash = [0xDE; 32];
        }

        assert!(!delta.apply_and_verify(&old_state, &policy()));
        assert_eq!(
            delta.verify(&old_state, &policy()),
            FoldVerification::InvalidRemovalProof { index: 0 }
        );
    }

    #[test]
    fn fold_delta_verify_tampered_root() {
        let old_state = sample_state();
        let fact_to_remove = Fact::from_symbols("owns", &["alice", "file1"]);

        let mut delta = FoldDeltaBuilder::new(old_state.clone())
            .remove_fact(fact_to_remove)
            .build()
            .unwrap();

        // Tamper with the old root.
        delta.old_root = [0xFF; 32];

        assert!(!delta.apply_and_verify(&old_state, &policy()));
    }

    /// THE FORGERY. Every root in a `FoldDelta` is a field its author chose, so
    /// checking `surviving_proof.new_root == self.new_root` compares two fields on
    /// the SAME attacker-supplied struct and proves nothing. An author could name a
    /// `new_root` belonging to a state with MORE capabilities than the old one and
    /// the delta verified — attenuation that ESCALATES. Only recomputing the root
    /// from the verifier's own `old_state` catches this.
    #[test]
    fn forged_widening_delta_is_refused() {
        let old_state = sample_state();

        // The attacker's desired post-state: strictly MORE than the old state.
        let mut wider = sample_state();
        wider.add_fact(Fact::from_symbols("owns", &["alice", "the_whole_disk"]));
        let wider_root = wider.root();

        // A delta that claims to attenuate `old_state` but names `wider_root` as its
        // result. Every self-consistency check the old verifier performed still holds:
        // both survival-witness roots agree with the delta's roots, the added check has
        // a non-zero rule-prefixed predicate, and there are no subtrees to inspect.
        let forged = FoldDelta {
            old_root: old_state.root_immutable(),
            new_root: wider_root,
            removed: vec![],
            added_checks: vec![TokenState::make_rule("max_reads", &["2"])],
            surviving_proof: SurvivalWitness {
                old_root: old_state.root_immutable(),
                new_root: wider_root,
                unchanged_subtrees: vec![],
            },
        };

        assert_eq!(
            forged.verify(&old_state, &policy()),
            FoldVerification::RootMismatch,
            "a delta naming a post-state it did not produce must be refused"
        );
    }

    /// The second widening path: a raw capability fact smuggled in as an "added
    /// check". Such a delta is internally HONEST — its `new_root` really is the root
    /// of `old + capability` — so the root tooth cannot catch it. The rule-prefix
    /// policy is what must.
    #[test]
    fn capability_smuggled_as_added_check_is_refused() {
        let old_state = sample_state();
        let capability = Fact::from_symbols("owns", &["alice", "the_whole_disk"]);

        let delta = FoldDeltaBuilder::new(old_state.clone())
            .add_check(capability)
            .build()
            .unwrap();

        // Confirm the root tooth alone does NOT bite here: the delta is consistent.
        assert!(
            delta.reconstruct_new_state(&old_state).is_some(),
            "this forgery is root-consistent; only the check policy can refuse it"
        );
        assert_eq!(
            delta.verify(&old_state, &policy()),
            FoldVerification::InvalidCheck { index: 0 },
            "an added check that is not a rule-prefixed restriction must be refused"
        );
    }

    /// A well-formed rule that is simply not one the verifier admits.
    #[test]
    fn rule_outside_the_allowlist_is_refused() {
        let old_state = sample_state();

        let delta = FoldDeltaBuilder::new(old_state.clone())
            .add_named_check("grant_everything", &[])
            .build()
            .unwrap();

        assert_eq!(
            delta.verify(&old_state, &policy()),
            FoldVerification::InvalidCheck { index: 0 }
        );
    }

    /// A verifier with no allowlist cannot tell a restriction from a capability, so
    /// it must refuse added checks outright — but removal-only deltas still verify.
    #[test]
    fn no_added_checks_policy_is_fail_closed() {
        let old_state = sample_state();

        let removal_only = FoldDeltaBuilder::new(old_state.clone())
            .remove_fact(Fact::from_symbols("owns", &["alice", "file3"]))
            .build()
            .unwrap();
        assert!(removal_only.apply_and_verify(&old_state, &CheckPolicy::NoAddedChecks));

        let with_check = FoldDeltaBuilder::new(old_state.clone())
            .add_named_check("max_reads", &["2"])
            .build()
            .unwrap();
        assert_eq!(
            with_check.verify(&old_state, &CheckPolicy::NoAddedChecks),
            FoldVerification::InvalidCheck { index: 0 }
        );
    }

    /// A delta is evidence only about the state it was computed from. Presenting it
    /// against a different pre-state must be refused, not silently accepted.
    #[test]
    fn delta_verified_against_the_wrong_state_is_refused() {
        let old_state = sample_state();
        let delta = FoldDeltaBuilder::new(old_state.clone())
            .remove_fact(Fact::from_symbols("owns", &["alice", "file3"]))
            .build()
            .unwrap();

        let mut other = sample_state();
        other.add_fact(Fact::from_symbols("owns", &["bob", "file9"]));

        assert_eq!(
            delta.verify(&other, &policy()),
            FoldVerification::OldRootMismatch
        );
    }
}
