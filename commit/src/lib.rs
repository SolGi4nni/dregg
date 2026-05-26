//! `dregg-commit`: Core commitment scheme for the dregg ZK token system.
//!
//! This crate provides the foundational data structures for the dregg token system:
//!
//! - **Field elements**: 253-bit values representing facts in the algebraic domain.
//! - **Facts**: Fixed-arity tuples (predicate + up to 3 terms) encoded as field elements.
//! - **4-ary Poseidon Merkle tree**: Sparse Merkle tree with 4-way branching.
//! - **FactSet**: Ordered set of facts with Merkle commitment and proof generation.
//! - **StateCommitment**: Token state as a commitment to facts and rules.
//! - **FoldDelta**: Represents an attenuation step (narrowing of capabilities).
//! - **Symbol table**: Bidirectional mapping between strings and field elements.
//!
//! # Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────────┐
//! │                  TokenState                       │
//! │  ┌───────────────────────────────────────────┐  │
//! │  │              FactSet                       │  │
//! │  │  ┌─────────────────────────────────────┐  │  │
//! │  │  │        4-ary Merkle Tree            │  │  │
//! │  │  │  ┌───┐ ┌───┐ ┌───┐ ┌───┐          │  │  │
//! │  │  │  │ F │ │ F │ │ R │ │ R │  ...      │  │  │
//! │  │  │  └───┘ └───┘ └───┘ └───┘          │  │  │
//! │  │  │   facts        rules               │  │  │
//! │  │  └─────────────────────────────────────┘  │  │
//! │  └───────────────────────────────────────────┘  │
//! └─────────────────────────────────────────────────┘
//!                        │
//!                   FoldDelta
//!                        │
//!                        ▼
//! ┌─────────────────────────────────────────────────┐
//! │            Attenuated TokenState                  │
//! │         (fewer facts, more checks)               │
//! └─────────────────────────────────────────────────┘
//! ```
//!
//! # Hash Function
//!
//! Currently uses BLAKE3 as a placeholder for the algebraic Poseidon hash.
//! The tree structure and API are designed for drop-in replacement once
//! a concrete field (BN254, BLS12-381, etc.) is selected.

pub mod accumulator;
pub mod fact;
pub mod factset;
pub mod field;
pub mod fold;
pub mod hash;
pub mod merkle;
pub mod poseidon2_tree;
pub mod state;
pub mod symbol;
pub mod typed;

// Re-export primary types at crate root for convenience.
pub use accumulator::{AccumulatorWitness, BabyBear4, PolynomialAccumulator};
pub use fact::Fact;
pub use factset::FactSet;
pub use field::FieldElement;
pub use fold::{FoldDelta, FoldDeltaBuilder, FoldVerification, verify_fold_chain};
pub use hash::{HASH_ARITY, hash_leaf, hash_node};
pub use merkle::{MerkleProof, MerkleTree, NonMembershipProof, SurvivalWitness};
pub use poseidon2_tree::{
    Poseidon2MerkleProof, Poseidon2MerkleTree, commitment_to_field, hash_bytes_to_field,
};
pub use state::{StateCommitment, TokenState};
pub use symbol::SymbolTable;

#[cfg(test)]
mod integration_tests {
    use super::*;

    /// End-to-end test: create a token, attenuate it, verify the chain.
    #[test]
    fn full_attenuation_flow() {
        // Create a symbol table for readable names.
        let mut syms = SymbolTable::new();
        syms.intern("owns");
        syms.intern("can_read");
        syms.intern("can_write");
        syms.intern("alice");
        syms.intern("bob");
        syms.intern("secret.txt");
        syms.intern("public.txt");

        // Initial state: Alice owns two files and can read/write both.
        let mut state = TokenState::new();
        state.add_fact(Fact::from_symbols("owns", &["alice", "secret.txt"]));
        state.add_fact(Fact::from_symbols("owns", &["alice", "public.txt"]));
        state.add_fact(Fact::from_symbols("can_read", &["alice", "secret.txt"]));
        state.add_fact(Fact::from_symbols("can_read", &["alice", "public.txt"]));
        state.add_fact(Fact::from_symbols("can_write", &["alice", "secret.txt"]));
        state.add_fact(Fact::from_symbols("can_write", &["alice", "public.txt"]));

        let initial_root = state.root();

        // First attenuation: remove write access to secret.txt.
        let remove_write_secret = Fact::from_symbols("can_write", &["alice", "secret.txt"]);

        let delta1 = FoldDeltaBuilder::new(state.clone())
            .remove_fact(remove_write_secret)
            .add_named_check("no_write", &["secret.txt"])
            .build()
            .expect("delta1 should build");

        assert!(delta1.apply_and_verify(), "delta1 should verify");
        assert_eq!(delta1.old_root, initial_root);

        // Reconstruct state after first attenuation.
        let state1 = delta1.reconstruct_new_state(&state).unwrap();
        assert!(!state1.contains(&remove_write_secret));
        assert!(state1.contains(&Fact::from_symbols("can_read", &["alice", "secret.txt"])));

        // Second attenuation: remove all access to secret.txt.
        let remove_read_secret = Fact::from_symbols("can_read", &["alice", "secret.txt"]);
        let remove_own_secret = Fact::from_symbols("owns", &["alice", "secret.txt"]);

        let delta2 = FoldDeltaBuilder::new(state1.clone())
            .remove_fact(remove_read_secret)
            .remove_fact(remove_own_secret)
            .build()
            .expect("delta2 should build");

        assert!(delta2.apply_and_verify(), "delta2 should verify");

        // Final state should only have public.txt access.
        let final_state = delta2.reconstruct_new_state(&state1).unwrap();

        // Verify the chain.
        assert!(verify_fold_chain(&[delta1, delta2]));
        assert!(final_state.contains(&Fact::from_symbols("owns", &["alice", "public.txt"])));
        assert!(final_state.contains(&Fact::from_symbols("can_read", &["alice", "public.txt"])));
        assert!(final_state.contains(&Fact::from_symbols("can_write", &["alice", "public.txt"])));
        assert!(!final_state.contains(&Fact::from_symbols("owns", &["alice", "secret.txt"])));
    }

    /// Test: membership proofs survive across multiple operations.
    #[test]
    fn proofs_across_operations() {
        let mut fs = FactSet::new();
        let facts: Vec<Fact> = (0..20)
            .map(|i| Fact::unary(FieldElement::from_symbol("item"), FieldElement::from_u64(i)))
            .collect();

        for f in &facts {
            fs.insert(*f);
        }

        let root = fs.root();

        // All facts should have valid membership proofs.
        for f in &facts {
            let proof = fs.membership_proof(f).unwrap();
            assert!(
                FactSet::verify_membership(&root, f, &proof),
                "proof failed for item {}",
                f.terms[0]
            );
        }

        // Remove some facts and verify the rest still have valid proofs.
        for f in &facts[10..] {
            fs.remove(f);
        }

        let new_root = fs.root();
        assert_ne!(root, new_root);

        for f in &facts[..10] {
            let proof = fs.membership_proof(f).unwrap();
            assert!(FactSet::verify_membership(&new_root, f, &proof));
        }

        // Removed facts should not have membership proofs.
        for f in &facts[10..] {
            assert!(fs.membership_proof(f).is_none());
        }
    }

    /// Test: symbol table integration with facts.
    #[test]
    fn symbol_table_with_facts() {
        let mut syms = SymbolTable::new();

        let pred = syms.intern("likes");
        let t1 = syms.intern("alice");
        let t2 = syms.intern("chocolate");

        let fact = Fact::binary(pred, t1, t2);

        // Can resolve back.
        assert_eq!(syms.resolve(fact.predicate), Some("likes"));
        assert_eq!(syms.resolve(fact.terms[0]), Some("alice"));
        assert_eq!(syms.resolve(fact.terms[1]), Some("chocolate"));
    }

    /// Test: non-membership proofs for absent facts.
    #[test]
    fn non_membership_in_populated_set() {
        let mut fs = FactSet::new();
        fs.insert(Fact::from_symbols("a", &["1"]));
        fs.insert(Fact::from_symbols("c", &["3"]));
        fs.insert(Fact::from_symbols("e", &["5"]));

        let root = fs.root();
        let absent = Fact::from_symbols("b", &["2"]);
        let proof = fs.non_membership_proof(&absent).unwrap();
        assert!(FactSet::verify_non_membership(&root, &absent, &proof));
    }

    /// Test: large fact set performance sanity check.
    #[test]
    fn large_factset() {
        let mut fs = FactSet::new();
        let n = 100;

        for i in 0..n {
            let fact = Fact::binary(
                FieldElement::from_symbol("edge"),
                FieldElement::from_u64(i),
                FieldElement::from_u64(i + 1),
            );
            fs.insert(fact);
        }

        assert_eq!(fs.len(), n as usize);
        let root = fs.root();

        // Spot-check a few proofs.
        for i in [0u64, 25, 50, 75, 99] {
            let fact = Fact::binary(
                FieldElement::from_symbol("edge"),
                FieldElement::from_u64(i),
                FieldElement::from_u64(i + 1),
            );
            let proof = fs.membership_proof(&fact).unwrap();
            assert!(FactSet::verify_membership(&root, &fact, &proof));
        }
    }

    /// Test: state commitment is deterministic regardless of insertion order.
    #[test]
    fn state_commitment_order_independent() {
        let facts = vec![
            Fact::from_symbols("x", &["1"]),
            Fact::from_symbols("y", &["2"]),
            Fact::from_symbols("z", &["3"]),
        ];

        let mut s1 = TokenState::new();
        for f in &facts {
            s1.add_fact(*f);
        }

        let mut s2 = TokenState::new();
        for f in facts.iter().rev() {
            s2.add_fact(*f);
        }

        assert_eq!(s1.root(), s2.root());
    }

    /// Test: fold delta with only added checks (no removals).
    #[test]
    fn fold_add_checks_only() {
        let mut state = TokenState::new();
        state.add_fact(Fact::from_symbols("access", &["resource"]));

        let delta = FoldDeltaBuilder::new(state)
            .add_named_check("expires", &["tomorrow"])
            .build()
            .unwrap();

        assert!(delta.apply_and_verify());
        assert_eq!(delta.num_removed(), 0);
        assert_eq!(delta.num_added_checks(), 1);
    }

    /// Test: empty delta is rejected.
    #[test]
    fn empty_delta_rejected() {
        // Can't build an empty delta from the builder because it would have
        // old_root == new_root. Let's construct one manually.
        let delta = FoldDelta {
            old_root: [0; 32],
            new_root: [0; 32],
            removed: vec![],
            added_checks: vec![],
            surviving_proof: SurvivalWitness {
                old_root: [0; 32],
                new_root: [0; 32],
                unchanged_subtrees: vec![],
            },
        };
        assert_eq!(delta.verify(), FoldVerification::EmptyDelta);
    }
}
