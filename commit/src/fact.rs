//! Facts: fixed-arity tuples of field elements.
//!
//! A Fact is a predicate + up to 3 terms. Unused term slots are zero.
//! This is the fundamental unit of knowledge in the dregg system.

use serde::{Deserialize, Serialize};

use crate::field::FieldElement;
use crate::hash::hash_leaf;

/// A fact: predicate + up to 3 terms (unused slots are `FieldElement::ZERO`).
///
/// Facts are ordered: first by predicate, then by terms lexicographically.
/// This ordering defines their position in the Merkle tree.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Serialize, Deserialize)]
pub struct Fact {
    /// The predicate (relation name, hashed to field element).
    pub predicate: FieldElement,
    /// Up to 3 terms. Unused positions are `FieldElement::ZERO`.
    pub terms: [FieldElement; 3],
}

impl Fact {
    /// Create a nullary fact (predicate with no arguments).
    pub fn nullary(predicate: FieldElement) -> Self {
        Self {
            predicate,
            terms: [FieldElement::ZERO; 3],
        }
    }

    /// Create a unary fact (predicate with 1 argument).
    pub fn unary(predicate: FieldElement, term: FieldElement) -> Self {
        Self {
            predicate,
            terms: [term, FieldElement::ZERO, FieldElement::ZERO],
        }
    }

    /// Create a binary fact (predicate with 2 arguments).
    pub fn binary(predicate: FieldElement, t1: FieldElement, t2: FieldElement) -> Self {
        Self {
            predicate,
            terms: [t1, t2, FieldElement::ZERO],
        }
    }

    /// Create a ternary fact (predicate with 3 arguments).
    pub fn ternary(
        predicate: FieldElement,
        t1: FieldElement,
        t2: FieldElement,
        t3: FieldElement,
    ) -> Self {
        Self {
            predicate,
            terms: [t1, t2, t3],
        }
    }

    /// Create a fact from string symbols (hashes predicate and all terms).
    pub fn from_symbols(predicate: &str, terms: &[&str]) -> Self {
        let pred_fe = FieldElement::from_symbol(predicate);
        let mut term_fes = [FieldElement::ZERO; 3];
        for (i, t) in terms.iter().take(3).enumerate() {
            term_fes[i] = FieldElement::from_symbol(t);
        }
        Self {
            predicate: pred_fe,
            terms: term_fes,
        }
    }

    /// Create a fact with integer terms.
    pub fn with_ints(predicate: &str, terms: &[i64]) -> Self {
        let pred_fe = FieldElement::from_symbol(predicate);
        let mut term_fes = [FieldElement::ZERO; 3];
        for (i, &t) in terms.iter().take(3).enumerate() {
            term_fes[i] = FieldElement::from_i64(t);
        }
        Self {
            predicate: pred_fe,
            terms: term_fes,
        }
    }

    /// Serialize this fact to 128 bytes (4 × 32 bytes).
    pub fn to_bytes(&self) -> [u8; 128] {
        let mut out = [0u8; 128];
        out[0..32].copy_from_slice(&self.predicate.0);
        out[32..64].copy_from_slice(&self.terms[0].0);
        out[64..96].copy_from_slice(&self.terms[1].0);
        out[96..128].copy_from_slice(&self.terms[2].0);
        out
    }

    /// Deserialize a fact from 128 bytes.
    pub fn from_bytes(bytes: &[u8; 128]) -> Self {
        let mut predicate = [0u8; 32];
        let mut t0 = [0u8; 32];
        let mut t1 = [0u8; 32];
        let mut t2 = [0u8; 32];
        predicate.copy_from_slice(&bytes[0..32]);
        t0.copy_from_slice(&bytes[32..64]);
        t1.copy_from_slice(&bytes[64..96]);
        t2.copy_from_slice(&bytes[96..128]);
        Self {
            predicate: FieldElement(predicate),
            terms: [FieldElement(t0), FieldElement(t1), FieldElement(t2)],
        }
    }

    /// Compute the leaf hash of this fact using the domain-separated leaf hash.
    ///
    /// Uses `hash::hash_leaf()` (domain: "dregg-commit leaf v1") to ensure
    /// consistency with the Merkle tree's leaf hashing and prevent
    /// domain-confusion attacks between leaf and node hashes.
    pub fn leaf_hash(&self) -> [u8; 32] {
        let bytes = self.to_bytes();
        hash_leaf(&bytes)
    }

    /// The arity of this fact (number of non-zero terms).
    pub fn arity(&self) -> usize {
        self.terms.iter().filter(|t| !t.is_zero()).count()
    }

    /// Whether this fact represents a rule (predicate starts with special prefix).
    /// Rules use predicates hashed from strings starting with "rule:".
    pub fn is_rule_predicate(predicate_name: &str) -> bool {
        predicate_name.starts_with("rule:")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fact_roundtrip_bytes() {
        let fact = Fact::ternary(
            FieldElement::from_symbol("parent"),
            FieldElement::from_symbol("alice"),
            FieldElement::from_symbol("bob"),
            FieldElement::from_u64(2024),
        );
        let bytes = fact.to_bytes();
        let recovered = Fact::from_bytes(&bytes);
        assert_eq!(fact, recovered);
    }

    #[test]
    fn fact_arity() {
        assert_eq!(Fact::nullary(FieldElement::from_symbol("alive")).arity(), 0);
        assert_eq!(
            Fact::unary(
                FieldElement::from_symbol("exists"),
                FieldElement::from_u64(1)
            )
            .arity(),
            1
        );
        assert_eq!(
            Fact::binary(
                FieldElement::from_symbol("edge"),
                FieldElement::from_u64(1),
                FieldElement::from_u64(2)
            )
            .arity(),
            2
        );
        assert_eq!(
            Fact::ternary(
                FieldElement::from_symbol("triple"),
                FieldElement::from_u64(1),
                FieldElement::from_u64(2),
                FieldElement::from_u64(3)
            )
            .arity(),
            3
        );
    }

    #[test]
    fn fact_from_symbols() {
        let f1 = Fact::from_symbols("parent", &["alice", "bob"]);
        let f2 = Fact::binary(
            FieldElement::from_symbol("parent"),
            FieldElement::from_symbol("alice"),
            FieldElement::from_symbol("bob"),
        );
        assert_eq!(f1, f2);
    }

    #[test]
    fn fact_ordering() {
        let f1 = Fact::from_symbols("aaa", &["x"]);
        let f2 = Fact::from_symbols("zzz", &["x"]);
        // Should have a defined ordering (by predicate hash).
        assert_ne!(f1, f2);
        // The actual order depends on the hash values, but it must be consistent.
        let order1 = f1.cmp(&f2);
        let order2 = f1.cmp(&f2);
        assert_eq!(order1, order2);
    }

    #[test]
    fn leaf_hash_deterministic() {
        let fact = Fact::from_symbols("owns", &["alice", "file.txt"]);
        let h1 = fact.leaf_hash();
        let h2 = fact.leaf_hash();
        assert_eq!(h1, h2);
    }
}
