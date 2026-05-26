//! Proposal types for privacy-preserving voting.
//!
//! A `Proposal` defines a question and the set of allowed vote values. Eligible
//! voters submit hidden commitments during the `Commit` phase, then reveal during
//! the `Reveal` phase. The tally is computable from the revealed triples in the
//! per-proposal queue.

use serde::{Deserialize, Serialize};

/// 32-byte proposal identifier (hex-encoded on the wire).
pub type ProposalId = [u8; 32];

/// Phase of a proposal's lifecycle.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Phase {
    /// Voters may submit `(commitment)` only. No reveals accepted.
    Commit,
    /// Commit window closed. Voters may submit `(commitment, vote, randomness)` reveals.
    Reveal,
    /// Reveal window closed. Tally is final.
    Closed,
}

/// A proposal voters can cast hidden votes on.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Proposal {
    pub id: ProposalId,
    pub question: String,
    /// Allowed vote values. Indexed by `u32` on the wire.
    pub options: Vec<String>,
    pub phase: Phase,
}

impl Proposal {
    pub fn new(id: ProposalId, question: impl Into<String>, options: Vec<String>) -> Self {
        Self {
            id,
            question: question.into(),
            options,
            phase: Phase::Commit,
        }
    }

    /// `true` iff `option_index` names a valid option.
    pub fn is_valid_option(&self, option_index: u32) -> bool {
        (option_index as usize) < self.options.len()
    }
}

/// Derive a stable proposal id from a slug.
pub fn derive_proposal_id(slug: &str) -> ProposalId {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-proposal-id-v1");
    hasher.update(slug.as_bytes());
    *hasher.finalize().as_bytes()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn derive_proposal_id_is_deterministic() {
        assert_eq!(derive_proposal_id("hello"), derive_proposal_id("hello"));
        assert_ne!(derive_proposal_id("hello"), derive_proposal_id("hello2"));
    }

    #[test]
    fn option_bounds_check() {
        let p = Proposal::new([0u8; 32], "?", vec!["yes".into(), "no".into()]);
        assert!(p.is_valid_option(0));
        assert!(p.is_valid_option(1));
        assert!(!p.is_valid_option(2));
    }
}
