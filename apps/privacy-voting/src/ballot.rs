//! Ballot commitments and reveal verification.
//!
//! A ballot is `(option_index: u32, randomness: [u8; 32])`. The voter publishes
//! only the commitment during the commit phase:
//!
//! ```text
//! commit = blake3-derive("dregg-ballot-v1" || proposal_id || option_index_le || randomness)
//! ```
//!
//! and reveals the underlying `(option_index, randomness)` later. Anyone can
//! verify that a reveal matches a previously-published commitment by recomputing
//! the hash with the same domain tag.
//!
//! The domain tag, plus the randomness, ensures:
//! - Commitments hide the vote (an adversary cannot brute-force `option_index`
//!   without also guessing the 32-byte randomness — `2^{256+32}` work).
//! - Two commits from different proposals are unforgeable to each other.

use serde::{Deserialize, Serialize};

use crate::proposal::ProposalId;

/// 32-byte ballot commitment.
pub type Commitment = [u8; 32];

/// A revealed ballot: option index plus randomness used to bind the commitment.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct BallotReveal {
    pub option_index: u32,
    /// Hex-encoded on the wire; the 32-byte randomness used at commit time.
    pub randomness: [u8; 32],
}

/// Domain tag for ballot commitments. Mismatched tags produce different
/// commitments, preventing cross-protocol replay.
pub const BALLOT_COMMIT_TAG: &str = "dregg-ballot-v1";

/// Compute a ballot commitment.
pub fn commit(proposal_id: &ProposalId, option_index: u32, randomness: &[u8; 32]) -> Commitment {
    let mut hasher = blake3::Hasher::new_derive_key(BALLOT_COMMIT_TAG);
    hasher.update(proposal_id);
    hasher.update(&option_index.to_le_bytes());
    hasher.update(randomness);
    *hasher.finalize().as_bytes()
}

/// Verify a reveal against a stored commitment.
pub fn verify_reveal(
    proposal_id: &ProposalId,
    expected: &Commitment,
    reveal: &BallotReveal,
) -> bool {
    let recomputed = commit(proposal_id, reveal.option_index, &reveal.randomness);
    // Constant-time comparison for 32 bytes.
    constant_time_eq(&recomputed, expected)
}

fn constant_time_eq(a: &[u8; 32], b: &[u8; 32]) -> bool {
    let mut diff = 0u8;
    for i in 0..32 {
        diff |= a[i] ^ b[i];
    }
    diff == 0
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn commit_is_deterministic() {
        let pid = [7u8; 32];
        let r = [3u8; 32];
        assert_eq!(commit(&pid, 0, &r), commit(&pid, 0, &r));
    }

    #[test]
    fn different_randomness_yields_different_commitment() {
        // Privacy property: same vote with different randomness must produce
        // different commitments, so an observer cannot learn that two voters
        // chose the same option by comparing commitment bytes.
        let pid = [0u8; 32];
        let c1 = commit(&pid, 1, &[1u8; 32]);
        let c2 = commit(&pid, 1, &[2u8; 32]);
        assert_ne!(c1, c2, "commitments must differ when randomness differs");
    }

    #[test]
    fn different_proposal_yields_different_commitment() {
        // A commit for proposal A must not be re-usable as a commit for
        // proposal B, even with identical vote+randomness.
        let r = [1u8; 32];
        let c_a = commit(&[0xAAu8; 32], 0, &r);
        let c_b = commit(&[0xBBu8; 32], 0, &r);
        assert_ne!(c_a, c_b);
    }

    #[test]
    fn reveal_roundtrip() {
        let pid = [9u8; 32];
        let reveal = BallotReveal {
            option_index: 1,
            randomness: [42u8; 32],
        };
        let c = commit(&pid, reveal.option_index, &reveal.randomness);
        assert!(verify_reveal(&pid, &c, &reveal));
    }

    #[test]
    fn reveal_rejects_tampered_ballot() {
        // Adversarial: a voter cannot change their vote or randomness at reveal
        // time without also changing the commitment.
        let pid = [9u8; 32];
        let r = [42u8; 32];
        let c = commit(&pid, 1, &r);

        let cases = [
            (
                "wrong vote",
                BallotReveal {
                    option_index: 0,
                    randomness: r,
                },
            ),
            (
                "wrong randomness",
                BallotReveal {
                    option_index: 1,
                    randomness: [43u8; 32],
                },
            ),
        ];
        for (label, bad) in cases {
            assert!(!verify_reveal(&pid, &c, &bad), "{label}");
        }
    }
}
