//! Verifiable tally over a proposal's revealed ballots.
//!
//! After the reveal phase, every revealed `(commitment, vote, randomness)`
//! triple is appended to a positional sequence. The sequence has a clear root:
//!
//! ```text
//! reveal_leaf_i = blake3-derive("dregg-tally-leaf-v1"
//!                               || commitment_i
//!                               || option_index_i_le
//!                               || randomness_i)
//! reveal_root = merkle_root(reveal_leaf_0, reveal_leaf_1, ...)
//! ```
//!
//! ## Why this is verifiable
//!
//! Given the public reveal log (commit_i, option_index_i, randomness_i for all
//! i), anyone can:
//! 1. Recompute each commitment via `ballot::commit` — must equal `commit_i`.
//!    This catches any tally entry that doesn't correspond to a true commit.
//! 2. Recompute `reveal_root` — must equal the value the server returns.
//!    This pins the set of accepted reveals to a single Merkle-committed list.
//! 3. Recompute the per-option counts — must equal the tally totals.
//!
//! ## REVIEW[P2]: KZG fallback
//!
//! The KZG-flavored tally proposed in `plans/app-upgrade.md` (Privacy Voting)
//! would yield O(1) per-position witnesses against the commitment-queue root.
//! That requires wiring `storage/src/poly_queue.rs::KzgQueue` with a global
//! SRS — practical, but heavier than this app's ~800-LOC budget. We instead
//! use a Merkle-root reveal sequence (positional, deterministic), which gives
//! the same verifiability property up to constant factors.
//!
//! Migration path: replace `RevealLog::merkle_root` with a KZG commitment over
//! field-encoded leaves; the rest of the API stays the same.

use serde::{Deserialize, Serialize};

use crate::ballot::{self, BallotReveal, Commitment};
use crate::proposal::ProposalId;

/// A single revealed ballot in the public reveal log.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct RevealedBallot {
    pub commitment: Commitment,
    pub option_index: u32,
    pub randomness: [u8; 32],
}

impl RevealedBallot {
    /// Compute this entry's tally leaf hash.
    pub fn leaf_hash(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("dregg-tally-leaf-v1");
        hasher.update(&self.commitment);
        hasher.update(&self.option_index.to_le_bytes());
        hasher.update(&self.randomness);
        *hasher.finalize().as_bytes()
    }
}

/// The reveal log for a proposal: an ordered list of `(commit, vote, randomness)`.
///
/// Insertion order is the public ordering; that's what the Merkle root commits to.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct RevealLog {
    pub entries: Vec<RevealedBallot>,
}

impl RevealLog {
    pub fn new() -> Self {
        Self {
            entries: Vec::new(),
        }
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Append a verified reveal. Caller must have verified that the reveal
    /// matches the commitment (see [`ballot::verify_reveal`]).
    pub fn append(&mut self, entry: RevealedBallot) {
        self.entries.push(entry);
    }

    /// Compute the Merkle root over leaf hashes.
    ///
    /// Uses a duplicate-last-leaf pattern to handle odd levels (same as the
    /// blinded queue's internal helper). For an empty log, the root is
    /// `blake3-derive("dregg-tally-empty-v1")`.
    pub fn merkle_root(&self) -> [u8; 32] {
        if self.entries.is_empty() {
            let mut hasher = blake3::Hasher::new_derive_key("dregg-tally-empty-v1");
            hasher.update(b"empty");
            return *hasher.finalize().as_bytes();
        }

        let mut layer: Vec<[u8; 32]> = self.entries.iter().map(|e| e.leaf_hash()).collect();

        while layer.len() > 1 {
            let mut next = Vec::with_capacity(layer.len().div_ceil(2));
            let mut i = 0;
            while i < layer.len() {
                let left = layer[i];
                let right = if i + 1 < layer.len() {
                    layer[i + 1]
                } else {
                    layer[i]
                };
                let mut hasher = blake3::Hasher::new_derive_key("dregg-tally-node-v1");
                hasher.update(&left);
                hasher.update(&right);
                next.push(*hasher.finalize().as_bytes());
                i += 2;
            }
            layer = next;
        }

        layer[0]
    }

    /// Compute the per-option tally counts.
    ///
    /// Returns a vector of length `n_options`; entries outside `[0, n_options)`
    /// are silently ignored (the caller should reject such reveals at append
    /// time).
    pub fn tally(&self, n_options: usize, proposal_id: &ProposalId) -> Vec<u64> {
        let mut counts = vec![0u64; n_options];
        for entry in &self.entries {
            // Re-verify each entry against its own commitment. This makes the
            // tally robust against a corrupted log: any tampered entry would
            // change `commitment` but not recompute correctly.
            let reveal = BallotReveal {
                option_index: entry.option_index,
                randomness: entry.randomness,
            };
            if !ballot::verify_reveal(proposal_id, &entry.commitment, &reveal) {
                continue;
            }
            if (entry.option_index as usize) < n_options {
                counts[entry.option_index as usize] += 1;
            }
        }
        counts
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ballot::commit;

    fn entry(pid: &ProposalId, opt: u32, r: [u8; 32]) -> RevealedBallot {
        RevealedBallot {
            commitment: commit(pid, opt, &r),
            option_index: opt,
            randomness: r,
        }
    }

    #[test]
    fn empty_root_is_deterministic() {
        let log = RevealLog::new();
        assert_eq!(log.merkle_root(), RevealLog::new().merkle_root());
    }

    #[test]
    fn root_changes_on_append() {
        let pid = [1u8; 32];
        let mut log = RevealLog::new();
        let r0 = log.merkle_root();
        log.append(entry(&pid, 0, [1u8; 32]));
        let r1 = log.merkle_root();
        assert_ne!(r0, r1);
    }

    #[test]
    fn tally_counts_correctly() {
        let pid = [2u8; 32];
        let mut log = RevealLog::new();
        log.append(entry(&pid, 0, [1u8; 32]));
        log.append(entry(&pid, 1, [2u8; 32]));
        log.append(entry(&pid, 0, [3u8; 32]));
        log.append(entry(&pid, 0, [4u8; 32]));
        let counts = log.tally(2, &pid);
        assert_eq!(counts, vec![3, 1]);
    }

    #[test]
    fn tally_rejects_tampered_entry() {
        // Adversarial: if someone tampers with an entry's `option_index`
        // after insertion (without changing the commitment), the tally
        // skips it (the re-verify check fails).
        let pid = [3u8; 32];
        let mut log = RevealLog::new();
        log.append(entry(&pid, 0, [9u8; 32]));
        // Tamper: flip option_index but leave commitment alone.
        log.entries[0].option_index = 1;
        let counts = log.tally(2, &pid);
        // Original entry was option 0 (commitment binds to option=0). After
        // tampering, neither option is counted.
        assert_eq!(counts, vec![0, 0]);
    }
}
