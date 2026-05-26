//! Checkpoint-based pruning: periodic state snapshots attested by the federation.
//!
//! A checkpoint is a snapshot of the full system state at a specific block height,
//! attested by a quorum certificate. Nodes can safely discard all blocks below the
//! latest checkpoint, retaining only:
//!
//! 1. The checkpoint itself (proves state was attested by quorum at that height)
//! 2. Current state (verified against checkpoint roots or subsequent block chain)
//! 3. Blocks since the checkpoint (for replay if needed)
//!
//! This enables:
//! - Pruning of old blocks, receipts, and audit log entries
//! - Fast bootstrap for new nodes (download checkpoint + state + replay recent blocks)
//! - Bounded storage growth proportional to checkpoint interval

use serde::{Deserialize, Serialize};

use crate::types::{NodeIdentity, PublicKey, QuorumCertificate};

/// Default interval between checkpoints (in blocks).
pub const DEFAULT_CHECKPOINT_INTERVAL: u64 = 1000;

/// A checkpoint: a snapshot of system state at a specific height, attested by federation quorum.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Checkpoint {
    /// The block height at which this checkpoint was created.
    pub height: u64,
    /// Merkle root of the ledger state (cell balances, agent states).
    pub ledger_state_root: [u8; 32],
    /// Root of the note commitment tree at this height.
    pub note_tree_root: [u8; 32],
    /// Root of the nullifier set at this height.
    pub nullifier_set_root: [u8; 32],
    /// Root of the revocation tree at this height.
    pub revocation_tree_root: [u8; 32],
    /// The federation members at the time of this checkpoint.
    pub federation_members: Vec<PublicKey>,
    /// The epoch number (incremented on federation membership changes).
    pub epoch: u64,
    /// Quorum certificate: federation attestation over this checkpoint.
    pub qc: QuorumCertificate,
    /// Unix timestamp (seconds) when the checkpoint was created.
    pub timestamp: i64,
}

/// Errors from checkpoint operations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CheckpointError {
    /// The quorum certificate does not have enough valid signatures.
    InsufficientQuorum { have: usize, need: usize },
    /// The QC block hash does not match the checkpoint's content hash.
    QcMismatch,
    /// The checkpoint height is not at a valid interval boundary.
    InvalidHeight { height: u64, interval: u64 },
    /// The checkpoint is too old (newer checkpoint exists).
    Stale {
        checkpoint_height: u64,
        current_height: u64,
    },
    /// Serialization/deserialization failure.
    Serialization(String),
}

impl std::fmt::Display for CheckpointError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InsufficientQuorum { have, need } => {
                write!(f, "insufficient quorum: have {have}, need {need}")
            }
            Self::QcMismatch => write!(f, "QC block hash does not match checkpoint content hash"),
            Self::InvalidHeight { height, interval } => {
                write!(
                    f,
                    "height {height} is not at checkpoint interval {interval}"
                )
            }
            Self::Stale {
                checkpoint_height,
                current_height,
            } => {
                write!(
                    f,
                    "checkpoint at height {checkpoint_height} is stale (current: {current_height})"
                )
            }
            Self::Serialization(msg) => write!(f, "serialization error: {msg}"),
        }
    }
}

impl std::error::Error for CheckpointError {}

impl Checkpoint {
    /// Compute the content hash of this checkpoint (used as the QC's block_hash target).
    ///
    /// The hash commits to all state roots, federation members, epoch, and height.
    pub fn content_hash(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("dregg-checkpoint-v1");
        hasher.update(&self.height.to_le_bytes());
        hasher.update(&self.ledger_state_root);
        hasher.update(&self.note_tree_root);
        hasher.update(&self.nullifier_set_root);
        hasher.update(&self.revocation_tree_root);
        hasher.update(&self.epoch.to_le_bytes());
        hasher.update(&(self.federation_members.len() as u64).to_le_bytes());
        for member in &self.federation_members {
            hasher.update(&member.0);
        }
        hasher.update(&self.timestamp.to_le_bytes());
        *hasher.finalize().as_bytes()
    }

    /// Verify that this checkpoint's QC is valid against the given federation keys.
    ///
    /// Checks:
    /// 1. The QC references the correct content hash
    /// 2. The QC height matches the checkpoint height
    /// 3. The QC has enough valid signatures from the given node identities
    pub fn verify(&self, nodes: &[NodeIdentity]) -> Result<(), CheckpointError> {
        let content_hash = self.content_hash();

        // QC must reference this checkpoint's content hash.
        if self.qc.block_hash != content_hash {
            return Err(CheckpointError::QcMismatch);
        }

        // QC must be at the same height.
        if self.qc.height != self.height {
            return Err(CheckpointError::QcMismatch);
        }

        // Verify signatures.
        if !self.qc.is_valid_with_keys(nodes) {
            return Err(CheckpointError::InsufficientQuorum {
                have: self.qc.votes.len(),
                need: self.qc.threshold,
            });
        }

        Ok(())
    }

    /// Verify using the threshold committee (preferred path for BLS aggregate QCs).
    pub fn verify_with_committee(
        &self,
        committee: &crate::threshold::FederationCommittee,
    ) -> Result<(), CheckpointError> {
        let content_hash = self.content_hash();

        if self.qc.block_hash != content_hash {
            return Err(CheckpointError::QcMismatch);
        }

        if self.qc.height != self.height {
            return Err(CheckpointError::QcMismatch);
        }

        if !self.qc.verify_with_committee(committee) {
            return Err(CheckpointError::InsufficientQuorum {
                have: self.qc.votes.len(),
                need: self.qc.threshold,
            });
        }

        Ok(())
    }
}

/// Create a checkpoint at the given height.
///
/// Assembles all state roots and federation member keys into a checkpoint struct.
/// The returned checkpoint has an empty QC that must be filled in by the consensus
/// process (proposer creates it, validators sign it, then the QC is attached).
pub fn create_checkpoint(
    height: u64,
    ledger_state_root: [u8; 32],
    note_tree_root: [u8; 32],
    nullifier_set_root: [u8; 32],
    revocation_tree_root: [u8; 32],
    federation_members: Vec<PublicKey>,
    epoch: u64,
) -> Checkpoint {
    let timestamp = crate::types::current_timestamp();

    Checkpoint {
        height,
        ledger_state_root,
        note_tree_root,
        nullifier_set_root,
        revocation_tree_root,
        federation_members,
        epoch,
        qc: QuorumCertificate {
            block_hash: [0u8; 32], // Filled after content_hash is computed
            height,
            view: 0,
            aggregate_qc: None,
            votes: Vec::new(),
            threshold: 0,
        },
        timestamp,
    }
}

/// Finalize a checkpoint by setting its QC.
///
/// After the proposer creates the checkpoint and validators sign it, this function
/// attaches the completed QC. The QC's block_hash must match the checkpoint's
/// content_hash.
pub fn finalize_checkpoint(
    mut checkpoint: Checkpoint,
    qc: QuorumCertificate,
) -> Result<Checkpoint, CheckpointError> {
    let content_hash = checkpoint.content_hash();
    if qc.block_hash != content_hash {
        return Err(CheckpointError::QcMismatch);
    }
    checkpoint.qc = qc;
    Ok(checkpoint)
}

/// Check whether a given height is a checkpoint boundary.
pub fn is_checkpoint_height(height: u64, interval: u64) -> bool {
    height > 0 && height % interval == 0
}

/// Verify a checkpoint and return the height if valid, suitable for deciding
/// whether to prune.
///
/// Checks:
/// 1. QC validity against known federation keys
/// 2. Checkpoint height is not in the future relative to `current_height`
pub fn verify_checkpoint(
    checkpoint: &Checkpoint,
    nodes: &[NodeIdentity],
    current_height: u64,
) -> Result<(), CheckpointError> {
    // Must not be a future checkpoint.
    if checkpoint.height > current_height {
        return Err(CheckpointError::Stale {
            checkpoint_height: checkpoint.height,
            current_height,
        });
    }

    checkpoint.verify(nodes)
}

/// Compute the signing message for a checkpoint vote.
///
/// Validators sign this message to attest to the checkpoint's validity.
pub fn checkpoint_vote_message(content_hash: &[u8; 32], height: u64) -> Vec<u8> {
    // Reuses the same vote message format as QC for compatibility.
    QuorumCertificate::vote_message(content_hash, height, 0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::generate_keypair;

    #[test]
    fn test_checkpoint_content_hash_deterministic() {
        let members = vec![generate_keypair().1];
        let cp1 = create_checkpoint(
            1000,
            [1u8; 32],
            [2u8; 32],
            [3u8; 32],
            [4u8; 32],
            members.clone(),
            1,
        );
        let mut cp2 = cp1.clone();
        cp2.timestamp = cp1.timestamp; // same timestamp
        assert_eq!(cp1.content_hash(), cp2.content_hash());
    }

    #[test]
    fn test_checkpoint_content_hash_changes_with_height() {
        let members = vec![generate_keypair().1];
        let cp1 = create_checkpoint(
            1000,
            [1u8; 32],
            [2u8; 32],
            [3u8; 32],
            [4u8; 32],
            members.clone(),
            1,
        );
        let mut cp2 = cp1.clone();
        cp2.height = 2000;
        assert_ne!(cp1.content_hash(), cp2.content_hash());
    }

    #[test]
    fn test_is_checkpoint_height() {
        assert!(!is_checkpoint_height(0, 1000));
        assert!(is_checkpoint_height(1000, 1000));
        assert!(!is_checkpoint_height(1001, 1000));
        assert!(is_checkpoint_height(2000, 1000));
        assert!(is_checkpoint_height(500, 500));
    }

    #[test]
    fn test_verify_checkpoint_qc_mismatch() {
        let (signing_key, public_key) = generate_keypair();
        let members = vec![public_key.clone()];
        let mut cp =
            create_checkpoint(1000, [1u8; 32], [2u8; 32], [3u8; 32], [4u8; 32], members, 1);

        // Create a QC with wrong block hash.
        let wrong_hash = [99u8; 32];
        let vote_msg = QuorumCertificate::vote_message(&wrong_hash, 1000, 0);
        let sig = crate::types::sign(&signing_key, &vote_msg);
        cp.qc = QuorumCertificate {
            block_hash: wrong_hash,
            height: 1000,
            view: 0,
            aggregate_qc: None,
            votes: vec![(0, sig)],
            threshold: 1,
        };

        let nodes = vec![NodeIdentity {
            name: "test".to_string(),
            id: 0,
            public_key,
        }];
        assert_eq!(cp.verify(&nodes), Err(CheckpointError::QcMismatch));
    }

    #[test]
    fn test_verify_checkpoint_valid() {
        let (signing_key, public_key) = generate_keypair();
        let members = vec![public_key.clone()];
        let mut cp =
            create_checkpoint(1000, [1u8; 32], [2u8; 32], [3u8; 32], [4u8; 32], members, 1);

        // Create a QC with correct block hash.
        let content_hash = cp.content_hash();
        let vote_msg = QuorumCertificate::vote_message(&content_hash, 1000, 0);
        let sig = crate::types::sign(&signing_key, &vote_msg);
        cp.qc = QuorumCertificate {
            block_hash: content_hash,
            height: 1000,
            view: 0,
            aggregate_qc: None,
            votes: vec![(0, sig)],
            threshold: 1,
        };

        let nodes = vec![NodeIdentity {
            name: "test".to_string(),
            id: 0,
            public_key,
        }];
        assert!(cp.verify(&nodes).is_ok());
    }

    #[test]
    fn test_finalize_checkpoint() {
        let (signing_key, public_key) = generate_keypair();
        let members = vec![public_key.clone()];
        let cp = create_checkpoint(1000, [1u8; 32], [2u8; 32], [3u8; 32], [4u8; 32], members, 1);

        let content_hash = cp.content_hash();
        let vote_msg = QuorumCertificate::vote_message(&content_hash, 1000, 0);
        let sig = crate::types::sign(&signing_key, &vote_msg);
        let qc = QuorumCertificate {
            block_hash: content_hash,
            height: 1000,
            view: 0,
            aggregate_qc: None,
            votes: vec![(0, sig)],
            threshold: 1,
        };

        let finalized = finalize_checkpoint(cp, qc).unwrap();
        assert_eq!(finalized.qc.block_hash, content_hash);

        let nodes = vec![NodeIdentity {
            name: "test".to_string(),
            id: 0,
            public_key,
        }];
        assert!(finalized.verify(&nodes).is_ok());
    }
}
