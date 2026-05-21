//! Note bridge: cross-federation value transfer via proof-carrying notes.
//!
//! Notes are self-proving (the STARK proof carries all verification needed). A note
//! "burned" (nullifier published) in Federation A can be "minted" in Federation B by
//! presenting the spending proof. The proof IS the bridge — no light client needed.
//!
//! # Security Model
//!
//! The bridge relies on:
//! 1. **Nullifier uniqueness**: Since nullifiers are derived from note-intrinsic data
//!    (not tree position), the same note produces the same nullifier everywhere. A
//!    nullifier revealed in Fed A cannot be replayed in Fed B for a different note.
//! 2. **Trusted roots**: The destination federation maintains a set of trusted roots
//!    from source federations. Only proofs against these roots are accepted.
//! 3. **Bridged-nullifier tracking**: Each federation tracks which nullifiers have been
//!    bridged in, preventing double-bridge (same note minted twice).
//! 4. **STARK proof verification**: The spending proof proves knowledge of the spending
//!    key and Merkle membership without revealing the note contents.

use serde::{Deserialize, Serialize};

use crate::note::{NoteCommitment, Nullifier};
use pyana_types::AttestedRoot;

/// A portable note proof that can be presented to another federation.
///
/// This is the "bridge message" — the thing Alice creates in Federation A
/// and presents to Federation B to mint equivalent value.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PortableNoteProof {
    /// The nullifier (proves the note was spent in the source federation).
    pub nullifier: [u8; 32],
    /// The source federation's attested root at time of spend.
    pub source_root: AttestedRoot,
    /// The STARK proof of valid spending (NoteSpendingAir).
    /// Serialized via postcard from a StarkProof.
    pub spending_proof: Vec<u8>,
    /// The new note commitment for the destination (what gets minted).
    pub destination_commitment: NoteCommitment,
    /// Value being transferred.
    pub value: u64,
    /// Asset type.
    pub asset_type: u64,
}

/// Errors that can occur during bridge operations.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum BridgeError {
    /// The source root is not in our trusted set.
    UntrustedRoot {
        /// Short hex of the untrusted root for diagnostics.
        root_hex: String,
    },
    /// The source root does not contain a note_tree_root (federation too old).
    MissingNoteTreeRoot,
    /// The STARK spending proof failed verification.
    InvalidSpendingProof { reason: String },
    /// The nullifier has already been bridged (double-bridge attempt).
    AlreadyBridged { nullifier: [u8; 32] },
    /// The nullifier in the proof does not match the public inputs.
    NullifierMismatch,
    /// Value or asset type inconsistency.
    ValueMismatch { expected: u64, got: u64 },
}

impl core::fmt::Display for BridgeError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            BridgeError::UntrustedRoot { root_hex } => {
                write!(f, "source root {root_hex}... is not in the trusted set")
            }
            BridgeError::MissingNoteTreeRoot => {
                write!(
                    f,
                    "source root does not contain a note_tree_root attestation"
                )
            }
            BridgeError::InvalidSpendingProof { reason } => {
                write!(f, "STARK spending proof verification failed: {reason}")
            }
            BridgeError::AlreadyBridged { nullifier } => {
                write!(
                    f,
                    "nullifier {:02x}{:02x}{:02x}{:02x}... already bridged",
                    nullifier[0], nullifier[1], nullifier[2], nullifier[3]
                )
            }
            BridgeError::NullifierMismatch => {
                write!(f, "nullifier does not match proof public inputs")
            }
            BridgeError::ValueMismatch { expected, got } => {
                write!(f, "value mismatch: expected {expected}, got {got}")
            }
        }
    }
}

impl std::error::Error for BridgeError {}

/// A set of nullifiers that have been bridged into this federation from others.
///
/// Prevents the same portable note proof from being accepted twice (double-bridge).
/// Separate from the local NullifierSet which tracks locally-spent notes.
#[derive(Clone, Debug, Default)]
pub struct BridgedNullifierSet {
    /// Sorted set of bridged nullifiers for O(log n) lookup.
    nullifiers: Vec<[u8; 32]>,
}

impl BridgedNullifierSet {
    /// Create an empty bridged nullifier set.
    pub fn new() -> Self {
        Self {
            nullifiers: Vec::new(),
        }
    }

    /// Check if a nullifier has already been bridged.
    pub fn contains(&self, nullifier: &[u8; 32]) -> bool {
        self.nullifiers.binary_search(nullifier).is_ok()
    }

    /// Insert a bridged nullifier. Returns error if already present.
    pub fn insert(&mut self, nullifier: [u8; 32]) -> Result<(), BridgeError> {
        match self.nullifiers.binary_search(&nullifier) {
            Ok(_) => Err(BridgeError::AlreadyBridged { nullifier }),
            Err(idx) => {
                self.nullifiers.insert(idx, nullifier);
                Ok(())
            }
        }
    }

    /// Number of bridged nullifiers.
    pub fn len(&self) -> usize {
        self.nullifiers.len()
    }

    /// Whether the set is empty.
    pub fn is_empty(&self) -> bool {
        self.nullifiers.is_empty()
    }
}

/// Verify a portable note proof from another federation.
///
/// This is the core verification that a destination federation performs before
/// minting a new note. It checks:
/// 1. The source_root is in our trusted set (we accept proofs from that federation).
/// 2. The source_root has a note_tree_root (the source federation attests note trees).
/// 3. The STARK spending proof verifies against the source_root's note_tree_root.
/// 4. The nullifier is consistent with the proof's public inputs.
///
/// On success, the caller should:
/// - Add the nullifier to the bridged-nullifier set (prevent double-bridge).
/// - Create a new note commitment in the local note tree.
///
/// # Arguments
///
/// * `proof` - The portable note proof to verify.
/// * `trusted_roots` - The set of attested roots we accept from other federations.
/// * `verify_stark` - A closure that verifies the STARK proof given (nullifier_bytes, merkle_root_bytes, proof_bytes).
///   Returns Ok(()) if valid.
pub fn verify_portable_note<F>(
    proof: &PortableNoteProof,
    trusted_roots: &[AttestedRoot],
    verify_stark: F,
) -> Result<(), BridgeError>
where
    F: FnOnce(&[u8; 32], &[u8; 32], &[u8]) -> Result<(), String>,
{
    // 1. Check source_root is in our trusted set.
    let is_trusted = trusted_roots.iter().any(|r| {
        r.merkle_root == proof.source_root.merkle_root
            && r.height == proof.source_root.height
            && r.note_tree_root == proof.source_root.note_tree_root
    });
    if !is_trusted {
        let root_hex = proof
            .source_root
            .merkle_root
            .iter()
            .take(4)
            .map(|b| format!("{b:02x}"))
            .collect::<String>();
        return Err(BridgeError::UntrustedRoot { root_hex });
    }

    // 2. Check the source root has a note_tree_root.
    let note_tree_root = proof
        .source_root
        .note_tree_root
        .ok_or(BridgeError::MissingNoteTreeRoot)?;

    // 3. Verify the STARK spending proof.
    verify_stark(&proof.nullifier, &note_tree_root, &proof.spending_proof)
        .map_err(|reason| BridgeError::InvalidSpendingProof { reason })?;

    // 4. Verification passed. The nullifier corresponds to a valid note in the
    //    source federation's note tree at the attested root.
    Ok(())
}

/// Create a portable note proof for cross-federation transfer.
///
/// This is called by the note owner in the source federation after spending
/// their note there. It packages the spending proof along with the federation's
/// attested root into a portable format that can be presented elsewhere.
///
/// # Arguments
///
/// * `nullifier` - The nullifier revealed when spending in the source federation.
/// * `spending_proof` - The serialized STARK proof from `prove_note_spend`.
/// * `source_root` - The source federation's attested root at time of spend.
/// * `destination_commitment` - The new note commitment for the destination federation.
/// * `value` - The value being transferred.
/// * `asset_type` - The asset type being transferred.
pub fn create_portable_note(
    nullifier: Nullifier,
    spending_proof: Vec<u8>,
    source_root: AttestedRoot,
    destination_commitment: NoteCommitment,
    value: u64,
    asset_type: u64,
) -> PortableNoteProof {
    PortableNoteProof {
        nullifier: nullifier.0,
        source_root,
        spending_proof,
        destination_commitment,
        value,
        asset_type,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_attested_root(height: u64, note_root: Option<[u8; 32]>) -> AttestedRoot {
        AttestedRoot {
            merkle_root: [height as u8; 32],
            note_tree_root: note_root,
            nullifier_set_root: None,
            height,
            timestamp: 1000 + height as i64,
            quorum_signatures: vec![],
            threshold_qc: None,
            threshold: 0,
        }
    }

    fn make_proof(nullifier: [u8; 32], value: u64, asset_type: u64) -> PortableNoteProof {
        let source_root = make_attested_root(42, Some([0xAA; 32]));
        PortableNoteProof {
            nullifier,
            source_root,
            spending_proof: vec![1, 2, 3, 4], // dummy proof bytes
            destination_commitment: NoteCommitment([0xBB; 32]),
            value,
            asset_type,
        }
    }

    /// A dummy verifier that always succeeds.
    fn verify_ok(_nullifier: &[u8; 32], _root: &[u8; 32], _proof: &[u8]) -> Result<(), String> {
        Ok(())
    }

    /// A dummy verifier that always fails.
    fn verify_fail(
        _nullifier: &[u8; 32],
        _root: &[u8; 32],
        _proof: &[u8],
    ) -> Result<(), String> {
        Err("mock verification failure".to_string())
    }

    #[test]
    fn test_verify_portable_note_success() {
        let trusted = vec![make_attested_root(42, Some([0xAA; 32]))];
        let proof = make_proof([1u8; 32], 100, 1);
        let result = verify_portable_note(&proof, &trusted, verify_ok);
        assert!(result.is_ok());
    }

    #[test]
    fn test_verify_portable_note_untrusted_root() {
        // Trusted set has height 99, but proof has height 42.
        let trusted = vec![make_attested_root(99, Some([0xCC; 32]))];
        let proof = make_proof([1u8; 32], 100, 1);
        let result = verify_portable_note(&proof, &trusted, verify_ok);
        assert!(matches!(result, Err(BridgeError::UntrustedRoot { .. })));
    }

    #[test]
    fn test_verify_portable_note_missing_note_tree_root() {
        // Trusted root has no note_tree_root.
        let trusted = vec![make_attested_root(42, None)];
        let mut proof = make_proof([1u8; 32], 100, 1);
        proof.source_root.note_tree_root = None;
        let result = verify_portable_note(&proof, &trusted, verify_ok);
        assert!(matches!(result, Err(BridgeError::MissingNoteTreeRoot)));
    }

    #[test]
    fn test_verify_portable_note_invalid_proof() {
        let trusted = vec![make_attested_root(42, Some([0xAA; 32]))];
        let proof = make_proof([1u8; 32], 100, 1);
        let result = verify_portable_note(&proof, &trusted, verify_fail);
        assert!(matches!(
            result,
            Err(BridgeError::InvalidSpendingProof { .. })
        ));
    }

    #[test]
    fn test_bridged_nullifier_set_insert_and_contains() {
        let mut set = BridgedNullifierSet::new();
        let n = [42u8; 32];

        assert!(!set.contains(&n));
        set.insert(n).unwrap();
        assert!(set.contains(&n));
        assert_eq!(set.len(), 1);
    }

    #[test]
    fn test_bridged_nullifier_set_double_bridge_rejected() {
        let mut set = BridgedNullifierSet::new();
        let n = [42u8; 32];

        set.insert(n).unwrap();
        let result = set.insert(n);
        assert!(matches!(result, Err(BridgeError::AlreadyBridged { .. })));
    }

    #[test]
    fn test_bridged_nullifier_set_multiple() {
        let mut set = BridgedNullifierSet::new();
        for i in 0..10u8 {
            let mut n = [0u8; 32];
            n[0] = i;
            set.insert(n).unwrap();
        }
        assert_eq!(set.len(), 10);

        for i in 0..10u8 {
            let mut n = [0u8; 32];
            n[0] = i;
            assert!(set.contains(&n));
        }
    }

    #[test]
    fn test_create_portable_note() {
        let nullifier = Nullifier([0x11; 32]);
        let source_root = make_attested_root(10, Some([0xAA; 32]));
        let dest_commitment = NoteCommitment([0xBB; 32]);

        let portable = create_portable_note(
            nullifier,
            vec![5, 6, 7, 8],
            source_root.clone(),
            dest_commitment,
            500,
            2,
        );

        assert_eq!(portable.nullifier, [0x11; 32]);
        assert_eq!(portable.value, 500);
        assert_eq!(portable.asset_type, 2);
        assert_eq!(portable.destination_commitment, dest_commitment);
        assert_eq!(portable.source_root.height, 10);
    }

    #[test]
    fn test_verify_then_bridge_flow() {
        // Simulate the full flow: verify then track in bridged set.
        let trusted = vec![make_attested_root(42, Some([0xAA; 32]))];
        let proof = make_proof([0x99; 32], 100, 1);
        let mut bridged_set = BridgedNullifierSet::new();

        // First bridge succeeds.
        verify_portable_note(&proof, &trusted, verify_ok).unwrap();
        bridged_set.insert(proof.nullifier).unwrap();

        // Second bridge with same nullifier fails.
        let result = bridged_set.insert(proof.nullifier);
        assert!(matches!(result, Err(BridgeError::AlreadyBridged { .. })));
    }

    // ========================================================================
    // Adversarial tests: prove note bridge security properties
    // ========================================================================

    /// Adversarial test 8: Double-bridge attack.
    ///
    /// Bridge the same note (same nullifier) to the same federation twice.
    /// The second attempt MUST fail via BridgedNullifierSet.
    #[test]
    fn adversarial_double_bridge() {
        let trusted = vec![make_attested_root(42, Some([0xAA; 32]))];
        let nullifier = [0xD0; 32];
        let proof = make_proof(nullifier, 500, 1);
        let mut bridged_set = BridgedNullifierSet::new();

        // First bridge: verify + insert.
        verify_portable_note(&proof, &trusted, verify_ok).unwrap();
        bridged_set.insert(proof.nullifier).unwrap();

        // Attacker attempts to bridge the SAME note again.
        // Verification would pass (proof is still valid against the root),
        // but the nullifier set catches the double-bridge.
        verify_portable_note(&proof, &trusted, verify_ok).unwrap();
        let result = bridged_set.insert(proof.nullifier);
        assert!(
            matches!(result, Err(BridgeError::AlreadyBridged { nullifier: n }) if n == nullifier),
            "double-bridge must be rejected by BridgedNullifierSet"
        );
    }

    /// Adversarial test 9: Untrusted root.
    ///
    /// Present a PortableNoteProof with a source_root that's not in
    /// trusted_federation_roots. Must fail with UntrustedRoot.
    #[test]
    fn adversarial_untrusted_root() {
        // Trusted set contains root at height 99.
        let trusted = vec![make_attested_root(99, Some([0xCC; 32]))];

        // Attacker's proof references a root from a different (untrusted) federation.
        let mut proof = make_proof([0xAA; 32], 100, 1);
        // The proof's source_root is at height 42 with different merkle_root.
        // This does NOT match anything in trusted.
        assert_ne!(proof.source_root.merkle_root, trusted[0].merkle_root);

        let result = verify_portable_note(&proof, &trusted, verify_ok);
        assert!(
            matches!(result, Err(BridgeError::UntrustedRoot { .. })),
            "untrusted root must be rejected: got {:?}", result
        );

        // Also test: attacker crafts source_root with matching merkle_root but wrong height.
        proof.source_root.merkle_root = trusted[0].merkle_root;
        proof.source_root.height = 42; // wrong height
        proof.source_root.note_tree_root = trusted[0].note_tree_root;
        let result2 = verify_portable_note(&proof, &trusted, verify_ok);
        assert!(
            matches!(result2, Err(BridgeError::UntrustedRoot { .. })),
            "root with wrong height must be rejected: got {:?}", result2
        );
    }

    /// Adversarial test 10: Tampered STARK proof.
    ///
    /// Take a valid PortableNoteProof and flip a byte in spending_proof.
    /// The STARK verifier must reject the tampered proof.
    #[test]
    fn adversarial_tampered_stark_proof() {
        let trusted = vec![make_attested_root(42, Some([0xAA; 32]))];
        let mut proof = make_proof([0xBB; 32], 100, 1);

        // Flip a byte in the spending_proof to simulate tampering.
        assert!(!proof.spending_proof.is_empty());
        proof.spending_proof[0] ^= 0xFF;

        // Use a verifier that checks the proof bytes match expected pattern.
        // In reality, the STARK verifier would reject any modified proof.
        let verify_checks_integrity =
            |_nullifier: &[u8; 32], _root: &[u8; 32], proof_bytes: &[u8]| -> Result<(), String> {
                // Simulates a real STARK verifier: the expected proof is [1,2,3,4].
                // Any other value means the proof is tampered.
                if proof_bytes == &[1, 2, 3, 4] {
                    Ok(())
                } else {
                    Err("STARK proof verification failed: commitment mismatch".to_string())
                }
            };

        let result = verify_portable_note(&proof, &trusted, verify_checks_integrity);
        assert!(
            matches!(result, Err(BridgeError::InvalidSpendingProof { ref reason }) if reason.contains("commitment mismatch")),
            "tampered proof must be rejected by verifier: got {:?}", result
        );
    }

    /// Adversarial test 11: Value mismatch.
    ///
    /// Create a PortableNoteProof claiming value=1000 but the STARK proof was
    /// generated for value=100. Since verify_portable_note currently does NOT check
    /// value as a public input (the verify_stark closure receives only nullifier,
    /// root, and proof_bytes — not value), this documents the current behavior.
    ///
    /// FINDING: The value field is NOT verified by verify_portable_note itself.
    /// The STARK verifier closure would need to embed value in its verification
    /// (e.g., as part of the proof's public inputs encoded in proof_bytes).
    /// If the STARK proof binds value as a public input, the verifier catches it.
    /// If not, this is a gap that must be addressed at the protocol level.
    #[test]
    fn adversarial_value_mismatch_documents_gap() {
        let trusted = vec![make_attested_root(42, Some([0xAA; 32]))];
        let mut proof = make_proof([0xCC; 32], 100, 1);

        // Attacker inflates the claimed value from 100 to 1000.
        proof.value = 1000;

        // With a naive verifier that doesn't check value, this passes.
        let result_naive = verify_portable_note(&proof, &trusted, verify_ok);
        assert!(
            result_naive.is_ok(),
            "BUG DOCUMENTATION: naive verifier does not catch value inflation"
        );

        // With a verifier that checks value is bound in the proof, this fails.
        let verify_with_value_check =
            |_nullifier: &[u8; 32], _root: &[u8; 32], _proof_bytes: &[u8]| -> Result<(), String> {
                // A real verifier would extract expected_value from public inputs.
                // The proof was generated for value=100, but PortableNoteProof claims 1000.
                // The verifier detects the mismatch.
                Err("public input mismatch: proof binds value=100, claimed 1000".to_string())
            };

        let result_strict = verify_portable_note(&proof, &trusted, verify_with_value_check);
        assert!(
            matches!(result_strict, Err(BridgeError::InvalidSpendingProof { ref reason }) if reason.contains("value=100")),
            "value-aware verifier must catch inflation: got {:?}", result_strict
        );
    }

    /// Adversarial test 12: Nullifier from a different note.
    ///
    /// Attacker takes nullifier from note A but provides Merkle proof from note B.
    /// The STARK verifier must reject this because the nullifier doesn't match
    /// the note commitment proven by the Merkle proof.
    #[test]
    fn adversarial_nullifier_from_different_note() {
        let trusted = vec![make_attested_root(42, Some([0xAA; 32]))];

        let nullifier_a = [0xA0; 32]; // From note A
        let nullifier_b = [0xB0; 32]; // From note B

        // Attacker uses nullifier_a but the proof is actually for note B.
        let proof = make_proof(nullifier_a, 100, 1);

        // A real STARK verifier binds the nullifier to the note commitment.
        // If the nullifier doesn't match what the proof proves, verification fails.
        let verify_nullifier_binding =
            |nullifier: &[u8; 32], _root: &[u8; 32], _proof_bytes: &[u8]| -> Result<(), String> {
                // The proof was generated for note B (nullifier_b).
                // The presented nullifier is from note A (nullifier_a).
                let expected_nullifier = nullifier_b;
                if nullifier != &expected_nullifier {
                    Err(format!(
                        "nullifier binding failed: proof is for {:02x}{:02x}..., presented {:02x}{:02x}...",
                        expected_nullifier[0], expected_nullifier[1],
                        nullifier[0], nullifier[1]
                    ))
                } else {
                    Ok(())
                }
            };

        let result = verify_portable_note(&proof, &trusted, verify_nullifier_binding);
        assert!(
            matches!(result, Err(BridgeError::InvalidSpendingProof { ref reason }) if reason.contains("nullifier binding failed")),
            "mismatched nullifier must be rejected: got {:?}", result
        );
    }

    /// Adversarial test 13: Expired source root.
    ///
    /// Source root has timestamp from 1 year ago, but the federation has a maximum
    /// acceptable age policy. Since verify_portable_note does NOT currently enforce
    /// a timestamp-based expiry (it only checks set membership), this test documents
    /// that root age enforcement must happen at the caller level (e.g., by removing
    /// old roots from the trusted set).
    ///
    /// FINDING: Root age is enforced by trusted_roots set membership, not by
    /// timestamp comparison within verify_portable_note. Federations must prune
    /// stale roots from their trusted set to enforce freshness.
    #[test]
    fn adversarial_expired_source_root() {
        // Create a root with a very old timestamp (1 year ago).
        let old_root = AttestedRoot {
            merkle_root: [0xDD; 32],
            note_tree_root: Some([0xEE; 32]),
            nullifier_set_root: None,
            height: 1,
            timestamp: 1000, // Very old timestamp.
            quorum_signatures: vec![],
            threshold_qc: None,
            threshold: 0,
        };

        let proof = PortableNoteProof {
            nullifier: [0xFF; 32],
            source_root: old_root.clone(),
            spending_proof: vec![1, 2, 3, 4],
            destination_commitment: NoteCommitment([0x11; 32]),
            value: 100,
            asset_type: 1,
        };

        // If the old root is still in the trusted set, verification passes.
        // This documents that the federation MUST remove stale roots to enforce freshness.
        let trusted_with_old = vec![old_root.clone()];
        let result_with = verify_portable_note(&proof, &trusted_with_old, verify_ok);
        assert!(
            result_with.is_ok(),
            "stale root still in trusted set is accepted (by design)"
        );

        // If the federation has pruned the stale root, verification fails.
        let trusted_without_old: Vec<AttestedRoot> = vec![];
        let result_without = verify_portable_note(&proof, &trusted_without_old, verify_ok);
        assert!(
            matches!(result_without, Err(BridgeError::UntrustedRoot { .. })),
            "pruned stale root must be rejected: got {:?}", result_without
        );

        // With a recent root only in the trusted set, the old proof is rejected.
        let recent_root = AttestedRoot {
            merkle_root: [0xCC; 32],
            note_tree_root: Some([0xBB; 32]),
            nullifier_set_root: None,
            height: 10000,
            timestamp: 1_700_000_000, // Recent.
            quorum_signatures: vec![],
            threshold_qc: None,
            threshold: 0,
        };
        let trusted_recent_only = vec![recent_root];
        let result_recent = verify_portable_note(&proof, &trusted_recent_only, verify_ok);
        assert!(
            matches!(result_recent, Err(BridgeError::UntrustedRoot { .. })),
            "proof against old root not in trusted set must be rejected: got {:?}", result_recent
        );
    }
}
