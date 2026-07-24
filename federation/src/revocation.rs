//! Revocation Merkle tree management.
//!
//! This module wraps the `dregg-commit` Merkle tree to maintain a set of
//! revoked token IDs. Each revoked token is represented as a leaf in the
//! 4-ary Merkle tree, where the leaf data is the BLAKE3 hash of the token ID.
//!
//! The tree supports:
//! - Adding revoked token IDs (insert)
//! - Checking if a token is revoked (membership)
//! - Proving a token is NOT revoked (non-membership proof)
//! - Getting the current Merkle root

use dregg_commit::merkle::MerkleTree;
use dregg_commit::{NonMembershipProof, hash_leaf};
use std::collections::HashSet;

use crate::types::{AttestedRoot, PublicKey, RevocationProof, hex_encode};

// =============================================================================
// Revocation Tree
// =============================================================================

/// A revocation tree backed by a 4-ary Merkle tree from `dregg-commit`.
///
/// Each leaf represents a revoked token: leaf_hash = H_leaf(token_id_bytes).
/// The tree root commits to the entire revocation set.
#[derive(Clone, Debug)]
pub struct RevocationTree {
    /// The underlying Merkle tree.
    tree: MerkleTree,
    /// Set of revoked token IDs (for quick lookup without tree traversal).
    revoked: HashSet<String>,
}

impl RevocationTree {
    /// Create a new empty revocation tree.
    pub fn new() -> Self {
        Self {
            tree: MerkleTree::new(),
            revoked: HashSet::new(),
        }
    }

    /// Get the current Merkle root of the revocation tree.
    pub fn root(&mut self) -> [u8; 32] {
        self.tree.root()
    }

    /// Short hex of the current root for display.
    pub fn root_hex(&mut self) -> String {
        let r = self.root();
        hex_encode(&r[..4])
    }

    /// Number of revoked tokens in the tree.
    pub fn len(&self) -> usize {
        self.revoked.len()
    }

    /// Whether the tree is empty (no revocations).
    pub fn is_empty(&self) -> bool {
        self.revoked.is_empty()
    }

    /// Check if a token ID is in the revoked set.
    pub fn is_revoked(&self, token_id: &str) -> bool {
        self.revoked.contains(token_id)
    }

    /// Revoke a token by adding it to the tree.
    /// Returns the new Merkle root after insertion.
    /// Returns None if the token was already revoked.
    pub fn revoke(&mut self, token_id: &str) -> Option<[u8; 32]> {
        if self.revoked.contains(token_id) {
            return None;
        }
        self.revoked.insert(token_id.to_string());
        let leaf_data = token_id_to_leaf_data(token_id);
        let new_root = self.tree.insert(&leaf_data);
        Some(new_root)
    }

    /// Batch-revoke multiple tokens. Returns the new root after all insertions.
    pub fn revoke_batch(&mut self, token_ids: &[String]) -> [u8; 32] {
        for token_id in token_ids {
            if !self.revoked.contains(token_id) {
                self.revoked.insert(token_id.clone());
                let leaf_data = token_id_to_leaf_data(token_id);
                self.tree.insert(&leaf_data);
            }
        }
        self.tree.root()
    }

    /// Generate a non-membership proof for a token ID.
    ///
    /// This proves that a token is NOT in the revocation set (i.e., it is still valid).
    /// Returns None if the token IS revoked (cannot prove non-membership).
    pub fn prove_non_membership(&self, token_id: &str) -> Option<NonMembershipProof> {
        if self.revoked.contains(token_id) {
            return None;
        }
        let leaf_data = token_id_to_leaf_data(token_id);
        let leaf_hash = hash_leaf(&leaf_data);
        self.tree.non_membership_proof_hash(&leaf_hash)
    }

    /// Verify a non-membership proof against the current root.
    pub fn verify_non_membership(&mut self, token_id: &str, proof: &NonMembershipProof) -> bool {
        let root = self.root();
        Self::verify_non_membership_against_root(&root, token_id, proof)
    }

    /// Verify a non-membership proof against a specific root (static method).
    pub fn verify_non_membership_against_root(
        root: &[u8; 32],
        _token_id: &str,
        proof: &NonMembershipProof,
    ) -> bool {
        MerkleTree::verify_non_membership(root, proof)
    }

    /// Check if a token is in the tree using the Merkle tree directly.
    pub fn contains_in_tree(&self, token_id: &str) -> bool {
        let leaf_data = token_id_to_leaf_data(token_id);
        self.tree.contains(&leaf_data)
    }
}

impl Default for RevocationTree {
    fn default() -> Self {
        Self::new()
    }
}

// =============================================================================
// Revocation Verifier
// =============================================================================

/// A verifier that checks whether a token is valid (not revoked) given an
/// attested root and a non-membership proof.
///
/// A `RevocationVerifier` is bound to a **trusted committee** — the set of
/// Ed25519 public keys whose quorum signature over an [`AttestedRoot`]'s
/// canonical preimage is what makes that root's `merkle_root` trustworthy.
/// Without a committee there is no anchor of trust: an attested root's
/// `merkle_root` is chosen by whoever produced the proof, so a non-membership
/// check would run against a prover-controlled tree (e.g. an empty one, in
/// which nothing is revoked). Binding the committee at construction makes it
/// structurally impossible to verify a proof without naming the trust anchor.
///
/// This is the revocation-proof twin of
/// [`Federation::verify_attested_root`](crate::federation::Federation::verify_attested_root),
/// which gates the same way (`root.is_valid(&members)`).
pub struct RevocationVerifier {
    /// The trusted federation committee. An attested root is trusted only when
    /// a quorum of THESE keys have cryptographically signed it (typically
    /// `Federation::members`).
    committee: Vec<PublicKey>,
}

impl RevocationVerifier {
    /// Create a verifier bound to a trusted federation committee.
    ///
    /// `committee` is the set of member public keys the verifier trusts to
    /// attest revocation roots (typically a `Federation`'s `members`).
    pub fn new(committee: Vec<PublicKey>) -> Self {
        Self { committee }
    }

    /// Verify a revocation proof: confirm that the token is NOT in the
    /// revocation tree as of the attested root.
    ///
    /// Checks, in order:
    /// 1. **Cryptographic.** The attested root carries a valid quorum of
    ///    signatures from the trusted committee over its canonical preimage
    ///    ([`AttestedRoot::is_valid`]). This BINDS `merkle_root`: a root the
    ///    prover fabricated — a chosen `merkle_root` with junk or absent
    ///    signatures, or signers outside the committee — does not carry a real
    ///    committee quorum and is REFUSED here, before its `merkle_root` is
    ///    ever trusted. (`is_valid` also subsumes the count-only quorum check:
    ///    it first rejects `quorum_signatures.len() < threshold`, then verifies
    ///    each signature against a committee-member key.)
    /// 2. The non-membership proof is valid against the now-trusted
    ///    `merkle_root`.
    ///
    /// A count-only quorum check (`has_quorum`) MUST NOT be used here: it would
    /// accept threshold-many unverified `(key, signature)` pairs over a
    /// prover-chosen root, letting a revoked token read "not revoked".
    pub fn verify(&self, proof: &RevocationProof) -> RevocationVerification {
        // Check 1: the attested root is cryptographically valid against the
        // TRUSTED committee. A fabricated root with a prover-chosen
        // `merkle_root` and junk/absent signatures does not carry a real
        // committee quorum, so we only trust `merkle_root` AFTER the committee
        // has signed it.
        if !proof.attested_root.is_valid(&self.committee) {
            return RevocationVerification {
                valid: false,
                reason: "Attested root not signed by a quorum of the trusted committee".to_string(),
                signatures_present: proof.attested_root.quorum_signatures.len(),
                signatures_required: proof.attested_root.threshold,
            };
        }

        // Check 2: non-membership proof is valid against the committee-attested
        // (now trusted) root.
        let nm_valid = MerkleTree::verify_non_membership(
            &proof.attested_root.merkle_root,
            &proof.non_membership,
        );

        if !nm_valid {
            return RevocationVerification {
                valid: false,
                reason: "Non-membership proof invalid against attested root".to_string(),
                signatures_present: proof.attested_root.quorum_signatures.len(),
                signatures_required: proof.attested_root.threshold,
            };
        }

        RevocationVerification {
            valid: true,
            reason:
                "Token is not revoked (non-membership verified against committee-attested root)"
                    .to_string(),
            signatures_present: proof.attested_root.quorum_signatures.len(),
            signatures_required: proof.attested_root.threshold,
        }
    }

    /// Build a complete RevocationProof given a tree, attested root, and token ID.
    ///
    /// This is a prover-side helper: it packages a non-membership proof for
    /// `token_id` against `tree` together with the `attested_root` it is
    /// relative to. It performs no committee check — the trust gate is applied
    /// by [`verify`](Self::verify) at check time.
    pub fn build_proof(
        tree: &RevocationTree,
        attested_root: &AttestedRoot,
        token_id: &str,
    ) -> Option<RevocationProof> {
        let nm_proof = tree.prove_non_membership(token_id)?;
        Some(RevocationProof {
            token_id: token_id.to_string(),
            attested_root: attested_root.clone(),
            non_membership: nm_proof,
        })
    }
}

/// Result of verifying a revocation proof.
#[derive(Clone, Debug)]
pub struct RevocationVerification {
    /// Whether the verification passed.
    pub valid: bool,
    /// Human-readable explanation.
    pub reason: String,
    /// Number of quorum signatures present.
    pub signatures_present: usize,
    /// Number of quorum signatures required.
    pub signatures_required: usize,
}

// =============================================================================
// Helpers
// =============================================================================

/// Convert a token ID to the leaf data that gets inserted into the Merkle tree.
/// We hash the token ID string to get a fixed-size leaf.
fn token_id_to_leaf_data(token_id: &str) -> Vec<u8> {
    // Use domain-separated hashing for the token ID.
    let mut hasher = blake3::Hasher::new_derive_key("dregg-federation revoked-token v1");
    hasher.update(token_id.as_bytes());
    hasher.finalize().as_bytes().to_vec()
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_tree() {
        let mut tree = RevocationTree::new();
        assert!(tree.is_empty());
        assert_eq!(tree.len(), 0);
        let root = tree.root();
        assert_ne!(root, [0u8; 32]); // Empty tree has a defined root (not all zeros).
    }

    #[test]
    fn revoke_single_token() {
        let mut tree = RevocationTree::new();
        let empty_root = tree.root();

        let new_root = tree.revoke("token-1");
        assert!(new_root.is_some());
        assert_ne!(new_root.unwrap(), empty_root);
        assert!(tree.is_revoked("token-1"));
        assert!(!tree.is_revoked("token-2"));
        assert_eq!(tree.len(), 1);
    }

    #[test]
    fn revoke_duplicate_returns_none() {
        let mut tree = RevocationTree::new();
        tree.revoke("token-1");
        assert!(tree.revoke("token-1").is_none());
        assert_eq!(tree.len(), 1);
    }

    #[test]
    fn non_membership_proof() {
        let mut tree = RevocationTree::new();
        tree.revoke("token-1");
        tree.revoke("token-3");

        // token-2 is NOT revoked, should have a non-membership proof.
        let proof = tree.prove_non_membership("token-2");
        assert!(proof.is_some());

        let proof = proof.unwrap();
        let root = tree.root();
        assert!(MerkleTree::verify_non_membership(&root, &proof));
    }

    #[test]
    fn no_non_membership_for_revoked() {
        let mut tree = RevocationTree::new();
        tree.revoke("token-1");

        // token-1 IS revoked, cannot prove non-membership.
        let proof = tree.prove_non_membership("token-1");
        assert!(proof.is_none());
    }

    #[test]
    fn batch_revoke() {
        let mut tree = RevocationTree::new();
        let ids = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        tree.revoke_batch(&ids);
        assert_eq!(tree.len(), 3);
        assert!(tree.is_revoked("a"));
        assert!(tree.is_revoked("b"));
        assert!(tree.is_revoked("c"));
        assert!(!tree.is_revoked("d"));
    }

    #[test]
    fn non_membership_proof_empty_tree() {
        let mut tree = RevocationTree::new();
        let proof = tree.prove_non_membership("anything");
        assert!(proof.is_some());

        let root = tree.root();
        assert!(MerkleTree::verify_non_membership(&root, &proof.unwrap()));
    }

    #[test]
    fn deterministic_root() {
        let mut t1 = RevocationTree::new();
        let mut t2 = RevocationTree::new();

        t1.revoke("alpha");
        t1.revoke("beta");

        t2.revoke("alpha");
        t2.revoke("beta");

        assert_eq!(t1.root(), t2.root());
    }

    #[test]
    fn order_independent_root() {
        let mut t1 = RevocationTree::new();
        let mut t2 = RevocationTree::new();

        t1.revoke("alpha");
        t1.revoke("beta");

        t2.revoke("beta");
        t2.revoke("alpha");

        assert_eq!(t1.root(), t2.root());
    }

    // =========================================================================
    // RevocationVerifier: committee-gated soundness (CLASS-1 revocation-bypass)
    // =========================================================================

    use crate::types::{Signature, SigningKey, generate_keypair, sign};

    /// Build an `AttestedRoot` committing to `merkle_root`, cryptographically
    /// signed by every `(signing_key, public_key)` in `signers`, with the given
    /// `threshold`.
    fn signed_attested_root(
        merkle_root: [u8; 32],
        signers: &[(SigningKey, PublicKey)],
        threshold: usize,
    ) -> AttestedRoot {
        let mut root = AttestedRoot {
            merkle_root,
            note_tree_root: None,
            nullifier_set_root: None,
            height: 1,
            timestamp: 1_700_000_000,
            blocklace_block_id: None,
            finality_round: None,
            quorum_signatures: Vec::new(),
            threshold_qc: None,
            threshold,
            federation_id: dregg_types::FederationId::PLACEHOLDER,
            receipt_stream_root: None,
            hybrid_quorum: Vec::new(),
        };
        let msg = root.signing_message();
        root.quorum_signatures = signers
            .iter()
            .map(|(sk, pk)| (*pk, sign(sk, &msg)))
            .collect();
        root
    }

    /// FALSIFIER (revocation-bypass): a fabricated `RevocationProof` — a
    /// prover-chosen `merkle_root` with junk (and then absent) unverified
    /// signatures, plus a genuine non-membership proof against that chosen root
    /// — MUST be refused. Under the old count-only `has_quorum` gate this forged
    /// proof returned `valid: true`, so a revoked token read "not revoked".
    #[test]
    fn forged_root_with_junk_signatures_is_refused() {
        // The GENUINE, committee-controlled revocation set: "revoked-token" IS
        // revoked here.
        let mut real_tree = RevocationTree::new();
        real_tree.revoke("revoked-token");

        // The trusted committee (the verifier's anchor of trust).
        let committee: Vec<(SigningKey, PublicKey)> = (0..3).map(|_| generate_keypair()).collect();
        let committee_keys: Vec<PublicKey> = committee.iter().map(|(_, pk)| *pk).collect();
        let verifier = RevocationVerifier::new(committee_keys);

        // FORGERY: the attacker uses an EMPTY revocation tree, whose root the
        // committee never signed. Against THAT root "revoked-token" is a
        // non-member, so a genuine non-membership proof exists.
        let attacker_tree = RevocationTree::new();
        let forged_root = attacker_tree.clone().root();
        let nm = attacker_tree
            .prove_non_membership("revoked-token")
            .expect("empty tree yields a non-membership proof for any token");

        // Attach threshold-many junk, UNVERIFIED (pk, sig) pairs and a small
        // threshold — the exact shape the old count-only `has_quorum` accepted.
        let forged = AttestedRoot {
            merkle_root: forged_root,
            note_tree_root: None,
            nullifier_set_root: None,
            height: 1,
            timestamp: 1_700_000_000,
            blocklace_block_id: None,
            finality_round: None,
            quorum_signatures: vec![(PublicKey([0x11; 32]), Signature([0x22; 64]))],
            threshold_qc: None,
            threshold: 1,
            federation_id: dregg_types::FederationId::PLACEHOLDER,
            receipt_stream_root: None,
            hybrid_quorum: Vec::new(),
        };
        let proof = RevocationProof {
            token_id: "revoked-token".to_string(),
            attested_root: forged,
            non_membership: nm,
        };

        // The non-membership proof itself is genuinely valid against the forged
        // root — the ONLY thing between the attacker and a revocation bypass is
        // the committee gate.
        assert!(
            MerkleTree::verify_non_membership(
                &proof.attested_root.merkle_root,
                &proof.non_membership
            ),
            "sanity: forged non-membership proof is valid against the prover-chosen root",
        );

        let result = verifier.verify(&proof);
        assert!(
            !result.valid,
            "revocation-bypass: a fabricated root with junk signatures MUST be refused, got: {}",
            result.reason,
        );

        // Absent signatures (empty quorum) with the same threshold is likewise
        // refused.
        let mut forged_absent = proof.clone();
        forged_absent.attested_root.quorum_signatures.clear();
        assert!(
            !verifier.verify(&forged_absent).valid,
            "revocation-bypass: a fabricated root with NO signatures MUST be refused",
        );

        // A root signed by keys OUTSIDE the trusted committee is refused too:
        // real signatures, wrong signers.
        let outsider: (SigningKey, PublicKey) = generate_keypair();
        let outsider_signed = signed_attested_root(forged_root, std::slice::from_ref(&outsider), 1);
        let outsider_proof = RevocationProof {
            token_id: "revoked-token".to_string(),
            attested_root: outsider_signed,
            non_membership: attacker_tree
                .prove_non_membership("revoked-token")
                .expect("empty tree non-membership"),
        };
        assert!(
            !verifier.verify(&outsider_proof).valid,
            "revocation-bypass: a root signed by non-committee keys MUST be refused",
        );
    }

    /// The sound counterpart: a genuine committee-signed attested root over the
    /// real revocation tree, with a real non-membership proof for a token that
    /// is NOT revoked, MUST be accepted.
    #[test]
    fn genuine_committee_signed_root_is_accepted() {
        let mut tree = RevocationTree::new();
        tree.revoke("revoked-token");
        let root_hash = tree.root();

        let committee: Vec<(SigningKey, PublicKey)> = (0..3).map(|_| generate_keypair()).collect();
        let committee_keys: Vec<PublicKey> = committee.iter().map(|(_, pk)| *pk).collect();
        let verifier = RevocationVerifier::new(committee_keys);

        // A GENUINE attested root: the committee signs the real tree root, with
        // threshold 2 of 3.
        let attested = signed_attested_root(root_hash, &committee, 2);

        // "valid-token" is NOT revoked — a real non-membership proof exists.
        let proof = RevocationVerifier::build_proof(&tree, &attested, "valid-token")
            .expect("valid-token is not revoked, so a non-membership proof exists");

        let result = verifier.verify(&proof);
        assert!(
            result.valid,
            "a genuine committee-signed root with a real non-membership proof MUST be accepted, got: {}",
            result.reason,
        );
    }
}
