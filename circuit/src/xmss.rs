//! XMSS-style key tree for managing WOTS one-time signatures.
//!
//! Validators get a tree of keys per epoch, each leaf used once. XMSS (eXtended
//! Merkle Signature Scheme) provides:
//! - A binary tree of WOTS key pairs
//! - The root is the "public key" (one value, verifiable)
//! - Each leaf is a one-time WOTS key
//! - Signing consumes one leaf (in order)
//! - The signature includes the Merkle authentication path from leaf to root
//!
//! The entire scheme is STARK-native: Poseidon2 for internal Merkle nodes,
//! Poseidon2-WOTS for one-time signatures.

use crate::field::BabyBear;
use crate::native_signature::{
    WOTS_TOTAL_CHAINS, WotsPublicKey, WotsSecretKey, WotsSignature, wots_keygen, wots_sign,
    wots_verify,
};
use crate::poseidon2;

// ============================================================================
// Types
// ============================================================================

/// Errors from XMSS operations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum XmssError {
    /// All leaf keys have been consumed; the tree is exhausted.
    KeysExhausted,
    /// The tree height is invalid (must be > 0 and <= 30).
    InvalidHeight(usize),
    /// Verification failed: the computed root does not match the public key.
    RootMismatch,
    /// Verification failed: the WOTS signature is invalid.
    WotsVerifyFailed,
}

impl std::fmt::Display for XmssError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::KeysExhausted => write!(f, "all XMSS leaf keys have been consumed"),
            Self::InvalidHeight(h) => write!(f, "invalid tree height: {h}"),
            Self::RootMismatch => write!(f, "XMSS root mismatch during verification"),
            Self::WotsVerifyFailed => write!(f, "WOTS signature verification failed"),
        }
    }
}

impl std::error::Error for XmssError {}

/// An XMSS key tree. Manages a binary Merkle tree of WOTS one-time key pairs.
///
/// The tree root serves as the public key. Signing consumes leaves sequentially;
/// each signature includes the Merkle authentication path from the used leaf to root.
#[derive(Clone, Debug)]
pub struct XmssTree {
    /// Tree height (h). The tree has 2^h leaves.
    height: usize,
    /// Master seed from which all leaf WOTS keys are derived.
    seed: [u8; 32],
    /// Index of the next unused leaf (0-based). Incremented after each signing.
    index: u64,
    /// Merkle tree root — the XMSS "public key".
    root: BabyBear,
}

/// An XMSS signature: WOTS signature + Merkle authentication path.
#[derive(Clone, Debug)]
pub struct XmssSignature {
    /// The one-time WOTS signature for this leaf.
    pub wots_signature: WotsSignature,
    /// The WOTS public key for this leaf (needed for verification).
    pub wots_public_key: WotsPublicKey,
    /// Which leaf index was used to produce this signature.
    pub leaf_index: u64,
    /// Merkle authentication path from the leaf to the root (h sibling hashes).
    pub auth_path: Vec<BabyBear>,
}

/// The XMSS public key: just the tree root and height.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct XmssPublicKey {
    /// The Merkle root of the XMSS tree.
    pub root: BabyBear,
    /// Tree height (determines number of available one-time keys: 2^height).
    pub height: usize,
}

// ============================================================================
// Key Derivation
// ============================================================================

/// Derive the WOTS seed for a specific leaf index from the master seed.
///
/// Uses BLAKE3 key derivation with a domain-separated context string.
fn derive_wots_seed(master_seed: &[u8; 32], index: u64) -> [u8; 32] {
    let mut input = [0u8; 40];
    input[..32].copy_from_slice(master_seed);
    input[32..40].copy_from_slice(&index.to_le_bytes());
    blake3::derive_key("dregg-xmss-leaf-v1", &input)
}

/// Generate the WOTS keypair for a specific leaf.
fn leaf_keypair(master_seed: &[u8; 32], index: u64) -> (WotsSecretKey, WotsPublicKey) {
    let seed = derive_wots_seed(master_seed, index);
    wots_keygen(&seed)
}

/// Compute the leaf hash (the Merkle leaf value) for a given leaf index.
///
/// This is the Poseidon2 hash of the WOTS public key's `pk_hash` — giving us a
/// single BabyBear element that represents the leaf in the Merkle tree.
fn compute_leaf(master_seed: &[u8; 32], index: u64) -> BabyBear {
    let (_, pk) = leaf_keypair(master_seed, index);
    pk.pk_hash
}

// ============================================================================
// Tree Construction
// ============================================================================

/// Compute a Merkle internal node from its two children using Poseidon2.
#[inline]
fn compute_node(left: BabyBear, right: BabyBear) -> BabyBear {
    poseidon2::hash_2_to_1(left, right)
}

/// Compute the root of the XMSS tree.
///
/// Builds the full binary Merkle tree bottom-up from all 2^height leaves.
fn compute_root(seed: &[u8; 32], height: usize) -> BabyBear {
    let num_leaves = 1u64 << height;

    // Build the leaf layer
    let mut layer: Vec<BabyBear> = (0..num_leaves).map(|i| compute_leaf(seed, i)).collect();

    // Hash layers bottom-up
    while layer.len() > 1 {
        let mut next = Vec::with_capacity(layer.len() / 2);
        for pair in layer.chunks_exact(2) {
            next.push(compute_node(pair[0], pair[1]));
        }
        layer = next;
    }

    layer[0]
}

/// Compute the Merkle authentication path for a given leaf index.
///
/// Returns h sibling hashes (one per tree level, bottom to top).
fn compute_auth_path(seed: &[u8; 32], height: usize, leaf_index: u64) -> Vec<BabyBear> {
    let num_leaves = 1u64 << height;

    // Build the full leaf layer
    let mut layer: Vec<BabyBear> = (0..num_leaves).map(|i| compute_leaf(seed, i)).collect();

    let mut path = Vec::with_capacity(height);
    let mut idx = leaf_index as usize;

    // At each level, record the sibling and then reduce the layer
    while layer.len() > 1 {
        let sibling_idx = idx ^ 1;
        path.push(layer[sibling_idx]);

        let mut next = Vec::with_capacity(layer.len() / 2);
        for pair in layer.chunks_exact(2) {
            next.push(compute_node(pair[0], pair[1]));
        }
        layer = next;
        idx /= 2;
    }

    path
}

// ============================================================================
// XMSS Tree Implementation
// ============================================================================

impl XmssTree {
    /// Create a new XMSS tree from a seed and desired height.
    ///
    /// Height determines the number of available one-time keys:
    /// - Height 10: 1024 signatures (~85 minutes at 5s blocks)
    /// - Height 15: 32768 signatures (~45 hours)
    /// - Height 20: 1048576 signatures (~58 days)
    ///
    /// Tree construction computes all 2^h leaves and builds the Merkle tree;
    /// for large heights this can be expensive (one-time cost at epoch start).
    pub fn new(seed: &[u8; 32], height: usize) -> Result<Self, XmssError> {
        if height == 0 || height > 30 {
            return Err(XmssError::InvalidHeight(height));
        }

        let root = compute_root(seed, height);

        Ok(Self {
            height,
            seed: *seed,
            index: 0,
            root,
        })
    }

    /// Get the public key for this XMSS tree.
    pub fn public_key(&self) -> XmssPublicKey {
        XmssPublicKey {
            root: self.root,
            height: self.height,
        }
    }

    /// Sign a message, consuming the next available leaf key.
    ///
    /// Returns an `XmssSignature` containing the WOTS signature plus the
    /// Merkle authentication path, or an error if all keys are exhausted.
    pub fn sign(&mut self, message: &[u8]) -> Result<XmssSignature, XmssError> {
        let max_leaves = 1u64 << self.height;
        if self.index >= max_leaves {
            return Err(XmssError::KeysExhausted);
        }

        let leaf_index = self.index;

        // Generate the WOTS keypair for this leaf
        let (sk, pk) = leaf_keypair(&self.seed, leaf_index);

        // Sign the message with the one-time key
        let wots_sig = wots_sign(&sk, message);

        // Compute the authentication path
        let auth_path = compute_auth_path(&self.seed, self.height, leaf_index);

        // Consume this leaf
        self.index += 1;

        Ok(XmssSignature {
            wots_signature: wots_sig,
            wots_public_key: pk,
            leaf_index,
            auth_path,
        })
    }

    /// Number of remaining unused signatures.
    pub fn remaining_signatures(&self) -> u64 {
        (1u64 << self.height) - self.index
    }

    /// Current leaf index (number of signatures issued so far).
    pub fn current_index(&self) -> u64 {
        self.index
    }

    /// Tree height.
    pub fn height(&self) -> usize {
        self.height
    }

    /// The tree root (public key).
    pub fn root(&self) -> BabyBear {
        self.root
    }
}

// ============================================================================
// Verification
// ============================================================================

/// Verify an XMSS signature against a public key and message.
///
/// Steps:
/// 1. Verify the WOTS signature to confirm the leaf key signed this message.
/// 2. Compute the leaf hash from the WOTS public key.
/// 3. Walk the authentication path from leaf to root.
/// 4. Check that the computed root matches the XMSS public key root.
pub fn xmss_verify(pk: &XmssPublicKey, message: &[u8], signature: &XmssSignature) -> bool {
    // 1. Verify WOTS signature
    if !wots_verify(
        &signature.wots_public_key,
        &signature.wots_signature,
        message,
    ) {
        return false;
    }

    // 2. Compute leaf hash from the WOTS public key
    let leaf_hash = signature.wots_public_key.pk_hash;

    // 3. Walk auth path from leaf to root
    if signature.auth_path.len() != pk.height {
        return false;
    }

    let mut current = leaf_hash;
    let mut idx = signature.leaf_index;

    for sibling in &signature.auth_path {
        if idx & 1 == 0 {
            current = compute_node(current, *sibling);
        } else {
            current = compute_node(*sibling, current);
        }
        idx >>= 1;
    }

    // 4. Check root
    current == pk.root
}

// ============================================================================
// Epoch Management
// ============================================================================

/// Create a new XMSS tree for a validator epoch.
///
/// Derives a per-epoch seed from the validator's long-term seed and the epoch number,
/// then constructs the XMSS tree. Each epoch gets an independent tree so that
/// key exhaustion in one epoch does not affect others.
///
/// Recommended heights:
/// - Height 15 for epoch-per-day (~45 hours of 5s blocks)
/// - Height 20 for month-long epochs (~58 days)
pub fn new_epoch_tree(
    validator_seed: &[u8; 32],
    epoch: u64,
    height: usize,
) -> Result<XmssTree, XmssError> {
    let mut input = [0u8; 40];
    input[..32].copy_from_slice(validator_seed);
    input[32..40].copy_from_slice(&epoch.to_le_bytes());
    let epoch_seed = blake3::derive_key("dregg-xmss-epoch-v1", &input);
    XmssTree::new(&epoch_seed, height)
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn keygen_sign_verify_basic() {
        let seed = [0x42u8; 32];
        let mut tree = XmssTree::new(&seed, 4).unwrap(); // 16 leaves
        let pk = tree.public_key();

        let msg = b"block header at slot 7";
        let sig = tree.sign(msg).unwrap();

        assert!(xmss_verify(&pk, msg, &sig));
    }

    #[test]
    fn sign_10_messages_verify_all() {
        let seed = [0xAB; 32];
        let mut tree = XmssTree::new(&seed, 4).unwrap(); // 16 leaves
        let pk = tree.public_key();

        let mut signatures = Vec::new();
        for i in 0..10 {
            let msg = format!("message number {i}");
            let sig = tree.sign(msg.as_bytes()).unwrap();
            signatures.push((msg, sig));
        }

        // Verify all
        for (msg, sig) in &signatures {
            assert!(
                xmss_verify(&pk, msg.as_bytes(), sig),
                "failed to verify message: {msg}"
            );
        }
    }

    #[test]
    fn exhausted_keys_returns_error() {
        let seed = [0x01; 32];
        let mut tree = XmssTree::new(&seed, 2).unwrap(); // 4 leaves only

        // Sign 4 messages (exhaust all leaves)
        for i in 0..4 {
            let msg = format!("msg {i}");
            tree.sign(msg.as_bytes()).unwrap();
        }

        // 5th should fail
        let result = tree.sign(b"one too many");
        assert_eq!(result.unwrap_err(), XmssError::KeysExhausted);
    }

    #[test]
    fn wrong_message_fails_verification() {
        let seed = [0x55; 32];
        let mut tree = XmssTree::new(&seed, 3).unwrap();
        let pk = tree.public_key();

        let sig = tree.sign(b"correct message").unwrap();
        assert!(!xmss_verify(&pk, b"wrong message", &sig));
    }

    #[test]
    fn wrong_auth_path_fails_verification() {
        let seed = [0x77; 32];
        let mut tree = XmssTree::new(&seed, 3).unwrap();
        let pk = tree.public_key();

        let mut sig = tree.sign(b"test").unwrap();
        // Corrupt one element of the auth path
        if let Some(first) = sig.auth_path.first_mut() {
            *first = *first + BabyBear::ONE;
        }
        assert!(!xmss_verify(&pk, b"test", &sig));
    }

    #[test]
    fn deterministic_same_seed_same_tree() {
        let seed = [0xCC; 32];
        let tree1 = XmssTree::new(&seed, 4).unwrap();
        let tree2 = XmssTree::new(&seed, 4).unwrap();

        assert_eq!(tree1.root(), tree2.root());
    }

    #[test]
    fn deterministic_same_signature() {
        let seed = [0xDD; 32];
        let mut tree1 = XmssTree::new(&seed, 3).unwrap();
        let mut tree2 = XmssTree::new(&seed, 3).unwrap();

        let msg = b"determinism test";
        let sig1 = tree1.sign(msg).unwrap();
        let sig2 = tree2.sign(msg).unwrap();

        // Same leaf index, same WOTS signature values
        assert_eq!(sig1.leaf_index, sig2.leaf_index);
        assert_eq!(
            sig1.wots_signature.chain_values,
            sig2.wots_signature.chain_values
        );
        assert_eq!(sig1.auth_path, sig2.auth_path);
    }

    #[test]
    fn remaining_signatures_decrements() {
        let seed = [0xEE; 32];
        let mut tree = XmssTree::new(&seed, 3).unwrap(); // 8 leaves

        assert_eq!(tree.remaining_signatures(), 8);
        tree.sign(b"a").unwrap();
        assert_eq!(tree.remaining_signatures(), 7);
        tree.sign(b"b").unwrap();
        assert_eq!(tree.remaining_signatures(), 6);
    }

    #[test]
    fn different_seeds_different_roots() {
        let tree1 = XmssTree::new(&[0x01; 32], 3).unwrap();
        let tree2 = XmssTree::new(&[0x02; 32], 3).unwrap();
        assert_ne!(tree1.root(), tree2.root());
    }

    #[test]
    fn epoch_trees_independent() {
        let validator_seed = [0xFF; 32];
        let tree_e0 = new_epoch_tree(&validator_seed, 0, 3).unwrap();
        let tree_e1 = new_epoch_tree(&validator_seed, 1, 3).unwrap();

        // Different epochs produce different roots
        assert_ne!(tree_e0.root(), tree_e1.root());
    }

    #[test]
    fn epoch_tree_deterministic() {
        let validator_seed = [0xAA; 32];
        let tree1 = new_epoch_tree(&validator_seed, 42, 3).unwrap();
        let tree2 = new_epoch_tree(&validator_seed, 42, 3).unwrap();
        assert_eq!(tree1.root(), tree2.root());
    }

    #[test]
    fn invalid_height_rejected() {
        assert_eq!(
            XmssTree::new(&[0; 32], 0).unwrap_err(),
            XmssError::InvalidHeight(0)
        );
        assert_eq!(
            XmssTree::new(&[0; 32], 31).unwrap_err(),
            XmssError::InvalidHeight(31)
        );
    }

    #[test]
    fn cross_tree_signature_rejected() {
        let mut tree_a = XmssTree::new(&[0x11; 32], 3).unwrap();
        let tree_b = XmssTree::new(&[0x22; 32], 3).unwrap();
        let pk_b = tree_b.public_key();

        let sig = tree_a.sign(b"hello").unwrap();
        // Signature from tree_a should not verify against tree_b's public key
        assert!(!xmss_verify(&pk_b, b"hello", &sig));
    }

    #[test]
    fn leaf_index_in_signature_matches() {
        let seed = [0x99; 32];
        let mut tree = XmssTree::new(&seed, 3).unwrap();

        for expected_idx in 0..5u64 {
            let sig = tree.sign(b"x").unwrap();
            assert_eq!(sig.leaf_index, expected_idx);
        }
    }

    #[test]
    fn auth_path_length_matches_height() {
        for height in 2..=5 {
            let mut tree = XmssTree::new(&[height as u8; 32], height).unwrap();
            let sig = tree.sign(b"check path len").unwrap();
            assert_eq!(sig.auth_path.len(), height);
        }
    }
}
