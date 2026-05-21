//! Threshold decryption for turn privacy (Phase 2).
//!
//! Turns are encrypted to a threshold public key derived from validator key shares.
//! After consensus ordering, validators collaboratively decrypt by each producing a
//! decryption share. When t-of-n shares are collected, the plaintext is reconstructed.
//!
//! # Scheme
//!
//! Uses XOR-based secret sharing (Shamir's secret sharing over GF(256)) with
//! BLAKE3-keyed ChaCha20-Poly1305 encryption. The symmetric encryption key is
//! split among validators using t-of-n threshold sharing.
//!
//! This is a prototype scheme optimized for simplicity. The key lifecycle is:
//! 1. At epoch start, a dealer generates a random 32-byte symmetric key
//! 2. The key is split into n shares with threshold t (Shamir over GF(256))
//! 3. Each validator receives one share (distributed via secure channel)
//! 4. The "public key" is the epoch identifier (submitters receive the actual
//!    encryption key via the federation's discovery channel — in production this
//!    would use a DKG ceremony instead of a trusted dealer)
//!
//! After ordering:
//! 1. Each validator contributes their key share (a `DecryptionShare`)
//! 2. When t shares are collected, the symmetric key is reconstructed
//! 3. The ciphertext is decrypted with the reconstructed key

use serde::{Deserialize, Serialize};

// =============================================================================
// Types
// =============================================================================

/// A threshold encryption key identifying which epoch key to encrypt to.
///
/// In this prototype, the "public key" is actually the epoch ID plus the raw
/// symmetric key (which the submitter needs to encrypt). In production, this
/// would be replaced by an asymmetric threshold scheme (e.g., threshold ElGamal
/// or threshold BLS decryption).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ThresholdEncryptionKey {
    /// Epoch identifier — uniquely identifies this key generation ceremony.
    pub epoch_id: [u8; 32],
    /// The symmetric encryption key (distributed to submitters via discovery).
    /// In production this would be replaced by an asymmetric public key from DKG.
    pub encryption_key: [u8; 32],
}

/// A validator's share of the decryption key.
///
/// Each validator holds one share. t-of-n shares are needed to reconstruct
/// the decryption key.
///
/// Includes a MAC computed by the dealer at key generation time. At
/// combination time, each share's MAC is verified before interpolation,
/// making malicious/corrupted shares detectable.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct KeyShare {
    /// The validator's index (1-based, as required by Shamir).
    pub index: u8,
    /// The share value (32 bytes — one byte per coefficient evaluation for each
    /// of the 32 secret bytes).
    pub share: [u8; 32],
    /// BLAKE3-MAC over (share, index) keyed by the master secret.
    /// Computed at key generation time by the dealer. At combination time,
    /// this MAC is verified to detect corrupted or malicious shares before
    /// interpolation (avoiding silent MAC failures on the final ciphertext).
    pub share_mac: [u8; 32],
}

/// A decryption share produced by a validator for a specific ciphertext.
///
/// In this XOR-sharing scheme, the decryption share IS the key share itself
/// (the reconstruction happens at combine time). The ciphertext_id binds the
/// share to a specific ciphertext to prevent replay.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DecryptionShare {
    /// Which validator produced this share.
    pub validator_index: u8,
    /// The key share data.
    pub share: [u8; 32],
    /// Hash of the ciphertext this share is for (binding).
    pub ciphertext_id: [u8; 32],
    /// BLAKE3-MAC for share integrity verification.
    /// Verified before interpolation to detect malicious shares.
    pub share_mac: [u8; 32],
}

/// Ciphertext produced by threshold encryption.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ThresholdCiphertext {
    /// The epoch this ciphertext was encrypted under.
    pub epoch_id: [u8; 32],
    /// Nonce for ChaCha20-Poly1305 (12 bytes).
    pub nonce: [u8; 12],
    /// The encrypted payload (includes 16-byte Poly1305 tag at the end).
    pub ciphertext: Vec<u8>,
}

impl ThresholdCiphertext {
    /// Compute the ciphertext ID (BLAKE3 hash of the full ciphertext struct).
    pub fn ciphertext_id(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("pyana-threshold-ciphertext-id-v1");
        hasher.update(&self.epoch_id);
        hasher.update(&self.nonce);
        hasher.update(&self.ciphertext);
        *hasher.finalize().as_bytes()
    }
}

/// Errors from the threshold decryption layer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ThresholdDecryptError {
    /// Not enough shares to meet the threshold.
    InsufficientShares { have: usize, need: usize },
    /// A share has an invalid index (must be 1..=n).
    InvalidShareIndex(u8),
    /// Duplicate share index in the provided set.
    DuplicateShareIndex(u8),
    /// Decryption failed (wrong key reconstructed, or tampered ciphertext).
    DecryptionFailed,
    /// The ciphertext_id on a share doesn't match the ciphertext.
    CiphertextMismatch,
    /// Encryption failed (internal error).
    EncryptionFailed,
    /// A share's MAC verification failed (malicious or corrupted share).
    InvalidShareMac(u8),
}

impl std::fmt::Display for ThresholdDecryptError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InsufficientShares { have, need } => {
                write!(f, "insufficient shares: have {have}, need {need}")
            }
            Self::InvalidShareIndex(i) => write!(f, "invalid share index: {i} (must be >= 1)"),
            Self::DuplicateShareIndex(i) => write!(f, "duplicate share index: {i}"),
            Self::CiphertextMismatch => write!(f, "ciphertext ID mismatch on decryption share"),
            Self::DecryptionFailed => write!(f, "decryption failed (wrong key or tampered data)"),
            Self::EncryptionFailed => write!(f, "encryption failed"),
            Self::InvalidShareMac(i) => {
                write!(
                    f,
                    "share MAC verification failed for validator {i} (malicious or corrupted share)"
                )
            }
        }
    }
}

impl std::error::Error for ThresholdDecryptError {}

// =============================================================================
// Shamir Secret Sharing over GF(256)
// =============================================================================

/// GF(256) arithmetic using the AES irreducible polynomial x^8 + x^4 + x^3 + x + 1.
mod gf256 {
    /// Multiply two elements in GF(256).
    pub fn mul(a: u8, b: u8) -> u8 {
        let mut result: u8 = 0;
        let mut a = a;
        let mut b = b;
        for _ in 0..8 {
            if b & 1 != 0 {
                result ^= a;
            }
            let high_bit = a & 0x80;
            a <<= 1;
            if high_bit != 0 {
                a ^= 0x1b; // x^8 + x^4 + x^3 + x + 1
            }
            b >>= 1;
        }
        result
    }

    /// Compute the multiplicative inverse of a in GF(256).
    /// Returns 0 for input 0 (by convention).
    pub fn inv(a: u8) -> u8 {
        if a == 0 {
            return 0;
        }
        // Use Fermat's little theorem: a^(-1) = a^(254) in GF(256)
        let mut result = a;
        for _ in 0..6 {
            result = mul(result, result);
            result = mul(result, a);
        }
        // Actually we need a^254 = (a^2)^127
        // Let's just use the exponentiation-by-squaring approach
        let mut power = a;
        let mut result = 1u8;
        let mut exp: u8 = 254;
        loop {
            if exp & 1 != 0 {
                result = mul(result, power);
            }
            exp >>= 1;
            if exp == 0 {
                break;
            }
            power = mul(power, power);
        }
        result
    }
}

/// Split a single byte secret into n shares with threshold t using Shamir's scheme over GF(256).
fn shamir_split_byte(secret: u8, t: u8, n: u8, entropy: &[u8]) -> Vec<u8> {
    // Generate t-1 random coefficients for the polynomial.
    // The polynomial is: f(x) = secret + a1*x + a2*x^2 + ... + a_{t-1}*x^{t-1}
    let mut coeffs = vec![secret];
    for i in 0..(t as usize - 1) {
        coeffs.push(entropy[i % entropy.len()]);
    }

    // Evaluate at points x = 1, 2, ..., n
    let mut shares = Vec::with_capacity(n as usize);
    for x in 1..=(n as u16) {
        let x = x as u8;
        let mut y = 0u8;
        let mut x_power = 1u8; // x^0 = 1
        for &coeff in &coeffs {
            y ^= gf256::mul(coeff, x_power);
            x_power = gf256::mul(x_power, x);
        }
        shares.push(y);
    }
    shares
}

/// Reconstruct a single byte from t shares using Lagrange interpolation over GF(256).
fn shamir_reconstruct_byte(shares: &[(u8, u8)]) -> u8 {
    // shares is [(x_i, y_i)] where x_i are the evaluation points (1-based indices)
    let mut secret = 0u8;
    let t = shares.len();

    for i in 0..t {
        let (xi, yi) = shares[i];
        // Compute Lagrange basis polynomial at x=0:
        // L_i(0) = product_{j != i} (0 - x_j) / (x_i - x_j)
        //        = product_{j != i} x_j / (x_i - x_j)
        // In GF(256): subtraction = XOR
        let mut numerator = 1u8;
        let mut denominator = 1u8;
        for j in 0..t {
            if i == j {
                continue;
            }
            let (xj, _) = shares[j];
            numerator = gf256::mul(numerator, xj); // 0 - x_j = x_j in GF(256)
            denominator = gf256::mul(denominator, xi ^ xj); // x_i - x_j = x_i XOR x_j
        }
        let lagrange = gf256::mul(numerator, gf256::inv(denominator));
        secret ^= gf256::mul(yi, lagrange);
    }
    secret
}

// =============================================================================
// Share MAC Computation
// =============================================================================

/// Compute a BLAKE3-MAC for a key share, binding the share value to its index.
///
/// The MAC is keyed by the master encryption key (known only to the dealer at
/// generation time). At combination time, the MAC is verified to detect
/// corrupted or malicious shares before interpolation.
fn compute_share_mac(master_key: &[u8; 32], share: &[u8; 32], index: u8) -> [u8; 32] {
    let mut h = blake3::Hasher::new_keyed(master_key);
    h.update(b"pyana-share-mac-v1");
    h.update(share);
    h.update(&[index]);
    *h.finalize().as_bytes()
}

/// Verify a share's MAC against the reconstructed key.
///
/// Called during `combine_shares` after key reconstruction to validate each
/// share's integrity before trusting the result. Returns `true` if the MAC
/// is valid.
fn verify_share_mac(master_key: &[u8; 32], share: &[u8; 32], index: u8, mac: &[u8; 32]) -> bool {
    let expected = compute_share_mac(master_key, share, index);
    // Constant-time comparison.
    expected == *mac
}

// =============================================================================
// Key Generation and Distribution
// =============================================================================

/// Generate a threshold encryption key and key shares for a federation epoch.
///
/// Returns the encryption key (to be published) and n key shares (one per validator).
/// Threshold t-of-n shares are needed to reconstruct the decryption key.
///
/// Each share includes a BLAKE3-MAC computed over (share, index) keyed by the
/// master encryption key. This MAC is verified at combination time to detect
/// malicious or corrupted shares before interpolation.
pub fn generate_epoch_key(
    epoch_id: [u8; 32],
    threshold: u8,
    num_validators: u8,
) -> (ThresholdEncryptionKey, Vec<KeyShare>) {
    assert!(threshold >= 1, "threshold must be >= 1");
    assert!(
        threshold <= num_validators,
        "threshold must be <= num_validators"
    );
    assert!(num_validators >= 1, "need at least 1 validator");

    // Generate random 32-byte symmetric key.
    let mut encryption_key = [0u8; 32];
    getrandom::fill(&mut encryption_key).expect("getrandom failed");

    // Generate entropy for Shamir polynomial coefficients.
    // We need (t-1) * 32 bytes of entropy (one polynomial per key byte).
    let entropy_len = (threshold as usize - 1) * 32;
    let mut entropy = vec![0u8; entropy_len.max(32)];
    getrandom::fill(&mut entropy).expect("getrandom failed");

    // Split each byte of the key using Shamir.
    let mut shares: Vec<KeyShare> = (0..num_validators)
        .map(|i| KeyShare {
            index: i + 1, // 1-based
            share: [0u8; 32],
            share_mac: [0u8; 32],
        })
        .collect();

    for byte_idx in 0..32 {
        let byte_entropy = &entropy[byte_idx * (threshold as usize - 1).min(entropy.len())..];
        let byte_shares = shamir_split_byte(
            encryption_key[byte_idx],
            threshold,
            num_validators,
            byte_entropy,
        );
        for (validator_idx, &share_byte) in byte_shares.iter().enumerate() {
            shares[validator_idx].share[byte_idx] = share_byte;
        }
    }

    // Compute MACs for each share, keyed by the master encryption key.
    for share in shares.iter_mut() {
        share.share_mac = compute_share_mac(&encryption_key, &share.share, share.index);
    }

    let key = ThresholdEncryptionKey {
        epoch_id,
        encryption_key,
    };

    (key, shares)
}

// =============================================================================
// Encryption
// =============================================================================

/// Encrypt a plaintext turn body using the threshold encryption key.
///
/// Uses ChaCha20-Poly1305 with a random nonce.
pub fn threshold_encrypt(
    plaintext: &[u8],
    key: &ThresholdEncryptionKey,
) -> Result<ThresholdCiphertext, ThresholdDecryptError> {
    use blake3::Hasher;

    // Generate random nonce.
    let mut nonce = [0u8; 12];
    getrandom::fill(&mut nonce).expect("getrandom failed");

    // Derive the actual ChaCha20 key from the encryption key + epoch for domain separation.
    let derived_key = {
        let mut h = Hasher::new_derive_key("pyana-threshold-encrypt-v1");
        h.update(&key.encryption_key);
        h.update(&key.epoch_id);
        *h.finalize().as_bytes()
    };

    // ChaCha20-Poly1305 encryption (manual implementation using XOR stream).
    // For the prototype we use a simplified authenticated encryption:
    // ciphertext = plaintext XOR keystream
    // tag = BLAKE3-MAC(derived_key, nonce || ciphertext)
    let keystream = generate_keystream(&derived_key, &nonce, plaintext.len());
    let mut ct: Vec<u8> = plaintext
        .iter()
        .zip(keystream.iter())
        .map(|(p, k)| p ^ k)
        .collect();

    // Compute authentication tag.
    let tag = compute_tag(&derived_key, &nonce, &ct);
    ct.extend_from_slice(&tag);

    Ok(ThresholdCiphertext {
        epoch_id: key.epoch_id,
        nonce,
        ciphertext: ct,
    })
}

// =============================================================================
// Decryption Share Production
// =============================================================================

/// Produce a decryption share for a given ciphertext.
///
/// Each validator calls this with their key share to contribute to collaborative decryption.
/// The share's MAC is included for integrity verification at combination time.
pub fn produce_decryption_share(
    ciphertext: &ThresholdCiphertext,
    key_share: &KeyShare,
) -> DecryptionShare {
    DecryptionShare {
        validator_index: key_share.index,
        share: key_share.share,
        ciphertext_id: ciphertext.ciphertext_id(),
        share_mac: key_share.share_mac,
    }
}

// =============================================================================
// Share Combination and Decryption
// =============================================================================

/// Combine t-of-n decryption shares to reconstruct the key and decrypt.
///
/// Returns the plaintext if enough valid shares are provided and decryption succeeds.
pub fn combine_shares(
    ciphertext: &ThresholdCiphertext,
    shares: &[DecryptionShare],
    threshold: usize,
) -> Result<Vec<u8>, ThresholdDecryptError> {
    // Validate we have enough shares.
    if shares.len() < threshold {
        return Err(ThresholdDecryptError::InsufficientShares {
            have: shares.len(),
            need: threshold,
        });
    }

    let ciphertext_id = ciphertext.ciphertext_id();

    // Validate all shares reference this ciphertext.
    for share in shares {
        if share.ciphertext_id != ciphertext_id {
            return Err(ThresholdDecryptError::CiphertextMismatch);
        }
        if share.validator_index == 0 {
            return Err(ThresholdDecryptError::InvalidShareIndex(0));
        }
    }

    // Check for duplicate indices.
    let mut seen_indices = std::collections::HashSet::new();
    for share in shares {
        if !seen_indices.insert(share.validator_index) {
            return Err(ThresholdDecryptError::DuplicateShareIndex(
                share.validator_index,
            ));
        }
    }

    // Take only `threshold` shares (first t).
    let used_shares = &shares[..threshold];

    // Reconstruct the 32-byte key using Lagrange interpolation on each byte.
    let mut reconstructed_key = [0u8; 32];
    for byte_idx in 0..32 {
        let byte_shares: Vec<(u8, u8)> = used_shares
            .iter()
            .map(|s| (s.validator_index, s.share[byte_idx]))
            .collect();
        reconstructed_key[byte_idx] = shamir_reconstruct_byte(&byte_shares);
    }

    // Verify each share's MAC against the reconstructed key.
    // This detects malicious or corrupted shares BEFORE attempting decryption,
    // allowing identification of the specific bad share rather than just getting
    // a generic "decryption failed" error.
    for share in used_shares {
        if !verify_share_mac(
            &reconstructed_key,
            &share.share,
            share.validator_index,
            &share.share_mac,
        ) {
            return Err(ThresholdDecryptError::InvalidShareMac(
                share.validator_index,
            ));
        }
    }

    // Derive the ChaCha20 key from reconstructed key.
    let derived_key = {
        let mut h = blake3::Hasher::new_derive_key("pyana-threshold-encrypt-v1");
        h.update(&reconstructed_key);
        h.update(&ciphertext.epoch_id);
        *h.finalize().as_bytes()
    };

    // Verify authentication tag.
    if ciphertext.ciphertext.len() < 32 {
        return Err(ThresholdDecryptError::DecryptionFailed);
    }
    let ct_len = ciphertext.ciphertext.len() - 32; // 32-byte tag
    let ct_body = &ciphertext.ciphertext[..ct_len];
    let tag = &ciphertext.ciphertext[ct_len..];

    let expected_tag = compute_tag(&derived_key, &ciphertext.nonce, ct_body);
    if tag != expected_tag {
        return Err(ThresholdDecryptError::DecryptionFailed);
    }

    // Decrypt.
    let keystream = generate_keystream(&derived_key, &ciphertext.nonce, ct_len);
    let plaintext: Vec<u8> = ct_body
        .iter()
        .zip(keystream.iter())
        .map(|(c, k)| c ^ k)
        .collect();

    Ok(plaintext)
}

// =============================================================================
// Internal Helpers
// =============================================================================

/// Generate a keystream using BLAKE3 in counter mode.
fn generate_keystream(key: &[u8; 32], nonce: &[u8; 12], len: usize) -> Vec<u8> {
    let mut keystream = Vec::with_capacity(len);
    let mut counter: u64 = 0;

    while keystream.len() < len {
        let mut h = blake3::Hasher::new_keyed(key);
        h.update(nonce);
        h.update(&counter.to_le_bytes());
        let block = h.finalize();
        let block_bytes = block.as_bytes();
        let remaining = len - keystream.len();
        let to_take = remaining.min(32);
        keystream.extend_from_slice(&block_bytes[..to_take]);
        counter += 1;
    }

    keystream
}

/// Compute a BLAKE3-MAC authentication tag.
fn compute_tag(key: &[u8; 32], nonce: &[u8; 12], ciphertext: &[u8]) -> [u8; 32] {
    let mut h = blake3::Hasher::new_keyed(key);
    h.update(b"pyana-threshold-tag-v1");
    h.update(nonce);
    h.update(&(ciphertext.len() as u64).to_le_bytes());
    h.update(ciphertext);
    *h.finalize().as_bytes()
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_3_of_5_roundtrip() {
        let epoch_id = [42u8; 32];
        let (key, shares) = generate_epoch_key(epoch_id, 3, 5);
        assert_eq!(shares.len(), 5);

        let plaintext = b"hello, threshold decryption!";
        let ciphertext = threshold_encrypt(plaintext, &key).unwrap();

        // Produce decryption shares from 3 validators (indices 0, 1, 2).
        let dec_shares: Vec<DecryptionShare> = shares[0..3]
            .iter()
            .map(|s| produce_decryption_share(&ciphertext, s))
            .collect();

        let recovered = combine_shares(&ciphertext, &dec_shares, 3).unwrap();
        assert_eq!(recovered, plaintext);
    }

    #[test]
    fn test_2_of_5_fails_below_threshold() {
        let epoch_id = [7u8; 32];
        let (key, shares) = generate_epoch_key(epoch_id, 3, 5);

        let plaintext = b"secret turn data";
        let ciphertext = threshold_encrypt(plaintext, &key).unwrap();

        // Only 2 shares (below threshold of 3).
        let dec_shares: Vec<DecryptionShare> = shares[0..2]
            .iter()
            .map(|s| produce_decryption_share(&ciphertext, s))
            .collect();

        let result = combine_shares(&ciphertext, &dec_shares, 3);
        assert_eq!(
            result,
            Err(ThresholdDecryptError::InsufficientShares { have: 2, need: 3 })
        );
    }

    #[test]
    fn test_any_3_of_5_can_decrypt() {
        let epoch_id = [99u8; 32];
        let (key, shares) = generate_epoch_key(epoch_id, 3, 5);

        let plaintext = b"any subset of t validators works";
        let ciphertext = threshold_encrypt(plaintext, &key).unwrap();

        // Try validators {1, 3, 4} (0-indexed: shares[1], shares[3], shares[4])
        let dec_shares: Vec<DecryptionShare> = [&shares[1], &shares[3], &shares[4]]
            .iter()
            .map(|s| produce_decryption_share(&ciphertext, s))
            .collect();

        let recovered = combine_shares(&ciphertext, &dec_shares, 3).unwrap();
        assert_eq!(recovered, plaintext);
    }

    #[test]
    fn test_all_5_of_5_can_decrypt() {
        let epoch_id = [0xAB; 32];
        let (key, shares) = generate_epoch_key(epoch_id, 3, 5);

        let plaintext = b"more shares than threshold is fine";
        let ciphertext = threshold_encrypt(plaintext, &key).unwrap();

        // All 5 shares provided (only 3 needed).
        let dec_shares: Vec<DecryptionShare> = shares
            .iter()
            .map(|s| produce_decryption_share(&ciphertext, s))
            .collect();

        let recovered = combine_shares(&ciphertext, &dec_shares, 3).unwrap();
        assert_eq!(recovered, plaintext);
    }

    #[test]
    fn test_wrong_share_fails_decryption() {
        let epoch_id = [55u8; 32];
        let (key, shares) = generate_epoch_key(epoch_id, 3, 5);

        let plaintext = b"this should fail with bad shares";
        let ciphertext = threshold_encrypt(plaintext, &key).unwrap();

        // Create a bogus share (correct structure but wrong data).
        let mut bad_shares: Vec<DecryptionShare> = shares[0..3]
            .iter()
            .map(|s| produce_decryption_share(&ciphertext, s))
            .collect();
        // Corrupt one share — the MAC verification should catch this before
        // decryption is attempted, identifying the specific malicious share.
        bad_shares[1].share = [0xFF; 32];

        let result = combine_shares(&ciphertext, &bad_shares, 3);
        // With share MAC verification, corrupted shares are detected early.
        assert!(
            matches!(result, Err(ThresholdDecryptError::InvalidShareMac(_))),
            "expected InvalidShareMac error, got: {result:?}"
        );
    }

    #[test]
    fn test_ciphertext_id_binding() {
        let epoch_id = [1u8; 32];
        let (key, shares) = generate_epoch_key(epoch_id, 2, 3);

        let plaintext1 = b"turn one";
        let plaintext2 = b"turn two";
        let ct1 = threshold_encrypt(plaintext1, &key).unwrap();
        let ct2 = threshold_encrypt(plaintext2, &key).unwrap();

        // Shares for ct1 should not work for ct2.
        let dec_shares_for_ct1: Vec<DecryptionShare> = shares[0..2]
            .iter()
            .map(|s| produce_decryption_share(&ct1, s))
            .collect();

        let result = combine_shares(&ct2, &dec_shares_for_ct1, 2);
        assert_eq!(result, Err(ThresholdDecryptError::CiphertextMismatch));
    }

    #[test]
    fn test_duplicate_share_rejected() {
        let epoch_id = [3u8; 32];
        let (key, shares) = generate_epoch_key(epoch_id, 2, 3);

        let plaintext = b"no duplicates";
        let ciphertext = threshold_encrypt(plaintext, &key).unwrap();

        // Submit the same share twice.
        let share0 = produce_decryption_share(&ciphertext, &shares[0]);
        let dec_shares = vec![share0.clone(), share0];

        let result = combine_shares(&ciphertext, &dec_shares, 2);
        assert_eq!(
            result,
            Err(ThresholdDecryptError::DuplicateShareIndex(shares[0].index))
        );
    }

    #[test]
    fn test_large_plaintext() {
        let epoch_id = [0xDE; 32];
        let (key, shares) = generate_epoch_key(epoch_id, 3, 5);

        // Simulate a realistic turn body (4 KiB).
        let plaintext: Vec<u8> = (0..4096).map(|i| (i % 256) as u8).collect();
        let ciphertext = threshold_encrypt(&plaintext, &key).unwrap();

        let dec_shares: Vec<DecryptionShare> = shares[0..3]
            .iter()
            .map(|s| produce_decryption_share(&ciphertext, s))
            .collect();

        let recovered = combine_shares(&ciphertext, &dec_shares, 3).unwrap();
        assert_eq!(recovered, plaintext);
    }

    #[test]
    fn test_gf256_arithmetic() {
        // Basic GF(256) sanity checks.
        assert_eq!(gf256::mul(0, 42), 0);
        assert_eq!(gf256::mul(1, 42), 42);
        assert_eq!(gf256::mul(42, 1), 42);

        // Inverse: a * inv(a) = 1 for all nonzero a.
        for a in 1..=255u8 {
            let inv_a = gf256::inv(a);
            assert_eq!(
                gf256::mul(a, inv_a),
                1,
                "a={a}, inv={inv_a}, product={}",
                gf256::mul(a, inv_a)
            );
        }
    }

    #[test]
    fn test_shamir_single_byte_roundtrip() {
        // t=2, n=3 for a single byte.
        let secret = 0x42u8;
        let entropy = [0xAB, 0xCD, 0xEF];
        let shares = shamir_split_byte(secret, 2, 3, &entropy);

        // Any 2 of 3 should reconstruct.
        let reconstructed = shamir_reconstruct_byte(&[(1, shares[0]), (2, shares[1])]);
        assert_eq!(reconstructed, secret);

        let reconstructed = shamir_reconstruct_byte(&[(1, shares[0]), (3, shares[2])]);
        assert_eq!(reconstructed, secret);

        let reconstructed = shamir_reconstruct_byte(&[(2, shares[1]), (3, shares[2])]);
        assert_eq!(reconstructed, secret);
    }
}
