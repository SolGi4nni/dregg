//! 1-of-2 Oblivious Transfer from X25519 Diffie-Hellman (Chou-Orlandi construction).
//!
//! # Protocol
//!
//! Sender has messages (m0, m1). Receiver has choice bit b.
//! After the protocol: receiver learns m_b, sender learns nothing about b.
//!
//! 1. Sender generates keypair: `(a, A = a*G)`, sends A to receiver
//! 2. Receiver generates keypair `(b_key, B)`:
//!    - If choice=0: `B = b_key * G`
//!    - If choice=1: `B = A + b_key * G`
//! 3. Receiver sends B to sender
//! 4. Sender computes:
//!    - `k0 = kdf(a * B)` — key for message 0
//!    - `k1 = kdf(a * (B - A))` — key for message 1
//! 5. Sender encrypts: `e0 = Enc(k0, m0)`, `e1 = Enc(k1, m1)`, sends both
//! 6. Receiver computes:
//!    - `k_b = kdf(b_key * A)` — equals k0 if choice=0, k1 if choice=1
//!    - Decrypts `e_b` with `k_b`
//!
//! # Security
//!
//! Under DDH on Curve25519, the sender cannot distinguish B (choice=0) from
//! A-offset (choice=1). The receiver can only compute one of the two DH shared
//! secrets, so they learn exactly one message.
//!
//! # Malicious-model scope (honest statement)
//!
//! This is Chou-Orlandi 1-of-2 OT hardened with point validation and transcript
//! binding, NOT a full UC / simulation-secure maliciously-secure OT:
//!
//! - **Point validation (both sides).** The receiver rejects a sender point `A`
//!   and the sender rejects a receiver point `B` that is the identity or carries
//!   any torsion component (`is_torsion_free`). This closes two leaks a bare
//!   construction has: (i) a malicious sender sending `A = P' + T` (T a torsion
//!   point) would echo `T` into `B = A + b·G` on choice=1 but not into
//!   `B = b·G` on choice=0, so testing `is_torsion_free(B)` would reveal the
//!   choice bit; and (ii) `is_small_order()` alone MISSES mixed-order points
//!   (prime-order + small-order), a selective-failure leak of a `(mod 8)` on the
//!   choice bit.
//! - **Transcript binding.** The per-message key is `kdf(DH_point, A, B)` — bound
//!   to the full transcript `(A, B)`, not just the raw DH point — so a key cannot
//!   be replayed under a different transcript.
//!
//! What this does NOT provide: there is no extractable proof that the sender's
//! `A` was honestly sampled (a random-oracle / Fiat-Shamir consistency argument),
//! and no commitment forcing the receiver to fix its choice before it sees the
//! ciphertexts. Against a fully malicious counterparty the guarantee is input
//! privacy plus the validated-point / bound-transcript hardening above, not
//! simulation-based malicious security. A UC-secure upgrade (the Chou-Orlandi RO
//! proof with the sender-side consistency check, or a committed-OT wrapper) is a
//! protocol change beyond this validation layer.
//!
//! # Implementation notes
//!
//! We work in Edwards form (`EdwardsPoint`) for point addition/subtraction,
//! but use the same underlying Curve25519. Key derivation uses BLAKE3 and
//! encryption uses ChaCha20-Poly1305, consistent with `seal.rs`.

use curve25519_dalek::constants::ED25519_BASEPOINT_TABLE;
use curve25519_dalek::edwards::EdwardsPoint;
use curve25519_dalek::scalar::Scalar;

/// First message from sender to receiver: the sender's public key.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OtSenderSetup {
    /// Sender's public point A = a*G (compressed Edwards Y coordinate).
    pub sender_public: [u8; 32],
}

/// Message from receiver to sender: the receiver's (possibly offset) public key.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OtReceiverResponse {
    /// Receiver's public point B (compressed Edwards Y coordinate).
    pub receiver_public: [u8; 32],
}

/// Second message from sender to receiver: both encrypted messages.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OtSenderPayload {
    /// ChaCha20-Poly1305 encrypted m0 (under k0).
    pub encrypted_m0: Vec<u8>,
    /// ChaCha20-Poly1305 encrypted m1 (under k1).
    pub encrypted_m1: Vec<u8>,
}

/// The sender's state in the OT protocol.
pub struct OtSender {
    /// Sender's secret scalar a.
    secret: Scalar,
    /// Sender's public point A = a*G.
    public: EdwardsPoint,
}

/// The receiver's state in the OT protocol.
pub struct OtReceiver {
    /// The receiver's choice bit.
    choice: bool,
    /// Receiver's secret scalar b_key.
    secret: Scalar,
    /// Sender's public point A (needed to derive the shared key).
    sender_public: EdwardsPoint,
    /// Receiver's own public point B, retained so the key derivation can bind
    /// the full transcript `(A, B)` — matching the sender, who also binds both.
    receiver_public: EdwardsPoint,
}

/// Errors that can occur during oblivious transfer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OtError {
    /// The sender's public key could not be decompressed to a valid curve point.
    InvalidSenderPublic,
    /// The receiver's public key could not be decompressed to a valid curve point.
    InvalidReceiverPublic,
    /// The receiver's public key is a small-order point (cofactor attack).
    InvalidReceiverPoint,
    /// Decryption of the chosen message failed (corrupted ciphertext or wrong key).
    DecryptionFailed,
}

impl core::fmt::Display for OtError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            OtError::InvalidSenderPublic => write!(f, "invalid sender public key"),
            OtError::InvalidReceiverPublic => write!(f, "invalid receiver public key"),
            OtError::InvalidReceiverPoint => {
                write!(f, "receiver public key is a small-order point")
            }
            OtError::DecryptionFailed => write!(f, "OT decryption failed"),
        }
    }
}

impl std::error::Error for OtError {}

impl OtSender {
    /// Step 1: Sender generates a keypair and produces the setup message.
    pub fn new() -> (Self, OtSenderSetup) {
        let secret = random_scalar();
        let public = &secret * ED25519_BASEPOINT_TABLE;
        let setup = OtSenderSetup {
            sender_public: compress_point(&public),
        };
        (OtSender { secret, public }, setup)
    }

    /// Step 4-5: Sender receives B from receiver, derives both keys, encrypts both messages.
    pub fn encrypt(
        &self,
        receiver_msg: &OtReceiverResponse,
        m0: &[u8],
        m1: &[u8],
    ) -> Result<OtSenderPayload, OtError> {
        use curve25519_dalek::traits::IsIdentity;

        let b_point = decompress_point(&receiver_msg.receiver_public)
            .ok_or(OtError::InvalidReceiverPublic)?;

        // Reject the identity AND any point carrying a torsion component.
        // `is_small_order()` alone missed mixed-order points (a small-order
        // component added to a prime-order point): those pass `is_small_order()`
        // yet still make the DH shared secret partially predictable — a
        // selective-failure leak of a `(mod 8)` on the receiver's choice bit.
        // `is_torsion_free()` rejects that whole class (identity is handled
        // separately, as it is trivially torsion-free).
        if b_point.is_identity() || !b_point.is_torsion_free() {
            return Err(OtError::InvalidReceiverPoint);
        }

        // Bind the full transcript (A, B) into every derived key (see
        // `derive_ot_key`). Use canonical compressed encodings on both sides so
        // the sender and receiver agree byte-for-byte.
        let a_bytes = compress_point(&self.public);
        let b_bytes = compress_point(&b_point);

        // k0 = kdf(a * B, A, B)
        let shared0 = self.secret * b_point;
        let k0 = derive_ot_key(&compress_point(&shared0), &a_bytes, &b_bytes);

        // k1 = kdf(a * (B - A), A, B)
        let b_minus_a = b_point - self.public;
        let shared1 = self.secret * b_minus_a;
        let k1 = derive_ot_key(&compress_point(&shared1), &a_bytes, &b_bytes);

        let encrypted_m0 = encrypt_message(&k0, m0);
        let encrypted_m1 = encrypt_message(&k1, m1);

        Ok(OtSenderPayload {
            encrypted_m0,
            encrypted_m1,
        })
    }
}

impl OtReceiver {
    /// Step 2-3: Receiver generates keypair with embedded choice, produces response message.
    ///
    /// - If choice=false (0): `B = b_key * G`
    /// - If choice=true  (1): `B = A + b_key * G`
    pub fn new(
        choice: bool,
        sender_msg: &OtSenderSetup,
    ) -> Result<(Self, OtReceiverResponse), OtError> {
        use curve25519_dalek::traits::IsIdentity;

        let sender_public =
            decompress_point(&sender_msg.sender_public).ok_or(OtError::InvalidSenderPublic)?;

        // Validate the sender's point A: reject the identity and any point with a
        // torsion component. A malicious sender who sends `A = P' + T` (T an
        // order-8 torsion point) would otherwise get T echoed into `B = A + b·G`
        // on choice=1 but NOT into `B = b·G` on choice=0; testing
        // `is_torsion_free(B)` on the response would then LEAK the choice bit (a
        // small-subgroup / selective-failure attack). Forcing A into the
        // prime-order subgroup makes B torsion-free for BOTH choices, closing the
        // leak.
        if sender_public.is_identity() || !sender_public.is_torsion_free() {
            return Err(OtError::InvalidSenderPublic);
        }

        let secret = random_scalar();
        let b_key_point = &secret * ED25519_BASEPOINT_TABLE;

        let b_point = if choice {
            sender_public + b_key_point
        } else {
            b_key_point
        };

        let response = OtReceiverResponse {
            receiver_public: compress_point(&b_point),
        };

        Ok((
            OtReceiver {
                choice,
                secret,
                sender_public,
                receiver_public: b_point,
            },
            response,
        ))
    }

    /// Step 6: Receiver derives the key and decrypts the chosen message.
    ///
    /// `k_b = kdf(b_key * A)` — this equals k0 if choice=0, k1 if choice=1.
    pub fn decrypt(&self, sender_payload: &OtSenderPayload) -> Result<Vec<u8>, OtError> {
        // b_key * A = b_key * (a * G) = a * (b_key * G)
        // If choice=0: sender computed k0 = kdf(a * B, A, B) = kdf(b_key * A, A, B) ✓
        // If choice=1: sender computed k1 = kdf(a * (B-A), A, B) = kdf(b_key * A, A, B) ✓
        // The (A, B) transcript bytes match the sender's because both sides use
        // the canonical compressed encoding of the SAME two points.
        let shared = self.secret * self.sender_public;
        let a_bytes = compress_point(&self.sender_public);
        let b_bytes = compress_point(&self.receiver_public);
        let key = derive_ot_key(&compress_point(&shared), &a_bytes, &b_bytes);

        let ciphertext = if self.choice {
            &sender_payload.encrypted_m1
        } else {
            &sender_payload.encrypted_m0
        };

        decrypt_message(&key, ciphertext).ok_or(OtError::DecryptionFailed)
    }
}

// --- 1-of-N OT extension ---

/// Perform 1-of-N oblivious transfer, built from ceil(log2(N)) instances of 1-of-2 OT.
///
/// The receiver selects index `choice` from `messages` (0-indexed).
/// Returns the chosen message or an error.
///
/// # Panics
///
/// Panics if `messages` is empty or if `choice >= messages.len()`.
pub fn ot_1_of_n(messages: &[&[u8]], choice: usize) -> Result<Vec<u8>, OtError> {
    assert!(!messages.is_empty(), "messages must not be empty");
    assert!(choice < messages.len(), "choice out of bounds");

    let n = messages.len();
    if n == 1 {
        // Trivial case: only one message, no OT needed.
        return Ok(messages[0].to_vec());
    }

    // Number of bits needed to represent the choice index.
    let num_bits = (usize::BITS - (n - 1).leading_zeros()) as usize;

    // Run `num_bits` independent 1-of-2 OTs. For each bit position i of `choice`,
    // the receiver obtains one key. Messages are encrypted under the XOR of all
    // keys corresponding to their index bits.
    //
    // For each bit position, sender generates a pair of keys (key_0, key_1).
    // The receiver obtains key_{choice_bit_i} via OT.
    // Each message m_j is encrypted under: XOR(key_{bit_0(j)}, key_{bit_1(j)}, ...).

    // Generate per-bit key pairs and run OT for each bit of choice.
    let mut receiver_keys = Vec::with_capacity(num_bits);

    // Collect sender key pairs for final encryption.
    let mut sender_key_pairs: Vec<([u8; 32], [u8; 32])> = Vec::with_capacity(num_bits);

    for bit_idx in 0..num_bits {
        let choice_bit = (choice >> bit_idx) & 1 == 1;

        // Generate two random 32-byte keys for this bit position.
        let key0 = random_key();
        let key1 = random_key();

        sender_key_pairs.push((key0, key1));

        // Run 1-of-2 OT: sender offers (key0, key1), receiver picks choice_bit.
        let (sender, setup) = OtSender::new();
        let (receiver, response) = OtReceiver::new(choice_bit, &setup)?;
        let payload = sender.encrypt(&response, &key0, &key1)?;
        let received_key = receiver.decrypt(&payload)?;

        let mut k = [0u8; 32];
        k.copy_from_slice(&received_key);
        receiver_keys.push(k);
    }

    // Encrypt each message under the combined key for its index.
    // The receiver can only decrypt the message at `choice` because they only
    // have the correct key for each bit of `choice`.
    let mut encrypted_messages: Vec<Vec<u8>> = Vec::with_capacity(n);
    for j in 0..n {
        let combined_key = combine_keys_for_index(j, &sender_key_pairs, num_bits);
        encrypted_messages.push(encrypt_message(&combined_key, messages[j]));
    }

    // Receiver combines their keys and decrypts.
    let receiver_combined = combine_keys_for_index_receiver(choice, &receiver_keys, num_bits);
    decrypt_message(&receiver_combined, &encrypted_messages[choice])
        .ok_or(OtError::DecryptionFailed)
}

// --- Internal helpers ---

/// Generate a random scalar using the system CSPRNG.
fn random_scalar() -> Scalar {
    let mut bytes = [0u8; 64];
    getrandom::fill(&mut bytes).expect("getrandom failed");
    Scalar::from_bytes_mod_order_wide(&bytes)
}

/// Generate a random 32-byte key.
fn random_key() -> [u8; 32] {
    let mut key = [0u8; 32];
    getrandom::fill(&mut key).expect("getrandom failed");
    key
}

/// Compress an EdwardsPoint to its 32-byte canonical representation.
fn compress_point(point: &EdwardsPoint) -> [u8; 32] {
    point.compress().to_bytes()
}

/// Decompress a 32-byte representation to an EdwardsPoint, if valid.
fn decompress_point(bytes: &[u8; 32]) -> Option<EdwardsPoint> {
    curve25519_dalek::edwards::CompressedEdwardsY(*bytes).decompress()
}

/// Derive a symmetric key from a DH shared secret using BLAKE3's KDF mode,
/// BOUND to the OT transcript `(A, B)` (the sender's setup point and the
/// receiver's response point) in addition to the raw DH point.
///
/// Binding `(A, B)` — not just the DH point — means a key is scoped to the exact
/// exchange that produced it, so it cannot be replayed under a different
/// transcript. `a_bytes`/`b_bytes` MUST be the canonical compressed encodings of
/// the same two points on both sides (the caller enforces this via
/// `compress_point`). The `-v2` domain tag reflects the widened input over the
/// previous DH-point-only `-v1` KDF.
fn derive_ot_key(
    shared_point_bytes: &[u8; 32],
    a_bytes: &[u8; 32],
    b_bytes: &[u8; 32],
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-ot-key-v2");
    hasher.update(shared_point_bytes);
    hasher.update(a_bytes);
    hasher.update(b_bytes);
    *hasher.finalize().as_bytes()
}

/// Encrypt a message with ChaCha20-Poly1305 using a derived key.
/// Generates a random 12-byte nonce and prepends it to the ciphertext.
fn encrypt_message(key: &[u8; 32], plaintext: &[u8]) -> Vec<u8> {
    use chacha20poly1305::{ChaCha20Poly1305, KeyInit, aead::Aead};

    let mut nonce_bytes = [0u8; 12];
    getrandom::fill(&mut nonce_bytes).expect("getrandom failed");

    let cipher = ChaCha20Poly1305::new(key.into());
    let nonce = chacha20poly1305::Nonce::from_slice(&nonce_bytes);
    let ciphertext = cipher
        .encrypt(nonce, plaintext)
        .expect("encryption should not fail");

    // Prepend nonce to ciphertext: [nonce (12 bytes) || ciphertext+tag]
    let mut output = Vec::with_capacity(12 + ciphertext.len());
    output.extend_from_slice(&nonce_bytes);
    output.extend_from_slice(&ciphertext);
    output
}

/// Decrypt a message with ChaCha20-Poly1305. Input format: [nonce (12) || ciphertext+tag].
fn decrypt_message(key: &[u8; 32], data: &[u8]) -> Option<Vec<u8>> {
    use chacha20poly1305::{ChaCha20Poly1305, KeyInit, aead::Aead};

    if data.len() < 12 {
        return None;
    }

    let (nonce_bytes, ciphertext) = data.split_at(12);
    let cipher = ChaCha20Poly1305::new(key.into());
    let nonce = chacha20poly1305::Nonce::from_slice(nonce_bytes);
    cipher.decrypt(nonce, ciphertext).ok()
}

/// Combine per-bit keys for a given index j using BLAKE3.
/// The combined key is: BLAKE3("dregg-ot-combine-v1", key_{bit0(j)} || key_{bit1(j)} || ...).
fn combine_keys_for_index(
    index: usize,
    key_pairs: &[([u8; 32], [u8; 32])],
    num_bits: usize,
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-ot-combine-v1");
    for bit_idx in 0..num_bits {
        let bit = (index >> bit_idx) & 1;
        if bit == 0 {
            hasher.update(&key_pairs[bit_idx].0);
        } else {
            hasher.update(&key_pairs[bit_idx].1);
        }
    }
    *hasher.finalize().as_bytes()
}

/// Combine the receiver's obtained keys for their choice index.
fn combine_keys_for_index_receiver(
    choice: usize,
    receiver_keys: &[[u8; 32]],
    num_bits: usize,
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-ot-combine-v1");
    for bit_idx in 0..num_bits {
        // The receiver obtained key_{choice_bit_i} for each bit position.
        // We just hash them in order — the bit value is implicit in which key was received.
        let _ = (choice >> bit_idx) & 1; // same bit pattern, same key order
        hasher.update(&receiver_keys[bit_idx]);
    }
    *hasher.finalize().as_bytes()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ot_choice_0_gets_m0() {
        let m0 = b"hello, this is message zero";
        let m1 = b"goodbye, this is message one";

        let (sender, setup) = OtSender::new();
        let (receiver, response) = OtReceiver::new(false, &setup).unwrap();
        let payload = sender.encrypt(&response, m0, m1).unwrap();
        let result = receiver.decrypt(&payload).unwrap();

        assert_eq!(result, m0);
    }

    #[test]
    fn ot_choice_1_gets_m1() {
        let m0 = b"hello, this is message zero";
        let m1 = b"goodbye, this is message one";

        let (sender, setup) = OtSender::new();
        let (receiver, response) = OtReceiver::new(true, &setup).unwrap();
        let payload = sender.encrypt(&response, m0, m1).unwrap();
        let result = receiver.decrypt(&payload).unwrap();

        assert_eq!(result, m1);
    }

    #[test]
    fn ot_choice_0_cannot_decrypt_m1() {
        let m0 = b"message zero";
        let m1 = b"message one - secret!";

        let (sender, setup) = OtSender::new();
        let (receiver, response) = OtReceiver::new(false, &setup).unwrap();
        let payload = sender.encrypt(&response, m0, m1).unwrap();

        // Receiver got m0 correctly
        let result = receiver.decrypt(&payload).unwrap();
        assert_eq!(result, m0);

        // Try to decrypt m1 with the receiver's key — should fail.
        // The receiver's key is kdf(b_key * A, A, B). For choice=0 this equals k0, not k1.
        let shared = receiver.secret * receiver.sender_public;
        let key = derive_ot_key(
            &compress_point(&shared),
            &compress_point(&receiver.sender_public),
            &compress_point(&receiver.receiver_public),
        );
        let decrypted_m1 = decrypt_message(&key, &payload.encrypted_m1);
        assert!(decrypted_m1.is_none() || decrypted_m1.unwrap() != m1);
    }

    #[test]
    fn ot_choice_1_cannot_decrypt_m0() {
        let m0 = b"message zero - secret!";
        let m1 = b"message one";

        let (sender, setup) = OtSender::new();
        let (receiver, response) = OtReceiver::new(true, &setup).unwrap();
        let payload = sender.encrypt(&response, m0, m1).unwrap();

        // Receiver got m1 correctly
        let result = receiver.decrypt(&payload).unwrap();
        assert_eq!(result, m1);

        // Try to decrypt m0 with the receiver's key — should fail.
        let shared = receiver.secret * receiver.sender_public;
        let key = derive_ot_key(
            &compress_point(&shared),
            &compress_point(&receiver.sender_public),
            &compress_point(&receiver.receiver_public),
        );
        let decrypted_m0 = decrypt_message(&key, &payload.encrypted_m0);
        assert!(decrypted_m0.is_none() || decrypted_m0.unwrap() != m0);
    }

    #[test]
    fn sender_cannot_determine_choice_from_receiver_message() {
        // Statistical test: sender sees many receiver messages and cannot
        // distinguish choice=0 from choice=1 (both B values are random points).
        let mut points_choice_0 = Vec::new();
        let mut points_choice_1 = Vec::new();

        for _ in 0..50 {
            let (_sender, setup) = OtSender::new();
            let (_r0, resp0) = OtReceiver::new(false, &setup).unwrap();
            let (_r1, resp1) = OtReceiver::new(true, &setup).unwrap();
            points_choice_0.push(resp0.receiver_public);
            points_choice_1.push(resp1.receiver_public);
        }

        // All points should be distinct (with overwhelming probability).
        for i in 0..50 {
            for j in (i + 1)..50 {
                assert_ne!(points_choice_0[i], points_choice_0[j]);
                assert_ne!(points_choice_1[i], points_choice_1[j]);
            }
            // No structural difference between the two sets — both are random Edwards points.
            // (We can't distinguish them computationally; this test just verifies they're all valid.)
            assert!(decompress_point(&points_choice_0[i]).is_some());
            assert!(decompress_point(&points_choice_1[i]).is_some());
        }
    }

    #[test]
    fn ot_large_messages() {
        // Test with 1KB messages.
        let m0 = vec![0xAAu8; 1024];
        let m1 = vec![0xBBu8; 1024];

        let (sender, setup) = OtSender::new();
        let (receiver, response) = OtReceiver::new(false, &setup).unwrap();
        let payload = sender.encrypt(&response, &m0, &m1).unwrap();
        let result = receiver.decrypt(&payload).unwrap();
        assert_eq!(result, m0);

        let (sender, setup) = OtSender::new();
        let (receiver, response) = OtReceiver::new(true, &setup).unwrap();
        let payload = sender.encrypt(&response, &m0, &m1).unwrap();
        let result = receiver.decrypt(&payload).unwrap();
        assert_eq!(result, m1);
    }

    #[test]
    fn ot_randomized_100_choices() {
        let m0 = b"the zeroth message content here";
        let m1 = b"the first message content here!";

        // Use a simple deterministic sequence for test reproducibility,
        // but verify both branches get exercised.
        let mut count_0 = 0usize;
        let mut count_1 = 0usize;

        for i in 0..100u8 {
            // Alternate choices based on a hash to get a mix.
            let choice = blake3::hash(&[i, 0x42]).as_bytes()[0] & 1 == 1;

            let (sender, setup) = OtSender::new();
            let (receiver, response) = OtReceiver::new(choice, &setup).unwrap();
            let payload = sender.encrypt(&response, m0, m1).unwrap();
            let result = receiver.decrypt(&payload).unwrap();

            if choice {
                assert_eq!(result, m1, "failed at iteration {i} with choice=1");
                count_1 += 1;
            } else {
                assert_eq!(result, m0, "failed at iteration {i} with choice=0");
                count_0 += 1;
            }
        }

        // Ensure both branches were well-exercised (expect ~50/50 with hash).
        assert!(count_0 > 20, "too few choice=0: {count_0}");
        assert!(count_1 > 20, "too few choice=1: {count_1}");
    }

    #[test]
    fn ot_empty_messages() {
        let m0 = b"";
        let m1 = b"";

        let (sender, setup) = OtSender::new();
        let (receiver, response) = OtReceiver::new(false, &setup).unwrap();
        let payload = sender.encrypt(&response, m0, m1).unwrap();
        let result = receiver.decrypt(&payload).unwrap();
        assert_eq!(result, b"");
    }

    #[test]
    fn ot_receiver_rejects_torsion_sender_point() {
        // F2(a): a malicious sender offers A = (a·G) + T with T an order-8
        // torsion point. If the receiver accepted it, the torsion would echo into
        // B on choice=1 but not choice=0, leaking the choice bit. The receiver
        // must reject A as not torsion-free, on BOTH choices.
        use curve25519_dalek::constants::EIGHT_TORSION;

        let a_prime = &random_scalar() * ED25519_BASEPOINT_TABLE;
        let a_malicious = a_prime + EIGHT_TORSION[1]; // add an order-8 component
        assert!(!a_malicious.is_torsion_free());
        let setup = OtSenderSetup {
            sender_public: compress_point(&a_malicious),
        };

        for choice in [false, true] {
            let result = OtReceiver::new(choice, &setup);
            assert_eq!(
                result.err(),
                Some(OtError::InvalidSenderPublic),
                "receiver must reject a torsion-tainted sender point (choice={choice})"
            );
        }
    }

    #[test]
    fn ot_sender_rejects_mixed_order_receiver_point() {
        // F2(b): a receiver point B = (b·G) + T (prime-order + order-8 torsion) is
        // MIXED-order. The old `is_small_order()` guard let it through, yet it
        // still partially predicts the DH secret (a selective-failure leak of a
        // (mod 8) on the choice bit). The `is_torsion_free()` guard must reject
        // it — and this point is specifically NOT small-order, so it exercises
        // exactly the class the previous check missed.
        use curve25519_dalek::constants::EIGHT_TORSION;

        let (sender, _setup) = OtSender::new();

        let b_prime = &random_scalar() * ED25519_BASEPOINT_TABLE;
        let b_mixed = b_prime + EIGHT_TORSION[1];
        assert!(
            !b_mixed.is_small_order(),
            "constructed point must be mixed-order (not small-order), or the test is vacuous"
        );
        assert!(!b_mixed.is_torsion_free());

        let response = OtReceiverResponse {
            receiver_public: compress_point(&b_mixed),
        };
        let result = sender.encrypt(&response, b"m0", b"m1");
        assert_eq!(
            result.err(),
            Some(OtError::InvalidReceiverPoint),
            "sender must reject a mixed-order receiver point that is_small_order() misses"
        );
    }

    #[test]
    fn ot_key_binds_transcript_ab() {
        // F2(c): the KDF must depend on BOTH transcript points A and B, not just
        // the DH point. Changing A (or B) with a fixed DH point yields a different
        // key; an identical transcript reproduces the same key.
        let shared = [7u8; 32];
        let a = [1u8; 32];
        let a2 = [2u8; 32];
        let b = [3u8; 32];
        let b2 = [4u8; 32];

        let base = derive_ot_key(&shared, &a, &b);
        assert_ne!(base, derive_ot_key(&shared, &a2, &b), "key must depend on A");
        assert_ne!(base, derive_ot_key(&shared, &a, &b2), "key must depend on B");
        assert_eq!(base, derive_ot_key(&shared, &a, &b), "same transcript ⇒ same key");
    }

    #[test]
    fn ot_1_of_n_basic() {
        let messages: Vec<&[u8]> = vec![b"msg0", b"msg1", b"msg2", b"msg3"];

        for choice in 0..4 {
            let result = ot_1_of_n(&messages, choice).unwrap();
            assert_eq!(result, messages[choice], "failed for choice={choice}");
        }
    }

    #[test]
    fn ot_1_of_n_large_n() {
        let msgs: Vec<Vec<u8>> = (0..16u8).map(|i| vec![i; 32]).collect();
        let msg_refs: Vec<&[u8]> = msgs.iter().map(|m| m.as_slice()).collect();

        for choice in 0..16 {
            let result = ot_1_of_n(&msg_refs, choice).unwrap();
            assert_eq!(result, msgs[choice], "failed for choice={choice}");
        }
    }

    #[test]
    fn ot_1_of_n_single_message() {
        let result = ot_1_of_n(&[b"only one"], 0).unwrap();
        assert_eq!(result, b"only one");
    }

    #[test]
    fn ot_1_of_n_non_power_of_two() {
        // 5 messages: needs 3 bits, but index 5,6,7 are invalid.
        let messages: Vec<&[u8]> = vec![b"a", b"b", b"c", b"d", b"e"];
        for choice in 0..5 {
            let result = ot_1_of_n(&messages, choice).unwrap();
            assert_eq!(result, messages[choice]);
        }
    }
}
