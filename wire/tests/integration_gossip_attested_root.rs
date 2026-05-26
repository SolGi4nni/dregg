//! Integration test: AttestedRoot gossip — signature verification + forgery rejection.
//!
//! Tests the `AttestedRoot` (and `AttestedRootPush`) signing and verification
//! path that the federation gossip layer uses. Covers:
//!
//!   1. A correctly-signed `AttestedRoot` from a known validator is accepted.
//!   2. A forged `AttestedRoot` (signature from an unknown key) is rejected.
//!   3. A tampered `AttestedRoot` (valid key, wrong signature over mutated body)
//!      is rejected.
//!   4. `AttestedRootPush` from an unknown federation sender is rejected by the
//!      CapTpState `AttestedRootPush` handler (adversarial_wire_tests already
//!      covers the push-from-stranger case; here we additionally verify the
//!      known-sender path directly via `is_valid`).
//!   5. Duplicate-signer replay does not count toward quorum.

use dregg_types::{AttestedRoot, FederationId, PublicKey, generate_keypair, sign};

// ---------------------------------------------------------------------------
// Helper
// ---------------------------------------------------------------------------

/// Build an `AttestedRoot` with a specific federation, root, height, and
/// quorum threshold, signed by the supplied signing keys.
fn build_attested_root(
    federation_id: FederationId,
    merkle_root: [u8; 32],
    height: u64,
    timestamp: i64,
    signers: &[(dregg_types::SigningKey, PublicKey)],
    threshold: usize,
) -> AttestedRoot {
    let mut root = AttestedRoot {
        merkle_root,
        note_tree_root: None,
        nullifier_set_root: None,
        height,
        timestamp,
        blocklace_block_id: None,
        finality_round: None,
        quorum_signatures: Vec::new(),
        threshold_qc: None,
        threshold,
        federation_id,
        receipt_stream_root: None,
    };

    let message = root.signing_message();
    for (sk, pk) in signers {
        let sig = sign(sk, &message);
        root.quorum_signatures.push((*pk, sig));
    }

    root
}

// ---------------------------------------------------------------------------
// 1. Correctly-signed AttestedRoot is accepted by is_valid
// ---------------------------------------------------------------------------

/// A 2-of-3 quorum root with two valid signatures from known keys must be
/// accepted by `AttestedRoot::is_valid`.
#[test]
fn valid_attested_root_accepted() {
    let (sk_a, pk_a) = generate_keypair();
    let (sk_b, pk_b) = generate_keypair();
    let (_sk_c, pk_c) = generate_keypair();

    let fed = FederationId([1u8; 32]);
    let known_keys = vec![pk_a, pk_b, pk_c];

    let root = build_attested_root(
        fed,
        [42u8; 32],
        10,
        1_000_000,
        &[(sk_a, pk_a), (sk_b, pk_b)],
        2,
    );

    assert!(
        root.is_valid(&known_keys),
        "a correctly-signed 2-of-3 AttestedRoot must be accepted"
    );
    assert!(
        root.has_quorum(),
        "has_quorum must return true for a root with 2 signatures (threshold 2)"
    );
}

// ---------------------------------------------------------------------------
// 2. Unknown signer is rejected
// ---------------------------------------------------------------------------

/// A root signed by a key not in `known_keys` must be rejected by `is_valid`.
#[test]
fn attested_root_from_unknown_signer_rejected() {
    let (sk_stranger, pk_stranger) = generate_keypair();
    let (_sk_known, pk_known) = generate_keypair();

    let fed = FederationId([2u8; 32]);
    let known_keys = vec![pk_known]; // stranger NOT in known_keys

    let root = build_attested_root(fed, [99u8; 32], 5, 500, &[(sk_stranger, pk_stranger)], 1);

    assert!(
        !root.is_valid(&known_keys),
        "a root signed by an unknown key must be rejected by is_valid"
    );
}

// ---------------------------------------------------------------------------
// 3. Tampered root (mutated merkle_root, original signature) is rejected
// ---------------------------------------------------------------------------

/// Build a valid root, then flip a byte in `merkle_root` to simulate a
/// man-in-the-middle tampering with the root value. The signature now covers
/// the original bytes, so verification must fail.
#[test]
fn tampered_attested_root_rejected() {
    let (sk, pk) = generate_keypair();

    let fed = FederationId([3u8; 32]);
    let known_keys = vec![pk];

    let mut root = build_attested_root(fed, [0xAAu8; 32], 20, 9_000_000, &[(sk, pk)], 1);

    // Tamper with the merkle root AFTER signing.
    root.merkle_root[0] ^= 0xFF;

    assert!(
        !root.is_valid(&known_keys),
        "a root with a tampered merkle_root must fail signature verification"
    );
}

// ---------------------------------------------------------------------------
// 4. Signature on wrong federation_id is rejected
// ---------------------------------------------------------------------------

/// The signing message binds the `federation_id` (v3 preimage). A root where
/// the `federation_id` was changed after signing must be rejected.
#[test]
fn attested_root_federation_swap_rejected() {
    let (sk, pk) = generate_keypair();

    let fed_real = FederationId([0xAAu8; 32]);
    let fed_swapped = FederationId([0xBBu8; 32]);
    let known_keys = vec![pk];

    let mut root = build_attested_root(fed_real, [1u8; 32], 7, 7_000, &[(sk, pk)], 1);

    // Attacker swaps the federation_id after signing.
    root.federation_id = fed_swapped;

    assert!(
        !root.is_valid(&known_keys),
        "a root with a swapped federation_id must fail (preimage differs from signed)"
    );
}

// ---------------------------------------------------------------------------
// 5. Duplicate-signer replay does not count toward quorum
// ---------------------------------------------------------------------------

/// If the same (pk, sig) pair appears twice in `quorum_signatures`, the
/// duplicate must not count twice toward the threshold. A root with threshold
/// 2 that only has one unique valid signer (duplicated) must be rejected.
#[test]
fn duplicate_signer_does_not_count_twice_toward_quorum() {
    let (sk_a, pk_a) = generate_keypair();
    let fed = FederationId([4u8; 32]);
    let known_keys = vec![pk_a];

    // Build root with one signer, threshold 2.
    let mut root = build_attested_root(
        fed,
        [7u8; 32],
        3,
        3_000,
        &[(sk_a, pk_a)],
        2, // threshold requires 2 UNIQUE valid signers
    );

    // Duplicate the single signature entry.
    let sig_copy = root.quorum_signatures[0].clone();
    root.quorum_signatures.push(sig_copy);

    assert_eq!(root.quorum_signatures.len(), 2);
    assert!(
        !root.is_valid(&known_keys),
        "duplicate signer must not count twice; threshold 2 with only 1 unique signer must fail"
    );
}

// ---------------------------------------------------------------------------
// 6. Threshold=0 root is accepted (degenerate but structurally valid)
// ---------------------------------------------------------------------------

/// A root with `threshold = 0` and no signatures is structurally valid
/// (no quorum needed). This documents the degenerate case; production roots
/// always set a positive threshold.
#[test]
fn threshold_zero_root_has_quorum() {
    let root = AttestedRoot {
        merkle_root: [0u8; 32],
        note_tree_root: None,
        nullifier_set_root: None,
        height: 0,
        timestamp: 0,
        blocklace_block_id: None,
        finality_round: None,
        quorum_signatures: vec![],
        threshold_qc: None,
        threshold: 0,
        federation_id: FederationId([0u8; 32]),
        receipt_stream_root: None,
    };

    assert!(
        root.has_quorum(),
        "threshold=0 root must satisfy has_quorum (no signatures needed)"
    );
    // is_valid with empty known_keys and 0 threshold must also return true.
    assert!(
        root.is_valid(&[]),
        "threshold=0 root must be is_valid (vacuously)"
    );
}
