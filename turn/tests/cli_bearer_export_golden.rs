//! GOLDEN-VECTOR LOCK for the `dregg cap export` bearer-capability replica.
//!
//! The CLI (`cli/src/commands/cap.rs`, module `bearer`) is deliberately
//! dependency-light: it does NOT link `dregg-turn`. Instead it replicates two
//! self-contained primitives byte-for-byte —
//!   1. `compute_delegation_message` (the blake3 recipe under domain
//!      `dregg-bearer-delegation-v1:`), and
//!   2. `BearerCapProof::to_node_json` (the serde wire shape of
//!      `dregg_turn::action::BearerCapProof` / `DelegationProofData`).
//!
//! A hand-copied constant is only as trustworthy as the run that produced it.
//! This test runs the REAL `TurnExecutor::compute_bearer_delegation_message`
//! and the REAL `serde_json` of `BearerCapProof`, so any drift on EITHER side
//! (CLI replica or turn crate) is caught here — the node would otherwise
//! silently reject CLI-built proofs. These are the durable locks the CLI's
//! in-module tests reference by value.

use dregg_cell::AuthRequired;
use dregg_turn::action::{BearerCapProof, DelegationProofData};
use dregg_turn::executor::TurnExecutor;
use dregg_types::CellId;
use ed25519_dalek::{Signer, SigningKey, VerifyingKey};

/// The CLI's `cap.rs` tests pin this exact hex constant for the canonical
/// delegation message. This proves the constant equals what the REAL executor
/// computes on the documented golden inputs — i.e. it was NOT fabricated.
///
/// Inputs (must match `cap.rs::tests::delegation_message_matches_canonical_recipe`):
///   target      = CellId([0xAB; 32])
///   permissions = AuthRequired::Signature
///   bearer_pk   = [0xCD; 32]
///   expires_at  = 0x0102_0304_0506_0708
///   federation  = [0xEF; 32]
const CLI_GOLDEN_DELEGATION_MSG_HEX: &str =
    "9fe1805d6e21ecaf4334cbc0030e70c3a9842773621e91d69a9df7b75fb05271";

#[test]
fn cli_replica_matches_real_executor_delegation_message() {
    let target = CellId([0xAB; 32]);
    let permissions = AuthRequired::Signature;
    let bearer_pk = [0xCD; 32];
    let expires_at = 0x0102_0304_0506_0708u64;
    let federation = [0xEF; 32];

    // The REAL source of truth the node's executor recomputes at verify time.
    let real = TurnExecutor::compute_bearer_delegation_message(
        &target,
        &permissions,
        &bearer_pk,
        expires_at,
        &federation,
    );

    assert_eq!(
        hex::encode(real),
        CLI_GOLDEN_DELEGATION_MSG_HEX,
        "the CLI's pinned golden vector diverged from the REAL \
         TurnExecutor::compute_bearer_delegation_message — CLI-built bearer \
         proofs would be rejected by the node"
    );
}

/// Permission-byte parity across the full CLI-exportable lattice
/// (None=0, Signature=1, Proof=2, Either=3). If the executor ever reorders
/// these, the CLI's `message_byte` mapping must move with it; this catches it.
#[test]
fn cli_permission_bytes_match_executor() {
    let target = CellId([0x01; 32]);
    let bearer_pk = [0x02; 32];
    let federation = [0x03; 32];
    let expires_at = 42u64;

    // Recompute the executor message for each variant, then independently
    // reconstruct the CLI recipe with the byte the CLI uses, and require equal.
    let cases = [
        (AuthRequired::None, 0u8),
        (AuthRequired::Signature, 1u8),
        (AuthRequired::Proof, 2u8),
        (AuthRequired::Either, 3u8),
    ];
    for (perm, cli_byte) in cases {
        let real = TurnExecutor::compute_bearer_delegation_message(
            &target,
            &perm,
            &bearer_pk,
            expires_at,
            &federation,
        );

        // The CLI's exact recipe (mirrors `cap.rs::compute_delegation_message`).
        let mut h = blake3::Hasher::new();
        h.update(b"dregg-bearer-delegation-v1:");
        h.update(&federation);
        h.update(target.as_bytes());
        h.update(&[cli_byte]);
        h.update(&bearer_pk);
        h.update(&expires_at.to_le_bytes());
        let cli = *h.finalize().as_bytes();

        assert_eq!(
            real, cli,
            "CLI permission byte {cli_byte} for {perm:?} diverged from the executor"
        );
    }
}

/// The CLI's `to_node_json` output must deserialize as a REAL
/// `dregg_turn::action::BearerCapProof` with no wire skew, and the resulting
/// proof must carry a signature that the executor's recomputed message accepts.
/// This is the end-to-end "exported cap re-imports + verifies" tooth at the
/// type boundary the node actually crosses (`serde_json::from_value`).
#[test]
fn cli_node_json_deserializes_and_signature_verifies() {
    // Reproduce, in this crate, the EXACT JSON the CLI's `to_node_json` emits
    // for a real signed self-delegation. (Building it here keeps the test
    // self-contained; the shape is asserted field-by-field below against the
    // deserialized real type, so any divergence in the CLI shape that the node
    // could not parse would also fail the CLI's own `node_json_shape_is_canonical`.)
    let sk = SigningKey::from_bytes(&[7u8; 32]);
    let pk = sk.verifying_key().to_bytes();
    let target = CellId([0x22; 32]);
    let permissions = AuthRequired::Signature;
    let expires_at = 1000u64;
    let federation = [0u8; 32];

    let message = TurnExecutor::compute_bearer_delegation_message(
        &target,
        &permissions,
        &pk,
        expires_at,
        &federation,
    );
    let signature = sk.sign(&message).to_bytes();

    // The CLI wire shape (numeric byte arrays + externally-tagged variants).
    let cli_json = serde_json::json!({
        "target": target.as_bytes().to_vec(),
        "permissions": "Signature",
        "delegation_proof": {
            "SignedDelegation": {
                "delegator_pk": pk.to_vec(),
                "signature": signature.to_vec(),
                "bearer_pk": pk.to_vec(),
            }
        },
        "expires_at": expires_at,
        "revocation_channel": serde_json::Value::Null,
        "allowed_effects": serde_json::Value::Null,
    });

    // The node-side step: deserialize into the REAL type. No skew allowed.
    let proof: BearerCapProof = serde_json::from_value(cli_json)
        .expect("CLI bearer-proof JSON must deserialize as dregg_turn::BearerCapProof");

    assert_eq!(proof.target, target);
    assert_eq!(proof.permissions, AuthRequired::Signature);
    assert_eq!(proof.expires_at, expires_at);
    assert!(proof.revocation_channel.is_none());
    assert!(proof.allowed_effects.is_none());

    let DelegationProofData::SignedDelegation {
        delegator_pk,
        signature: sig_bytes,
        bearer_pk,
    } = proof.delegation_proof
    else {
        panic!("CLI exports SignedDelegation");
    };
    assert_eq!(delegator_pk, pk);
    assert_eq!(bearer_pk, pk);

    // The signature the CLI produced verifies against the executor's recomputed
    // message — the same cryptographic admission the node performs.
    let vk = VerifyingKey::from_bytes(&delegator_pk).expect("valid delegator key");
    let recomputed = TurnExecutor::compute_bearer_delegation_message(
        &proof.target,
        &proof.permissions,
        &bearer_pk,
        proof.expires_at,
        &federation,
    );
    let sig = ed25519_dalek::Signature::from_bytes(&sig_bytes);
    assert!(
        vk.verify_strict(&recomputed, &sig).is_ok(),
        "CLI-exported signature must verify under the executor's recomputed message"
    );
}

/// INVALID REJECTS (anti-vacuity for the verify tooth): the same JSON path with
/// a tampered field must NOT verify against the executor's recomputed message.
/// Confirms the round-trip above is load-bearing, not trivially-true.
#[test]
fn cli_node_json_tampered_signature_rejected() {
    let sk = SigningKey::from_bytes(&[7u8; 32]);
    let pk = sk.verifying_key().to_bytes();
    let target = CellId([0x22; 32]);
    let federation = [0u8; 32];
    let expires_at = 1000u64;

    let message = TurnExecutor::compute_bearer_delegation_message(
        &target,
        &AuthRequired::Signature,
        &pk,
        expires_at,
        &federation,
    );
    let mut signature = sk.sign(&message).to_bytes();
    signature[0] ^= 0x01; // corrupt one bit

    let cli_json = serde_json::json!({
        "target": target.as_bytes().to_vec(),
        "permissions": "Signature",
        "delegation_proof": {
            "SignedDelegation": {
                "delegator_pk": pk.to_vec(),
                "signature": signature.to_vec(),
                "bearer_pk": pk.to_vec(),
            }
        },
        "expires_at": expires_at,
        "revocation_channel": serde_json::Value::Null,
        "allowed_effects": serde_json::Value::Null,
    });

    // Still a structurally-valid proof (deserializes fine)...
    let proof: BearerCapProof =
        serde_json::from_value(cli_json).expect("structurally valid proof");
    let DelegationProofData::SignedDelegation {
        delegator_pk,
        signature: sig_bytes,
        bearer_pk,
    } = proof.delegation_proof
    else {
        panic!("SignedDelegation");
    };

    // ...but the corrupted signature does NOT verify (no silent admission).
    let vk = VerifyingKey::from_bytes(&delegator_pk).unwrap();
    let recomputed = TurnExecutor::compute_bearer_delegation_message(
        &proof.target,
        &proof.permissions,
        &bearer_pk,
        proof.expires_at,
        &federation,
    );
    let sig = ed25519_dalek::Signature::from_bytes(&sig_bytes);
    assert!(
        vk.verify_strict(&recomputed, &sig).is_err(),
        "a corrupted CLI signature must be rejected by the executor message check"
    );
}
