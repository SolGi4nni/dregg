//! Integration test: encrypted turn build + decrypt roundtrip.
//!
//! Tests the `make_encrypted_turn` → `EncryptedTurn::decrypt_for_executor` →
//! `TurnExecutor::apply_encrypted_turn` pipeline at the library level (no HTTP).
//!
//! Also exercises the forged-sealer path: using the wrong secret must cause
//! decryption to fail and `apply_encrypted_turn` to return an error.

mod common;

use pyana_sdk::CellId;
use pyana_cell::Ledger;
use pyana_turn::{
    CallForest, EncryptedTurn, EncryptedTurnError, TurnExecutor, ComputronCosts,
    Turn,
};

// ---------------------------------------------------------------------------
// Helper: build a minimal Turn for the given agent
// ---------------------------------------------------------------------------

fn empty_turn(agent: CellId) -> Turn {
    Turn {
        agent,
        nonce: 0,
        fee: 0,
        memo: None,
        valid_until: None,
        call_forest: CallForest::new(),
        depends_on: vec![],
        previous_receipt_hash: None,
        conservation_proof: None,
        sovereign_witnesses: Default::default(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: vec![],
        cross_effect_dependencies: vec![],
        effect_witness_index_map: vec![],
    }
}

// ---------------------------------------------------------------------------
// 1. Encrypt + decrypt + apply: was_encrypted flag is set
// ---------------------------------------------------------------------------

/// Encrypt a minimal turn, decrypt it with the correct unsealer secret, apply
/// via `apply_encrypted_turn`, assert the receipt has `was_encrypted = true`.
#[test]
fn encrypted_turn_roundtrip_sets_was_encrypted_flag() {
    // Executor holds an unsealer X25519 keypair.
    let mut unsealer_secret = [0u8; 32];
    // Use a deterministic "secret" for tests.
    unsealer_secret.copy_from_slice(blake3::hash(b"test-unsealer-secret").as_bytes());
    let unsealer_public = {
        let pk = x25519_dalek::PublicKey::from(
            &x25519_dalek::StaticSecret::from(unsealer_secret),
        );
        *pk.as_bytes()
    };

    // Build a cipherclerk; the agent cell is derived from the public key.
    let cclerk = common::cclerk_from_label("encrypted-roundtrip");
    let agent = cclerk.cell_id("default");
    let turn = empty_turn(agent);

    // Encrypt the turn to the executor's public key.
    let encrypted = cclerk
        .make_encrypted_turn(&turn, &unsealer_public, 0)
        .expect("make_encrypted_turn must succeed");

    // Metadata consistency must hold before we even try to decrypt.
    assert!(
        encrypted.verify_metadata().is_ok(),
        "verify_metadata must pass for a freshly-built EncryptedTurn"
    );

    // Apply via the executor.
    let executor = TurnExecutor::new(ComputronCosts::default());
    let mut ledger = Ledger::new();
    let receipt = executor
        .apply_encrypted_turn(&encrypted, &unsealer_secret, &mut ledger)
        .expect("apply_encrypted_turn must succeed with correct secret");

    assert!(
        receipt.was_encrypted,
        "receipt.was_encrypted must be true for turns submitted via the encrypted path"
    );
}

// ---------------------------------------------------------------------------
// 2. Forged sealer secret → decryption fails
// ---------------------------------------------------------------------------

/// Using a different (forged) unsealer secret must cause decryption to fail.
/// The `apply_encrypted_turn` call must return an error — it must NOT succeed
/// with `was_encrypted = false` or anything similarly misleading.
#[test]
fn encrypted_turn_wrong_sealer_secret_is_rejected() {
    // Real executor secret.
    let mut real_secret = [0u8; 32];
    real_secret.copy_from_slice(blake3::hash(b"real-unsealer").as_bytes());
    let real_public = {
        let pk = x25519_dalek::PublicKey::from(
            &x25519_dalek::StaticSecret::from(real_secret),
        );
        *pk.as_bytes()
    };

    // Forged (attacker) secret — different from the real executor's key.
    let mut forged_secret = [0u8; 32];
    forged_secret.copy_from_slice(blake3::hash(b"attacker-secret").as_bytes());
    assert_ne!(forged_secret, real_secret);

    let cclerk = common::cclerk_from_label("forged-sealer");
    let agent = cclerk.cell_id("default");
    let turn = empty_turn(agent);

    // Encrypt to the real executor.
    let encrypted = cclerk
        .make_encrypted_turn(&turn, &real_public, 0)
        .expect("encryption must succeed");

    // Attempt decryption with the forged key.
    let forged_public = {
        let pk = x25519_dalek::PublicKey::from(
            &x25519_dalek::StaticSecret::from(forged_secret),
        );
        *pk.as_bytes()
    };
    let decrypt_result = encrypted.decrypt_for_executor(&forged_secret, &forged_public);
    assert!(
        decrypt_result.is_err(),
        "decryption with wrong secret must fail; got: {:?}",
        decrypt_result
    );

    // `apply_encrypted_turn` with the wrong secret must also fail.
    let executor = TurnExecutor::new(ComputronCosts::default());
    let mut ledger = Ledger::new();
    let apply_result = executor.apply_encrypted_turn(&encrypted, &forged_secret, &mut ledger);
    assert!(
        apply_result.is_err(),
        "apply_encrypted_turn with wrong secret must return an error"
    );
}

// ---------------------------------------------------------------------------
// 3. Direct decryption with correct key succeeds and recovers the Turn
// ---------------------------------------------------------------------------

/// Verify that `decrypt_for_executor` with the right key returns a `Turn`
/// whose `agent` matches what was encrypted.
#[test]
fn encrypted_turn_decrypt_recovers_correct_agent() {
    let mut secret = [0u8; 32];
    secret.copy_from_slice(blake3::hash(b"recovery-test-secret").as_bytes());
    let public = {
        let pk = x25519_dalek::PublicKey::from(&x25519_dalek::StaticSecret::from(secret));
        *pk.as_bytes()
    };

    let cclerk = common::cclerk_from_label("decrypt-recovery");
    let agent = cclerk.cell_id("main");
    let turn = empty_turn(agent);

    let encrypted = cclerk
        .make_encrypted_turn(&turn, &public, 42)
        .expect("encryption must succeed");

    let recovered = encrypted
        .decrypt_for_executor(&secret, &public)
        .expect("decryption must succeed with correct key");

    assert_eq!(
        recovered.agent, agent,
        "recovered turn agent must match the original"
    );
}

// ---------------------------------------------------------------------------
// 4. Ciphertext mutation → commitment verification fails
// ---------------------------------------------------------------------------

/// Flip a byte in the ciphertext after encryption. `decrypt_for_executor`
/// must detect the AEAD authentication failure and return `DecryptionFailed`.
#[test]
fn mutated_ciphertext_rejected_by_commitment_check() {
    let mut secret = [0u8; 32];
    secret.copy_from_slice(blake3::hash(b"mutation-test-secret").as_bytes());
    let public = {
        let pk = x25519_dalek::PublicKey::from(&x25519_dalek::StaticSecret::from(secret));
        *pk.as_bytes()
    };

    let cclerk = common::cclerk_from_label("mutation-test");
    let agent = cclerk.cell_id("main");
    let turn = empty_turn(agent);

    let mut encrypted = cclerk
        .make_encrypted_turn(&turn, &public, 0)
        .expect("encryption must succeed");

    // Flip the first byte of the ciphertext to simulate bit-flip / tamper.
    if !encrypted.ciphertext.is_empty() {
        encrypted.ciphertext[0] ^= 0xFF;
    }

    let result = encrypted.decrypt_for_executor(&secret, &public);
    assert!(
        matches!(result, Err(EncryptedTurnError::DecryptionFailed)),
        "AEAD-tampered ciphertext must return DecryptionFailed, got: {result:?}"
    );
}
