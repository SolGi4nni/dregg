//! Privacy stack checks: stealth addresses, Pedersen commitments, range proofs, SSE.

use dregg_cell::stealth::StealthKeys;
use dregg_cell::value_commitment::{
    BulletproofRangeProof, ValueCommitment, prove_conservation, verify_conservation,
};
use dregg_intent::sse::EncryptedIntent;
use dregg_intent::{CommitmentId, MatchSpec};

use crate::report::{CheckResult, run_check};

pub fn run() -> Vec<CheckResult> {
    vec![
        run_check("stealth", check_stealth_addresses),
        run_check("pedersen", check_pedersen_conservation),
        run_check("pedersen_tampered", check_pedersen_tampered_rejected),
        run_check("range", check_range_proof),
        run_check("sse", check_encrypted_intent),
        run_check("note_nullifier", check_note_nullifier_derivation),
    ]
}

fn check_stealth_addresses() -> Result<(), String> {
    // Generate stealth keys for receiver.
    // StealthKeys uses X25519 for view (DH) and passes spend_private_key as-is.
    // The check_ownership function derives Ed25519 public key from the spend_private_key,
    // so we need a valid Ed25519 secret key (clamped scalar).
    use ed25519_dalek::SigningKey;

    // Use a deterministic but valid Ed25519 signing key for the spend key
    let spend_seed = *blake3::hash(b"stealth-spend-key-seed").as_bytes();
    let signing_key = SigningKey::from_bytes(&spend_seed);
    let spend_private_key = signing_key.to_bytes();

    // Use a random view key (X25519 accepts any 32 bytes as a private key)
    let view_private_key = *blake3::hash(b"stealth-view-key-seed").as_bytes();

    let receiver_keys = StealthKeys::from_keys(view_private_key, spend_private_key);
    let meta_address = receiver_keys.meta_address();

    // Sender creates a stealth address for receiver
    let (stealth_address, _ephemeral_secret) = meta_address.generate_stealth_address();

    // Receiver checks ownership with their view and spend keys
    // check_ownership takes view_private_key and spend_pubkey (the Ed25519 public key bytes)
    let spend_pubkey = signing_key.verifying_key().to_bytes();
    let owns = stealth_address.check_ownership(&view_private_key, &spend_pubkey);
    if !owns {
        return Err("receiver should be able to detect ownership of stealth address".into());
    }

    // Derive spending key
    let spending_key = stealth_address.derive_spending_key(&view_private_key, &spend_private_key);
    // derive_spending_key returns [u8; 32], should be non-zero
    if spending_key == [0u8; 32] {
        return Err("spending key should not be all zeros".into());
    }

    Ok(())
}

fn check_pedersen_conservation() -> Result<(), String> {
    use curve25519_dalek::scalar::Scalar;

    // Inputs: 2 notes worth 100 and 200
    let blinding_in1 = Scalar::from(111u64);
    let blinding_in2 = Scalar::from(222u64);
    let commit_in1 = ValueCommitment::commit(100, &blinding_in1);
    let commit_in2 = ValueCommitment::commit(200, &blinding_in2);

    // Outputs: 2 notes worth 150 and 150
    let blinding_out1 = Scalar::from(333u64);
    let blinding_out2 = blinding_in1 + blinding_in2 - blinding_out1; // balance blindings
    let commit_out1 = ValueCommitment::commit(150, &blinding_out1);
    let commit_out2 = ValueCommitment::commit(150, &blinding_out2);

    // The excess blinding: sum(input blindings) - sum(output blindings)
    let excess_blinding = (blinding_in1 + blinding_in2) - (blinding_out1 + blinding_out2);

    // Prove conservation: sum(inputs) == sum(outputs)
    let inputs = vec![commit_in1, commit_in2];
    let outputs = vec![commit_out1, commit_out2];
    let message = b"preflight-conservation-test";

    let proof = prove_conservation(&inputs, &outputs, &excess_blinding, message);
    let valid = verify_conservation(&inputs, &outputs, &proof, message);
    if valid.is_err() {
        return Err(format!(
            "conservation proof should verify (100+200 == 150+150): {:?}",
            valid.err()
        ));
    }

    Ok(())
}

fn check_range_proof() -> Result<(), String> {
    use curve25519_dalek::scalar::Scalar;

    let value: u64 = 42;
    let blinding = Scalar::from(12345u64);
    let commitment = ValueCommitment::commit(value, &blinding);

    // Generate a Bulletproof range proof
    let range_proof = BulletproofRangeProof::prove_range(value, &blinding);

    // Verify range proof
    range_proof
        .verify_range(&commitment)
        .map_err(|e| format!("range proof verification failed: {e:?}"))?;

    Ok(())
}

fn check_encrypted_intent() -> Result<(), String> {
    let spec = MatchSpec::default();

    let commitment = CommitmentId([0xABu8; 32]);
    let epoch = 1;
    let expiry = Some(1000u64);

    // Create encrypted intent
    let (encrypted, creator_keypair) = EncryptedIntent::create(&spec, commitment, epoch, expiry);

    // Decrypt with correct key
    let decrypted = encrypted.decrypt(&creator_keypair.secret);
    match decrypted {
        Some(_decoded_spec) => {
            // Successfully decrypted
        }
        None => return Err("decryption with correct key should succeed".into()),
    }

    // Decrypt with wrong key should fail
    let wrong_key = [0xFFu8; 32];
    let bad_decrypt = encrypted.decrypt(&wrong_key);
    if bad_decrypt.is_some() {
        return Err("decryption with wrong key should fail".into());
    }

    Ok(())
}

/// Adversarial: Pedersen conservation proof with WRONG amounts should be rejected.
fn check_pedersen_tampered_rejected() -> Result<(), String> {
    use curve25519_dalek::scalar::Scalar;

    // Inputs: 100 + 200 = 300
    let blinding_in1 = Scalar::from(111u64);
    let blinding_in2 = Scalar::from(222u64);
    let commit_in1 = ValueCommitment::commit(100, &blinding_in1);
    let commit_in2 = ValueCommitment::commit(200, &blinding_in2);

    // BAD outputs: 200 + 200 = 400 (does NOT equal 300)
    let blinding_out1 = Scalar::from(333u64);
    let blinding_out2 = Scalar::from(444u64); // not balanced
    let commit_out1 = ValueCommitment::commit(200, &blinding_out1);
    let commit_out2 = ValueCommitment::commit(200, &blinding_out2);

    // The "excess blinding" is computed wrong (doesn't balance)
    let excess_blinding = (blinding_in1 + blinding_in2) - (blinding_out1 + blinding_out2);

    let inputs = vec![commit_in1, commit_in2];
    let outputs = vec![commit_out1, commit_out2];
    let message = b"preflight-tampered-conservation";

    let proof = prove_conservation(&inputs, &outputs, &excess_blinding, message);
    let result = verify_conservation(&inputs, &outputs, &proof, message);

    // This should FAIL because sum(inputs) != sum(outputs).
    if result.is_ok() {
        return Err(
            "conservation proof should REJECT when amounts don't balance (100+200 != 200+200)"
                .into(),
        );
    }

    Ok(())
}

/// Verify the note -> nullifier -> double-spend detection path end-to-end.
fn check_note_nullifier_derivation() -> Result<(), String> {
    use dregg_cell::{Note, NullifierSet};

    let owner = *blake3::hash(b"note-owner-key").as_bytes();
    let spending_key = *blake3::hash(b"spending-key-secret").as_bytes();
    let randomness = *blake3::hash(b"note-randomness").as_bytes();

    // Create a note with a specific value.
    let note = Note::with_randomness(owner, [500, 0, 0, 0, 0, 0, 0, 0], randomness);

    // Verify commitment is deterministic.
    let commitment_1 = note.commitment();
    let commitment_2 = note.commitment();
    if commitment_1.0 != commitment_2.0 {
        return Err("note commitment should be deterministic".into());
    }

    // Derive nullifier.
    let nullifier = note.nullifier(&spending_key);
    if nullifier.0 == [0u8; 32] {
        return Err("nullifier should not be all zeros".into());
    }

    // Nullifier should be deterministic (same key => same nullifier).
    let nullifier_2 = note.nullifier(&spending_key);
    if nullifier.0 != nullifier_2.0 {
        return Err("nullifier should be deterministic".into());
    }

    // Different spending key => different nullifier (unlinkability).
    let other_key = *blake3::hash(b"other-spending-key").as_bytes();
    let other_nullifier = note.nullifier(&other_key);
    if nullifier.0 == other_nullifier.0 {
        return Err("different spending keys should produce different nullifiers".into());
    }

    // Double-spend prevention via NullifierSet.
    let mut nullifier_set = NullifierSet::new();
    nullifier_set
        .insert(nullifier)
        .map_err(|e| format!("first spend failed: {e:?}"))?;

    // Second spend of same nullifier: MUST fail.
    let double_result = nullifier_set.insert(nullifier);
    if double_result.is_ok() {
        return Err("double-spend (same nullifier inserted twice) should be REJECTED".into());
    }

    Ok(())
}
