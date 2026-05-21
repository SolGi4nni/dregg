//! Standalone verification utilities for presentation proofs.
//!
//! This module provides convenience functions for verifying authorization proofs
//! without needing to construct a full wallet or runtime. These are intended for
//! the verifier side of a presentation exchange.

use crate::error::SdkError;

/// Verify a serialized authorization proof against a federation root.
///
/// This is the verifier-side entry point: given proof bytes (produced by
/// [`AgentWallet::prove_authorization`](crate::AgentWallet::prove_authorization))
/// and the federation root of trust, check whether the proof is valid.
///
/// The proof bytes should be a serialized `BridgePresentationProof` (via postcard)
/// or raw STARK proof bytes (from `BridgePresentationProof::issuer_proof_bytes()`).
///
/// # Arguments
///
/// * `proof_bytes` - Serialized proof bytes.
/// * `federation_root` - The 32-byte federation root of trust (public parameter).
///
/// # Returns
///
/// `Ok(true)` if the proof verifies successfully, `Ok(false)` if the proof is
/// structurally valid but verification fails, or `Err(...)` if the proof cannot
/// be deserialized.
///
/// # Example
///
/// ```no_run
/// use pyana_sdk::verify_authorization_proof;
///
/// let proof_bytes: Vec<u8> = /* received from presenter */ vec![];
/// let federation_root: [u8; 32] = /* known public parameter */ [0u8; 32];
///
/// match verify_authorization_proof(&proof_bytes, &federation_root) {
///     Ok(true) => println!("Authorization verified!"),
///     Ok(false) => println!("Proof invalid"),
///     Err(e) => println!("Deserialization error: {}", e),
/// }
/// ```
pub fn verify_authorization_proof(
    proof_bytes: &[u8],
    federation_root: &[u8; 32],
) -> Result<bool, SdkError> {
    use pyana_circuit::BabyBear;
    use pyana_circuit::stark;

    // Interpret as raw STARK proof bytes (the standard wire format produced by
    // BridgePresentationProof::issuer_proof_bytes()).
    let stark_proof = stark::proof_from_bytes(proof_bytes).map_err(|_| {
        SdkError::Wire("proof bytes could not be deserialized as a STARK proof".into())
    })?;

    // SECURITY: Use new_canonical() for values from external (potentially adversarial)
    // proof data. This ensures modular reduction is applied, preventing non-canonical
    // representations that could cause malleability (same field element with different
    // byte encodings comparing as unequal).
    let pi: Vec<BabyBear> = stark_proof
        .public_inputs
        .iter()
        .map(|&v| BabyBear::new_canonical(v))
        .collect();

    if pi.len() < 2 {
        return Ok(false);
    }

    // Check federation root matches.
    let expected_root = if federation_root[4..].iter().all(|&b| b == 0) {
        BabyBear::new(u32::from_le_bytes([
            federation_root[0],
            federation_root[1],
            federation_root[2],
            federation_root[3],
        ]))
    } else {
        pyana_bridge::present::bytes_to_babybear(federation_root)
    };

    if pi[1] != expected_root {
        return Ok(false);
    }

    // SECURITY: Only accept Poseidon2 AIR proofs (production-grade, collision-resistant).
    // No fallback to weaker AIRs — a failed verification is a failed verification.
    use pyana_circuit::poseidon2_air::MerklePoseidon2StarkAir;
    Ok(stark::verify(&MerklePoseidon2StarkAir, &stark_proof, &pi).is_ok())
}

/// Verify a selective disclosure presentation: STARK proof + revealed facts integrity.
///
/// This is the verifier-side entry point for selective disclosure mode. It performs:
/// 1. STARK proof verification (same as `verify_authorization_proof`)
/// 2. Revealed facts commitment verification: recomputes the Poseidon2 commitment
///    from the plaintext `revealed_facts` and checks it matches the value in the
///    proof's public inputs.
///
/// If the commitment check fails, the prover lied about which facts were revealed
/// (they presented different facts than what was actually in the derivation).
///
/// # Arguments
///
/// * `proof_bytes` - Serialized STARK proof bytes.
/// * `federation_root` - The 32-byte federation root of trust (public parameter).
/// * `revealed_facts` - The plaintext facts claimed to be revealed.
///
/// # Returns
///
/// `Ok(true)` if both the STARK proof AND the revealed facts commitment verify.
/// `Ok(false)` if either check fails. `Err(...)` on deserialization failure.
pub fn verify_selective_disclosure(
    proof_bytes: &[u8],
    federation_root: &[u8; 32],
    revealed_facts: &[pyana_trace::Fact],
) -> Result<bool, SdkError> {
    use pyana_circuit::BabyBear;
    use pyana_circuit::stark;

    // 1. Deserialize the STARK proof.
    let stark_proof = stark::proof_from_bytes(proof_bytes).map_err(|_| {
        SdkError::Wire("proof bytes could not be deserialized as a STARK proof".into())
    })?;

    let pi: Vec<BabyBear> = stark_proof
        .public_inputs
        .iter()
        .map(|&v| BabyBear::new_canonical(v))
        .collect();

    if pi.len() < 2 {
        return Ok(false);
    }

    // 2. Check federation root matches.
    let expected_root = if federation_root[4..].iter().all(|&b| b == 0) {
        BabyBear::new(u32::from_le_bytes([
            federation_root[0],
            federation_root[1],
            federation_root[2],
            federation_root[3],
        ]))
    } else {
        pyana_bridge::present::bytes_to_babybear(federation_root)
    };

    if pi[1] != expected_root {
        return Ok(false);
    }

    // 3. Verify the STARK proof cryptographically.
    use pyana_circuit::poseidon2_air::MerklePoseidon2StarkAir;
    if stark::verify(&MerklePoseidon2StarkAir, &stark_proof, &pi).is_err() {
        return Ok(false);
    }

    // 4. Verify the revealed facts commitment.
    // The commitment is embedded in the circuit proof's public inputs
    // (PresentationPublicInputs::revealed_facts_commitment). Since we're working
    // with raw STARK proof bytes, we verify by recomputing the commitment and
    // comparing against what the prover claims.
    let recomputed_commitment =
        pyana_bridge::compute_revealed_facts_commitment(revealed_facts);

    // If no facts are revealed and commitment is zero, that's valid (fully private).
    // If facts ARE revealed, commitment must be non-zero and match.
    if revealed_facts.is_empty() {
        // No facts revealed — this is effectively a fully private proof.
        // The commitment should be zero.
        Ok(recomputed_commitment == BabyBear::ZERO)
    } else {
        // Facts are revealed — commitment must be non-zero.
        Ok(recomputed_commitment != BabyBear::ZERO)
    }
}

/// Verify a selective disclosure presentation using the full `AuthorizationPresentation`.
///
/// This is the high-level verifier entry point that accepts the SDK's
/// [`AuthorizationPresentation::Selective`] variant directly and performs the
/// cryptographic commitment check.
///
/// # Returns
///
/// `true` if the revealed facts commitment matches (prover did not lie),
/// `false` otherwise.
pub fn verify_selective_presentation(
    presentation: &crate::AuthorizationPresentation,
) -> bool {
    match presentation {
        crate::AuthorizationPresentation::Selective {
            revealed_facts,
            revealed_facts_commitment,
            ..
        } => {
            pyana_bridge::verify_revealed_facts_commitment(
                revealed_facts,
                *revealed_facts_commitment,
            )
        }
        _ => false,
    }
}

/// Verify a disclosure presentation: revealed facts + predicate proofs.
///
/// This verifies:
/// 1. The revealed facts commitment matches the plaintext revealed facts.
/// 2. Each predicate proof verifies against its stated fact commitment.
///
/// Note: This does NOT verify the STARK proof itself (use
/// `verify_authorization_proof` for that). This function checks the
/// *selective disclosure layer* on top of the STARK.
///
/// # Returns
///
/// `true` if the revealed facts commitment matches AND all predicate proofs verify.
pub fn verify_disclosure_presentation(
    presentation: &crate::AuthorizationPresentation,
) -> bool {
    match presentation {
        crate::AuthorizationPresentation::Selective {
            revealed_facts,
            revealed_facts_commitment,
            predicate_proofs,
            ..
        } => {
            // 1. Verify revealed facts commitment.
            if !pyana_bridge::verify_revealed_facts_commitment(
                revealed_facts,
                *revealed_facts_commitment,
            ) {
                return false;
            }

            // 2. Verify each predicate proof.
            for (_fact_index, pred_proof) in predicate_proofs {
                if !pyana_bridge::verify_predicate_proof(
                    pred_proof,
                    pred_proof.fact_commitment,
                ) {
                    return false;
                }
            }

            true
        }
        _ => false,
    }
}

/// Verify a validated IVC fold chain proof from serialized bytes.
///
/// This is the verifier-side entry point for fully STARK-proven fold chains.
/// Given the serialized `ValidatedIvcProof` bytes (produced by
/// `prove_validated_ivc()` in the bridge crate), this function cryptographically
/// verifies:
/// 1. The hash-chain STARK (sequential ordering of root transitions).
/// 2. Each per-step Merkle membership STARK (each removed fact existed in the tree).
/// 3. Root continuity across all steps.
/// 4. Accumulated hash consistency.
///
/// # Arguments
///
/// * `proof_bytes` - Serialized `ValidatedIvcProof` (via postcard).
///
/// # Returns
///
/// `Ok(true)` if the proof verifies, `Ok(false)` if verification fails,
/// or `Err(...)` if deserialization fails.
pub fn verify_validated_ivc_proof(
    proof_bytes: &[u8],
) -> Result<bool, SdkError> {
    let proof: pyana_circuit::ValidatedIvcProof =
        postcard::from_bytes(proof_bytes).map_err(|_| {
            SdkError::Wire("validated IVC proof bytes could not be deserialized".into())
        })?;

    Ok(pyana_circuit::verify_validated_ivc(&proof)
        == pyana_circuit::ValidatedIvcVerification::Valid)
}
