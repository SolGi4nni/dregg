//! Standalone verification utilities for presentation proofs.
//!
//! This module provides convenience functions for verifying authorization proofs
//! without needing to construct a full cipherclerk or runtime. These are intended for
//! the verifier side of a presentation exchange.

use crate::error::SdkError;
use dregg_circuit::presentation::{DescriptorProofWire, verify_descriptor_wire};

/// The descriptor-wire bundle the SDK verifier consumes after the `StarkProof` → IR-v2
/// wire flip (Golden Lift S3c): the two committed descriptor proofs a presentation reduces
/// to, each verified via `descriptor_by_name` → decode `postcard(Ir2BatchProof)` →
/// `verify_vm_descriptor2` (the [`verify_descriptor_wire`] helper).
///
/// This replaces the opaque single hand-STARK `proof_to_bytes(StarkProof)` blob (a merkle-membership
/// STARK that baked leaf/root + action-binding into one AIR). That combined statement is now
/// split across two committed descriptors, mirroring
/// [`dregg_circuit::presentation::RealPresentationProof::verify`]:
///
/// * `blinded_membership` — the depth-general 4-ary blinded ring-membership proof
///   (`dregg-blinded-membership-4ary-general-depth{N}`); PIs `[blinded_leaf, root]`. Proves the
///   issuer is a member of the federation rooted at `root` (unlinkably).
/// * `bound_presentation` — the bound-presentation proof (`dregg-bound-presentation::v1`); PIs
///   `[federation_root, action_binding(8), timestamp, presentation_tag, revealed_facts(8),
///   verifier_nonce]`. Binds the action/resource and (for selective disclosure) the revealed-facts
///   commitment in-circuit.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct AuthorizationDescriptorProof {
    /// AUTH: the bound-presentation descriptor wire (action binding + revealed facts + tag).
    pub bound_presentation: DescriptorProofWire,
    /// RING/UNLINKABILITY: the blinded ring-membership descriptor wire (issuer ∈ federation).
    pub blinded_membership: DescriptorProofWire,
}

/// Categorised outcome of a verification call.
///
/// Several SDK verification helpers historically returned `bool` and silently
/// swallowed the underlying failure category (decode error, STARK rejection,
/// wrong federation root, expired freshness, …). Callers that wrote
/// `if !verify(...) { reject }` could not distinguish a structural decode
/// failure from a valid proof against the wrong root. This enum surfaces those
/// distinctions for operational logging and alerting (P2-3 from
/// `AUDIT-sdk-rest.md`).
///
/// Use [`VerifyOutcome::is_ok`] when callers only need a boolean answer.
#[derive(Debug, Clone)]
pub enum VerifyOutcome {
    /// The proof verified successfully.
    Ok,
    /// The proof bytes could not be deserialized.
    DecodeError(String),
    /// The STARK verifier rejected the proof.
    StarkInvalid,
    /// The proof was structurally valid but bound to a different federation root.
    RootMismatch,
    /// The proof's freshness window has elapsed.
    FreshnessExpired,
    /// The proof carries an AIR name that does not match what the verifier expected.
    WrongAir {
        /// Expected AIR identifier.
        expected: &'static str,
        /// AIR identifier carried by the proof.
        got: String,
    },
    /// A STARK proof was required but not present.
    NoStarkProof,
    /// The presentation kind (e.g., `Selective` vs `Trusted`) did not match the verifier.
    WrongPresentationKind,
    /// The revealed-facts commitment does not match the revealed plaintext.
    RevealedFactsMismatch,
    /// A predicate-proof variant failed verification.
    PredicateProofInvalid,
}

impl VerifyOutcome {
    /// Returns `true` only for [`VerifyOutcome::Ok`].
    pub fn is_ok(&self) -> bool {
        matches!(self, VerifyOutcome::Ok)
    }
}

/// Verify a serialized authorization proof against a federation root.
///
/// This is the verifier-side entry point: given proof bytes (produced by
/// [`AgentCipherclerk::prove_authorization`](crate::AgentCipherclerk::prove_authorization))
/// and the federation root of trust, check whether the proof is valid.
///
/// The proof bytes are a postcard-encoded [`AuthorizationDescriptorProof`] (the two committed
/// descriptor wires — blinded ring-membership + bound-presentation).
///
/// # Arguments
///
/// * `proof_bytes` - Serialized proof bytes.
/// * `federation_root` - The 32-byte federation root of trust (public parameter).
/// * `expected_action` - The action string the proof must be bound to (e.g., "read", "write").
/// * `expected_resource` - The resource string the proof must be bound to (e.g., "api/v1/users").
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
/// use dregg_sdk::verify_authorization_proof;
///
/// let proof_bytes: Vec<u8> = /* received from presenter */ vec![];
/// let federation_root: [u8; 32] = /* known public parameter */ [0u8; 32];
/// let expected_action = "read";
/// let expected_resource = "api/v1/users";
///
/// match verify_authorization_proof(&proof_bytes, &federation_root, expected_action, expected_resource) {
///     Ok(true) => println!("Authorization verified!"),
///     Ok(false) => println!("Proof invalid"),
///     Err(e) => println!("Deserialization error: {}", e),
/// }
/// ```
pub fn verify_authorization_proof(
    proof_bytes: &[u8],
    federation_root: &[u8; 32],
    expected_action: &str,
    expected_resource: &str,
) -> Result<bool, SdkError> {
    let bundle: AuthorizationDescriptorProof = postcard::from_bytes(proof_bytes).map_err(|_| {
        SdkError::Wire(
            "proof bytes could not be deserialized as an AuthorizationDescriptorProof".into(),
        )
    })?;
    verify_authorization_bundle(&bundle, federation_root, expected_action, expected_resource)
}

/// The expected federation root as a canonical `BabyBear`, using the same 32-byte decode the
/// legacy hand-STARK path used: a value that fits in the low 4 bytes is read as an LE `u32`;
/// otherwise the full-width Poseidon2 compression (`bytes_to_babybear`) is applied.
fn expected_federation_root(federation_root: &[u8; 32]) -> dregg_circuit::BabyBear {
    use dregg_circuit::BabyBear;
    if federation_root[4..].iter().all(|&b| b == 0) {
        BabyBear::new(u32::from_le_bytes([
            federation_root[0],
            federation_root[1],
            federation_root[2],
            federation_root[3],
        ]))
    } else {
        dregg_bridge::present::bytes_to_babybear(federation_root)
    }
}

/// Fail-closed descriptor-identity gate: the two wires MUST name the exact expected descriptors
/// (bound-presentation + a depth-general 4-ary blinded-membership). A wire naming any other
/// descriptor is refused with the typed [`SdkError::UnknownAir`] — never checked against the
/// wrong constraint semantics (the flip's analog of the removed air-name dispatch guard).
fn check_bundle_predicates(bundle: &AuthorizationDescriptorProof) -> Result<(), SdkError> {
    use dregg_circuit::blinded_membership_witness::BLINDED_4ARY_NAME_PREFIX;
    use dregg_circuit::bound_presentation_witness::BOUND_PRESENTATION_NAME;

    if bundle.bound_presentation.predicate != BOUND_PRESENTATION_NAME {
        return Err(SdkError::UnknownAir {
            air_name: bundle.bound_presentation.predicate.clone(),
        });
    }
    if !bundle
        .blinded_membership
        .predicate
        .starts_with(BLINDED_4ARY_NAME_PREFIX)
    {
        return Err(SdkError::UnknownAir {
            air_name: bundle.blinded_membership.predicate.clone(),
        });
    }
    Ok(())
}

/// Verify both committed descriptor wires and return the bound-presentation public inputs on
/// success (so a caller like [`verify_selective_disclosure`] can additionally bind the
/// revealed-facts commitment). Mirrors
/// [`dregg_circuit::presentation::RealPresentationProof::verify`] steps 4(a)/4(b):
///   (a) MEMBERSHIP: the blinded ring-membership proof's committed root must be `federation_root`.
///   (b) AUTH: the bound-presentation proof's federation-root PI must match, and its action-binding
///       PIs must equal the binding recomputed from `(expected_action, expected_resource)`.
/// Fail-closed: any decode/verify/PI-length/root/action mismatch is `Ok(None)`; an unknown
/// descriptor identity is `Err(SdkError::UnknownAir)`.
fn verify_authorization_wires(
    bundle: &AuthorizationDescriptorProof,
    federation_root: &[u8; 32],
    expected_action: &str,
    expected_resource: &str,
) -> Result<Option<Vec<dregg_circuit::BabyBear>>, SdkError> {
    use dregg_circuit::blinded_membership_witness::PI_ROOT_4ARY;
    use dregg_circuit::bound_presentation_witness::{FEDERATION_ROOT, REQUEST_PREDICATE_BASE};

    check_bundle_predicates(bundle)?;
    let expected_root = expected_federation_root(federation_root);

    // (a) MEMBERSHIP: verify the blinded ring-membership proof; PIs [blinded_leaf, root].
    let blinded_pis = match verify_descriptor_wire(&bundle.blinded_membership) {
        Some(pis) if pis.len() > PI_ROOT_4ARY => pis,
        _ => return Ok(None),
    };
    if blinded_pis[PI_ROOT_4ARY] != expected_root {
        // Issuer is not a member of the federation rooted at `federation_root`.
        return Ok(None);
    }

    // (b) AUTH: verify the bound-presentation proof; bind federation_root + action binding.
    let bound_pis = match verify_descriptor_wire(&bundle.bound_presentation) {
        Some(pis) if pis.len() >= REQUEST_PREDICATE_BASE + dregg_circuit::ACTION_BINDING_WIDTH => {
            pis
        }
        _ => return Ok(None),
    };
    if bound_pis[FEDERATION_ROOT] != expected_root {
        return Ok(None);
    }
    let expected_binding =
        dregg_circuit::compute_action_binding(expected_action, expected_resource);
    for i in 0..dregg_circuit::ACTION_BINDING_WIDTH {
        if bound_pis[REQUEST_PREDICATE_BASE + i] != expected_binding[i] {
            return Ok(None); // proof not bound to this (action, resource)
        }
    }

    Ok(Some(bound_pis))
}

/// Verify an [`AuthorizationDescriptorProof`] against a federation root and expected action/resource.
///
/// This is the descriptor-verify body [`verify_authorization_proof`] dispatches to after decoding
/// the wire bundle. It accepts only when BOTH committed descriptors verify AND bind this
/// federation root + action, preserving the legacy accept/reject semantics (membership + action)
/// against the IR-v2 descriptor prover instead of the removed hand-STARK path.
pub fn verify_authorization_bundle(
    bundle: &AuthorizationDescriptorProof,
    federation_root: &[u8; 32],
    expected_action: &str,
    expected_resource: &str,
) -> Result<bool, SdkError> {
    Ok(
        verify_authorization_wires(bundle, federation_root, expected_action, expected_resource)?
            .is_some(),
    )
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
    expected_action: &str,
    expected_resource: &str,
    revealed_facts: &[dregg_trace::Fact],
) -> Result<bool, SdkError> {
    use dregg_circuit::binding::WideHash;
    use dregg_circuit::bound_presentation_witness::REVEALED_FACTS_BASE;

    // 1. Decode the descriptor-wire bundle (replaces the removed hand-STARK proof_from_bytes).
    let bundle: AuthorizationDescriptorProof = postcard::from_bytes(proof_bytes).map_err(|_| {
        SdkError::Wire(
            "proof bytes could not be deserialized as an AuthorizationDescriptorProof".into(),
        )
    })?;

    // 2. Verify membership + federation-root + action binding on the two committed descriptors
    //    (same as verify_authorization_proof); recover the bound-presentation public inputs.
    let bound_pis = match verify_authorization_wires(
        &bundle,
        federation_root,
        expected_action,
        expected_resource,
    )? {
        Some(pis) => pis,
        None => return Ok(false),
    };

    // 3. Verify the revealed-facts commitment against the bound-presentation descriptor's
    //    revealed_facts PIs (cols REVEALED_FACTS_BASE..+8, constrained in-circuit). Recompute
    //    the commitment from the plaintext revealed_facts and compare to the committed value.
    let recomputed_commitment = dregg_bridge::compute_revealed_facts_commitment(revealed_facts);

    if revealed_facts.is_empty() {
        // No facts revealed — effectively fully private; the recomputed commitment must be zero.
        return Ok(recomputed_commitment.is_zero());
    }

    // Facts ARE revealed — the recomputed commitment must be non-zero.
    if recomputed_commitment.is_zero() {
        return Ok(false);
    }

    // The bound-presentation PIs carry the revealed_facts commitment as a WideHash::WIDTH-felt
    // slice. If the PI vector is too short, it was not a selective-disclosure proof — reject.
    if bound_pis.len() < REVEALED_FACTS_BASE + WideHash::WIDTH {
        return Ok(false);
    }
    let proof_commitment = WideHash::from_felts(
        &bound_pis[REVEALED_FACTS_BASE..REVEALED_FACTS_BASE + WideHash::WIDTH],
    )
    .expect("RFC slice is exactly WideHash::WIDTH felts by construction");

    Ok(recomputed_commitment == proof_commitment)
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
pub fn verify_selective_presentation(presentation: &crate::AuthorizationPresentation) -> bool {
    match presentation {
        crate::AuthorizationPresentation::Selective {
            revealed_facts,
            revealed_facts_commitment,
            ..
        } => dregg_bridge::verify_revealed_facts_commitment(
            revealed_facts,
            *revealed_facts_commitment,
        ),
        _ => false,
    }
}

/// Verify the revealed-facts half of a disclosure presentation.
///
/// This verifies ONE thing: the revealed facts commitment matches the plaintext revealed facts.
/// It does NOT verify the STARK proof itself (use `verify_authorization_proof` for that).
///
/// # Predicate proofs are NOT verified here — and CANNOT be
///
/// A predicate proof is a claim about a fact the verifier never sees, pinned to a
/// `fact_commitment`. Checking it requires the commitment the VERIFIER derives from token state it
/// trusts (`dregg_bridge::verify_predicate_proof`'s `expected_fact_commitment`). Nothing in an
/// `AuthorizationPresentation` is such a source: `predicate_proofs` carries only the prover's own
/// `fact_commitment`, and the authorization STARK binds `revealed_facts_commitment` but does not
/// attest the predicate facts' commitments as public inputs.
///
/// This function previously "verified" them by feeding `verify_predicate_proof` the proof's own
/// commitment — reducing its gate to `x != x`, always false, never rejecting. Every predicate proof
/// passed, including one about a fact of the prover's own invention. That is fail-OPEN, so it is
/// gone. A presentation carrying predicate proofs now fails CLOSED here (mirroring
/// [`verify_validated_ivc_proof`]): this function has no trusted state, so it never accepts a claim
/// it cannot check.
///
/// Callers holding trusted token state must use
/// [`verify_disclosure_presentation_against_state`], which derives each expected commitment
/// canonically and is the only sound way to accept a predicate proof.
///
/// # Returns
///
/// `true` if the revealed facts commitment matches AND the presentation carries no predicate
/// proofs. `false` for any other variant, a commitment mismatch, or any predicate proof present.
pub fn verify_disclosure_presentation(presentation: &crate::AuthorizationPresentation) -> bool {
    match presentation {
        crate::AuthorizationPresentation::Selective {
            revealed_facts,
            revealed_facts_commitment,
            predicate_proofs,
            ..
        } => {
            // 1. Verify revealed facts commitment.
            if !dregg_bridge::verify_revealed_facts_commitment(
                revealed_facts,
                *revealed_facts_commitment,
            ) {
                return false;
            }

            // 2. FAIL-CLOSED: no trusted state here, so no predicate proof can be checked. Never
            //    accept one on the prover's say-so.
            predicate_proofs.is_empty()
        }
        _ => false,
    }
}

/// Verify a disclosure presentation against TRUSTED token state: revealed facts + predicate proofs.
///
/// This is the sound counterpart to [`verify_disclosure_presentation`]. It verifies:
/// 1. The revealed facts commitment matches the plaintext revealed facts.
/// 2. Every predicate proof verifies against the fact commitment the VERIFIER derives from
///    `trusted_facts` — never the commitment the proof presents.
///
/// It does NOT verify the STARK proof itself (use `verify_authorization_proof` for that).
///
/// # The derivation is the whole point
///
/// `dregg_bridge::verify_predicate_proof` pins `expected_fact_commitment` as the descriptor's
/// `pi[1]`, and the descriptor's value↔fact weld forces the compared value to be the one that
/// commitment covers. So the chain closes only if `expected_fact_commitment` comes from somewhere
/// the prover does not control. Here it comes from `trusted_facts[fact_index]` via
/// [`AgentCipherclerk::derive_fact_commitment`] — the same construction the prover uses, so an
/// honest proof about that fact matches, and a proof about any other fact or value does not.
///
/// # Arguments
///
/// * `presentation` — the presentation to check.
/// * `trusted_facts` — the verifier's OWN copy of the derivation's facts, in trace order (the
///   `derived_fact` of each step, which is what `fact_index` indexes). This must come from state
///   the verifier trusts — re-evaluating the policy itself, an issuer-side record — NOT from the
///   presentation.
/// * `state_root` — the token-state root the commitments are taken against
///   ([`AgentCipherclerk::fact_commitment_state_root`] of the trusted token).
///
/// # Returns
///
/// `true` if the revealed facts commitment matches AND every predicate proof verifies against its
/// derived expected commitment. Fail-closed: a `fact_index` with no trusted fact, a fact whose
/// value cannot be canonically derived, or any failed proof yields `false`.
pub fn verify_disclosure_presentation_against_state(
    presentation: &crate::AuthorizationPresentation,
    trusted_facts: &[dregg_trace::Fact],
    state_root: dregg_circuit::BabyBear,
) -> bool {
    match presentation {
        crate::AuthorizationPresentation::Selective {
            revealed_facts,
            revealed_facts_commitment,
            predicate_proofs,
            ..
        } => {
            // 1. Verify revealed facts commitment.
            if !dregg_bridge::verify_revealed_facts_commitment(
                revealed_facts,
                *revealed_facts_commitment,
            ) {
                return false;
            }

            // 2. Verify each predicate proof against a commitment DERIVED FROM TRUSTED STATE.
            for (fact_index, pred_proof) in predicate_proofs {
                // A proof pointing at an index the verifier has no trusted fact for is refused:
                // the verifier cannot say what fact it is about, so it cannot accept it.
                let Some(trusted_fact) = trusted_facts.get(*fact_index) else {
                    return false;
                };
                // The VALUE comes from trusted state; only the blinding (the opening) comes from the
                // proof, and that freedom cannot move which fact the commitment names.
                let Ok(expected) = crate::AgentCipherclerk::derive_fact_commitment(
                    trusted_fact,
                    state_root,
                    dregg_circuit::predicate_arith_witness::Blinding(pred_proof.blinding),
                ) else {
                    return false;
                };
                if !dregg_bridge::verify_predicate_proof(pred_proof, expected) {
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
/// Currently always `Ok(false)` (fail-closed). The validated-IVC fold proof was produced
/// and checked by the retired hand-STARK engine (`ValidatedIvcProof` /
/// `verify_validated_ivc`), which was deleted; no descriptor replacement for the
/// validated-IVC fold statement exists yet. Rather than accept an unverifiable claim
/// (fail-open), this rejects every input — mirroring the bridge's validated-IVC handling
/// (`dregg_bridge` returns `false` with no proof to check).
pub fn verify_validated_ivc_proof(_proof_bytes: &[u8]) -> Result<bool, SdkError> {
    // FAIL-CLOSED: no way to cryptographically verify a validated-IVC fold proof in this
    // build (the hand-STARK verifier was retired, no descriptor path exists). Never accept.
    Ok(false)
}

// ============================================================================
// Tier-gated verification
// ============================================================================

/// Verify a serialized authorization proof (production entry point).
///
/// This is the production-safe entry point. It performs full STARK verification
/// including action/resource binding and composition commitment checks.
///
/// Tier gating has been removed per the verification policy simplification:
/// if a proof cryptographically verifies (passes `verify_authorization_proof`),
/// it is valid regardless of which backend produced it. Structural stubs cannot
/// produce valid STARK proofs and are rejected by the cryptographic check itself.
/// The tier is retained as informational metadata only.
///
/// # Errors
///
/// Returns `Err` if:
/// - The proof cannot be deserialized
/// - STARK verification fails
/// - Action/resource binding fails
/// - Composition commitment is missing or invalid
pub fn verify_production(
    proof_bytes: &[u8],
    federation_root: &[u8; 32],
    expected_action: &str,
    expected_resource: &str,
) -> Result<dregg_circuit::VerifiedProof, SdkError> {
    use dregg_circuit::proof_tier;

    // Perform the standard verification (including action/resource binding).
    let valid = verify_authorization_proof(
        proof_bytes,
        federation_root,
        expected_action,
        expected_resource,
    )?;
    if !valid {
        return Err(SdkError::Wire("proof verification failed".into()));
    }

    // Return a VerifiedProof with informational tier metadata.
    // No tier gating: if the STARK verified, the proof is accepted.
    Ok(dregg_circuit::VerifiedProof::with_federation_root(
        proof_tier::stark_tier(),
        proof_tier::STARK_BACKEND,
        *federation_root,
    ))
}

/// Verify a serialized authorization proof accepting any tier.
///
/// This function is only available in tests or when the `dev` feature is enabled.
/// It performs standard verification but does not enforce a minimum proof tier,
/// allowing structural stubs and experimental backends to pass.
///
/// # Safety
///
/// This MUST NOT be used in production code paths. It exists solely for testing
/// and development workflows where real cryptographic proofs are unavailable.
#[cfg(any(test, feature = "dev"))]
pub fn verify_any_tier(
    proof_bytes: &[u8],
    federation_root: &[u8; 32],
    expected_action: &str,
    expected_resource: &str,
) -> Result<dregg_circuit::VerifiedProof, SdkError> {
    use dregg_circuit::proof_tier;

    let valid = verify_authorization_proof(
        proof_bytes,
        federation_root,
        expected_action,
        expected_resource,
    )?;
    if !valid {
        return Err(SdkError::Wire("proof verification failed".into()));
    }

    // In dev mode, accept any tier.
    Ok(dregg_circuit::VerifiedProof::with_federation_root(
        proof_tier::stark_tier(),
        proof_tier::STARK_BACKEND,
        *federation_root,
    ))
}

/// Verify a committed threshold proof at the SDK level.
///
/// This is the verifier-side convenience function for anonymous credential gates.
/// Given a serialized `CommittedThresholdProof`, a threshold commitment, and a fact
/// commitment, this function verifies that the prover holds a value >= the committed
/// threshold without revealing the actual value.
///
/// # Arguments
///
/// * `proof_bytes` - Serialized `CommittedThresholdProof` bytes (via postcard).
/// * `threshold_commitment` - The 32-byte commitment to the threshold value.
///   Only the first 4 bytes are used (BabyBear field element, little-endian).
/// * `fact_commitment` - The 32-byte commitment to the fact value being proven.
///   Only the first 4 bytes are used (BabyBear field element, little-endian).
///
/// # Returns
///
/// `Ok(true)` if the proof verifies (the prover's value meets the threshold),
/// `Ok(false)` if verification fails, or `Err(...)` if deserialization fails.
///
/// # Example
///
/// ```no_run
/// use dregg_sdk::verify_committed_threshold;
///
/// let proof_bytes: Vec<u8> = /* received from prover */ vec![];
/// let threshold_commitment: [u8; 32] = /* public parameter */ [0u8; 32];
/// let fact_commitment: [u8; 32] = /* from the credential */ [0u8; 32];
///
/// match verify_committed_threshold(&proof_bytes, &threshold_commitment, &fact_commitment) {
///     Ok(true) => println!("Threshold met!"),
///     Ok(false) => println!("Proof invalid or threshold not met"),
///     Err(e) => println!("Error: {}", e),
/// }
/// ```
pub fn verify_committed_threshold(
    _proof_bytes: &[u8],
    _threshold_commitment: &[u8; 32],
    _fact_commitment: &[u8; 32],
) -> Result<bool, SdkError> {
    // FAIL-CLOSED. The committed-threshold (hidden value + hidden threshold) predicate was
    // produced/checked by the retired hand-STARK engine (`CommittedThresholdProof` /
    // `dregg_circuit::verify_committed_threshold`), which was deleted. No IR-v2 descriptor
    // for the committed-threshold statement exists yet — the bridge's counterparts
    // (`prove_committed_threshold` / `verify_committed_threshold_proof`) are themselves
    // fail-closed. Rather than accept an unverifiable claim (fail-open), reject every input.
    // (Since no valid committed-threshold proof can be produced in this build, this rejects
    // all inputs, including the empty-`ProgramProof`-style placeholder blobs.)
    Ok(false)
}

/// Build a federation Merkle tree from member public keys and return the root.
///
/// This is the verifier-side helper for constructing the federation tree that
/// anonymous credential gates need. Given a list of member Ed25519 public keys,
/// this builds the same Merkle tree structure used by `authorize_anonymously` and
/// returns the root hash.
///
/// # Arguments
///
/// * `member_keys` - Slice of 32-byte Ed25519 public keys for federation members.
///
/// # Returns
///
/// The 32-byte Merkle root that can be used as the `federation_root` parameter
/// when verifying ring membership proofs.
pub fn build_federation_tree(member_keys: &[[u8; 32]]) -> [u8; 32] {
    if member_keys.is_empty() {
        return *blake3::hash(b"dregg-federation:empty").as_bytes();
    }

    // Hash each member key to produce leaves.
    let mut leaves: Vec<[u8; 32]> = member_keys
        .iter()
        .map(|key| {
            let mut hasher = blake3::Hasher::new_derive_key("dregg-federation-leaf-v1");
            hasher.update(key);
            *hasher.finalize().as_bytes()
        })
        .collect();

    // Sort for deterministic ordering.
    leaves.sort();

    // Build binary Merkle tree.
    if leaves.len() == 1 {
        return leaves[0];
    }

    // Pad to next power of two.
    let next_pow2 = leaves.len().next_power_of_two();
    leaves.resize(next_pow2, [0u8; 32]);

    let mut current_level = leaves;
    while current_level.len() > 1 {
        let mut next_level = Vec::with_capacity(current_level.len() / 2);
        for chunk in current_level.chunks(2) {
            let mut hasher = blake3::Hasher::new();
            hasher.update(&chunk[0]);
            hasher.update(&chunk[1]);
            next_level.push(*hasher.finalize().as_bytes());
        }
        current_level = next_level;
    }
    current_level[0]
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_circuit::BabyBear;
    use dregg_circuit::blinded_membership_witness::{
        PI_ROOT_4ARY, blinded_membership_descriptor_of_depth_4ary, blinded_membership_witness_4ary,
    };
    use dregg_circuit::bound_presentation_witness::{
        BOUND_PRESENTATION_NAME, bound_presentation_witness_h4,
    };
    use dregg_circuit::compute_action_binding;
    use dregg_circuit::descriptor_by_name::descriptor_by_name;
    use dregg_circuit::descriptor_ir2::{
        EffectVmDescriptor2, MemBoundaryWitness, prove_vm_descriptor2,
    };

    /// Build a [`DescriptorProofWire`] from a descriptor + honest witness: prove through the REAL
    /// IR-v2 prover, postcard-encode the batch proof, and encode the public inputs into `vk`.
    fn wire_from(
        desc: &EffectVmDescriptor2,
        trace: Vec<Vec<BabyBear>>,
        pis: Vec<BabyBear>,
    ) -> DescriptorProofWire {
        let proof = prove_vm_descriptor2(desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
            .expect("honest witness must prove through the dispatched descriptor");
        let blob = postcard::to_allocvec(&proof).expect("encode batch proof");
        let mut vk = Vec::with_capacity(pis.len() * 4);
        for p in &pis {
            vk.extend_from_slice(&p.0.to_le_bytes());
        }
        DescriptorProofWire {
            predicate: desc.name.clone(),
            blob,
            vk,
        }
    }

    /// Build an honest [`AuthorizationDescriptorProof`] bundle bound to `(action, resource)` with the
    /// given `revealed_facts` commitment felts, plus the matching 32-byte federation root. The blinded
    /// ring-membership proof's committed root becomes the federation root (so the two wires agree).
    fn honest_bundle(
        action: &str,
        resource: &str,
        revealed: [BabyBear; 8],
    ) -> (AuthorizationDescriptorProof, [u8; 32]) {
        // (a) blinded ring-membership (depth-2, 4-ary) — its committed root is the federation root.
        let leaf = BabyBear::new(0xABCD);
        let blinding = BabyBear::new(0xB11D);
        let sibs = [
            [
                BabyBear::new(2002),
                BabyBear::new(3003),
                BabyBear::new(4004),
            ],
            [
                BabyBear::new(5005),
                BabyBear::new(6006),
                BabyBear::new(7007),
            ],
        ];
        let pos = [0u8, 0u8];
        let (bl_trace, bl_pis) =
            blinded_membership_witness_4ary(leaf, blinding, &sibs, &pos).expect("blinded witness");
        let root = bl_pis[PI_ROOT_4ARY];
        let desc_bl = blinded_membership_descriptor_of_depth_4ary(2);
        let blinded_membership = wire_from(&desc_bl, bl_trace, bl_pis);

        // The federation root the caller passes: root's canonical u32 in the low 4 bytes.
        let mut fed = [0u8; 32];
        fed[0..4].copy_from_slice(&root.as_u32().to_le_bytes());

        // (b) bound-presentation — action binding + federation_root + revealed_facts commitment.
        let action_binding = compute_action_binding(action, resource);
        let (bp_trace, bp_pis) = bound_presentation_witness_h4(
            root,
            action_binding,
            BabyBear::new(300),
            revealed,
            BabyBear::new(0xF1A1),
            BabyBear::new(0xBEEF),
            BabyBear::new(0xC0FFEE),
        )
        .expect("bound-presentation witness");
        let desc_bp =
            descriptor_by_name(BOUND_PRESENTATION_NAME).expect("bound-presentation dispatch");
        let bound_presentation = wire_from(&desc_bp, bp_trace, bp_pis);

        (
            AuthorizationDescriptorProof {
                bound_presentation,
                blinded_membership,
            },
            fed,
        )
    }

    /// THE POSITIVE POLE: an honest bundle (both committed descriptors proven by the REAL IR-v2
    /// prover) is ACCEPTED when the federation root + action/resource match.
    #[test]
    fn verify_authorization_proof_accepts_honest_bundle() {
        let zero = [BabyBear::ZERO; 8];
        let (bundle, fed) = honest_bundle("read", "api/v1/users", zero);
        let bytes = postcard::to_allocvec(&bundle).expect("encode bundle");
        assert_eq!(
            verify_authorization_proof(&bytes, &fed, "read", "api/v1/users").unwrap(),
            true,
            "an honest bundle bound to (read, api/v1/users) must verify"
        );
    }

    /// A wrong federation root is REJECTED (membership root no longer matches).
    #[test]
    fn verify_authorization_proof_rejects_wrong_root() {
        let zero = [BabyBear::ZERO; 8];
        let (bundle, mut fed) = honest_bundle("read", "api/v1/users", zero);
        let bytes = postcard::to_allocvec(&bundle).expect("encode bundle");
        fed[0] ^= 0xFF; // perturb the federation root
        assert_eq!(
            verify_authorization_proof(&bytes, &fed, "read", "api/v1/users").unwrap(),
            false,
            "a bundle whose committed root != the caller's federation root must be rejected"
        );
    }

    /// A wrong (action, resource) is REJECTED (the bound-presentation action binding no longer matches).
    #[test]
    fn verify_authorization_proof_rejects_wrong_action() {
        let zero = [BabyBear::ZERO; 8];
        let (bundle, fed) = honest_bundle("read", "api/v1/users", zero);
        let bytes = postcard::to_allocvec(&bundle).expect("encode bundle");
        assert_eq!(
            verify_authorization_proof(&bytes, &fed, "write", "api/v1/users").unwrap(),
            false,
            "a bundle bound to 'read' must be rejected when 'write' is requested"
        );
    }

    /// FAIL-CLOSED: a wire naming a descriptor other than the expected bound-presentation refuses
    /// with the typed `SdkError::UnknownAir` — never checked against the wrong constraint semantics.
    #[test]
    fn verify_authorization_proof_refuses_unknown_predicate_typed() {
        let zero = [BabyBear::ZERO; 8];
        let (mut bundle, fed) = honest_bundle("read", "api/v1/users", zero);
        bundle.bound_presentation.predicate = "totally-unknown-descriptor-v0".to_string();
        let bytes = postcard::to_allocvec(&bundle).expect("encode bundle");
        match verify_authorization_proof(&bytes, &fed, "read", "api/v1/users") {
            Err(SdkError::UnknownAir { air_name }) => {
                assert_eq!(air_name, "totally-unknown-descriptor-v0");
            }
            other => panic!("expected typed SdkError::UnknownAir, got {:?}", other),
        }
    }

    /// A blinded wire whose predicate is not a 4-ary blinded-membership name refuses (typed).
    #[test]
    fn verify_authorization_proof_refuses_wrong_membership_predicate_typed() {
        let zero = [BabyBear::ZERO; 8];
        let (mut bundle, fed) = honest_bundle("read", "api/v1/users", zero);
        bundle.blinded_membership.predicate = "dfa-routing-toggle-2state::poseidon2-v1".to_string();
        let bytes = postcard::to_allocvec(&bundle).expect("encode bundle");
        assert!(
            matches!(
                verify_authorization_proof(&bytes, &fed, "read", "api/v1/users"),
                Err(SdkError::UnknownAir { .. })
            ),
            "a non-blinded-membership predicate must refuse with the typed error"
        );
    }

    /// A tampered proof blob is REJECTED (the IR-v2 verify fails → fail-closed Ok(false)).
    #[test]
    fn verify_authorization_proof_rejects_tampered_blob() {
        let zero = [BabyBear::ZERO; 8];
        let (mut bundle, fed) = honest_bundle("read", "api/v1/users", zero);
        if let Some(b) = bundle.blinded_membership.blob.last_mut() {
            *b ^= 0xFF;
        }
        let bytes = postcard::to_allocvec(&bundle).expect("encode bundle");
        assert_eq!(
            verify_authorization_proof(&bytes, &fed, "read", "api/v1/users").unwrap(),
            false,
            "a tampered membership proof blob must fail verification"
        );
    }

    /// Non-bundle bytes are a typed decode error, not a silent accept.
    #[test]
    fn verify_authorization_proof_rejects_garbage_bytes() {
        let fed = [0u8; 32];
        assert!(
            matches!(
                verify_authorization_proof(&[1, 2, 3, 4, 5], &fed, "read", "res"),
                Err(SdkError::Wire(_))
            ),
            "garbage bytes must be a typed Wire decode error"
        );
    }

    /// Selective disclosure ACCEPTS when the revealed facts match the committed revealed-facts PIs.
    #[test]
    fn verify_selective_disclosure_accepts_matching_facts() {
        let real_facts = vec![dregg_trace::Fact {
            predicate: dregg_trace::symbol_from_str("role"),
            terms: vec![
                dregg_trace::Term::Const(dregg_trace::symbol_from_str("alice")),
                dregg_trace::Term::Const(dregg_trace::symbol_from_str("admin")),
            ],
        }];
        let commitment = dregg_bridge::compute_revealed_facts_commitment(&real_facts);
        let (bundle, fed) = honest_bundle("read", "api/v1/users", *commitment.as_slice());
        let bytes = postcard::to_allocvec(&bundle).expect("encode bundle");
        assert_eq!(
            verify_selective_disclosure(&bytes, &fed, "read", "api/v1/users", &real_facts).unwrap(),
            true,
            "revealed facts matching the committed PIs must verify"
        );
    }

    /// P0 security regression: selective disclosure must REJECT revealed facts that do not match the
    /// commitment bound in the bound-presentation descriptor's revealed_facts public inputs.
    #[test]
    fn verify_selective_disclosure_rejects_wrong_revealed_facts() {
        let real_facts = vec![dregg_trace::Fact {
            predicate: dregg_trace::symbol_from_str("role"),
            terms: vec![
                dregg_trace::Term::Const(dregg_trace::symbol_from_str("alice")),
                dregg_trace::Term::Const(dregg_trace::symbol_from_str("admin")),
            ],
        }];
        let wrong_facts = vec![dregg_trace::Fact {
            predicate: dregg_trace::symbol_from_str("role"),
            terms: vec![
                dregg_trace::Term::Const(dregg_trace::symbol_from_str("mallory")),
                dregg_trace::Term::Const(dregg_trace::symbol_from_str("superadmin")),
            ],
        }];
        let real_commitment = dregg_bridge::compute_revealed_facts_commitment(&real_facts);
        let wrong_commitment = dregg_bridge::compute_revealed_facts_commitment(&wrong_facts);
        assert_ne!(real_commitment, wrong_commitment);

        // Bundle commits the REAL facts commitment; verifying with WRONG facts must not pass.
        let (bundle, fed) = honest_bundle("read", "api/v1/users", *real_commitment.as_slice());
        let bytes = postcard::to_allocvec(&bundle).expect("encode bundle");
        assert_eq!(
            verify_selective_disclosure(&bytes, &fed, "read", "api/v1/users", &wrong_facts)
                .unwrap(),
            false,
            "SECURITY: wrong revealed facts must be rejected"
        );
    }

    /// Empty revealed facts is a fully-private proof: accepted iff the recomputed commitment is zero.
    #[test]
    fn verify_selective_disclosure_empty_facts_is_private() {
        let zero = [BabyBear::ZERO; 8];
        let (bundle, fed) = honest_bundle("read", "api/v1/users", zero);
        let bytes = postcard::to_allocvec(&bundle).expect("encode bundle");
        assert_eq!(
            verify_selective_disclosure(&bytes, &fed, "read", "api/v1/users", &[]).unwrap(),
            true,
            "no revealed facts (empty) is the fully-private case"
        );
    }

    /// P2-3: `VerifyOutcome` exposes failure categories so callers can distinguish decode failure
    /// from STARK rejection. This test pins the shape so future migrations keep the variants.
    #[test]
    fn verify_outcome_shape_smoke() {
        let ok = VerifyOutcome::Ok;
        assert!(ok.is_ok());

        let decode = VerifyOutcome::DecodeError("bad bytes".into());
        assert!(!decode.is_ok());

        let stark = VerifyOutcome::StarkInvalid;
        assert!(!stark.is_ok());

        let root = VerifyOutcome::RootMismatch;
        assert!(!root.is_ok());

        let stale = VerifyOutcome::FreshnessExpired;
        assert!(!stale.is_ok());

        let wrong_air = VerifyOutcome::WrongAir {
            expected: "merkle-v1",
            got: "merkle-v0".into(),
        };
        assert!(!wrong_air.is_ok());

        let nostark = VerifyOutcome::NoStarkProof;
        assert!(!nostark.is_ok());

        let wrong_kind = VerifyOutcome::WrongPresentationKind;
        assert!(!wrong_kind.is_ok());

        let mismatch = VerifyOutcome::RevealedFactsMismatch;
        assert!(!mismatch.is_ok());

        let pred = VerifyOutcome::PredicateProofInvalid;
        assert!(!pred.is_ok());
    }
}
