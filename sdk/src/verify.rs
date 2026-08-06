//! Standalone verification utilities for presentation proofs.
//!
//! This module provides convenience functions for verifying authorization proofs
//! without needing to construct a full cipherclerk or runtime. These are intended for
//! the verifier side of a presentation exchange.

use crate::error::SdkError;
use dregg_circuit::membership_descriptor_4ary::{DIGEST_W, Digest8};
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
///   (`dregg-blinded-membership-4ary-wide-general-depth{N}`); PIs
///   `[blinded_leaf0..8, root0..8]`. Proves the issuer is a member of the federation rooted at
///   `root` (unlinkably).
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
    // ⚑ FIVE VARIANTS DELETED 2026-08-06 — `WrongAir { expected, got }`, `NoStarkProof`,
    // `WrongPresentationKind`, `RevealedFactsMismatch`, `PredicateProofInvalid`. Each was
    // defined, doc-commented, and CONSTRUCTED ZERO TIMES outside the smoke test that
    // pinned its existence: the same `TurnError::EffectsHashMismatch` shape this repo's
    // CLAUDE.md opens with. The enum's stated purpose is *"operational logging and
    // alerting"* — a `WrongAir` alert could never fire, so an operator watching for it was
    // watching a channel with no transmitter.
    //
    // The five that remain are the five the one production producer (`embed.rs`) can
    // actually emit. That producer reaches them by string-sniffing `format!("{e:?}")` for
    // "root" / "freshness", which is its own defect and the named follow-up: the typed
    // information exists at the source (`SdkError::UnknownAir` IS constructed twice in
    // this file) and is thrown away, then guessed at. Restoring `WrongAir` means plumbing
    // that typed error through `embed.rs` — reinstate the variant WITH its producer, not
    // before it.
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

/// ⚑ FLAG DAY — **the 32-byte federation root now CARRIES the 8-felt ring-membership root**, as
/// eight canonical little-endian `u32` limbs. It used to carry ONE `BabyBear` in bytes `0..4` with
/// `4..32` zeroed, because the blinded ring-membership descriptor's committed root was one felt.
/// After the `node8` cutover that root is a full [`Digest8`], and 8 felts × 4 bytes is exactly the
/// 32 the wire already had. A pre-cutover root (one felt, tail zeros) decodes to a digest whose
/// lanes `1..8` are zero, which no honest `node8_4ary` fold produces — so it is REFUSED (by
/// [`refuse_pre_cutover_root`], called on the verify path), never reinterpreted.
///
/// ⚠ **This is NOT an identity decode, and it said it was until 2026-08-06.** The line here
/// read *"This is the identity decode: nothing is projected or discarded."* The callee,
/// `bytes32_to_8_limbs`, computes `BabyBear::new(v % BABYBEAR_P)` per 4-byte chunk — a
/// PROJECTION — and its own docblock is emphatic about the consequence: *"⚑ THE ALIAS RATE IS
/// 100%, NOT 53.1%"*, *"every 32-byte value has at least 2^8 = 256 byte-distinct siblings with
/// an identical limb vector"*, refuted in general by the Lean theorem
/// `capFoldLimbs_not_injective` (`metatheory/Dregg2/Circuit/CapLeafTargetLanes9.lean`). So a
/// 32-byte federation root pinned by a caller has ≥256 byte-distinct siblings this comparison
/// admits. That is the felt-width campaign's boundary, not something a rename fixes — but the
/// sentence claiming the opposite, on the neighbour of an admirably honest *"⚠ This is a
/// ~31-bit binding"* note, is exactly the shape that stops a reader looking.
fn expected_federation_root_d8(federation_root: &[u8; 32]) -> Digest8 {
    dregg_circuit::effect_vm::bytes32_to_8_limbs(federation_root)
}

/// The refusal the docblock above has promised since the `node8` cutover and which, until
/// 2026-08-06, no code performed: a PRE-CUTOVER federation root — one felt in bytes `0..4`
/// and `4..32` zeroed — decodes to a digest whose lanes `1..8` are all zero.
///
/// No honest `node8_4ary` fold produces that (it is a Poseidon2 output; eight simultaneously
/// zero lanes is a ~2^-248 event), so it can only be an old-format 32-byte root being
/// reinterpreted under the new one. Reinterpreting it would compare ONE lane of real entropy
/// and seven zeros against a real 8-lane root — the exact ~31-bit waist the cutover widened.
///
/// Returns `true` when the root must be refused. `[0u8; 32]` — an unset/default anchor — is
/// caught by the same rule, which is correct: it is not a root either.
fn refuse_pre_cutover_root(root8: &Digest8) -> bool {
    root8[1..]
        .iter()
        .all(|lane| *lane == dregg_circuit::BabyBear::ZERO)
}

/// The expected federation root as ONE canonical `BabyBear` — the slot the Lean-emitted
/// `dregg-bound-presentation::v1` descriptor pins at [`FEDERATION_ROOT`].
///
/// ⚠ **This is a ~31-bit binding, and it is the AUTH leg's, not the ring leg's.** It is the
/// Poseidon2 hash of ALL EIGHT limbs of the 32-byte root (`bytes_to_babybear`), NOT lane 0 of
/// [`expected_federation_root_d8`] — the two are independent derivations from the same wire bytes,
/// so widening the ring leg introduced no projection here. The residual is the bound-presentation
/// descriptor's one-felt `federation_root` public input, which is authored in
/// `metatheory/Dregg2/Circuit/Emit/BoundPresentationEmit.lean` and is the named follow-up; the RING
/// leg below binds the root at the full 8-felt width today.
fn expected_federation_root(federation_root: &[u8; 32]) -> dregg_circuit::BabyBear {
    dregg_bridge::present::bytes_to_babybear(federation_root)
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
///   (a) MEMBERSHIP: the blinded ring-membership proof's committed 8-felt root must be
///       `federation_root`.
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
    use dregg_circuit::blinded_membership_witness::{BLINDED_4ARY_PI_COUNT, PI_ROOT_4ARY};
    use dregg_circuit::bound_presentation_witness::{FEDERATION_ROOT, REQUEST_PREDICATE_BASE};

    check_bundle_predicates(bundle)?;
    let expected_root = expected_federation_root(federation_root);
    let expected_root8 = expected_federation_root_d8(federation_root);
    // The promised pre-cutover refusal, now actually performed (see
    // [`refuse_pre_cutover_root`]). A caller that hands us an old one-felt root gets a
    // refusal rather than a ~31-bit comparison dressed as an 8-lane one.
    if refuse_pre_cutover_root(&expected_root8) {
        return Ok(None);
    }

    // (a) MEMBERSHIP: verify the blinded ring-membership proof. Its PIs are the 8-felt
    //     `blinded_leaf` then the 8-felt federation `root` — SIXTEEN slots, not two.
    let blinded_pis = match verify_descriptor_wire(&bundle.blinded_membership) {
        Some(pis) if pis.len() >= BLINDED_4ARY_PI_COUNT => pis,
        _ => return Ok(None),
    };
    // EVERY LANE. The retired one-felt family bound ~31 bits of the federation root, so a second
    // authentication path to a birthday-collided root was accepted; all eight lanes must agree.
    if blinded_pis[PI_ROOT_4ARY..PI_ROOT_4ARY + DIGEST_W] != expected_root8[..] {
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

    // ⚑ THE EMPTY BRANCH USED TO RETURN WITHOUT READING THE PROOF (fixed 2026-08-06).
    // It was:
    //
    //     if revealed_facts.is_empty() {
    //         return Ok(recomputed_commitment.is_zero());
    //     }
    //
    // and `dregg_bridge::compute_revealed_facts_commitment` opens with
    // `if facts.is_empty() { return WideHash::ZERO; }`. So `revealed_facts.is_empty()`
    // implied `recomputed_commitment.is_zero()` implied `Ok(true)` — unconditionally,
    // for any proof bytes, having never touched `bound_pis[REVEALED_FACTS_BASE..]`.
    // The comment "the recomputed commitment must be zero" stated a condition on a
    // value the function had just derived from the same emptiness it branched on:
    // `x == x`, the `verify_full_turn` shape. A presentation that revealed facts
    // IN-CIRCUIT was reported verified-and-fully-private by passing `&[]` here.
    //
    // Both branches now compare the recomputed commitment against the PI the AIR
    // constrained. The empty case is not exempt — it asserts the proof ALSO committed
    // to nothing, which is the actual claim "no facts were revealed".

    // Facts ARE revealed — the recomputed commitment must be non-zero.
    if !revealed_facts.is_empty() && recomputed_commitment.is_zero() {
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

// ⚑ `verify_selective_presentation` LIVED HERE UNTIL 2026-08-06. Deleted: zero callers,
// and strictly weaker than the `verify_disclosure_presentation` forty lines below, which
// DOES have a real consumer (`sdk-py`). Its docblock said *"the high-level verifier entry
// point … performs the cryptographic commitment check"*; it performed ONE check — the
// revealed-facts commitment — with no STARK, no federation root, no action binding, and
// it swallowed `predicate_proofs` through a `..` pattern where its surviving sibling
// FAILS CLOSED on them (`predicate_proofs.is_empty()`). "using the full
// `AuthorizationPresentation`" described the argument TYPE and read as coverage.
// Two entry points that agree on predicate-free presentations and disagree on the
// dangerous ones is the shape this sweep exists to remove.

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
/// Two entry points DO have a sound source and can accept a predicate proof:
///
/// * [`verify_disclosure_presentation_third_party`] — takes the presentation-attested `facts_root`
///   and accepts a proof whose commitment a [`dregg_bridge::BridgeFactAttestation`] proves is the
///   blinded image of a MEMBER of that tree. No trusted state, no knowledge of the value.
/// * [`verify_disclosure_presentation_against_state`] — for callers holding trusted token state;
///   derives each expected commitment canonically from a fact they already know.
///
/// This function stays fail-closed because it takes NEITHER: with no root and no state, there is
/// still nothing here to check a predicate proof against.
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
                // This path RE-DERIVES, so it needs the opening. A proof that carries none (the
                // third-party shape, `blinding: None`) cannot be checked here — the commitment is
                // unreproducible by construction. Refuse rather than guess: such a proof wants
                // [`verify_disclosure_presentation_third_party`].
                let Some(blinding) = pred_proof.blinding else {
                    return false;
                };
                // The VALUE comes from trusted state; only the blinding (the opening) comes from the
                // proof, and that freedom cannot move which fact the commitment names.
                let Ok(expected) = crate::AgentCipherclerk::derive_fact_commitment(
                    trusted_fact,
                    state_root,
                    dregg_circuit::predicate_arith_witness::Blinding(blinding),
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

/// **Verify a disclosure presentation as a THIRD PARTY** — no trusted state, no knowledge of the
/// values, predicate proofs included.
///
/// This is the entry point [`verify_disclosure_presentation`] could not be. That function has no
/// trusted state and no attested source for a predicate proof's expected commitment, so it fails
/// closed on any predicate proof — honest, but it means a third party cannot verify one at all.
/// Here the missing source arrives as a parameter: `facts_root`, the root of the token's facts tree,
/// which the presentation's STARK attests as a public input.
///
/// It verifies:
/// 1. the revealed facts commitment matches the plaintext revealed facts;
/// 2. every predicate proof carries a [`dregg_bridge::BridgeFactAttestation`] that VERIFIES against
///    `facts_root` — i.e. its `fact_commitment` is the blinded image of a fact that is a MEMBER of
///    the attested tree, not one the prover invented;
/// 3. every predicate STARK verifies against that ATTESTED commitment.
///
/// It does NOT verify the presentation STARK itself (use `verify_authorization_proof` for that);
/// `facts_root` must come from that proof's public inputs.
///
/// # What a caller may conclude, and what it may not
///
/// For each `(fact_index, proof)`: **"some fact of the token committed at `facts_root` has a value
/// satisfying `proof.predicate`."** That is what a third party needs for a policy decision like
/// "this holder is over 18" without learning the birthdate.
///
/// It may NOT conclude WHICH fact — the member is a hidden witness of the attestation, deliberately,
/// because publishing it would make two showings of one fact linkable. `fact_index` travels for
/// correlation with the trusted-state path but this function does not bind it: a caller needing the
/// fact NAMED still needs [`verify_disclosure_presentation_against_state`].
///
/// # Arguments
///
/// * `presentation` — the presentation to check.
/// * `facts_root` — the attested root of the token's facts tree, from the presentation STARK's
///   public inputs. Passing a root the prover chose reduces this to the vacuity it exists to close.
/// * `state_root` — the token state root the commitments are taken against.
///
/// # Returns
///
/// `true` if the revealed-facts commitment matches AND every predicate proof is attested under
/// `facts_root` and verifies against its attested commitment. Fail-closed on a missing attestation,
/// a root mismatch, or any failed proof.
pub fn verify_disclosure_presentation_third_party(
    presentation: &crate::AuthorizationPresentation,
    facts_root: dregg_circuit::BabyBear,
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

            // 2 + 3. Every predicate proof must be ATTESTED under the caller's trusted root. The
            //        expected commitment is manufactured by the attestation STARK, never read off
            //        the proof — that is the whole difference from the `x != x` gate.
            predicate_proofs.iter().all(|(_fact_index, pred_proof)| {
                dregg_bridge::verify_predicate_proof_third_party(pred_proof, facts_root, state_root)
            })
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

// ⚑ `verify_production` LIVED HERE UNTIL 2026-08-06. Deleted, along with the
// `verify_any_tier` / `verify_production` PAIR, because the pair was the claim.
//
// * `verify_production` — *"the production-safe entry point … full STARK verification
//   including action/resource binding and composition commitment checks"*, with an
//   `# Errors` bullet reading *"Composition commitment is missing or invalid"*. The
//   string "composition" appeared nowhere else in the file; there was no such check and
//   no error path could produce it. **Zero callers**, and not re-exported at the crate
//   root, so the word "production" described nothing that ran.
// * `verify_any_tier` carried a `# Safety` banner — *"This MUST NOT be used in
//   production code paths"* — over a body BYTE-IDENTICAL to `verify_production`'s: the
//   same `verify_authorization_proof` call, the same `VerifiedProof::with_federation_root(
//   stark_tier(), STARK_BACKEND, …)`. Neither read a tier. "does not enforce a minimum
//   proof tier" was not a DIFFERENCE between them, it was what both did, and the safety
//   banner marked a boundary between two functions that were the same function.
//
// What survives is [`verify_authorization_proof_tagged`] below: one function, named for
// what it does (verify, then TAG the result with backend metadata) rather than for a
// tier policy that was removed years ago.

/// Verify a serialized authorization proof, then TAG the result with the backend
/// metadata a consumer wants for logging.
///
/// The verdict is exactly [`verify_authorization_proof`]'s — the two committed
/// descriptor wires, the 8-felt federation-root binding, and the action/resource
/// binding. **No tier is enforced, here or anywhere.** Tier gating was removed under
/// the verification-policy simplification: a proof that cryptographically verifies is
/// valid regardless of which backend produced it, and a structural stub cannot produce
/// a verifying STARK. The [`ProofTier`](dregg_circuit::ProofTier) on the returned
/// [`VerifiedProof`](dregg_circuit::VerifiedProof) is therefore INFORMATIONAL, and the
/// name says "tagged" rather than "production" so a reader can tell that without
/// opening the callee.
///
/// ⚠ **The tag is currently `stark_tier()` / `STARK_BACKEND` — i.e. `Experimental` /
/// `"custom-stark"` — while the proof it verified is an IR-v2 descriptor wire.** That
/// is a mislabel, not a gate: nothing reads it. `dregg_circuit::proof_tier` has no
/// descriptor-wire constant to name yet, which is the named residual.
///
/// # Errors
///
/// `Err` if the proof cannot be deserialized, names an unexpected descriptor
/// ([`SdkError::UnknownAir`]), or fails verification.
#[cfg(any(test, feature = "dev"))]
pub fn verify_authorization_proof_tagged(
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
    // for the committed-threshold statement exists yet — the bridge's `prove_committed_threshold`
    // is itself fail-closed, and the `verify_committed_threshold_proof` beside it was deleted as an
    // uncalled always-`false` decider. Rather than accept an unverifiable claim (fail-open), reject every input.
    // (Since no valid committed-threshold proof can be produced in this build, this rejects
    // all inputs, including the empty-`ProgramProof`-style placeholder blobs.)
    Ok(false)
}

/// **THE LIGHT-CLIENT FINALITY ENTRY** — verify a whole-history aggregate AND the committee
/// certificate that finalizes it, arming this process's verified post-quantum cores first.
///
/// A drop-in for `dregg_lightclient::verify_finalized_history`, with the identical signature and
/// the identical verdict; the SDK's root re-export now names THIS one.
///
/// # Why the SDK wraps it rather than re-exporting it
///
/// Each committee vote in a [`FinalityCert`](dregg_lightclient::FinalityCert) carries an ML-DSA-65
/// half, and a missing or forged one must drop the signer — so
/// `dregg_lightclient::verify_ml_dsa_half` calls `dregg_pq::ml_dsa_verify` on the honest path, for
/// every vote. `dregg-lightclient` is a LIGHT leaf by design: it cannot link the Lean archive and
/// therefore cannot install the verified core itself (its own lib tests reach for
/// `dregg-pq-testkit` under `#[cfg(test)]` for exactly this reason). Until this wrapper, the only
/// thing in an SDK-hosted process that armed the verify core was an
/// [`AgentRuntime`](crate::AgentRuntime) constructor — and a light client is precisely the consumer
/// that has no runtime, no cipherclerk, no ledger and no keys. It holds a trust anchor and a proof.
/// That consumer reached `dregg-pq`'s audit gate with nothing installed, and the gate did the only
/// correct thing available to it: `process::abort()`.
///
/// This is not a weakening of anything. The install is export-gated and once-per-process; an
/// archive that exports no verify core still installs none and the refusal at the point of use
/// still stands, exactly as before.
///
/// [`verify_history`](dregg_lightclient::verify_history) is re-exported directly and NOT wrapped:
/// it is the succinct-aggregate leg alone (VK pin + Fiat–Shamir attestation + root) and reaches no
/// PQ primitive. The asymmetry is the honest one — wrap what can reach the gate.
pub fn verify_finalized_history(
    agg: &dregg_circuit_prove::ivc_turn_chain::WholeChainProof,
    expected_vk: &dregg_circuit_prove::ivc_turn_chain::RecursionVk,
    finalized_root: [dregg_circuit::field::BabyBear;
        dregg_circuit_prove::ivc_turn_chain::SEG_ANCHOR_WIDTH],
    cert: &dregg_lightclient::FinalityCert,
    committee: &[[u8; 32]],
    ml_dsa_committee: &[Vec<u8>],
    expected_genesis: Option<
        [dregg_circuit::field::BabyBear; dregg_circuit_prove::ivc_turn_chain::SEG_ANCHOR_WIDTH],
    >,
) -> Result<dregg_lightclient::FinalizedAttestation, dregg_lightclient::FinalizedError> {
    crate::runtime::install_verified_pq_cores();
    dregg_lightclient::verify_finalized_history(
        agg,
        expected_vk,
        finalized_root,
        cert,
        committee,
        ml_dsa_committee,
        expected_genesis,
    )
}

// ⚑ `build_federation_tree` LIVED HERE UNTIL 2026-08-06 AND ITS OUTPUT WAS ACCEPTED BY
// NOTHING. Its docblock promised *"the same Merkle tree structure used by
// `authorize_anonymously`"* and a root *"that can be used as the `federation_root`
// parameter when verifying ring membership proofs"*. Both were false:
//
// * it built a SORTED, zero-padded, BINARY tree over blake3 leaves
//   (`new_derive_key("dregg-federation-leaf-v1")`), and
// * the `federation_root` parameter is consumed two ways, neither of which is a blake3
//   digest — `expected_federation_root_d8` reads the 32 bytes as eight canonical LE
//   `u32` lanes of a Poseidon2 `node8_4ary` root, and `expected_federation_root`
//   Poseidon2-hashes those lanes. Feeding this function's output to
//   `verify_authorization_proof` rejects every honest proof.
// * `authorize_anonymously` (`privacy.rs`) builds no tree at all — it delegates to
//   `prove_authorization`.
//
// Zero callers. A helper whose whole contract is "the value this returns goes THERE"
// and whose value is refused THERE is worse than an absent one, because the next
// reader wires it up. Building the real thing means a Poseidon2 4-ary `node8` fold
// matching `blinded_membership_witness_4ary` — that is the replacement, and it is not
// this. Named residual, recorded in `old-docs/app-blockers.md`.

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
        // (a) blinded ring-membership (depth-2, 4-ary `node8`) — its committed 8-felt root IS the
        //     federation root. Leaf and every co-path sibling are full `Digest8` nodes.
        let leaf: Digest8 = core::array::from_fn(|k| BabyBear::new(0xABCD + k as u32));
        let blinding = BabyBear::new(0xB11D);
        let sibs: [[Digest8; 3]; 2] = core::array::from_fn(|lvl| {
            core::array::from_fn(|s| {
                core::array::from_fn(|k| {
                    BabyBear::new(2002 + (lvl * 3 + s) as u32 * 1001 + k as u32)
                })
            })
        });
        let pos = [0u8, 0u8];
        let (bl_trace, bl_pis) =
            blinded_membership_witness_4ary(leaf, blinding, &sibs, &pos).expect("blinded witness");
        let root8: Digest8 = bl_pis[PI_ROOT_4ARY..PI_ROOT_4ARY + DIGEST_W]
            .try_into()
            .expect("the blinded wire publishes an 8-felt root");
        let desc_bl = blinded_membership_descriptor_of_depth_4ary(2);
        let blinded_membership = wire_from(&desc_bl, bl_trace, bl_pis);

        // The federation root the caller passes: the 8-felt root as eight canonical LE-u32 limbs
        // (the FLAG-DAY encoding — see `expected_federation_root_d8`).
        let mut fed = [0u8; 32];
        for (k, felt) in root8.iter().enumerate() {
            fed[k * 4..k * 4 + 4].copy_from_slice(&felt.as_u32().to_le_bytes());
        }
        // The AUTH leg's ONE-felt pin: a Poseidon2 hash of all eight limbs, recomputed by the
        // verifier from the same bytes (never a lane of the digest).
        let root = expected_federation_root(&fed);

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

    /// A wrong federation root is REJECTED (membership root no longer matches) — in EVERY one of
    /// the eight limbs. The retired one-felt encoding put the whole root in bytes `0..4` and left
    /// `4..32` zero, so a root differing only in the high limbs was literally the SAME wire value;
    /// perturbing limb 7 is the case that could not previously exist.
    #[test]
    fn verify_authorization_proof_rejects_wrong_root() {
        let zero = [BabyBear::ZERO; 8];
        let (bundle, fed) = honest_bundle("read", "api/v1/users", zero);
        let bytes = postcard::to_allocvec(&bundle).expect("encode bundle");
        assert!(
            verify_authorization_proof(&bytes, &fed, "read", "api/v1/users").unwrap(),
            "the honest bundle must verify (else the wrong-root canary is vacuous)"
        );
        for limb in 0..DIGEST_W {
            let mut wrong = fed;
            wrong[limb * 4] ^= 0xFF;
            assert_eq!(
                verify_authorization_proof(&bytes, &wrong, "read", "api/v1/users").unwrap(),
                false,
                "a bundle whose committed root differs from the caller's in limb {limb} must be \
                 rejected"
            );
        }
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

    /// ⚑ THE REFUSAL THE EMPTY BRANCH GAINED (2026-08-06), SHOWN TO FIRE.
    ///
    /// The proof here COMMITS to a non-zero revealed-facts value in-circuit
    /// (`bound_pis[REVEALED_FACTS_BASE..+8]`), and the caller claims `&[]` — "nothing
    /// was revealed". The old body took `revealed_facts.is_empty()` as its whole
    /// question, recomputed `WideHash::ZERO` from that same emptiness, compared the two,
    /// and returned `Ok(true)` without ever reading the proof. So a presentation that
    /// revealed facts was reported verified-and-fully-private by passing an empty slice.
    ///
    /// Note the honest pole above uses the SAME construction with a ZERO commitment and
    /// still passes, so this is the commitment comparison biting, not a blanket refusal
    /// of the empty case.
    #[test]
    fn empty_facts_claim_against_a_proof_that_committed_facts_is_refused() {
        let revealed = [
            BabyBear::new(0x1234),
            BabyBear::new(0x5678),
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
        ];
        let (bundle, fed) = honest_bundle("read", "api/v1/users", revealed);
        let bytes = postcard::to_allocvec(&bundle).expect("encode bundle");
        assert_eq!(
            verify_selective_disclosure(&bytes, &fed, "read", "api/v1/users", &[]).unwrap(),
            false,
            "claiming NO facts were revealed against a proof whose in-circuit \
             revealed-facts commitment is non-zero must be refused"
        );
    }

    /// The pre-cutover federation-root refusal the docblock promised and no code performed
    /// until 2026-08-06, shown to fire: a one-felt root (bytes 0..4 set, 4..32 zeroed)
    /// decodes to a digest whose lanes 1..8 are all zero. No honest `node8_4ary` fold
    /// produces that, so it is REFUSED rather than compared at its ~31-bit waist.
    #[test]
    fn pre_cutover_one_felt_federation_root_is_refused_not_reinterpreted() {
        let zero = [BabyBear::ZERO; 8];
        let (bundle, fed) = honest_bundle("read", "api/v1/users", zero);
        let bytes = postcard::to_allocvec(&bundle).expect("encode bundle");
        // The honest 8-lane root still verifies.
        assert!(
            verify_authorization_proof(&bytes, &fed, "read", "api/v1/users").unwrap(),
            "the 8-lane root must still verify"
        );
        // A pre-cutover root: lane 0 carried in bytes 0..4, the tail zeroed.
        let mut old_shape = [0u8; 32];
        old_shape[..4].copy_from_slice(&fed[..4]);
        assert!(
            !verify_authorization_proof(&bytes, &old_shape, "read", "api/v1/users").unwrap(),
            "a pre-cutover one-felt root must be refused"
        );
        // And the all-zero (unset) anchor is caught by the same rule.
        assert!(
            !verify_authorization_proof(&bytes, &[0u8; 32], "read", "api/v1/users").unwrap(),
            "an unset [0u8; 32] anchor is not a root either"
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

        // The five never-constructed variants this used to also instantiate are gone
        // (see the note on the enum). This test could not have caught their deadness:
        // constructing a variant HERE is exactly what made it look alive.
    }
}
