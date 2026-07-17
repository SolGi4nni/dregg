//! Presentation proof: the complete zero-knowledge authorization proof.
//!
//! Combines:
//! 1. A chain of fold steps (attenuations)
//! 2. A final authorization derivation
//! 3. Issuer membership (Merkle inclusion against federation root)
//!
//! Public inputs:
//! - Federation root (the root of trust)
//! - Request predicate (what is being authorized)
//! - Timestamp (freshness)
//!
//! Private witness:
//! - Entire token chain (sequence of fold deltas)
//! - Derivation trace (proof that the final state authorizes the request)
//! - Issuer key (and its membership in the federation)
//!
//! The presentation proof proves: "I hold a valid attenuated token chain whose
//! final state authorizes action X" without revealing the chain or capabilities.

use crate::constraint_prover::{Air, Constraint, ConstraintValidator, TraceSummary};
use crate::derivation_air::{CircuitRule, DerivationAir, DerivationWitness};
use crate::dsl::fold::{FoldAir, FoldWitness, RemovedFact};
use crate::field::BabyBear;
use crate::merkle_air::{MerkleAir, MerkleLevelWitness, MerkleWitness};
use crate::poseidon2::hash_fact;

use crate::descriptor_by_name::descriptor_by_name;
use crate::descriptor_ir2::{
    DreggStarkConfig, EffectVmDescriptor2, Ir2BatchProof, MemBoundaryWitness, prove_vm_descriptor2,
    verify_vm_descriptor2,
};

/// A committed-descriptor proof in wire form: the two descriptors the presentation
/// family flips onto (bound-presentation auth + blinded ring-membership).
///
/// * `predicate` — the descriptor identity the CONSUMER dispatches on via
///   [`descriptor_by_name`]; NO air-name rides the blob.
/// * `blob` — `postcard(Ir2BatchProof)` produced by [`prove_vm_descriptor2`].
/// * `vk` — the expected public inputs, one canonical little-endian `u32` per 4 bytes.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct DescriptorProofWire {
    /// Descriptor identity the consumer dispatches on (never rides the blob).
    pub predicate: String,
    /// `postcard(Ir2BatchProof)` — the committed-descriptor proof.
    pub blob: Vec<u8>,
    /// Expected public inputs, one canonical LE `u32` per 4 bytes.
    pub vk: Vec<u8>,
}

/// Build a [`DescriptorProofWire`] from a descriptor + honest witness: prove through the
/// real IR-v2 prover, postcard-encode the batch proof, and encode the public inputs into `vk`.
pub fn build_descriptor_wire(
    desc: &EffectVmDescriptor2,
    trace: &[Vec<BabyBear>],
    pis: &[BabyBear],
) -> Option<DescriptorProofWire> {
    let proof = prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[]).ok()?;
    let blob = postcard::to_allocvec(&proof).ok()?;
    let mut vk = Vec::with_capacity(pis.len() * 4);
    for p in pis {
        vk.extend_from_slice(&p.0.to_le_bytes());
    }
    Some(DescriptorProofWire {
        predicate: desc.name.clone(),
        blob,
        vk,
    })
}

/// Decode a `vk` byte string into public inputs: one canonical `BabyBear` per little-endian
/// 4-byte group. Returns `None` for a length that is not a positive multiple of 4.
pub fn descriptor_wire_pis(vk: &[u8]) -> Option<Vec<BabyBear>> {
    if vk.is_empty() || vk.len() % 4 != 0 {
        return None;
    }
    Some(
        vk.chunks_exact(4)
            .map(|c| BabyBear::new_canonical(u32::from_le_bytes([c[0], c[1], c[2], c[3]])))
            .collect(),
    )
}

/// Verify one [`DescriptorProofWire`] end-to-end: `descriptor_by_name(predicate)` → decode
/// `postcard(Ir2BatchProof)` → `verify_vm_descriptor2` against the `vk` public inputs. Returns
/// the verified public inputs on success (so the caller can bind them), `None` on any failure.
/// Fail-closed: an unknown predicate, a malformed vk, a bad blob, or a failed/paniced verify
/// all return `None` — never a silent accept.
pub fn verify_descriptor_wire(wire: &DescriptorProofWire) -> Option<Vec<BabyBear>> {
    let desc = descriptor_by_name(&wire.predicate)?;
    let pis = descriptor_wire_pis(&wire.vk)?;
    let batch: Ir2BatchProof<DreggStarkConfig> = postcard::from_bytes(&wire.blob).ok()?;
    let ok = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        verify_vm_descriptor2(&desc, &batch, &pis).is_ok()
    }))
    .unwrap_or(false);
    ok.then_some(pis)
}

/// The complete presentation witness (all private data).
#[derive(Clone, Debug)]
pub struct PresentationWitness {
    /// The federation root (root of trust, public).
    pub federation_root: BabyBear,
    /// The action binding commitment (public, 4 elements for 124-bit security).
    pub request_predicate: crate::binding::ActionBinding,
    /// Timestamp for freshness (public).
    pub timestamp: BabyBear,
    /// Chain of fold steps (private).
    pub fold_chain: Vec<FoldWitness>,
    /// The final authorization derivation (private).
    pub derivation: DerivationWitness,
    /// Issuer membership proof in federation (private).
    pub issuer_membership: MerkleWitness,
    /// The issuer's public key hash (private).
    pub issuer_key_hash: BabyBear,
    /// Commitment to the set of facts being selectively revealed (public, 124-bit).
    ///
    /// For selective disclosure mode, this is a WideHash over `(hash(fact_1) || ... || hash(fact_n))`
    /// computed over the facts the prover chooses to reveal. The verifier recomputes this
    /// from the plaintext revealed facts and checks it matches, ensuring the prover cannot
    /// lie about which facts were derived during evaluation.
    ///
    /// For fully private mode, this is `WideHash::ZERO` (no facts revealed).
    pub revealed_facts_commitment: crate::binding::WideHash,
    /// Blinding factor for ring membership (private).
    ///
    /// When non-zero, the issuer membership proof uses blinded (ring) mode:
    /// the public input becomes `blinded_leaf = hash_2_to_1(leaf_hash, blinding_factor)`
    /// instead of the raw `leaf_hash`. This makes presentations unlinkable —
    /// the same issuer produces different `blinded_leaf` values each time.
    ///
    /// When `BabyBear::ZERO`, the legacy non-blinded path is used (leaf_hash is public).
    pub blinding_factor: BabyBear,
    /// Fresh randomness for the presentation tag (private).
    ///
    /// Used to compute `presentation_tag = Poseidon2(final_root, presentation_randomness, verifier_nonce)`.
    /// Must be freshly generated per presentation to ensure unlinkability.
    /// The final_root remains private; only the blinded tag is public.
    pub presentation_randomness: BabyBear,
    /// Composition commitment binding all sub-proofs together (public, 124-bit).
    ///
    /// This is a WideHash over `(fold_chain_commitment, derivation_state_root, presentation_tag)`
    /// where:
    /// - `fold_chain_commitment` is the Poseidon2 hash of the fold chain roots
    /// - `derivation_state_root` is the final state root from derivation
    /// - `presentation_tag` is the blinded tag (ties to this specific presentation)
    ///
    /// This value is appended as public inputs to the issuer membership STARK,
    /// cryptographically binding the STARK proof to the specific fold chain and
    /// derivation results. Without this, an attacker could attach a valid membership
    /// STARK from one token to a forged fold chain from another.
    ///
    /// When `WideHash::ZERO`, no composition commitment is enforced (legacy proofs).
    pub composition_commitment: crate::binding::WideHash,
    /// Verifier-issued nonce for replay protection (public).
    ///
    /// The verifier provides this challenge BEFORE proof generation. The prover must
    /// include it as a public input. During verification, the verifier checks that
    /// the proof's nonce matches the challenge they issued.
    ///
    /// This makes proofs non-replayable: a proof generated for one challenge cannot
    /// be replayed against a different challenge. The nonce also enters the Fiat-Shamir
    /// transcript (via the presentation_tag computation) to affect the STARK's internal
    /// randomness.
    ///
    /// When `BabyBear::ZERO`, no verifier nonce was provided (backward compatibility
    /// with older provers). Verifiers SHOULD reject proofs with a zero nonce in
    /// challenge-response protocols.
    pub verifier_nonce: BabyBear,
    /// Verifier-declared current block height for freshness binding (public).
    ///
    /// The verifier provides this value (the current chain height) as a public input.
    /// The circuit enforces that if the token has a `not_after_height` expiry caveat
    /// (non-zero), then `not_after_height >= verifier_block_height`. This ensures
    /// the token has not expired relative to the verifier's view of the chain.
    ///
    /// When `BabyBear::ZERO`, no freshness check is performed (backward compatibility).
    /// Verifiers operating in height-aware protocols SHOULD provide a non-zero value
    /// to enforce token expiry.
    pub verifier_block_height: BabyBear,
}

/// Public inputs for the presentation proof.
///
/// # Privacy Design (Phase 2)
///
/// The `initial_root` and `final_root` fields have been removed from public inputs
/// because they are deterministic per-token: same token always produces the same roots,
/// making presentations linkable across shows.
///
/// Instead, a `presentation_tag` is included:
///   `presentation_tag = Poseidon2(final_root, presentation_randomness, verifier_nonce)`
/// where `presentation_randomness` is fresh per presentation. The fold chain still
/// proves `initial_root -> final_root` internally (as private witness), and the STARK
/// proves the tag is well-formed. This makes presentations unlinkable.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct PresentationPublicInputs {
    /// Federation root of trust.
    pub federation_root: BabyBear,
    /// The action binding commitment (4 elements for 124-bit security).
    pub request_predicate: crate::binding::ActionBinding,
    /// Timestamp for freshness.
    pub timestamp: BabyBear,
    /// Blinded presentation tag for unlinkable multi-show.
    ///
    /// Computed as `Poseidon2(final_root, presentation_randomness, verifier_nonce)` where
    /// the randomness is fresh per presentation. The verifier cannot recover `final_root`
    /// from this tag, so the same credential produces a different tag every time it is shown.
    pub presentation_tag: BabyBear,
    /// Commitment to selectively revealed facts (zero if fully private, 124-bit).
    ///
    /// This is a WideHash over `(hash(fact_1) || ... || hash(fact_n))` for the facts the prover
    /// chose to reveal. The verifier recomputes this from the plaintext facts and checks
    /// it matches, cryptographically binding the revealed facts to the proof.
    pub revealed_facts_commitment: crate::binding::WideHash,
    /// Composition commitment binding all sub-proofs together (124-bit).
    ///
    /// This is a WideHash over `(fold_chain_commitment, derivation_state_root, presentation_tag)`
    /// and is included as public inputs in the issuer membership STARK. A verifier
    /// recomputes this from the other sub-proofs and checks it matches, ensuring
    /// sub-proofs cannot be mixed-and-matched across presentations.
    ///
    /// `WideHash::ZERO` means no composition commitment (legacy proofs).
    #[serde(default)]
    pub composition_commitment: crate::binding::WideHash,
    /// Verifier-issued nonce for replay protection.
    ///
    /// In a challenge-response protocol, the verifier sends this nonce to the prover
    /// BEFORE proof generation. The proof is then bound to this specific nonce.
    /// A proof generated for nonce N cannot be replayed against a different nonce N'.
    ///
    /// `BabyBear::ZERO` means no verifier nonce (legacy proofs, or non-interactive mode).
    /// Verifiers operating in challenge-response mode SHOULD reject proofs with zero nonce.
    #[serde(default)]
    pub verifier_nonce: BabyBear,
    /// Verifier-declared current block height for freshness binding.
    ///
    /// When non-zero, the verifier asserts "I am at block height H". The circuit
    /// enforces that the token's `not_after_height` (if present) satisfies
    /// `not_after_height >= verifier_block_height`, proving the token has not expired.
    ///
    /// `BabyBear::ZERO` means no freshness binding (legacy proofs).
    #[serde(default)]
    pub verifier_block_height: BabyBear,
}

/// A complete presentation proof.
///
/// # What is and is not proof here
///
/// Despite the field names (kept for wire compatibility — this struct rides
/// `WirePresentationProof` as postcard), the three trace-summary fields are
/// **not proofs**: they are prover-authored summaries (see
/// [`crate::constraint_prover`] — a digest nobody re-checks, plus public
/// inputs). No verifier in this workspace reads their digests; the
/// production verifiers (`dregg_bridge::present::verify_proof_complete` and
/// friends) require and cryptographically verify the SEPARATE
/// `real_stark_proof` descriptor wires, and only read `public_inputs` off this
/// struct as metadata to bind against the STARK's own public inputs.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct PresentationProof {
    /// The public inputs.
    pub public_inputs: PresentationPublicInputs,
    /// Trace summaries of the fold-chain constraint checks (NOT proofs).
    pub fold_proofs: Vec<TraceSummary>,
    /// Trace summary of the final derivation constraint check (NOT a proof).
    pub derivation_proof: TraceSummary,
    /// Trace summary for issuer membership (unchecked; real crypto is the
    /// issuer-membership STARK descriptor wire).
    pub issuer_membership_proof: TraceSummary,
    /// Sum of the ESTIMATED (simulated) sub-proof sizes in bytes.
    pub total_proof_size_bytes: usize,
}

impl PresentationProof {
    /// Get a human-readable size.
    pub fn proof_size_display(&self) -> String {
        let bytes = self.total_proof_size_bytes;
        if bytes < 1024 {
            format!("{bytes} B")
        } else if bytes < 1024 * 1024 {
            format!("{:.1} KiB", bytes as f64 / 1024.0)
        } else {
            format!("{:.1} MiB", bytes as f64 / (1024.0 * 1024.0))
        }
    }

    /// Plaintext consistency check over the prover-supplied public inputs.
    ///
    /// **This is NOT cryptographic verification** — every value it reads
    /// (`fold_proofs[i].public_inputs`, `derivation_proof.public_inputs`,
    /// `issuer_membership_proof.public_inputs`) is authored by the prover, so a
    /// lying prover trivially satisfies it. It has ZERO production callers
    /// (2026-07-17 census: only `circuit/src/tests.rs`); the production
    /// verifiers live in `dregg_bridge::present` and rest on the real STARK
    /// descriptor wires.
    ///
    /// What it checks, as internal consistency only:
    /// 1. Fold chain continuity (each step's old_root == previous new_root).
    /// 2. Derivation's state root matches end of fold chain.
    /// 3. (Presentation-tag well-formedness is NOT checked here.)
    /// 4. Issuer membership public input equals the claimed federation root.
    pub fn verify(&self) -> PresentationVerification {
        // 1. Check fold chain internal continuity
        let mut current_root = if let Some(first) = self.fold_proofs.first() {
            if first.public_inputs.len() < 4 {
                return PresentationVerification::InvalidFoldProof { index: 0 };
            }
            first.public_inputs[0]
        } else {
            // No fold proofs: the derivation state root IS the only root.
            if self.derivation_proof.public_inputs.is_empty() {
                return PresentationVerification::InvalidDerivation;
            }
            return self.verify_no_folds();
        };

        for (i, fold_proof) in self.fold_proofs.iter().enumerate() {
            if fold_proof.public_inputs.len() < 4 {
                return PresentationVerification::InvalidFoldProof { index: i };
            }
            if fold_proof.public_inputs[0] != current_root {
                return PresentationVerification::FoldChainBreak { index: i };
            }
            current_root = fold_proof.public_inputs[1];
        }

        // 2. Check derivation proof's state root matches end of fold chain
        if self.derivation_proof.public_inputs.is_empty() {
            return PresentationVerification::InvalidDerivation;
        }
        let derivation_state_root = self.derivation_proof.public_inputs[0];
        if derivation_state_root != current_root {
            return PresentationVerification::DerivationRootMismatch;
        }

        // 3. Presentation tag validity is enforced by the STARK — no comparison
        //    against final_root needed here (final_root is private witness).

        // 4. Check issuer membership in federation
        if self.issuer_membership_proof.public_inputs.len() < 2 {
            return PresentationVerification::InvalidIssuerProof;
        }
        let issuer_federation_root = self.issuer_membership_proof.public_inputs[1];
        if issuer_federation_root != self.public_inputs.federation_root {
            return PresentationVerification::IssuerNotInFederation;
        }

        // 5. Freshness binding: check token expiry against verifier's block height.
        if let Err(e) = self.verify_freshness_binding() {
            return e;
        }

        PresentationVerification::Valid
    }

    /// Helper for verification when there are no fold proofs.
    fn verify_no_folds(&self) -> PresentationVerification {
        // Check issuer membership in federation
        if self.issuer_membership_proof.public_inputs.len() < 2 {
            return PresentationVerification::InvalidIssuerProof;
        }
        let issuer_federation_root = self.issuer_membership_proof.public_inputs[1];
        if issuer_federation_root != self.public_inputs.federation_root {
            return PresentationVerification::IssuerNotInFederation;
        }

        // Freshness binding.
        if let Err(e) = self.verify_freshness_binding() {
            return e;
        }

        PresentationVerification::Valid
    }

    /// Verify freshness binding: token expiry vs verifier block height.
    ///
    /// If both `verifier_block_height` (public input) and `not_after_height`
    /// (derivation proof public input index 2) are non-zero, enforce:
    ///   `not_after_height >= verifier_block_height`
    ///
    /// If `not_after_height == 0`, the token has no expiry (always valid).
    /// If `verifier_block_height == 0`, no freshness check is requested.
    fn verify_freshness_binding(&self) -> Result<(), PresentationVerification> {
        let verifier_height = self.public_inputs.verifier_block_height;
        if verifier_height == BabyBear::ZERO {
            return Ok(());
        }

        // Extract not_after_height from derivation proof public inputs (index 2).
        let not_after_height = if self.derivation_proof.public_inputs.len() >= 3 {
            self.derivation_proof.public_inputs[2]
        } else {
            BabyBear::ZERO
        };

        // Zero means no expiry caveat — always valid.
        if not_after_height == BabyBear::ZERO {
            return Ok(());
        }

        // Enforce: not_after_height >= verifier_block_height
        // In the field, this means (not_after_height - verifier_block_height) is
        // a "small" non-negative value (fits in 30 bits, i.e., < p/2).
        let diff = not_after_height - verifier_height;
        let diff_val = diff.as_u32();
        // If the subtraction wrapped (result > p/2), the token is expired.
        if diff_val > 1_006_632_960 {
            // p/2 = 2013265921 / 2 = 1006632960
            return Err(PresentationVerification::TokenExpired);
        }

        Ok(())
    }
}

/// Result of presentation proof verification.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum PresentationVerification {
    /// The proof is valid (cryptographically verified via STARK).
    Valid,
    /// Local constraint check passed, but NO cryptographic proof was generated.
    ///
    /// This is the result from `prove_fast()`: the circuit constraints were
    /// satisfied locally, but without a STARK proof this provides zero security
    /// to a remote verifier. The prover could have fabricated any witness.
    ///
    /// **Do NOT treat this as equivalent to `Valid` in verification code.**
    LocalOnly,
    /// A fold proof in the chain failed.
    InvalidFoldProof { index: usize },
    /// The fold chain has a break (root mismatch between steps).
    FoldChainBreak { index: usize },
    /// The derivation proof is invalid.
    InvalidDerivation,
    /// The derivation's state root doesn't match the end of the fold chain.
    DerivationRootMismatch,
    /// The issuer membership proof is invalid.
    InvalidIssuerProof,
    /// The issuer is not in the federation.
    IssuerNotInFederation,
    /// A temporal predicate proof failed verification.
    ///
    /// Either the temporal proof's `final_state_root` does not match the
    /// presentation's state root (binding failure), or the STARK proof itself
    /// is invalid.
    InvalidTemporalProof { index: usize },
    /// The composition commitment is zero (missing sub-proof binding).
    ///
    /// A zero composition commitment means the sub-proofs are not cryptographically
    /// bound together, allowing an attacker to mix-and-match sub-proofs from
    /// different presentations. Verifiers MUST reject proofs with zero commitment.
    MissingCompositionCommitment,
    /// The token has expired: `not_after_height < verifier_block_height`.
    ///
    /// The verifier declared a current block height that exceeds the token's
    /// expiry height. The token is no longer valid at the verifier's current position.
    TokenExpired,
}

/// The presentation AIR: combines all sub-AIRs into one constraint system.
///
/// This is a "meta-AIR" that generates a unified trace by concatenating
/// the sub-proofs. In a real IVC/folding scheme, each step would be
/// recursively verified. Here we verify them sequentially.
pub struct PresentationAir {
    pub witness: PresentationWitness,
}

impl PresentationAir {
    /// Width of the summary trace / public-input vector:
    ///   federation_root (1)
    /// + request_predicate (`ACTION_BINDING_WIDTH` = 8)
    /// + timestamp (1)
    /// + presentation_tag (narrow, 1)
    /// + revealed_facts_commitment (`WideHash::WIDTH` = 8)
    pub const SUMMARY_WIDTH: usize =
        1 + crate::binding::ACTION_BINDING_WIDTH + 1 + 1 + crate::binding::WideHash::WIDTH;

    pub fn new(witness: PresentationWitness) -> Self {
        Self { witness }
    }

    /// Generate the full presentation proof.
    pub fn prove(&self) -> Option<PresentationProof> {
        let w = &self.witness;

        // 1. Locally validate + summarize each fold step (NOT proving — the
        //    summaries carry no adversarial soundness; see PresentationProof docs).
        let mut fold_proofs = Vec::new();
        for fold_witness in &w.fold_chain {
            let fold_air = FoldAir::new(fold_witness.clone());
            let result = ConstraintValidator::verify(&fold_air);
            if !result.is_valid() {
                return None;
            }
            let proof = TraceSummary::generate(&fold_air)?;
            fold_proofs.push(proof);
        }

        // 2. Locally validate the derivation (DEPRECATED: uses old DerivationAir).
        // Production STARK proofs use crate::dsl::descriptors::derivation_circuit().
        let derivation_air = DerivationAir::new(w.derivation.clone());
        let deriv_result = ConstraintValidator::verify(&derivation_air);
        if !deriv_result.is_valid() {
            return None;
        }
        let derivation_proof = TraceSummary::generate(&derivation_air)?;

        // 3. Summarize issuer membership.
        // The witness uses hash_fact (Poseidon2 DSL path) which differs from
        // MerkleAir's hash_4_to_1. Skip the local constraint check here — the real
        // cryptographic check is handled by the Poseidon2 STARK proof.
        let issuer_air = MerkleAir::new(w.issuer_membership.clone());
        let issuer_membership_proof = TraceSummary::generate_unchecked(&issuer_air);

        // Compute public inputs — initial_root and final_root stay private.
        // The presentation_tag blinds the final_root for unlinkability.
        let final_root = if let Some(last_fold) = w.fold_chain.last() {
            last_fold.new_root
        } else {
            w.derivation.state_root
        };

        let presentation_tag = crate::binding::compute_presentation_tag_narrow(
            final_root,
            w.presentation_randomness,
            w.verifier_nonce,
        );

        let public_inputs = PresentationPublicInputs {
            federation_root: w.federation_root,
            request_predicate: w.request_predicate,
            timestamp: w.timestamp,
            presentation_tag,
            revealed_facts_commitment: w.revealed_facts_commitment,
            composition_commitment: w.composition_commitment,
            verifier_nonce: w.verifier_nonce,
            verifier_block_height: w.verifier_block_height,
        };

        // Compute total proof size
        let total_size = fold_proofs
            .iter()
            .map(|p| p.simulated_proof_size_bytes)
            .sum::<usize>()
            + derivation_proof.simulated_proof_size_bytes
            + issuer_membership_proof.simulated_proof_size_bytes;

        Some(PresentationProof {
            public_inputs,
            fold_proofs,
            derivation_proof,
            issuer_membership_proof,
            total_proof_size_bytes: total_size,
        })
    }

    // RETIRED 2026-07-16 (mock-proof purge): `prove_ivc`/`prove_ivc_no_folds` produced an
    // `IvcPresentationProof` backed by the SIMULATED hash-chain IVC (`crate::ivc::prove_ivc`)
    // plus trace-digest constraint proofs — anyone who could call the prover could mint a
    // passing proof. No production caller existed (only a bench rode it). The real
    // presentation path is `BridgePresentationBuilder::prove()` (real STARK).

    /// Locally validate the entire presentation WITNESS (row-by-row constraint
    /// check of all sub-circuits). Prover-side sanity only: the caller holds
    /// the witness, so this is honest local checking, not verification of
    /// anything remote.
    pub fn verify_all(&self) -> PresentationVerification {
        let w = &self.witness;

        // Validate fold chain
        let mut current_root = if let Some(first) = w.fold_chain.first() {
            first.old_root
        } else {
            w.derivation.state_root
        };

        for (i, fold_witness) in w.fold_chain.iter().enumerate() {
            // Check continuity
            if fold_witness.old_root != current_root {
                return PresentationVerification::FoldChainBreak { index: i };
            }

            // Validate fold AIR constraints
            let fold_air = FoldAir::new(fold_witness.clone());
            let result = ConstraintValidator::verify(&fold_air);
            if !result.is_valid() {
                return PresentationVerification::InvalidFoldProof { index: i };
            }

            current_root = fold_witness.new_root;
        }

        // Validate derivation
        if w.derivation.state_root != current_root {
            return PresentationVerification::DerivationRootMismatch;
        }
        let derivation_air = DerivationAir::new(w.derivation.clone());
        let result = ConstraintValidator::verify(&derivation_air);
        if !result.is_valid() {
            return PresentationVerification::InvalidDerivation;
        }

        // Verify issuer membership: only check that the expected_root matches
        // the federation root. The actual hash constraint is validated by the
        // Poseidon2 STARK proof (which uses hash_fact via the DSL circuit).
        // MerkleAir uses hash_4_to_1 which is incompatible with the Poseidon2 witness.
        if w.issuer_membership.expected_root != w.federation_root {
            return PresentationVerification::IssuerNotInFederation;
        }

        // Freshness binding: check token expiry against verifier's block height.
        let verifier_height = w.verifier_block_height;
        if verifier_height != BabyBear::ZERO {
            let not_after_height = w.derivation.not_after_height;
            if not_after_height != BabyBear::ZERO {
                // Enforce: not_after_height >= verifier_block_height
                let diff = not_after_height - verifier_height;
                let diff_val = diff.as_u32();
                if diff_val > 1_006_632_960 {
                    return PresentationVerification::TokenExpired;
                }
            }
        }

        PresentationVerification::Valid
    }
}

/// Not a standalone AIR (it's a meta-proof), but we implement the Air trait
/// so the constraint prover infrastructure can validate the combined circuit.
/// The trace is a summary of the sub-proofs' public inputs.
impl Air for PresentationAir {
    fn trace_width(&self) -> usize {
        // Summary trace (public inputs as columns), laid out as:
        //   federation_root (1)
        //   request_predicate[0..ACTION_BINDING_WIDTH]   (8)
        //   timestamp (1)
        //   presentation_tag (narrow, 1)
        //   revealed_facts_commitment[0..PRESENTATION/WideHash::WIDTH] (8)
        // = 1 + 8 + 1 + 1 + 8 = 19
        Self::SUMMARY_WIDTH
    }

    fn num_public_inputs(&self) -> usize {
        Self::SUMMARY_WIDTH
    }

    fn constraints(&self) -> Vec<Constraint> {
        // The presentation AIR's constraints are just consistency checks on the
        // public inputs (`row[i] == public_inputs[i]`). The real work is done by
        // sub-AIRs. Generated from the layout so the full collision-resistant
        // binding width is bound, not just the first 4 felts.
        (0..Self::SUMMARY_WIDTH)
            .map(|i| Constraint {
                name: format!("summary_col_{i}_match"),
                eval: Box::new(move |row, _, public_inputs| row[i] - public_inputs[i]),
            })
            .collect()
    }

    fn generate_trace(&self) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
        let w = &self.witness;

        let final_root = if let Some(last) = w.fold_chain.last() {
            last.new_root
        } else {
            w.derivation.state_root
        };

        let presentation_tag = crate::binding::compute_presentation_tag_narrow(
            final_root,
            w.presentation_randomness,
            w.verifier_nonce,
        );

        let mut row = Vec::with_capacity(Self::SUMMARY_WIDTH);
        row.push(w.federation_root);
        row.extend_from_slice(&w.request_predicate); // 8 felts (ACTION_BINDING_WIDTH)
        row.push(w.timestamp);
        row.push(presentation_tag);
        row.extend_from_slice(w.revealed_facts_commitment.as_slice()); // 8 felts
        debug_assert_eq!(row.len(), Self::SUMMARY_WIDTH);

        let public_inputs = row.clone();

        (vec![row], public_inputs)
    }
}

// RETIRED 2026-07-16 (mock-proof purge): the free `prove_authorization` +
// `AuthorizationProof` (a trace-digest proof over `MultiStepDerivationAir`)
// had no callers. The production multi-step authorization proof is the rotated IR-v2
// descriptor path (`descriptor_by_name` + `prove_vm_descriptor2`).

/// Builder for constructing a presentation witness step by step.
pub struct PresentationBuilder {
    federation_root: BabyBear,
    request_predicate: crate::binding::ActionBinding,
    timestamp: BabyBear,
    fold_chain: Vec<FoldWitness>,
    derivation: Option<DerivationWitness>,
    issuer_membership: Option<MerkleWitness>,
    issuer_key_hash: BabyBear,
    revealed_facts_commitment: crate::binding::WideHash,
}

impl PresentationBuilder {
    /// Create a new presentation builder.
    pub fn new(
        federation_root: BabyBear,
        request_predicate: crate::binding::ActionBinding,
        timestamp: BabyBear,
    ) -> Self {
        Self {
            federation_root,
            request_predicate,
            timestamp,
            fold_chain: Vec::new(),
            derivation: None,
            issuer_membership: None,
            issuer_key_hash: BabyBear::ZERO,
            revealed_facts_commitment: crate::binding::WideHash::ZERO,
        }
    }

    /// Add a fold (attenuation) step to the chain.
    pub fn add_fold(mut self, fold: FoldWitness) -> Self {
        self.fold_chain.push(fold);
        self
    }

    /// Set the authorization derivation.
    pub fn set_derivation(mut self, derivation: DerivationWitness) -> Self {
        self.derivation = Some(derivation);
        self
    }

    /// Set the issuer membership proof.
    pub fn set_issuer_membership(mut self, membership: MerkleWitness, key_hash: BabyBear) -> Self {
        self.issuer_membership = Some(membership);
        self.issuer_key_hash = key_hash;
        self
    }

    /// Set the revealed facts commitment for selective disclosure.
    pub fn set_revealed_facts_commitment(mut self, commitment: crate::binding::WideHash) -> Self {
        self.revealed_facts_commitment = commitment;
        self
    }

    /// Build the presentation witness.
    pub fn build(self) -> Option<PresentationWitness> {
        let derivation = self.derivation?;
        let issuer_membership = self.issuer_membership?;

        Some(PresentationWitness {
            federation_root: self.federation_root,
            request_predicate: self.request_predicate,
            timestamp: self.timestamp,
            fold_chain: self.fold_chain,
            derivation,
            issuer_membership,
            issuer_key_hash: self.issuer_key_hash,
            revealed_facts_commitment: self.revealed_facts_commitment,
            composition_commitment: crate::binding::WideHash::ZERO,
            blinding_factor: BabyBear::ZERO,
            presentation_randomness: BabyBear::ZERO,
            verifier_nonce: BabyBear::ZERO,
            verifier_block_height: BabyBear::ZERO,
        })
    }
}

// ============================================================================
// Real STARK-backed presentation proof
// ============================================================================

/// Create a Merkle witness that uses Poseidon2 hashing (collision-resistant).
///
/// This builds the witness using `hash_fact(current, [sib0, sib1, sib2, position])` at each level,
/// making it compatible with the DSL `merkle_poseidon2_circuit()`.
/// Build a Merkle witness compatible with the Poseidon2 STARK prover.
pub fn create_poseidon2_compatible_witness(leaf_hash: BabyBear, depth: usize) -> MerkleWitness {
    use crate::poseidon2::hash_4_to_1;

    let mut current = leaf_hash;
    let mut levels = Vec::with_capacity(depth);

    for i in 0..depth {
        let position = (i % 4) as u8;
        let siblings = [
            BabyBear::new((i * 3 + 1) as u32),
            BabyBear::new((i * 3 + 2) as u32),
            BabyBear::new((i * 3 + 3) as u32),
        ];

        // DSL merkle_poseidon2_circuit uses hash_4_to_1(children) where
        // children are arranged by position: current at `position`, siblings
        // fill the remaining slots in order.
        let mut children = [BabyBear::ZERO; 4];
        children[position as usize] = current;
        let mut sib_idx = 0;
        for j in 0..4u8 {
            if j != position {
                children[j as usize] = siblings[sib_idx];
                sib_idx += 1;
            }
        }
        let parent = hash_4_to_1(&children);
        levels.push(MerkleLevelWitness { position, siblings });
        current = parent;
    }

    MerkleWitness {
        leaf_hash,
        levels,
        expected_root: current,
    }
}

/// Helper: Create a complete test presentation witness.
pub fn create_test_presentation() -> PresentationWitness {
    use crate::dsl::fold::build_shared_tree;

    let federation_root = BabyBear::new(1000000);
    let request_pred = crate::binding::compute_action_binding("test-action", "test-resource");
    let timestamp = BabyBear::new(1716000000); // some timestamp

    // Create a 2-step fold chain with valid membership proofs
    let final_root = BabyBear::new(333333);

    // Build tree for fold1
    let f1_hash = hash_fact(
        BabyBear::new(10),
        &[BabyBear::new(20), BabyBear::new(30), BabyBear::ZERO],
    );
    let (initial_root, f1_proofs) = build_shared_tree(&[f1_hash], 4);

    // Build tree for fold2
    let f2a_hash = hash_fact(
        BabyBear::new(40),
        &[BabyBear::new(50), BabyBear::ZERO, BabyBear::ZERO],
    );
    let f2b_hash = hash_fact(
        BabyBear::new(60),
        &[BabyBear::new(70), BabyBear::new(80), BabyBear::ZERO],
    );
    let (mid_root, f2_proofs) = build_shared_tree(&[f2a_hash, f2b_hash], 4);

    let fold1 = FoldWitness {
        old_root: initial_root,
        new_root: mid_root,
        removed_facts: vec![RemovedFact {
            predicate: BabyBear::new(10),
            terms: [BabyBear::new(20), BabyBear::new(30), BabyBear::ZERO],
            membership_proof: Some(f1_proofs.into_iter().next().unwrap()),
        }],
        num_added_checks: 1,
        added_checks_commitment: crate::dsl::fold::compute_test_checks_commitment(1),
    };

    let mut f2_iter = f2_proofs.into_iter();
    let fold2 = FoldWitness {
        old_root: mid_root,
        new_root: final_root,
        removed_facts: vec![
            RemovedFact {
                predicate: BabyBear::new(40),
                terms: [BabyBear::new(50), BabyBear::ZERO, BabyBear::ZERO],
                membership_proof: Some(f2_iter.next().unwrap()),
            },
            RemovedFact {
                predicate: BabyBear::new(60),
                terms: [BabyBear::new(70), BabyBear::new(80), BabyBear::ZERO],
                membership_proof: Some(f2_iter.next().unwrap()),
            },
        ],
        num_added_checks: 0,
        added_checks_commitment: crate::binding::WideHash::ZERO,
    };

    // Derivation: proves authorization from the final state
    let access_pred = BabyBear::new(300);
    let alice = BabyBear::new(1000);
    let resource = BabyBear::new(2000);
    let body_hash_1 = hash_fact(BabyBear::new(100), &[alice, resource, BabyBear::ZERO]);
    let body_hash_2 = hash_fact(BabyBear::new(200), &[alice, resource, BabyBear::ZERO]);

    let derivation = DerivationWitness {
        rule: CircuitRule {
            id: 1,
            num_body_atoms: 2,
            num_variables: 2,
            head_predicate: access_pred,
            head_terms: [
                (true, BabyBear::new(0)),
                (true, BabyBear::new(1)),
                (false, BabyBear::ZERO),
                (false, BabyBear::ZERO),
            ],
            body_atoms: vec![],
            equal_checks: vec![],
            memberof_checks: vec![],
            gte_check: None,
            lt_check: None,
        },
        state_root: final_root,
        body_fact_hashes: vec![body_hash_1, body_hash_2],
        substitution: vec![alice, resource],
        derived_predicate: access_pred,
        derived_terms: [alice, resource, BabyBear::ZERO, BabyBear::ZERO],
        not_after_height: BabyBear::ZERO,
        org_id_hash: BabyBear::ZERO,
        budget_remaining: BabyBear::ZERO,
    };

    // Issuer membership: prove issuer key is in the federation
    let issuer_key = BabyBear::new(42424242);
    let issuer_membership = create_issuer_membership(issuer_key, federation_root);

    PresentationWitness {
        federation_root,
        request_predicate: request_pred,
        timestamp,
        fold_chain: vec![fold1, fold2],
        derivation,
        issuer_membership,
        issuer_key_hash: issuer_key,
        revealed_facts_commitment: crate::binding::WideHash::ZERO,
        composition_commitment: crate::binding::WideHash::ZERO,
        blinding_factor: BabyBear::ZERO,
        presentation_randomness: BabyBear::new(123456789),
        verifier_nonce: BabyBear::ZERO,
        verifier_block_height: BabyBear::ZERO,
    }
}

/// Helper: Create a Merkle membership witness for the issuer key in the federation.
fn create_issuer_membership(issuer_key: BabyBear, _federation_root: BabyBear) -> MerkleWitness {
    use crate::merkle_air::compute_parent_poseidon2;

    // Build a witness that chains to the federation root
    let depth = 8; // shorter tree for federation
    let mut current = issuer_key;
    let mut levels = Vec::with_capacity(depth);

    for i in 0..depth {
        let position = (i % 4) as u8;
        let siblings = [
            BabyBear::new((i * 7 + 100) as u32),
            BabyBear::new((i * 7 + 200) as u32),
            BabyBear::new((i * 7 + 300) as u32),
        ];
        let parent = compute_parent_poseidon2(current, position, &siblings);
        levels.push(MerkleLevelWitness { position, siblings });
        current = parent;
    }

    // The computed root should match federation_root for a valid proof.
    // In test, we just use whatever root we compute.
    MerkleWitness {
        leaf_hash: issuer_key,
        levels,
        expected_root: current, // Will differ from federation_root in test
    }
}
