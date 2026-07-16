//! Full presentation builder.
//!
//! The presentation builder takes a plaintext token chain (a sequence of
//! attenuations) and produces a ZK-ready presentation proof. This is the
//! high-level API that orchestrates the entire pipeline:
//!
//! 1. Convert each token to a committed fact set.
//! 2. Compute fold deltas for each attenuation step.
//! 3. Evaluate the authorization request against the final state.
//! 4. Produce a circuit witness and generate the STARK proof.
//!
//! The resulting `BridgePresentationProof` can be verified without knowing
//! the token chain, capabilities, or any private data — only the public
//! inputs (federation root, request predicate, timestamp) are visible.

use dregg_circuit::binding::WideHash;
use dregg_circuit::derivation_air::{CircuitRule, DerivationWitness};
use dregg_circuit::fold_types::{FoldWitness, RemovedFact};
use dregg_circuit::merkle_air::{MerkleLevelWitness, MerkleWitness};
use dregg_circuit::merkle_types::compute_parent_poseidon2;
use dregg_circuit::poseidon2;
use dregg_circuit::predicate_arith_witness::{Blinding, FactBinding};
use dregg_circuit::presentation::{
    DescriptorProofWire, build_descriptor_wire, verify_descriptor_wire,
};
use dregg_circuit::{
    BabyBear, PresentationAir, PresentationProof, PresentationVerification, PresentationWitness,
};
use dregg_commit::merkle::{MerkleProof, MerkleTree};
use dregg_commit::{Fact, FieldElement, FoldDelta, SymbolTable, TokenState};
use dregg_dsl_runtime::fold::build_shared_tree;
use dregg_token::{Attenuation, AuthRequest, MacaroonToken};
use dregg_trace::{AuthorizationTrace, Conclusion, Term as TraceTerm, symbol_from_str};

use crate::authorize::{self, AuthError};
use crate::convert::macaroon_to_factset_secure;
use crate::delta::{further_attenuation_delta, initial_attenuation_delta};

/// Trait for resolving issuer membership in a federation.
///
/// A `FederationRegistry` provides real Merkle proofs from an externally-managed
/// federation tree. This is the production path for issuer membership: the tree
/// is maintained by the federation operator and the prover retrieves a proof for
/// its issuer key.
///
/// The synthetic/deterministic path in `build_issuer_membership()` is retained
/// as a **testing fallback only** and is clearly marked as such.
pub trait FederationRegistry {
    /// Look up the issuer's membership proof in the federation tree.
    ///
    /// Returns the Merkle proof (path indices + siblings at each level) and the
    /// current tree root, or `None` if the issuer is not a member.
    fn issuer_proof(&self, issuer_key: &[u8; 32]) -> Option<(MerkleProof, [u8; 32])>;
}

/// A step in the token chain: the token, its committed state, and the fold delta
/// from the previous state.
#[derive(Clone, Debug)]
pub struct ChainStep {
    /// The committed state at this step.
    pub state: TokenState,
    /// The fold delta from the previous step (None for the first step).
    pub delta: Option<FoldDelta>,
    /// Facts in the committed state.
    pub facts: Vec<Fact>,
}

/// Marker type that restricts access to the local-only constraint check path.
///
/// This type can only be constructed in test/benchmark code via
/// [`UnsafeLocalOnlyMarker::new_for_testing`]. Production code should never
/// hold an instance of this type.
pub struct UnsafeLocalOnlyMarker(());

impl UnsafeLocalOnlyMarker {
    /// Construct the marker. Only call this in tests or benchmarks.
    /// (Was gated on an undeclared `bench` feature — an always-false cfg; now uses
    /// the declared `test-utils` dev gate.)
    #[cfg(any(test, feature = "test-utils"))]
    pub fn new_for_testing() -> Self {
        Self(())
    }

    // AUDIT[P2]: `i_know_this_is_not_cryptographically_sound` is a `pub fn`
    // in production builds (not gated behind `cfg(test)` or a feature flag),
    // and grants a holder of `UnsafeLocalOnlyMarker` access to unsound
    // proof-generation paths. This is the same class of footgun as the
    // previous `DelegationAuthority::Open { warn: false }`: the obvious-name
    // strategy works for direct readers of the codebase but doesn't prevent
    // a derived crate from accidentally importing it. Recommended: gate
    // behind `#[cfg(any(test, feature = "unsafe-test-utils"))]` analogous
    // to the `DelegationAuthority::Open` fix in this PR.
    /// Escape hatch for non-test code that genuinely needs this (e.g., benchmarks
    /// in separate crates). Deliberately ugly name to discourage casual use.
    pub fn i_know_this_is_not_cryptographically_sound() -> Self {
        Self(())
    }
}

/// The high-level presentation builder that bridges plaintext tokens to ZK proofs.
///
/// Usage:
/// 1. Create with `new(issuer_key, federation_root)`.
/// 2. Call `set_root_token(token)` to set the initial (unrestricted) root token.
/// 3. Call `add_attenuation(attenuation)` for each attenuation step.
/// 4. Call `prove(request)` to generate the ZK presentation proof.
pub struct BridgePresentationBuilder {
    /// The issuer's key (used for federation membership proof).
    issuer_key: [u8; 32],
    /// The federation root of trust (raw bytes, for public input serialization).
    federation_root: [u8; 32],
    /// The federation root as a BabyBear field element (used for Merkle comparison).
    federation_root_bb: BabyBear,
    /// Chain of committed states and fold deltas.
    chain: Vec<ChainStep>,
    /// The accumulated symbol table.
    symbols: SymbolTable,
    /// The root token (first token in the chain).
    root_token: Option<MacaroonToken>,
    /// The authorization state: includes all semantic facts (app, service, feature, etc.)
    /// that are needed for policy evaluation. This is separate from the fold chain states
    /// because the fold chain only tracks structural narrowing.
    auth_state: TokenState,
    /// Optional external federation tree for real issuer membership proofs.
    /// When set, `build_issuer_membership` uses a real Merkle path from this tree
    /// instead of the synthetic/deterministic fallback.
    federation_tree: Option<MerkleTree>,
    /// Pre-generated federation membership proof (for delegated tokens).
    ///
    /// When set, `build_issuer_membership` and `build_issuer_membership_poseidon2` use
    /// this proof directly instead of looking up the issuer_key in the federation tree.
    /// This is the delegation architecture fix: the delegator (who has the real issuer key
    /// in the tree) pre-generates the proof and passes it to the delegatee.
    pre_generated_membership_proof: Option<MerkleProof>,
    /// Commitment to the set of facts being selectively disclosed.
    ///
    /// For selective disclosure mode, this is computed by the SDK before calling
    /// `prove()`. It is `poseidon2(hash(fact_1) || ... || hash(fact_n))` over the
    /// revealed facts. For fully private mode, this is `WideHash::ZERO`.
    revealed_facts_commitment: WideHash,
}

/// Bridge-side real presentation proof: the two committed in-circuit descriptor wires
/// (bound-presentation auth + blinded ring-membership) plus the fold/derivation roots the
/// composition-commitment binding recomputes over.
///
/// This replaced the retired `dregg_circuit::RealPresentationProof` when the presentation family
/// flipped off the hand-`StarkProof` onto the two committed descriptors. The cryptographic content
/// lives entirely in the two [`DescriptorProofWire`]s (each verified via `descriptor_by_name` →
/// `verify_vm_descriptor2`); `fold_step_roots` / `derivation_state_root` are the non-cryptographic
/// roots the composition commitment is recomputed over (they formerly rode inside the legacy
/// constraint-checked fold/derivation proofs, which carried no independent cryptographic weight).
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct RealPresentationProof {
    /// AUTH descriptor wire: the bound-presentation proof (`dregg-bound-presentation::v1`) —
    /// action_binding + revealed_facts + the in-circuit presentation-tag binding.
    /// Verified via `descriptor_by_name` → `verify_vm_descriptor2`; PIs `[summary(19), verifier_nonce]`.
    pub bound_presentation: DescriptorProofWire,
    /// RING/UNLINKABILITY descriptor wire: the depth-general 4-ary blinded ring-membership proof
    /// (issuer ∈ federation, unlinkable). PIs `[blinded_leaf, root]`.
    pub blinded_membership: DescriptorProofWire,
    /// Per-fold-step `[old_root, new_root]` pairs — the fold-chain roots the composition
    /// commitment is recomputed over.
    pub fold_step_roots: Vec<[BabyBear; 2]>,
    /// The final derivation state root — the second element the composition commitment binds.
    pub derivation_state_root: BabyBear,
}

impl RealPresentationProof {
    /// Total proof size in bytes (the two committed descriptor blobs).
    pub fn total_proof_size_bytes(&self) -> usize {
        self.bound_presentation.blob.len() + self.blinded_membership.blob.len()
    }

    /// Human-readable proof size.
    pub fn proof_size_display(&self) -> String {
        let bytes = self.total_proof_size_bytes();
        if bytes < 1024 {
            format!("{bytes} B")
        } else if bytes < 1024 * 1024 {
            format!("{:.1} KiB", bytes as f64 / 1024.0)
        } else {
            format!("{:.1} MiB", bytes as f64 / (1024.0 * 1024.0))
        }
    }
}

/// Build the bridge-side [`RealPresentationProof`] from a presentation witness.
///
/// This is the descriptor-wire PRODUCER that replaced the retired
/// `PresentationAir::prove_stark_poseidon2()`: issuer membership and bound-presentation auth are
/// each proven through the real IR-v2 prover and carried in wire form, verified by the consumer
/// via `descriptor_by_name` → `verify_vm_descriptor2`. Returns `None` (fail-closed) if either
/// descriptor fails to prove or the blinded ring-membership root does not bind the federation root.
fn build_real_presentation_proof(w: &PresentationWitness) -> Option<RealPresentationProof> {
    // The fold-chain roots + derivation state root the composition-commitment recompute hashes over.
    let fold_step_roots: Vec<[BabyBear; 2]> = w
        .fold_chain
        .iter()
        .map(|f| [f.old_root, f.new_root])
        .collect();
    let derivation_state_root = w.derivation.state_root;

    let final_root = if let Some(last_fold) = w.fold_chain.last() {
        last_fold.new_root
    } else {
        w.derivation.state_root
    };

    // (a) RING/UNLINKABILITY — the depth-general 4-ary BLINDED ring-membership descriptor.
    //     PIs [blinded_leaf, root]; the member leaf_hash + blinding factor stay hidden.
    let siblings: Vec<[BabyBear; 3]> = w
        .issuer_membership
        .levels
        .iter()
        .map(|l| l.siblings)
        .collect();
    let positions: Vec<u8> = w
        .issuer_membership
        .levels
        .iter()
        .map(|l| l.position)
        .collect();
    let depth = siblings.len();
    let (blinded_trace, blinded_pis) =
        dregg_circuit::blinded_membership_witness::blinded_membership_witness_4ary(
            w.issuer_membership.leaf_hash,
            w.blinding_factor,
            &siblings,
            &positions,
        )
        .ok()?;
    // Fail-closed: the committed root MUST be the federation root, else the proof would not bind
    // the issuer to this federation.
    if blinded_pis
        .get(dregg_circuit::blinded_membership_witness::PI_ROOT_4ARY)
        .copied()
        != Some(w.issuer_membership.expected_root)
    {
        return None;
    }
    let blinded_desc =
        dregg_circuit::blinded_membership_witness::blinded_membership_descriptor_of_depth_4ary(
            depth,
        );
    let blinded_membership = build_descriptor_wire(&blinded_desc, &blinded_trace, &blinded_pis)?;

    // (b) AUTH — the bound-presentation descriptor: action_binding + revealed_facts + the
    //     presentation_tag internalized in-circuit. PIs [summary(19), verifier_nonce].
    let revealed_facts: [BabyBear; 8] = *w.revealed_facts_commitment.as_slice();
    let (bound_trace, bound_pis) =
        dregg_circuit::bound_presentation_witness::bound_presentation_witness_h4(
            w.federation_root,
            w.request_predicate,
            w.timestamp,
            revealed_facts,
            final_root,
            w.presentation_randomness,
            w.verifier_nonce,
        )
        .ok()?;
    let bound_desc = dregg_circuit::descriptor_by_name::descriptor_by_name(
        dregg_circuit::bound_presentation_witness::BOUND_PRESENTATION_NAME,
    )?;
    let bound_presentation = build_descriptor_wire(&bound_desc, &bound_trace, &bound_pis)?;

    Some(RealPresentationProof {
        bound_presentation,
        blinded_membership,
        fold_step_roots,
        derivation_state_root,
    })
}

/// The complete bridge presentation proof.
///
/// Contains both the ZK proof (circuit-level) and the supporting metadata
/// needed for full verification.
///
/// # Zero-Knowledge Safety
///
/// The `trace` field contains the full authorization derivation trace (all derived
/// facts). This field is **never serialized** to prevent leaking private information
/// over the wire. It is only populated locally for debugging and off-chain verification.
#[derive(Clone, Debug)]
pub struct BridgePresentationProof {
    /// The circuit-level presentation proof (constraint-checked).
    pub circuit_proof: PresentationProof,
    /// Real STARK proof for issuer membership (generated by `prove()`).
    /// This is the proof that the wire protocol should extract and transmit.
    /// `None` when using the fast `prove_fast()` path.
    pub real_stark_proof: Option<RealPresentationProof>,
    /// The authorization trace (for debugging / off-chain verification).
    ///
    /// **SECURITY: This field MUST NOT be transmitted over the wire.** It contains
    /// the full derived fact set which would defeat the zero-knowledge property.
    /// Only available locally after proof generation.
    ///
    /// Use [`Self::into_wire_proof()`] to produce a wire-safe representation that
    /// strips the trace before transmission.
    pub trace: AuthorizationTrace,
    /// Number of attenuation steps in the chain.
    pub chain_length: usize,
    /// The final state root (public input).
    pub final_state_root: [u8; 32],
    /// The federation root (public input).
    pub federation_root: [u8; 32],
    /// Verification result from the circuit layer.
    pub verification: PresentationVerification,
    /// Commitment to the selectively revealed facts (BabyBear field element).
    ///
    /// For selective disclosure mode, this is the Poseidon2 hash over the revealed
    /// fact hashes. The verifier recomputes from the plaintext facts and checks equality.
    /// For fully private mode, this is `WideHash::ZERO`.
    pub revealed_facts_commitment: WideHash,
    /// Composition commitment binding all sub-proofs together.
    ///
    /// This is `poseidon2(fold_chain_commitment, derivation_state_root, presentation_tag)`.
    /// It is included as a public input in the issuer membership STARK, preventing
    /// an attacker from mixing sub-proofs across different presentations.
    /// The verifier recomputes this from the other sub-proofs and checks it matches
    /// the value committed in the STARK's public inputs.
    pub composition_commitment: WideHash,
}

impl BridgePresentationProof {
    /// Whether the proof is cryptographically valid.
    ///
    /// Returns `true` ONLY if a real STARK proof is present AND the circuit-level
    /// verification passed. Proofs generated via `prove_fast()` will return `false`
    /// because they have no cryptographic backing (no real STARK proof).
    ///
    /// For proofs from `prove_fast()`, use `is_constraint_checked()` to determine
    /// if the constraint system passed (useful for development, NOT for security).
    pub fn is_valid(&self) -> bool {
        // Cryptographic backing means a REAL STARK proof — nothing else counts.
        // (The retired mock `ivc_proof` used to satisfy this check; it never
        // provided soundness and is gone.)
        if self.real_stark_proof.is_none() {
            return false;
        }
        self.verification == PresentationVerification::Valid
    }

    /// Whether the proof passed local constraint checking.
    ///
    /// This indicates the circuit constraints were satisfied locally, which is
    /// useful for development and debugging. However, this provides NO security
    /// guarantee to a remote verifier because the prover runs the check themselves.
    ///
    /// For cryptographic verification across trust boundaries, use `is_valid()`
    /// which requires a real STARK proof.
    pub fn is_constraint_checked(&self) -> bool {
        matches!(
            self.verification,
            PresentationVerification::Valid | PresentationVerification::LocalOnly
        )
    }

    /// Get the proof size in bytes.
    pub fn proof_size_bytes(&self) -> usize {
        if let Some(real) = &self.real_stark_proof {
            real.total_proof_size_bytes()
        } else {
            self.circuit_proof.total_proof_size_bytes
        }
    }

    /// Human-readable proof size.
    pub fn proof_size_display(&self) -> String {
        if let Some(real) = &self.real_stark_proof {
            real.proof_size_display()
        } else {
            self.circuit_proof.proof_size_display()
        }
    }

    /// Whether this proof contains a real STARK issuer membership proof.
    pub fn has_real_stark_proof(&self) -> bool {
        self.real_stark_proof.is_some()
    }

    // MIGRATED wire accessors: the legacy `issuer_proof_bytes()` (opaque
    // `stark::proof_to_bytes(issuer_membership_stark_proof)` blob dispatched by
    // air-name) and `verify_issuer_stark()` (`stark::verify` on that blob) have been
    // removed on the `StarkProof` → `Ir2BatchProof` migration. The issuer-membership
    // producer is now `BridgePresentationBuilder::prove_issuer_membership_ir2_wire`
    // and the consumer is `crate::verifier::DescriptorDispatchVerifier`
    // (`descriptor_by_name(predicate)` → decode `postcard(Ir2BatchProof)` →
    // `verify_vm_descriptor2`) — no opaque issuer-STARK wire survives.

    /// Convert this proof into a wire-safe representation that strips the private trace.
    ///
    /// **All wire protocol code MUST use this method** before transmitting a proof.
    /// The returned `WirePresentationProof` contains only the cryptographic proof data
    /// and public inputs, with the private authorization trace completely removed.
    ///
    /// Fields stripped for privacy (Phase 2):
    /// - `trace` (was always stripped — contains full derivation)
    /// - `chain_length` (leaks delegation depth)
    /// - `final_state_root` (deterministic per-token, enables linkage)
    /// - `federation_root` bytes (available from the STARK proof's public inputs)
    pub fn into_wire_proof(self) -> WirePresentationProof {
        WirePresentationProof {
            circuit_proof: self.circuit_proof,
            real_stark_proof: self.real_stark_proof,
            verification: self.verification,
            revealed_facts_commitment: self.revealed_facts_commitment,
            composition_commitment: self.composition_commitment,
        }
    }
}

/// Wire-safe presentation proof (no private trace data).
///
/// This is the type that MUST be used for any network transmission of proofs.
/// It deliberately omits the `AuthorizationTrace` to preserve zero-knowledge.
///
/// # Privacy Design (Phase 2)
///
/// The `chain_length`, `final_state_root`, and raw `federation_root` bytes have been
/// removed because they leak delegation depth and enable cross-presentation linkage.
/// The presentation_tag (in the circuit proof's public inputs) replaces the deterministic
/// final_state_root for unlinkable multi-show.
///
// AUDIT[P3]: `WirePresentationProof` has all `pub` fields, including
// `verification: PresentationVerification`. A malicious prover deserializing
// this proof, mutating `verification = Valid` post-deserialization, and then
// (in some downstream code path that checks `proof.verification ==
// PresentationVerification::Valid` without re-running the actual STARK
// verifier) could short-circuit a verifier. We searched: the canonical
// `verify_proof_complete` does NOT rely on the prover-supplied
// `verification` field — it independently runs STARK + composition +
// freshness checks. So this is currently safe. But the field's existence on
// the wire is a footgun for future verifiers who might trust it. Severity
// P3: not currently exploitable but the field should either be removed
// from the wire form or marked `#[serde(skip)]`.
/// Obtain via [`BridgePresentationProof::into_wire_proof()`].
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct WirePresentationProof {
    /// The circuit-level presentation proof (constraint-checked).
    pub circuit_proof: PresentationProof,
    /// Real STARK proof for issuer membership.
    pub real_stark_proof: Option<RealPresentationProof>,
    /// Verification result from the circuit layer.
    pub verification: PresentationVerification,
    /// Commitment to the selectively revealed facts.
    pub revealed_facts_commitment: WideHash,
    /// Composition commitment binding all sub-proofs together.
    pub composition_commitment: WideHash,
}

/// The NEW IR-v2 issuer-membership wire triple — the flipped replacement for the
/// opaque `stark::proof_to_bytes(RealPresentationProof.issuer_membership_stark_proof)`
/// encoding on the `StarkProof` → `Ir2BatchProof` migration.
///
/// * `predicate` — the descriptor identity the CONSUMER dispatches on
///   (`merkle-membership::poseidon2-4ary-general-depth{N}`). NO air-name rides the
///   blob: the descriptor is resolved from this committed predicate identity via
///   [`dregg_circuit::descriptor_by_name::descriptor_by_name`], never from
///   prover-controlled proof bytes.
/// * `blob` — `postcard(Ir2BatchProof)`: the deployed 4-ary depth-general
///   Merkle-membership descriptor's proof, produced by the real
///   [`dregg_circuit::descriptor_ir2::prove_vm_descriptor2`].
/// * `vk` — the expected public inputs `[leaf, root]`, one canonical little-endian
///   `u32` per 4 bytes — exactly the encoding
///   [`crate::verifier::DescriptorDispatchVerifier`] (and the routed
///   `ProofVerifier::verify_with_predicate`) decodes.
#[derive(Clone, Debug)]
pub struct Ir2IssuerWire {
    /// Descriptor identity the consumer dispatches on (never rides the blob).
    pub predicate: String,
    /// `postcard(Ir2BatchProof)` — the NEW wire format for the membership proof.
    pub blob: Vec<u8>,
    /// Expected public inputs `[leaf, root]` as one canonical LE `u32` per 4 bytes.
    pub vk: Vec<u8>,
}

/// Prove issuer federation membership in the NEW IR-v2 descriptor wire format.
///
/// `(leaf, siblings, positions)` is a 4-ary Poseidon2 authentication path — each
/// `position ∈ {0,1,2,3}`, three co-path siblings per level — EXACTLY the shape
/// [`compute_parent_poseidon2`] / [`BridgePresentationBuilder::build_issuer_membership_poseidon2`]
/// already build. The implied root is BYTE-EQUAL to the deployed `hash_4_to_1`-chained
/// federation root and is committed as the second public input (`vk`'s second limb).
///
/// This is the opaque-byte-encoder flip: it replaces
/// `stark::proof_to_bytes(StarkProof)` with `postcard(Ir2BatchProof)` and drops the
/// air-name entirely. `depth` (`siblings.len()`) must be a power of two ≥ 2 (the
/// trace-height requirement of [`dregg_circuit::membership_descriptor_4ary::membership_witness_4ary`]).
pub fn prove_issuer_membership_ir2(
    leaf: BabyBear,
    siblings: &[[BabyBear; 3]],
    positions: &[u8],
) -> Result<Ir2IssuerWire, AuthError> {
    use dregg_circuit::descriptor_ir2::{MemBoundaryWitness, prove_vm_descriptor2};
    use dregg_circuit::membership_descriptor_4ary::{
        membership_descriptor_of_depth_4ary, membership_witness_4ary,
    };

    let depth = siblings.len();
    // Honest 4-ary witness → base trace + public inputs `[leaf, root]`.
    let (trace, pis) = membership_witness_4ary(leaf, siblings, positions)
        .map_err(|e| AuthError::InvalidRequest(format!("issuer membership 4-ary witness: {e}")))?;
    // The depth-general 4-ary descriptor (name pins the depth ⇒ VK-separated).
    let desc = membership_descriptor_of_depth_4ary(depth);
    // The REAL IR-v2 prover — the deployed descriptor-prover, not a mock.
    let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
        .map_err(|e| AuthError::InvalidRequest(format!("issuer membership IR-v2 prove: {e}")))?;
    // WIRE: postcard-encode the BatchProof (replaces stark::proof_to_bytes).
    let blob = postcard::to_allocvec(&proof)
        .map_err(|e| AuthError::InvalidRequest(format!("issuer membership blob encode: {e}")))?;
    // VK carries the expected public inputs as canonical LE-u32 limbs.
    let mut vk = Vec::with_capacity(pis.len() * 4);
    for p in &pis {
        vk.extend_from_slice(&p.0.to_le_bytes());
    }
    Ok(Ir2IssuerWire {
        predicate: desc.name,
        blob,
        vk,
    })
}

impl BridgePresentationBuilder {
    /// Create a new presentation builder.
    ///
    /// # Arguments
    ///
    /// * `issuer_key` - The issuer's 32-byte key (hashed for federation membership).
    /// * `federation_root` - The 32-byte canonical encoding of the federation root
    ///   (produced by [`bb_to_bytes`]: u32 LE in bytes [0..4], zeros in [4..32]).
    pub fn new(issuer_key: [u8; 32], federation_root: [u8; 32]) -> Self {
        let federation_root_bb = bb_from_bytes(&federation_root);
        Self {
            issuer_key,
            federation_root,
            federation_root_bb,
            chain: Vec::new(),
            symbols: SymbolTable::new(),
            root_token: None,
            auth_state: TokenState::new(),
            federation_tree: None,
            pre_generated_membership_proof: None,
            revealed_facts_commitment: WideHash::ZERO,
        }
    }

    /// Create a new presentation builder with a pre-computed BabyBear federation root.
    ///
    /// This is used when the federation root is known as a field element (e.g., from
    /// a Merkle tree that already operates in BabyBear). The `federation_root` bytes
    /// are still stored for public input serialization.
    pub fn new_with_root_bb(
        issuer_key: [u8; 32],
        federation_root: [u8; 32],
        federation_root_bb: BabyBear,
    ) -> Self {
        Self {
            issuer_key,
            federation_root,
            federation_root_bb,
            chain: Vec::new(),
            symbols: SymbolTable::new(),
            root_token: None,
            auth_state: TokenState::new(),
            federation_tree: None,
            pre_generated_membership_proof: None,
            revealed_facts_commitment: WideHash::ZERO,
        }
    }

    /// Set the revealed facts commitment for selective disclosure mode.
    ///
    /// This must be called before `prove()` when generating a selective disclosure
    /// proof. The commitment binds the revealed facts to the STARK proof, ensuring
    /// the prover cannot lie about which facts were part of the derivation.
    ///
    /// The commitment is `poseidon2(hash(fact_1) || hash(fact_2) || ... || hash(fact_n))`
    /// where each fact_i is hashed with `poseidon2::hash_fact()`.
    pub fn set_revealed_facts_commitment(&mut self, commitment: WideHash) -> &mut Self {
        self.revealed_facts_commitment = commitment;
        self
    }

    /// Attach an external federation Merkle tree for real issuer membership proofs.
    ///
    /// When a federation tree is provided, `build_issuer_membership()` will look up
    /// the issuer key in this tree and use the real Merkle path. This is the production
    /// path that connects to an actual federation registry.
    ///
    /// Without this, the builder falls back to a synthetic/deterministic path that is
    /// only suitable for testing.
    pub fn with_federation_tree(&mut self, tree: MerkleTree) -> &mut Self {
        // Recompute the federation root from the actual tree.
        // The tree root is a full 32-byte BLAKE3 hash; compress it to BabyBear
        // via Poseidon2, then store the canonical bb_to_bytes encoding so that
        // verifiers can recover it with bb_from_bytes.
        let mut tree_clone = tree.clone();
        let root_bytes = tree_clone.root();
        self.federation_root_bb = bytes_to_babybear(&root_bytes);
        self.federation_root = bb_to_bytes(self.federation_root_bb);
        self.federation_tree = Some(tree);
        self
    }

    /// Attach a pre-generated federation membership proof for delegation scenarios.
    ///
    /// Federation tree leaves are BLAKE3-derived proof keys (not raw root keys).
    /// The delegator pre-generates the membership proof at delegation time using the
    /// derived key, and the delegatee passes it here for direct use during proving.
    ///
    /// When this is set, `build_issuer_membership` and `build_issuer_membership_poseidon2`
    /// use this proof directly instead of querying the federation tree.
    ///
    /// The `federation_root` on this builder must still be set correctly (matching the
    /// root the proof was generated against) for the proof to verify.
    pub fn with_pre_generated_membership_proof(&mut self, proof: MerkleProof) -> &mut Self {
        self.pre_generated_membership_proof = Some(proof);
        self
    }

    /// Set the root (unrestricted) token.
    ///
    /// This is the initial token minted by the issuer. It has no caveats
    /// and represents unlimited access.
    pub fn set_root_token(&mut self, token: MacaroonToken) {
        let (factset, syms) = macaroon_to_factset_secure(&token);
        self.symbols.merge(&syms);

        let facts: Vec<Fact> = factset.iter().copied().collect();
        let mut state = TokenState::new();
        for &fact in &facts {
            state.add_fact(fact);
        }

        // Initialize the authorization state with the same facts.
        self.auth_state = TokenState::new();
        for &fact in &facts {
            self.auth_state.add_fact(fact);
        }

        self.chain.push(ChainStep {
            state,
            delta: None,
            facts,
        });
        self.root_token = Some(token);
    }

    /// Add an attenuation step to the chain.
    ///
    /// This takes the `Attenuation` spec (the restrictions being applied)
    /// and computes the fold delta from the current state to the new state.
    ///
    /// # Returns
    ///
    /// `true` if the attenuation was successfully applied, `false` if it
    /// was invalid (e.g., trying to attenuate an empty chain).
    pub fn add_attenuation(&mut self, attenuation: &Attenuation) -> bool {
        let current_step = match self.chain.last() {
            Some(step) => step,
            None => return false,
        };

        // SOUNDNESS: Reject delegation chains deeper than MAX_FOLD_DEPTH.
        // The chain length includes the root step, so fold count = chain.len() - 1.
        // After adding this attenuation it would be chain.len(), so the fold count
        // would be chain.len(). Reject if that exceeds the limit.
        if self.chain.len() as u32 >= dregg_circuit::MAX_FOLD_DEPTH {
            return false;
        }

        let current_state = &current_step.state;

        // Convert attenuation to new restriction facts.
        let new_facts = crate::convert::attenuation_to_facts(attenuation, &mut self.symbols);

        if new_facts.is_empty() {
            return false;
        }

        // If this is the first attenuation (from unrestricted root), we remove
        // the unrestricted fact and add checks.
        let is_first_attenuation = current_step.facts.len() == 1
            && current_step.facts[0].predicate == FieldElement::from_symbol("unrestricted");

        if is_first_attenuation {
            let result = initial_attenuation_delta(attenuation, &mut self.symbols);
            match result {
                Some((_old_state, new_state, delta)) => {
                    // SECURITY: The auth_state and the fold chain's fact set must be
                    // bound together. The circuit's DerivationWitness uses the Poseidon2
                    // root of `ChainStep.facts` as its state_root, and the authorization
                    // evaluator uses auth_state. By using the SAME semantic facts for
                    // both, we ensure the authorization decision IS what gets proven.
                    //
                    // The new_facts (semantic: app, service, feature, etc.) are used for
                    // auth_state AND stored as the chain step's facts (for Poseidon2 root).
                    // The new_state (structural: check-prefixed) is only for fold delta
                    // continuity.
                    self.auth_state = TokenState::new();
                    for fact in &new_facts {
                        self.auth_state.add_fact(*fact);
                    }

                    self.chain.push(ChainStep {
                        state: new_state,
                        delta: Some(delta),
                        facts: new_facts.clone(),
                    });
                    true
                }
                None => false,
            }
        } else {
            // Subsequent attenuation: add restrictions as checks.
            let result = further_attenuation_delta(current_state, &new_facts, &self.symbols);
            match result {
                Some((new_state, delta)) => {
                    // SECURITY: Accumulate semantic facts and use them for both
                    // auth_state and the chain step's Poseidon2 root computation.
                    // This ensures the derivation witness's state_root covers exactly
                    // the facts that the authorization evaluator used.
                    for fact in &new_facts {
                        if !self.auth_state.contains(fact) {
                            self.auth_state.add_fact(*fact);
                        }
                    }

                    // The chain step facts = all semantic facts accumulated so far.
                    let all_semantic_facts = self.auth_state.all_facts();

                    self.chain.push(ChainStep {
                        state: new_state,
                        delta: Some(delta),
                        facts: all_semantic_facts,
                    });
                    true
                }
                None => false,
            }
        }
    }

    /// Get the current chain length (number of states, including root).
    pub fn chain_length(&self) -> usize {
        self.chain.len()
    }

    /// Get the current (final) state, if any.
    pub fn final_state(&self) -> Option<&TokenState> {
        self.chain.last().map(|s| &s.state)
    }

    /// Get the symbol table.
    pub fn symbols(&self) -> &SymbolTable {
        &self.symbols
    }

    /// Verify the fold chain integrity.
    ///
    /// Checks that all fold deltas in the chain are valid and properly linked.
    pub fn verify_chain(&self) -> bool {
        let deltas: Vec<&FoldDelta> = self
            .chain
            .iter()
            .filter_map(|step| step.delta.as_ref())
            .collect();

        if deltas.is_empty() {
            return true; // Only the root, no attenuations.
        }

        // Each delta must individually verify.
        for delta in &deltas {
            if !delta.apply_and_verify() {
                return false;
            }
        }

        // Chain continuity: each delta's new_root must equal the next delta's old_root.
        for i in 0..deltas.len() - 1 {
            if deltas[i].new_root != deltas[i + 1].old_root {
                return false;
            }
        }

        true
    }

    /// Generate a real STARK-backed presentation proof for the given authorization request.
    ///
    /// This is the main entry point that:
    /// 1. Verifies the fold chain.
    /// 2. Evaluates the authorization request against the final state.
    /// 3. Converts the trace to circuit witnesses.
    /// 4. Generates a real Poseidon2 STARK proof for issuer membership.
    ///
    /// For the fast development path that skips real STARK proof generation,
    /// use [`prove_local_constraint_check_only()`](Self::prove_local_constraint_check_only) instead.
    ///
    /// # Arguments
    ///
    /// * `request` - The authorization request to prove.
    ///
    /// # Returns
    ///
    /// A `BridgePresentationProof` backed by a real STARK issuer membership proof,
    /// or an error if authorization fails or the proof cannot be generated.
    pub fn prove(&mut self, request: &AuthRequest) -> Result<BridgePresentationProof, AuthError> {
        self.prove_real(request)
    }

    /// Generate a local constraint-check-only presentation proof.
    ///
    /// **WARNING: NOT CRYPTOGRAPHICALLY SOUND.** This validates circuit constraints
    /// locally without producing a STARK proof. The resulting proof's `is_valid()`
    /// returns `false` because it has no cryptographic backing. Use
    /// `is_constraint_checked()` to query the local constraint result.
    ///
    /// This is suitable ONLY for:
    /// - Development iteration and debugging
    /// - Benchmarking constraint evaluation overhead
    /// - Scenarios where prover == verifier (co-located, trusted)
    ///
    /// **Do NOT use for untrusted provers or cross-trust-boundary verification.**
    /// For production use, call [`prove`](Self::prove) which generates a real STARK proof.
    ///
    /// # Arguments
    ///
    /// * `_unsafe_marker` - Proof that the caller acknowledges this is not cryptographically sound.
    /// * `request` - The authorization request to prove.
    ///
    /// # Returns
    ///
    /// A `BridgePresentationProof` with `is_valid() == false` (no cryptographic proof).
    /// Use `is_constraint_checked()` to check if constraints passed locally.
    pub fn prove_local_constraint_check_only(
        &mut self,
        _unsafe_marker: &UnsafeLocalOnlyMarker,
        request: &AuthRequest,
    ) -> Result<BridgePresentationProof, AuthError> {
        // 1. Get the final state.
        let final_step = self.chain.last().ok_or(AuthError::EmptyState)?;
        let final_state = &final_step.state;

        // 2. Evaluate authorization against the auth_state which contains the
        //    actual semantic facts (app, service, feature, etc.) needed by policy rules.
        let trace = authorize::authorize_with_trace(&self.auth_state, request, &self.symbols)?;

        // 3. Compute the final state root (from the fold chain state).
        let final_root_bytes = final_state.root_immutable();

        // 4. Build the circuit witness (Poseidon2 path — legacy linear path removed).
        let circuit_witness = self.build_circuit_witness_poseidon2(&trace, request)?;

        // 5. Generate the presentation proof.
        let air = PresentationAir::new(circuit_witness.clone());
        let constraint_result = air.verify_all();

        let circuit_proof = air
            .prove()
            .ok_or_else(|| AuthError::InvalidRequest("proof generation failed".into()))?;

        // SECURITY: prove_fast() produces NO cryptographic proof. Even if constraints
        // pass locally, we report `LocalOnly` to prevent callers from mistaking this
        // for a cryptographically verified proof. Only `prove()` (with a real STARK)
        // sets `Valid`.
        let verification = if constraint_result == PresentationVerification::Valid {
            PresentationVerification::LocalOnly
        } else {
            constraint_result
        };

        Ok(BridgePresentationProof {
            circuit_proof,
            real_stark_proof: None,
            trace,
            chain_length: self.chain.len(),
            final_state_root: final_root_bytes,
            federation_root: self.federation_root,
            verification,
            revealed_facts_commitment: self.revealed_facts_commitment,
            composition_commitment: WideHash::ZERO, // local constraint check has no STARK binding
        })
    }

    /// Generate a STARK-backed presentation proof using Poseidon2 hashing.
    ///
    /// This is the internal implementation of [`prove`](Self::prove). It calls
    /// [`build_real_presentation_proof`] to produce the two committed descriptor-wire proofs
    /// (bound-presentation auth + blinded ring-membership) via the real IR-v2 prover.
    ///
    /// # Arguments
    ///
    /// * `request` - The authorization request to prove.
    ///
    /// # Returns
    ///
    /// A `BridgePresentationProof` backed by a real STARK issuer membership proof
    /// with Poseidon2 hash constraints (collision-resistant), or an error if
    /// authorization fails or the proof cannot be generated.
    fn prove_real(&mut self, request: &AuthRequest) -> Result<BridgePresentationProof, AuthError> {
        // 1. Get the final state.
        let final_step = self.chain.last().ok_or(AuthError::EmptyState)?;
        let final_state = &final_step.state;

        // 2. Evaluate authorization against the auth_state.
        let trace = authorize::authorize_with_trace(&self.auth_state, request, &self.symbols)?;

        // 3. Compute the final state root.
        let final_root_bytes = final_state.root_immutable();

        // 4. Build the circuit witness with Poseidon2-compatible issuer membership.
        let circuit_witness = self.build_circuit_witness_poseidon2(&trace, request)?;

        // 5. Generate the presentation proof using the Poseidon2 STARK path.
        //    The STARK proof for issuer membership is stored in the result so the
        //    wire protocol extracts issuer membership via the IR-v2 descriptor wire
        //    (`prove_issuer_membership_ir2_wire`), not an opaque issuer-STARK blob.
        let air = PresentationAir::new(circuit_witness.clone());
        let verification = air.verify_all();

        // Generate the two committed descriptor-wire proofs (bound-presentation auth + blinded
        // ring-membership). This is the descriptor-wire flip off the retired hand-STARK issuer
        // proof: both descriptors are proven through the real IR-v2 prover and carried in wire form.
        let stark_proof = build_real_presentation_proof(&circuit_witness).ok_or_else(|| {
            AuthError::InvalidRequest("descriptor-wire presentation proof generation failed".into())
        })?;

        // Also generate the constraint proof for the circuit_proof field.
        let circuit_proof = air
            .prove()
            .ok_or_else(|| AuthError::InvalidRequest("proof generation failed".into()))?;

        // The composition_commitment was computed in build_circuit_witness_poseidon2
        // and binds the sub-proof roots (fold chain + derivation) to the presentation tag.
        let composition_commitment = circuit_witness.composition_commitment;

        Ok(BridgePresentationProof {
            circuit_proof,
            real_stark_proof: Some(stark_proof),
            trace,
            chain_length: self.chain.len(),
            final_state_root: final_root_bytes,
            federation_root: self.federation_root,
            verification,
            revealed_facts_commitment: self.revealed_facts_commitment,
            composition_commitment,
        })
    }

    // RETIRED 2026-07-16 (mock-proof purge): `prove_ivc` — the IVC-backed presentation
    // path — is gone. It produced a proof whose only "cryptographic" leg was the
    // simulated hash-chain IVC (mintable by anyone), yet `is_valid()` honored it.
    // Its sole caller was a bench. The real path is `prove()` (real STARK).

    /// Generate a STARK-backed presentation proof with per-fact disclosure control.
    ///
    /// This extends `prove()` with predicate proof generation for specified facts.
    /// For each fact in `predicate_facts`, a `BridgePredicateProof` is generated
    /// proving the fact's value satisfies the given predicate without revealing it.
    ///
    /// # Arguments
    ///
    /// * `request` - The authorization request to prove.
    /// * `predicate_facts` - List of `(fact_value, fact_terms, predicate)` tuples. `fact_terms`
    ///   carries the fact's IDENTITY (predicate symbol + terms 1..2); the fact hash is DERIVED from
    ///   it together with `fact_value`, which is the fact's `terms[0]`. It is deliberately not a
    ///   `fact_hash`: passing the value and its hash separately let a caller pair a value with
    ///   another value's fact, and for the `≥` predicate that mispairing was provable end-to-end
    ///   (the circuit did not relate the two). The state root is supplied by this chain, not the
    ///   caller.
    ///
    /// # Returns
    ///
    /// A tuple of (BridgePresentationProof, Vec<BridgePredicateProof>) where the
    /// presentation proof covers the full authorization and the predicate proofs
    /// cover individual fact predicates.
    pub fn prove_with_disclosure(
        &mut self,
        request: &AuthRequest,
        predicate_facts: &[(u32, FactTerms, &Predicate)],
    ) -> Result<(BridgePresentationProof, Vec<BridgePredicateProof>), AuthError> {
        // Generate the main STARK proof.
        let main_proof = self.prove_real(request)?;

        // Compute state root from the final state for fact commitment binding.
        let final_step = self.chain.last().ok_or(AuthError::EmptyState)?;
        let state_root_bytes = final_step.state.root_immutable();
        let state_root = bytes_to_babybear(&state_root_bytes);

        // Generate predicate proofs for each specified fact. The state root comes from THIS chain's
        // final step (above), so the caller cannot aim a predicate at a state it does not hold.
        let mut pred_proofs = Vec::with_capacity(predicate_facts.len());
        for &(value, terms, ref predicate) in predicate_facts {
            // A FRESH blinding factor PER PREDICATE PROOF — the same discipline as the ring-membership
            // `generate_blinding_factor` and the presentation tag above. Two disclosures of the same
            // fact therefore carry different `fact_commitment` PIs and cannot be correlated, while the
            // in-circuit weld still binds each to the value it covers.
            let blinding = fresh_predicate_blinding();
            let proof =
                prove_predicate_for_fact(value, terms.bind(state_root), blinding, predicate)
                    .ok_or_else(|| {
                        AuthError::InvalidRequest(format!(
                            "predicate proof generation failed for value {} with {:?}",
                            value, predicate
                        ))
                    })?;
            pred_proofs.push(proof);
        }

        Ok((main_proof, pred_proofs))
    }

    /// Build the circuit-level presentation witness from the authorization trace.
    /// Uses linear algebraic binding for the issuer membership (legacy path).
    #[allow(dead_code)] // Legacy linear-binding path, retained alongside the Merkle-membership presenter.
    fn build_circuit_witness(
        &self,
        trace: &AuthorizationTrace,
        request: &AuthRequest,
    ) -> Result<PresentationWitness, AuthError> {
        // Compute the canonical action binding commitment from (action, resource).
        // Resource = app_id OR service (whichever is present), matching the wire
        // verifier's expectation. This ensures service-scoped tokens produce the
        // same binding that the verifier will recompute.
        let action_str = request.action.as_deref().unwrap_or("");
        let resource_str = request
            .app_id
            .as_deref()
            .or(request.service.as_deref())
            .unwrap_or("");
        let request_pred_bb = dregg_circuit::compute_action_binding(action_str, resource_str);

        // Timestamp.
        let timestamp = request.now.unwrap_or(0);
        let timestamp_bb = BabyBear::from_u64(timestamp as u64);

        // Build fold witnesses from the chain deltas.
        let fold_chain = self.build_fold_witnesses();

        // Compute the Poseidon2 state root for the derivation witness.
        let derivation_state_root = self.final_state_poseidon2_root(&fold_chain);

        // Build the derivation witness from the trace.
        let derivation = self.build_derivation_witness(trace, derivation_state_root)?;

        // Build the issuer membership witness.
        let issuer_key_hash = bytes_to_babybear(&self.issuer_key);
        let issuer_membership = self.build_issuer_membership_poseidon2(issuer_key_hash)?;

        // Generate fresh presentation randomness for the presentation tag.
        let presentation_randomness = generate_presentation_randomness();

        // Assemble the presentation witness.
        // We need the federation_root to match the issuer_membership.expected_root
        // for the proof to verify.
        // NOTE: Legacy path uses blinding_factor=ZERO (no ring membership).
        // NOTE: Legacy path uses composition_commitment=ZERO (no sub-proof binding).
        let witness = PresentationWitness {
            federation_root: issuer_membership.expected_root,
            request_predicate: request_pred_bb,
            timestamp: timestamp_bb,
            fold_chain,
            derivation,
            issuer_membership,
            issuer_key_hash,
            revealed_facts_commitment: self.revealed_facts_commitment,
            blinding_factor: BabyBear::ZERO,
            presentation_randomness,
            composition_commitment: WideHash::ZERO,
            verifier_nonce: BabyBear::ZERO,
            verifier_block_height: BabyBear::ZERO,
        };

        Ok(witness)
    }

    /// Build the circuit-level presentation witness using Poseidon2 hashing
    /// for the issuer membership proof (collision-resistant, production path).
    ///
    /// This uses ring membership (blinded issuer proof) by default: a fresh
    /// random blinding factor is generated per presentation, making the proof
    /// unlinkable. The public inputs expose `blinded_leaf = hash_2_to_1(leaf_hash, blinding)`
    /// instead of the raw `leaf_hash`, so the verifier cannot determine which
    /// federation member issued the token.
    fn build_circuit_witness_poseidon2(
        &self,
        trace: &AuthorizationTrace,
        request: &AuthRequest,
    ) -> Result<PresentationWitness, AuthError> {
        // Compute the canonical action binding commitment from (action, resource).
        // Resource = app_id OR service (whichever is present), matching the wire
        // verifier's expectation. This ensures service-scoped tokens produce the
        // same binding that the verifier will recompute.
        let action_str = request.action.as_deref().unwrap_or("");
        let resource_str = request
            .app_id
            .as_deref()
            .or(request.service.as_deref())
            .unwrap_or("");
        let request_pred_bb = dregg_circuit::compute_action_binding(action_str, resource_str);

        // Timestamp: use the request's `now` field if provided, otherwise default to
        // the current system time. A non-zero timestamp is essential for proof freshness;
        // verifiers can reject proofs with stale timestamps.
        let timestamp = request.now.unwrap_or_else(|| {
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap_or_default()
                .as_secs() as i64
        });
        let timestamp_bb = BabyBear::from_u64(timestamp as u64);

        // Build fold witnesses from the chain deltas.
        let fold_chain = self.build_fold_witnesses();

        // Compute the Poseidon2 state root for the derivation witness.
        let derivation_state_root = self.final_state_poseidon2_root(&fold_chain);

        // Build the derivation witness from the trace.
        let derivation = self.build_derivation_witness(trace, derivation_state_root)?;

        // Build the issuer membership witness with Poseidon2 hashing.
        let issuer_key_hash = bytes_to_babybear(&self.issuer_key);
        let issuer_membership = self.build_issuer_membership_poseidon2(issuer_key_hash)?;

        // Generate a fresh random blinding factor for ring membership (unlinkability).
        // Each presentation gets a new blinding factor, so the public `blinded_leaf`
        // is different each time — even for the same issuer.
        let blinding_factor = generate_blinding_factor();

        // Generate fresh presentation randomness for the presentation tag.
        // This ensures the tag `Poseidon2(final_root, randomness, nonce)` is different each show.
        let presentation_randomness = generate_presentation_randomness();

        // Compute the presentation tag (same formula as the circuit uses).
        // The verifier_nonce is included to cryptographically bind the proof to a
        // specific verifier challenge, preventing replay attacks.
        let verifier_nonce = BabyBear::ZERO; // TODO: accept from verifier challenge
        let final_root = if let Some(last_fold) = fold_chain.last() {
            last_fold.new_root
        } else {
            derivation_state_root
        };
        let presentation_tag = dregg_circuit::binding::compute_presentation_tag(
            final_root,
            presentation_randomness,
            verifier_nonce,
        );

        // Compute the fold chain commitment: Poseidon2 over all fold step roots.
        // This summarizes the entire fold chain into a single field element.
        let fold_chain_commitment = if fold_chain.is_empty() {
            BabyBear::ZERO
        } else {
            let fold_roots: Vec<BabyBear> = fold_chain
                .iter()
                .flat_map(|f| [f.old_root, f.new_root])
                .collect();
            poseidon2::hash_many(&fold_roots)
        };

        // SECURITY: Composition commitment binds all sub-proofs together.
        // This is included as a public input in the issuer membership STARK.
        // If an attacker swaps ANY sub-proof (e.g., attaches a valid membership
        // STARK from one token to a forged fold chain from another), the
        // composition_commitment will not match, and STARK verification fails.
        // Use the narrow (single-element) tag for the composition hash since
        // the composition commitment is itself a single BabyBear element.
        let presentation_tag_narrow = poseidon2::hash_many(&presentation_tag);
        let composition_commitment = WideHash::from_poseidon2(
            "dregg-composition-v1",
            &[
                fold_chain_commitment,
                derivation_state_root,
                presentation_tag_narrow,
            ],
        );

        // Assemble the presentation witness.
        let witness = PresentationWitness {
            federation_root: issuer_membership.expected_root,
            request_predicate: request_pred_bb,
            timestamp: timestamp_bb,
            fold_chain,
            derivation,
            issuer_membership,
            issuer_key_hash,
            revealed_facts_commitment: self.revealed_facts_commitment,
            blinding_factor,
            presentation_randomness,
            composition_commitment,
            verifier_nonce,
            verifier_block_height: BabyBear::ZERO,
        };

        Ok(witness)
    }

    /// Build FoldWitness instances for the circuit from our chain deltas.
    ///
    /// This builds Poseidon2-based Merkle trees over the fact hashes at each step
    /// and produces membership proofs in the circuit's hash domain. The commit layer's
    /// BLAKE3-based roots/proofs are not directly usable in the circuit.
    pub fn build_fold_witnesses(&self) -> Vec<FoldWitness> {
        use dregg_circuit::poseidon2::hash_fact;

        let mut witnesses = Vec::new();

        for i in 1..self.chain.len() {
            let delta = match &self.chain[i].delta {
                Some(d) => d,
                None => continue,
            };

            // The "old" state is the previous step's facts.
            let old_facts = &self.chain[i - 1].facts;
            let new_facts = &self.chain[i].facts;

            // Compute fact hashes in the Poseidon2 domain for the old state.
            let old_leaf_hashes: Vec<BabyBear> = old_facts
                .iter()
                .map(|fact| {
                    let pred_bb = bytes_to_babybear(&fact.predicate.0);
                    let terms = [
                        bytes_to_babybear(&fact.terms[0].0),
                        bytes_to_babybear(&fact.terms[1].0),
                        bytes_to_babybear(&fact.terms[2].0),
                    ];
                    hash_fact(pred_bb, &terms)
                })
                .collect();

            // Build a Poseidon2 Merkle tree over the old state's fact hashes.
            let tree_depth = 4; // Match the circuit's tree depth.
            let (old_root, old_proofs) = build_shared_tree(&old_leaf_hashes, tree_depth);

            // Index old-leaf hash → first index for O(1) removed-fact lookup
            // (replaces the per-removed-fact O(old) `.position()` scan below).
            let old_leaf_index: std::collections::HashMap<BabyBear, usize> = {
                let mut m = std::collections::HashMap::with_capacity(old_leaf_hashes.len());
                for (idx, h) in old_leaf_hashes.iter().enumerate() {
                    m.entry(*h).or_insert(idx);
                }
                m
            };

            // Compute the new state's Poseidon2 root.
            let new_leaf_hashes: Vec<BabyBear> = new_facts
                .iter()
                .map(|fact| {
                    let pred_bb = bytes_to_babybear(&fact.predicate.0);
                    let terms = [
                        bytes_to_babybear(&fact.terms[0].0),
                        bytes_to_babybear(&fact.terms[1].0),
                        bytes_to_babybear(&fact.terms[2].0),
                    ];
                    hash_fact(pred_bb, &terms)
                })
                .collect();
            let (new_root, _) = build_shared_tree(&new_leaf_hashes, tree_depth);

            // For each removed fact, find its index in the old state and get its proof.
            let removed_facts: Vec<RemovedFact> = delta
                .removed
                .iter()
                .map(|(fact, _commit_proof)| {
                    let pred_bb = bytes_to_babybear(&fact.predicate.0);
                    let terms = [
                        bytes_to_babybear(&fact.terms[0].0),
                        bytes_to_babybear(&fact.terms[1].0),
                        bytes_to_babybear(&fact.terms[2].0),
                    ];
                    let fact_hash = hash_fact(pred_bb, &terms);

                    // Find this fact's index in the old state to get its Merkle proof.
                    let proof_idx = *old_leaf_index
                        .get(&fact_hash)
                        .expect("removed fact must exist in old state");

                    RemovedFact {
                        predicate: pred_bb,
                        terms,
                        membership_proof: Some(old_proofs[proof_idx].clone()),
                    }
                })
                .collect();

            // Compute the cryptographic commitment to added checks.
            // This binds the actual check content to the fold proof, preventing
            // a prover from claiming checks they didn't actually add.
            let added_checks_commitment = if delta.added_checks.is_empty() {
                WideHash::ZERO
            } else {
                let check_hashes: Vec<BabyBear> = delta
                    .added_checks
                    .iter()
                    .map(|check| {
                        let pred_bb = bytes_to_babybear(&check.predicate.0);
                        let terms = [
                            bytes_to_babybear(&check.terms[0].0),
                            bytes_to_babybear(&check.terms[1].0),
                            bytes_to_babybear(&check.terms[2].0),
                        ];
                        hash_fact(pred_bb, &terms)
                    })
                    .collect();
                WideHash::from_poseidon2("dregg-checks-v1", &check_hashes)
            };

            witnesses.push(FoldWitness {
                old_root,
                new_root,
                removed_facts,
                num_added_checks: delta.added_checks.len(),
                added_checks_commitment,
            });
        }

        witnesses
    }

    /// Compute the Poseidon2-domain state root for the derivation witness.
    ///
    /// If there are fold steps, this is the last fold's `new_root`. Otherwise,
    /// we compute it from the final (and only) state's facts.
    fn final_state_poseidon2_root(&self, fold_chain: &[FoldWitness]) -> BabyBear {
        use dregg_circuit::poseidon2::hash_fact;

        if let Some(last_fold) = fold_chain.last() {
            last_fold.new_root
        } else {
            // No folds — compute from the single state's facts.
            let final_step = match self.chain.last() {
                Some(step) => step,
                None => return BabyBear::ZERO,
            };
            let leaf_hashes: Vec<BabyBear> = final_step
                .facts
                .iter()
                .map(|fact| {
                    let pred_bb = bytes_to_babybear(&fact.predicate.0);
                    let terms = [
                        bytes_to_babybear(&fact.terms[0].0),
                        bytes_to_babybear(&fact.terms[1].0),
                        bytes_to_babybear(&fact.terms[2].0),
                    ];
                    hash_fact(pred_bb, &terms)
                })
                .collect();
            let (root, _) = build_shared_tree(&leaf_hashes, 4);
            root
        }
    }

    /// Build the DerivationWitness from the authorization trace.
    ///
    /// `state_root_bb` is the Poseidon2-domain root of the final state, matching
    /// the fold chain's last `new_root` (or the initial root if no folds).
    fn build_derivation_witness(
        &self,
        trace: &AuthorizationTrace,
        state_root_bb: BabyBear,
    ) -> Result<DerivationWitness, AuthError> {
        // The derivation witness proves that the final state authorizes the request.
        // We need to pick the rule that fired (from the trace conclusion).

        let rule_id = match &trace.conclusion {
            Conclusion::Allow { policy_rule_id } => *policy_rule_id,
            Conclusion::Deny => return Err(AuthError::Denied),
        };

        // Reconstruct the evaluator's fact set so we can look up body facts
        // by index. The evaluator builds: base facts + request facts + derived facts.
        let reconstructed_facts = self.reconstruct_evaluator_facts(trace);

        // Build body fact hashes from the derivation steps.
        // Use the last step that derived "allow".
        let allow_step = trace
            .steps
            .iter()
            .find(|s| s.derived_fact.predicate == symbol_from_str("allow"));

        let (body_fact_hashes, substitution, derived_pred, derived_terms) =
            if let Some(step) = allow_step {
                let body_hashes: Vec<BabyBear> = step
                    .body_fact_indices
                    .iter()
                    .map(|&idx| {
                        // Hash the actual body fact using Poseidon2 for circuit compatibility.
                        if let Some(fact) = reconstructed_facts.get(idx) {
                            let pred_bb = bytes_to_babybear(&fact.predicate);
                            let mut term_bbs = [BabyBear::ZERO; 3];
                            for (i, term) in fact.terms.iter().take(3).enumerate() {
                                term_bbs[i] = match term {
                                    TraceTerm::Const(sym) => bytes_to_babybear(sym),
                                    TraceTerm::Int(v) => BabyBear::from_u64(*v as u64),
                                    TraceTerm::Var(_) => BabyBear::ZERO,
                                };
                            }
                            poseidon2::hash_fact(pred_bb, &term_bbs)
                        } else {
                            // Index out of range — use a non-zero sentinel.
                            BabyBear::new(1)
                        }
                    })
                    .collect();

                let subst: Vec<BabyBear> = step
                    .substitution
                    .bindings
                    .iter()
                    .map(|(_, term)| match term {
                        TraceTerm::Const(sym) => bytes_to_babybear(sym),
                        TraceTerm::Int(i) => BabyBear::from_u64(*i as u64),
                        TraceTerm::Var(_) => BabyBear::ZERO,
                    })
                    .collect();

                let pred = bytes_to_babybear(&step.derived_fact.predicate);
                let mut terms = [BabyBear::ZERO; 4];
                for (i, term) in step.derived_fact.terms.iter().take(4).enumerate() {
                    terms[i] = match term {
                        TraceTerm::Const(sym) => bytes_to_babybear(sym),
                        TraceTerm::Int(v) => BabyBear::from_u64(*v as u64),
                        TraceTerm::Var(_) => BabyBear::ZERO,
                    };
                }

                (body_hashes, subst, pred, terms)
            } else {
                // No derivation step found — this shouldn't happen for Allow conclusions.
                // Fall back to a minimal witness.
                let allow_sym = symbol_from_str("allow");
                (
                    vec![BabyBear::new(rule_id)],
                    vec![],
                    bytes_to_babybear(&allow_sym),
                    [BabyBear::ZERO; 4],
                )
            };

        // Ensure we have at least one body hash.
        let body_fact_hashes = if body_fact_hashes.is_empty() {
            vec![BabyBear::new(1)]
        } else {
            body_fact_hashes
        };

        // Build the circuit rule representation.
        // The "allow" rule's head has no terms (it's just "allow()"),
        // so all head_terms are literal zeros.
        let circuit_rule = CircuitRule {
            id: rule_id,
            num_body_atoms: body_fact_hashes.len(),
            num_variables: substitution.len(),
            head_predicate: derived_pred,
            head_terms: [
                (false, derived_terms[0]),
                (false, derived_terms[1]),
                (false, derived_terms[2]),
                (false, BabyBear::ZERO),
            ],
            body_atoms: vec![],
            equal_checks: vec![],
            memberof_checks: vec![],
            gte_check: None,
            lt_check: None,
        };

        Ok(DerivationWitness {
            rule: circuit_rule,
            state_root: state_root_bb,
            body_fact_hashes,
            substitution,
            derived_predicate: derived_pred,
            derived_terms,
            not_after_height: BabyBear::ZERO,
            org_id_hash: BabyBear::ZERO,
            budget_remaining: BabyBear::ZERO,
        })
    }

    /// Reconstruct the evaluator's fact set from the authorization trace.
    ///
    /// The evaluator builds facts as: base committed facts (from auth_state) +
    /// request facts (injected by the evaluator) + derived facts from prior steps.
    /// The `body_fact_indices` in each DerivationStep index into this growing list.
    fn reconstruct_evaluator_facts(&self, trace: &AuthorizationTrace) -> Vec<dregg_trace::Fact> {
        use dregg_trace::{Fact as TraceFact, Term, symbol_from_bytes, symbol_from_str};

        let mut facts: Vec<TraceFact> = Vec::new();

        // 1. Base facts from the committed auth_state.
        // Use the same conversion as committed_facts_to_trace: symbol_from_str for
        // predicates (matches policy rule predicates), symbol_from_bytes for terms
        // (enables Contains check and matches what the evaluator used).
        for fact in self.auth_state.all_facts() {
            let pred_symbol = if let Some(name) = self.symbols.resolve(fact.predicate) {
                symbol_from_str(name)
            } else {
                fact.predicate.0
            };
            let mut terms = Vec::new();
            for term_fe in &fact.terms {
                if term_fe.is_zero() {
                    break;
                }
                if let Some(name) = self.symbols.resolve(*term_fe) {
                    terms.push(Term::Const(symbol_from_bytes(name.as_bytes())));
                } else {
                    terms.push(Term::Const(term_fe.0));
                }
            }
            facts.push(TraceFact::new(pred_symbol, terms));
        }

        // 2. Request facts (same injection as the evaluator performs).
        let req = &trace.request;
        if let Some(app_id) = &req.app_id {
            facts.push(TraceFact::new(
                symbol_from_str("request_app"),
                vec![Term::Const(*app_id)],
            ));
        }
        if let Some(service) = &req.service {
            facts.push(TraceFact::new(
                symbol_from_str("request_service"),
                vec![Term::Const(*service)],
            ));
        }
        if let Some(action) = &req.action {
            facts.push(TraceFact::new(
                symbol_from_str("request_action"),
                vec![Term::Const(*action)],
            ));
        }
        for feature in &req.features {
            facts.push(TraceFact::new(
                symbol_from_str("request_feature"),
                vec![Term::Const(*feature)],
            ));
        }
        if let Some(user_id) = &req.user_id {
            facts.push(TraceFact::new(
                symbol_from_str("request_user"),
                vec![Term::Const(*user_id)],
            ));
        }
        facts.push(TraceFact::new(
            symbol_from_str("request_time"),
            vec![Term::Int(req.now)],
        ));

        // 3. Derived facts from prior steps (in order).
        for step in &trace.steps {
            facts.push(step.derived_fact.clone());
        }

        facts
    }

    /// Build the issuer membership Merkle witness.
    ///
    /// If a federation tree was attached via `with_federation_tree()`, this uses
    /// a real Merkle proof from the tree. In test/test-utils builds, it falls back
    /// to a synthetic deterministic path.
    /// Build the issuer membership Merkle witness using Poseidon2 hashing.
    ///
    /// This produces a witness compatible with the DSL `merkle_poseidon2_circuit()` where
    /// parent = hash_4_to_1(children arranged by position). The resulting proof
    /// is collision-resistant (unlike the linear binding which has weaker security).
    ///
    /// If a federation tree is available, it uses real tree proofs with Poseidon2
    /// hashing. In test/test-utils builds, falls back to a synthetic path.
    /// In production builds without a federation tree, returns an error.
    pub fn build_issuer_membership_poseidon2(
        &self,
        issuer_key_hash: BabyBear,
    ) -> Result<MerkleWitness, AuthError> {
        // Delegation path: use pre-generated membership proof if available.
        // Uses Poseidon2 hashing to convert the byte-level proof to a field-level witness.
        if let Some(proof) = &self.pre_generated_membership_proof {
            return self.build_issuer_membership_poseidon2_from_proof(proof, issuer_key_hash);
        }

        // Production path: use real federation tree if available.
        if let Some(tree) = &self.federation_tree {
            return self.build_issuer_membership_poseidon2_from_tree(tree, issuer_key_hash);
        }

        // TESTING FALLBACK: synthetic Poseidon2 Merkle path.
        #[cfg(any(test, feature = "test-utils"))]
        {
            self.build_issuer_membership_poseidon2_synthetic(issuer_key_hash)
        }

        #[cfg(not(any(test, feature = "test-utils")))]
        {
            Err(AuthError::IssuerNotInFederation)
        }
    }

    /// Produce the issuer-membership proof in the NEW IR-v2 descriptor wire format
    /// from THIS builder's real federation authentication path.
    ///
    /// This is the flipped issuer-membership PRODUCER: it re-expresses the same
    /// [`Self::build_issuer_membership_poseidon2`] `MerkleWitness` (leaf + 4-ary path
    /// to the federation root) as a `postcard(Ir2BatchProof)` blob that a
    /// descriptor-dispatch consumer verifies with `verify_vm_descriptor2` — no
    /// air-name, no `StarkProof`. The returned [`Ir2IssuerWire`] is the exact
    /// `(predicate, blob, vk)` triple the routed
    /// [`crate::verifier::StarkProofVerifier::verify_with_predicate`] (via
    /// [`crate::verifier::DescriptorDispatchVerifier`]) consumes.
    ///
    /// The federation path depth must be a power of two ≥ 2 (the 4-ary witness
    /// trace-height requirement); the synthetic test path (depth 8) and any
    /// power-of-two federation tree satisfy it.
    pub fn prove_issuer_membership_ir2_wire(&self) -> Result<Ir2IssuerWire, AuthError> {
        let issuer_key_hash = bytes_to_babybear(&self.issuer_key);
        let witness = self.build_issuer_membership_poseidon2(issuer_key_hash)?;
        let siblings: Vec<[BabyBear; 3]> = witness.levels.iter().map(|l| l.siblings).collect();
        let positions: Vec<u8> = witness.levels.iter().map(|l| l.position).collect();
        prove_issuer_membership_ir2(witness.leaf_hash, &siblings, &positions)
    }

    /// Build Poseidon2 issuer membership from a real federation Merkle tree.
    fn build_issuer_membership_poseidon2_from_tree(
        &self,
        tree: &MerkleTree,
        issuer_key_hash: BabyBear,
    ) -> Result<MerkleWitness, AuthError> {
        let proof = tree
            .membership_proof(&self.issuer_key)
            .ok_or(AuthError::IssuerNotInFederation)?;

        let mut levels = Vec::with_capacity(proof.path_indices.len());
        let mut current = issuer_key_hash;

        for i in 0..proof.path_indices.len() {
            let position = proof.path_indices[i];
            let siblings = [
                bytes_to_babybear(&proof.siblings[i][0]),
                bytes_to_babybear(&proof.siblings[i][1]),
                bytes_to_babybear(&proof.siblings[i][2]),
            ];

            let parent = compute_parent_poseidon2(current, position, &siblings);

            levels.push(MerkleLevelWitness { position, siblings });
            current = parent;
        }

        if current != self.federation_root_bb {
            return Err(AuthError::IssuerNotInFederation);
        }

        Ok(MerkleWitness {
            leaf_hash: issuer_key_hash,
            levels,
            expected_root: current,
        })
    }

    /// Build Poseidon2 issuer membership from a pre-generated MerkleProof.
    ///
    /// Poseidon2 variant of the delegation path. The delegator pre-generated
    /// the proof using the BLAKE3-derived proof key (the actual federation tree
    /// leaf — raw root HMAC keys are never used as leaves). We convert byte-level
    /// siblings to BabyBear field elements and use Poseidon2 hashing to compute
    /// parents along the pre-generated path.
    fn build_issuer_membership_poseidon2_from_proof(
        &self,
        proof: &MerkleProof,
        _issuer_key_hash: BabyBear,
    ) -> Result<MerkleWitness, AuthError> {
        // Use the pre-generated proof's leaf_hash (BabyBear encoding of the
        // BLAKE3-derived proof key — the actual federation tree leaf).
        let real_leaf_hash = bytes_to_babybear(&proof.leaf_hash);

        let mut levels = Vec::with_capacity(proof.path_indices.len());
        let mut current = real_leaf_hash;

        for i in 0..proof.path_indices.len() {
            let position = proof.path_indices[i];
            let siblings = [
                bytes_to_babybear(&proof.siblings[i][0]),
                bytes_to_babybear(&proof.siblings[i][1]),
                bytes_to_babybear(&proof.siblings[i][2]),
            ];

            let parent = compute_parent_poseidon2(current, position, &siblings);

            levels.push(MerkleLevelWitness { position, siblings });
            current = parent;
        }

        if current != self.federation_root_bb {
            return Err(AuthError::IssuerNotInFederation);
        }

        Ok(MerkleWitness {
            leaf_hash: real_leaf_hash,
            levels,
            expected_root: current,
        })
    }

    /// Synthetic/deterministic Poseidon2 issuer membership proof (TESTING ONLY).
    ///
    /// Constructs a Merkle path using real Poseidon2 hashing at each level,
    /// with BLAKE3-derived sibling values. Compatible with the DSL `merkle_poseidon2_circuit()`.
    #[cfg(any(test, feature = "test-utils"))]
    fn build_issuer_membership_poseidon2_synthetic(
        &self,
        issuer_key_hash: BabyBear,
    ) -> Result<MerkleWitness, AuthError> {
        let depth = 8;
        let mut current = issuer_key_hash;
        let mut levels = Vec::with_capacity(depth);

        for i in 0..depth {
            let position = (i % 4) as u8;
            let siblings = [
                BabyBear::new(hash_index(i, 0, &self.issuer_key)),
                BabyBear::new(hash_index(i, 1, &self.issuer_key)),
                BabyBear::new(hash_index(i, 2, &self.issuer_key)),
            ];

            let parent = compute_parent_poseidon2(current, position, &siblings);

            levels.push(MerkleLevelWitness { position, siblings });
            current = parent;
        }

        // Verify that the computed root matches the expected federation root.
        if current != self.federation_root_bb {
            return Err(AuthError::IssuerNotInFederation);
        }

        Ok(MerkleWitness {
            leaf_hash: issuer_key_hash,
            levels,
            expected_root: current,
        })
    }
}

/// Encode a 32-byte value as 8 BabyBear field elements (4 bytes each, mod p).
/// This preserves full 256-bit distinguishability across the limb vector.
pub fn bytes_to_babybear_vec(bytes: &[u8; 32]) -> [BabyBear; 8] {
    BabyBear::encode_hash(bytes)
}

/// Compress a 32-byte value into a single BabyBear element by encoding as
/// 8 limbs and hashing them together with Poseidon2. This preserves collision
/// resistance up to the ~31-bit field size while using all 256 input bits.
pub fn bytes_to_babybear(bytes: &[u8; 32]) -> BabyBear {
    let limbs = bytes_to_babybear_vec(bytes);
    poseidon2::hash_many(&limbs)
}

/// Encode a BabyBear field element as a 32-byte array (canonical encoding).
///
/// The u32 value is stored in bytes [0..4] as little-endian, with bytes [4..32]
/// zeroed. This is the canonical wire encoding used by the cipherclerk, engine, and
/// verifier. Use [`bb_from_bytes`] to decode.
pub fn bb_to_bytes(bb: BabyBear) -> [u8; 32] {
    let mut bytes = [0u8; 32];
    bytes[..4].copy_from_slice(&bb.as_u32().to_le_bytes());
    bytes
}

/// Decode a BabyBear field element from its canonical 32-byte encoding.
///
/// Reads bytes [0..4] as a little-endian u32 and constructs a canonical BabyBear
/// element (reduced mod p). This is the inverse of [`bb_to_bytes`] and is used by
/// all verification paths to recover a federation root from its wire representation.
pub fn bb_from_bytes(bytes: &[u8; 32]) -> BabyBear {
    let val = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
    BabyBear::new_canonical(val)
}

/// Generate a fresh random blinding factor for ring membership proofs.
///
/// This produces a non-zero BabyBear field element from OS randomness.
/// A fresh blinding factor is generated per presentation to ensure unlinkability:
/// `blinded_leaf = hash_2_to_1(leaf_hash, blinding_factor)` is different each time.
fn generate_blinding_factor() -> BabyBear {
    let mut buf = [0u8; 4];
    getrandom::fill(&mut buf).expect("OS randomness unavailable");
    let raw = u32::from_le_bytes(buf) % dregg_circuit::field::BABYBEAR_P;
    // Ensure non-zero (zero blinding would reveal the raw leaf_hash via hash_2_to_1(x, 0))
    let val = if raw == 0 { 1 } else { raw };
    BabyBear::new(val)
}

/// **Draw a fresh per-presentation predicate [`Blinding`] from OS randomness.**
///
/// The blinding factor for the predicate family's fact commitment: leg 2 of the in-circuit weld is
/// an arity-4 Poseidon2 lookup over `[fact_hash, state_root, blinding, 0]`, so a fresh draw per
/// showing makes two presentations of the SAME fact carry different public `fact_commitment`s. This
/// is the predicate-side twin of [`generate_blinding_factor`] (ring membership) and
/// [`generate_presentation_randomness`] (the presentation tag) — the same unlinkability discipline,
/// applied to the third public artifact a presentation emits.
///
/// Non-zero like its siblings, though for a different reason: zero blinding is not a *leak* here
/// (the weld's arity-4 image is not the identity), it is merely the DEGENERATE, correlatable case
/// ([`Blinding::NONE`]). Every presentation path should draw, not default.
///
/// Exposed so callers that drive [`prove_predicate_for_fact`] directly (the SDK / credentials
/// selective-disclosure paths) get the unlinkable blinding by DEFAULT rather than reaching for
/// [`Blinding::NONE`].
pub fn fresh_predicate_blinding() -> Blinding {
    Blinding(generate_blinding_factor())
}

/// Generate fresh randomness for the presentation tag.
///
/// This produces a non-zero BabyBear field element from OS randomness.
/// A fresh value is generated per presentation to ensure unlinkability:
/// `presentation_tag = Poseidon2(final_root, presentation_randomness)` is different each time.
/// The final_root remains private; only the blinded tag is public.
fn generate_presentation_randomness() -> BabyBear {
    let mut buf = [0u8; 4];
    getrandom::fill(&mut buf).expect("OS randomness unavailable");
    let raw = u32::from_le_bytes(buf) % dregg_circuit::field::BABYBEAR_P;
    // Ensure non-zero (zero randomness would expose final_root directly via hash_2_to_1(x, 0))
    let val = if raw == 0 { 1 } else { raw };
    BabyBear::new(val)
}

/// Compute the revealed facts commitment for selective disclosure.
///
/// Given a set of `TraceFact`s that the prover chooses to reveal, this function
/// computes `poseidon2(hash(fact_1) || hash(fact_2) || ... || hash(fact_n))`.
/// Each fact is hashed by converting its predicate and terms into BabyBear field
/// elements and applying `poseidon2::hash_fact`.
///
/// The verifier recomputes this from the plaintext revealed facts and checks it
/// matches the commitment in the proof's public inputs. This cryptographically
/// binds the revealed facts to the STARK proof.
///
/// Returns `BabyBear::ZERO` if no facts are provided (fully private mode).
pub fn compute_revealed_facts_commitment(facts: &[dregg_trace::Fact]) -> WideHash {
    if facts.is_empty() {
        return WideHash::ZERO;
    }

    let fact_hashes: Vec<BabyBear> = facts
        .iter()
        .map(|fact| {
            let pred_bb = bytes_to_babybear(&fact.predicate);
            let mut term_bbs = [BabyBear::ZERO; 3];
            for (i, term) in fact.terms.iter().take(3).enumerate() {
                term_bbs[i] = match term {
                    dregg_trace::Term::Const(sym) => bytes_to_babybear(sym),
                    dregg_trace::Term::Int(v) => BabyBear::from_u64(*v as u64),
                    dregg_trace::Term::Var(_) => BabyBear::ZERO,
                };
            }
            poseidon2::hash_fact(pred_bb, &term_bbs)
        })
        .collect();

    WideHash::from_poseidon2("dregg-revealed-facts-v1", &fact_hashes)
}

/// Verify that a set of revealed facts matches the commitment in a proof.
///
/// This is the verifier-side counterpart to [`compute_revealed_facts_commitment`].
/// It recomputes the commitment from the plaintext facts and checks it matches
/// the value committed in the proof's public inputs.
///
/// Returns `true` if the commitment matches (the prover did not lie about revealed facts).
pub fn verify_revealed_facts_commitment(
    revealed_facts: &[dregg_trace::Fact],
    proof_commitment: WideHash,
) -> bool {
    let recomputed = compute_revealed_facts_commitment(revealed_facts);
    recomputed == proof_commitment
}

/// Derive a deterministic sibling hash for Merkle path construction.
/// This is part of the synthetic membership proof infrastructure and
/// MUST NOT be used in production.
pub fn hash_index(level: usize, sibling_idx: usize, key: &[u8; 32]) -> u32 {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&level.to_le_bytes());
    hasher.update(&sibling_idx.to_le_bytes());
    hasher.update(key);
    let hash = hasher.finalize();
    let bytes = hash.as_bytes();
    u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]])
        % (dregg_circuit::field::BABYBEAR_P)
}

/// Default maximum proof age in seconds (5 minutes).
///
/// Proofs older than this are rejected by `verify_presentation` and
/// `verify_presentation_full`. Callers who need a different window should use
/// `verify_presentation_full` with an explicit `max_proof_age`.
pub const DEFAULT_MAX_PROOF_AGE_SECS: i64 = 300;

/// Verify BOTH committed presentation descriptors — the flip off the legacy hand-StarkProof.
///
/// Each wire is checked via `descriptor_by_name(predicate)` → decode `postcard(Ir2BatchProof)` →
/// `verify_vm_descriptor2` (in [`dregg_circuit::presentation::verify_descriptor_wire`]). Returns
/// `(bound_pis, blinded_pis)` on success:
/// * `bound_pis` — the bound-presentation summary `[federation_root, action(8), timestamp, tag,
///   revealed(8), verifier_nonce]`.
/// * `blinded_pis` — the blinded ring-membership `[blinded_leaf, root]`.
///
/// Fail-closed: an unknown predicate, malformed vk, bad blob, or a failed/paniced verify on
/// EITHER descriptor yields `None` — never a silent accept.
fn verify_presentation_descriptor_wires(
    real: &RealPresentationProof,
) -> Option<(Vec<BabyBear>, Vec<BabyBear>)> {
    let bound = verify_descriptor_wire(&real.bound_presentation)?;
    let blinded = verify_descriptor_wire(&real.blinded_membership)?;
    Some((bound, blinded))
}

/// Verify one committed descriptor wire with a TYPED outcome (for [`verify_proof_complete`]):
/// an unknown predicate is [`VerifyError::UnknownAir`] (the fail-closed contract preserved from
/// the retired air-name dispatch); a malformed/failed proof is [`VerifyError::StarkInvalid`].
fn verify_wire_typed(wire: &DescriptorProofWire) -> Result<Vec<BabyBear>, VerifyError> {
    if dregg_circuit::descriptor_by_name::descriptor_by_name(&wire.predicate).is_none() {
        return Err(VerifyError::UnknownAir(wire.predicate.clone()));
    }
    verify_descriptor_wire(wire).ok_or_else(|| {
        VerifyError::StarkInvalid(format!(
            "descriptor '{}' verification failed",
            wire.predicate
        ))
    })
}

/// Verify a presentation proof cryptographically with full authorization checks.
///
/// This is the primary verification entry point. It checks:
/// 1. **Issuer membership**: The STARK proof for federation membership is valid.
/// 2. **Federation binding**: The proof's federation root matches `federation_root`.
/// 3. **Timestamp freshness**: The proof's timestamp is within `max_proof_age` seconds of `now`.
/// 4. **Request predicate**: The proof's committed `request_predicate` matches `expected_action`.
///
/// # Arguments
///
/// * `proof` - The presentation proof to verify.
/// * `federation_root` - The federation root of trust from an **external, trusted source**.
///   **SECURITY WARNING**: This MUST NOT come from the proof itself (e.g., `proof.federation_root`).
///   Using the proof's own federation root is circular and provides no security — an attacker
///   can forge a proof for any federation root they choose.
/// * `expected_action` - The action string the verifier expects the proof to authorize.
///   If `None`, the request predicate check is skipped (only safe when the action is
///   already authenticated by other means, e.g., TLS channel binding).
/// * `now` - Current Unix timestamp in seconds for freshness checking.
/// * `max_proof_age` - Maximum age of the proof in seconds. Use `DEFAULT_MAX_PROOF_AGE_SECS`
///   (300s / 5min) for typical interactive authorization.
///
/// # Returns
///
/// `true` if all checks pass, `false` otherwise.
pub fn verify_presentation_full(
    proof: &BridgePresentationProof,
    federation_root: &[u8; 32],
    expected_action: Option<&str>,
    now: i64,
    max_proof_age: i64,
) -> bool {
    // A real STARK proof is required for cryptographic verification.
    let real = match proof.real_stark_proof.as_ref() {
        Some(r) => r,
        None => return false,
    };

    // 0. Verify BOTH committed descriptors (the flip off the legacy hand-StarkProof).
    let (bound_pis, blinded_pis) = match verify_presentation_descriptor_wires(real) {
        Some(v) => v,
        None => return false,
    };

    // 1. Federation-root binding (EXTERNAL trust anchor): the blinded ring-membership root AND the
    //    bound-presentation summary federation_root must both equal the expected root.
    use dregg_circuit::blinded_membership_witness::PI_ROOT_4ARY;
    use dregg_circuit::bound_presentation_witness::{
        FEDERATION_ROOT as BOUND_FED_ROOT, REQUEST_PREDICATE_BASE,
    };
    let expected_root = bb_from_bytes(federation_root);
    if blinded_pis.get(PI_ROOT_4ARY).copied() != Some(expected_root)
        || bound_pis.get(BOUND_FED_ROOT).copied() != Some(expected_root)
    {
        return false;
    }

    // 2. Timestamp freshness: reject stale proofs.
    let proof_timestamp = proof.circuit_proof.public_inputs.timestamp;
    let proof_ts_val = proof_timestamp.0 as i64;
    if proof_ts_val == 0 {
        // A zero timestamp means no timestamp was set — reject as stale.
        return false;
    }
    let age = now.saturating_sub(proof_ts_val);
    if age > max_proof_age || age < -max_proof_age {
        // Proof is too old OR has a future timestamp beyond tolerance.
        return false;
    }

    // 3. Request predicate authorization: verify the proof actually authorizes
    //    the action being requested, not just any action.
    //    The action binding is a 4-element commitment with 124-bit security.
    if let Some(action) = expected_action {
        let expected_binding = dregg_circuit::compute_action_binding(action, "");
        if proof.circuit_proof.public_inputs.request_predicate != expected_binding {
            return false;
        }
        // Bind the bound-presentation descriptor's committed action to the requested action.
        for i in 0..dregg_circuit::ACTION_BINDING_WIDTH {
            if bound_pis.get(REQUEST_PREDICATE_BASE + i).copied() != Some(expected_binding[i]) {
                return false;
            }
        }
    }

    // 4. Verify composition commitment (sub-proof binding).
    //    If the STARK proof contains a composition_commitment (at
    //    pi[2 + ACTION_BINDING_WIDTH ..]), verify it matches the locally recomputed value
    //    from the fold chain and derivation sub-proofs. This prevents an attacker
    //    from attaching a valid membership STARK from one token to a forged fold
    //    chain from another.
    if !proof.composition_commitment.is_zero() {
        // Recompute the composition commitment from the sub-proof data.
        let fold_chain_commitment = if real.fold_step_roots.is_empty() {
            BabyBear::ZERO
        } else {
            let fold_roots: Vec<BabyBear> = real
                .fold_step_roots
                .iter()
                .flat_map(|r| [r[0], r[1]])
                .collect();
            poseidon2::hash_many(&fold_roots)
        };
        let derivation_state_root = real.derivation_state_root;
        let presentation_tag = proof.circuit_proof.public_inputs.presentation_tag;
        // The circuit PI already stores the narrow (single-element) presentation tag,
        // which is compute_presentation_tag_narrow(). Use it directly — no re-hashing.
        let recomputed = WideHash::from_poseidon2(
            "dregg-composition-v1",
            &[
                fold_chain_commitment,
                derivation_state_root,
                presentation_tag,
            ],
        );

        if recomputed != proof.composition_commitment {
            return false;
        }
        // (The composition value formerly rode the hand-STARK public inputs; with the descriptor
        //  flip the sub-proof binding is the recomputed-vs-stored check above.)
    }

    // Both committed descriptors verified in step 0, and root/action/composition are bound.
    true
}

/// Verify that a proof's verifier nonce matches the expected challenge.
///
/// In a challenge-response protocol, the verifier issues a random nonce BEFORE
/// the prover generates the proof. This function checks that the proof was generated
/// for the specific challenge the verifier issued, preventing replay attacks.
///
/// Returns `true` if:
/// - The proof's `verifier_nonce` matches `expected_nonce`, OR
/// - `expected_nonce` is `BabyBear::ZERO` (nonce check disabled, non-interactive mode)
///
/// Returns `false` if the nonces do not match (potential replay).
///
/// # Security
///
/// Verifiers operating in challenge-response mode SHOULD:
/// 1. Generate a fresh random nonce per session (at least 31 bits of entropy).
/// 2. Send the nonce to the prover.
/// 3. Call this function with the same nonce after receiving the proof.
/// 4. Reject proofs where this returns `false`.
pub fn verify_presentation_nonce(
    proof: &BridgePresentationProof,
    expected_nonce: BabyBear,
) -> bool {
    // Non-interactive mode: skip nonce check when expected_nonce is zero.
    if expected_nonce == BabyBear::ZERO {
        return true;
    }

    // The nonce is stored in the circuit proof's public inputs.
    proof.circuit_proof.public_inputs.verifier_nonce == expected_nonce
}

// =============================================================================
// Canonical production verifier — ALL production paths MUST use this
// =============================================================================

/// Error type for the canonical proof verifier.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerifyError {
    /// The federation root was all zeros (not configured).
    NoFederationRoot,
    /// Proof deserialization failed.
    DeserializeFailed(String),
    /// STARK verification failed.
    StarkInvalid(String),
    /// Federation root in proof does not match expected root.
    RootMismatch,
    /// Action/resource binding in proof does not match expected values.
    ActionMismatch,
    /// Proof timestamp is too old or missing.
    Expired,
    /// Composition commitment is zero (missing sub-proof binding).
    MissingComposition,
    /// Composition commitment does not match recomputed value.
    CompositionMismatch,
    /// No real STARK proof present (structural/mock proof).
    NoStarkProof,
    /// Proof has fewer public inputs than required.
    MalformedPublicInputs,
    /// The proof carries an AIR name that does not resolve to any registered
    /// circuit descriptor. Verification REFUSES rather than guessing a default
    /// circuit: an unknown AIR means the verifier has no pinned constraint
    /// semantics for the proof.
    UnknownAir(String),
}

impl std::fmt::Display for VerifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NoFederationRoot => write!(f, "federation root is zero (not configured)"),
            Self::DeserializeFailed(e) => write!(f, "deserialization failed: {e}"),
            Self::StarkInvalid(e) => write!(f, "STARK verification failed: {e}"),
            Self::RootMismatch => write!(f, "federation root mismatch"),
            Self::ActionMismatch => write!(f, "action/resource binding mismatch"),
            Self::Expired => write!(f, "proof expired or missing timestamp"),
            Self::MissingComposition => write!(f, "composition commitment is zero"),
            Self::CompositionMismatch => write!(f, "composition commitment mismatch"),
            Self::NoStarkProof => write!(f, "no real STARK proof present"),
            Self::MalformedPublicInputs => write!(f, "malformed public inputs"),
            Self::UnknownAir(name) => write!(
                f,
                "unknown AIR '{name}': no registered circuit descriptor — refusing to verify"
            ),
        }
    }
}

impl std::error::Error for VerifyError {}

/// Result of successful verification from [`verify_proof_complete`].
#[derive(Clone, Debug)]
pub struct VerifiedPresentation {
    /// The proof tier (informational only — not used for acceptance decisions).
    /// A proof that passes `verify_proof_complete` is always accepted regardless of tier.
    /// The tier is retained for logging, metrics, and diagnostics.
    pub tier: dregg_circuit::ProofTier,
    /// The action the proof was verified against.
    pub action: String,
    /// The resource the proof was verified against.
    pub resource: String,
    /// The federation root the proof was verified against.
    pub federation_root: [u8; 32],
}

/// Configuration for the verification policy.
///
/// This replaces tier-based gating with explicit policy configuration.
/// Devnet accepts all AIRs. Production might restrict to Poseidon2-backed AIRs only.
///
/// # Example
///
/// ```
/// use dregg_bridge::present::VerifierConfig;
///
/// // Production: only accept Poseidon2-backed AIRs.
/// let production = VerifierConfig::production();
///
/// // Devnet: accept any cryptographically valid AIR.
/// let devnet = VerifierConfig::devnet();
/// ```
#[derive(Clone, Debug)]
pub struct VerifierConfig {
    /// Which AIR names are acceptable. Empty means "accept all known AIRs".
    pub accepted_air_names: Vec<String>,
    /// Maximum proof age in seconds. 0 disables freshness check.
    pub max_proof_age_secs: i64,
    /// Whether composition commitment is required (binds sub-proofs together).
    /// Set to `false` for single-step proofs that have no fold chain.
    pub require_composition: bool,
}

impl Default for VerifierConfig {
    fn default() -> Self {
        Self::production()
    }
}

impl VerifierConfig {
    /// Production config: accepts only Poseidon2-backed AIRs, requires composition,
    /// and enforces a 5-minute freshness window.
    pub fn production() -> Self {
        Self {
            accepted_air_names: vec![
                dregg_dsl_runtime::descriptors::BLINDED_MERKLE_AIR_NAME.to_string(),
                dregg_dsl_runtime::descriptors::MERKLE_POSEIDON2_AIR_NAME.to_string(),
            ],
            max_proof_age_secs: 300,
            require_composition: true,
        }
    }

    /// Devnet config: accepts any cryptographically valid AIR (including the legacy
    /// MerkleStarkAir), with a generous freshness window and relaxed composition.
    pub fn devnet() -> Self {
        Self {
            accepted_air_names: Vec::new(), // empty = accept all known AIRs
            max_proof_age_secs: 3600,
            require_composition: false,
        }
    }

    /// Returns true if the given AIR name is accepted by this config.
    /// An empty `accepted_air_names` list means all known AIRs are accepted.
    pub fn accepts_air(&self, air_name: &str) -> bool {
        self.accepted_air_names.is_empty() || self.accepted_air_names.iter().any(|a| a == air_name)
    }
}

/// The ONLY verification function that should be called in production.
///
/// Checks ALL of:
/// 1. Reject zero federation root
/// 2. Real STARK proof presence
/// 3. STARK validity (issuer membership, cryptographic verification)
/// 4. Federation root binding (proof's root == expected root)
/// 5. Action binding (proof's request_predicate == compute_action_binding(action, resource))
/// 6. Timestamp freshness (proof not older than max_age_secs)
/// 7. Composition commitment (non-zero AND correctly recomputed from sub-proofs)
///
/// Tier is NOT checked for acceptance. If a proof passes cryptographic STARK
/// verification for a known AIR, it is valid. The tier is retained in the
/// returned `VerifiedPresentation` as informational metadata for logging/metrics.
/// Structural stubs cannot produce valid STARK proofs, so they are naturally
/// rejected by step 3 without needing a separate tier gate.
///
/// For deployment-specific policy (restricting which AIRs are accepted), use
/// [`VerifierConfig`] to filter at the caller level.
///
/// # Arguments
///
/// * `wire_proof` - The deserialized wire presentation proof.
/// * `expected_action` - The action string the proof must be bound to.
/// * `expected_resource` - The resource string the proof must be bound to.
/// * `federation_root` - The federation root from an EXTERNAL trusted source.
/// * `current_timestamp` - Current Unix timestamp in seconds.
/// * `max_age_secs` - Maximum age of proof in seconds. 0 disables freshness check.
///
/// # Returns
///
/// `Ok(VerifiedPresentation)` if ALL checks pass.
/// `Err(VerifyError)` with a specific reason on any failure.
pub fn verify_proof_complete(
    wire_proof: &WirePresentationProof,
    expected_action: &str,
    expected_resource: &str,
    federation_root: &[u8; 32],
    current_timestamp: i64,
    max_age_secs: i64,
) -> Result<VerifiedPresentation, VerifyError> {
    // 1. Reject zero federation root.
    if *federation_root == [0u8; 32] {
        return Err(VerifyError::NoFederationRoot);
    }

    // 2. Require a real STARK proof (no structural/mock proofs).
    let real = wire_proof
        .real_stark_proof
        .as_ref()
        .ok_or(VerifyError::NoStarkProof)?;

    // 3. Verify BOTH committed descriptors (the flip off the legacy hand-StarkProof). An unknown
    //    predicate is a typed UnknownAir; a decode/verify failure is StarkInvalid.
    use dregg_circuit::blinded_membership_witness::PI_ROOT_4ARY;
    use dregg_circuit::bound_presentation_witness::{
        FEDERATION_ROOT as BOUND_FED_ROOT, REQUEST_PREDICATE_BASE,
    };
    let bound_pis = verify_wire_typed(&real.bound_presentation)?;
    let blinded_pis = verify_wire_typed(&real.blinded_membership)?;

    // 4. Federation root binding: the blinded ring-membership root AND the bound-presentation
    //    summary federation_root must both equal the expected root.
    let expected_root = bb_from_bytes(federation_root);
    if blinded_pis.get(PI_ROOT_4ARY).copied() != Some(expected_root)
        || bound_pis.get(BOUND_FED_ROOT).copied() != Some(expected_root)
    {
        return Err(VerifyError::RootMismatch);
    }

    // 5. Action binding: proof must be bound to (expected_action, expected_resource).
    let expected_binding =
        dregg_circuit::compute_action_binding(expected_action, expected_resource);
    if wire_proof.circuit_proof.public_inputs.request_predicate != expected_binding {
        return Err(VerifyError::ActionMismatch);
    }

    // Also bind the bound-presentation descriptor's committed action.
    for i in 0..dregg_circuit::ACTION_BINDING_WIDTH {
        if bound_pis.get(REQUEST_PREDICATE_BASE + i).copied() != Some(expected_binding[i]) {
            return Err(VerifyError::ActionMismatch);
        }
    }

    // 6. Timestamp freshness.
    if max_age_secs > 0 {
        let proof_ts = wire_proof.circuit_proof.public_inputs.timestamp.0 as i64;
        if proof_ts == 0 {
            return Err(VerifyError::Expired);
        }
        let age = current_timestamp.saturating_sub(proof_ts);
        if age > max_age_secs || age < -max_age_secs {
            return Err(VerifyError::Expired);
        }
    }

    // 7. Composition commitment (non-zero AND correctly recomputed).
    if wire_proof.composition_commitment.is_zero() {
        // For single-step tokens (no attenuation chain), a zero composition is acceptable
        // only if there are no fold proofs. Multi-step proofs MUST have a non-zero
        // composition commitment to bind the sub-proofs together.
        if !real.fold_step_roots.is_empty() {
            return Err(VerifyError::MissingComposition);
        }
    } else {
        // Recompute the composition commitment from the sub-proof data.
        let fold_chain_commitment = if real.fold_step_roots.is_empty() {
            BabyBear::ZERO
        } else {
            let fold_roots: Vec<BabyBear> = real
                .fold_step_roots
                .iter()
                .flat_map(|r| [r[0], r[1]])
                .collect();
            poseidon2::hash_many(&fold_roots)
        };
        let derivation_state_root = real.derivation_state_root;
        let presentation_tag = wire_proof.circuit_proof.public_inputs.presentation_tag;

        let recomputed = WideHash::from_poseidon2(
            "dregg-composition-v1",
            &[
                fold_chain_commitment,
                derivation_state_root,
                presentation_tag,
            ],
        );

        if recomputed != wire_proof.composition_commitment {
            return Err(VerifyError::CompositionMismatch);
        }
        // (The composition value formerly rode the hand-STARK public inputs; with the descriptor
        //  flip the sub-proof binding is the recomputed-vs-stored check above.)
    }

    // 8. Both committed descriptors were cryptographically verified in step 3 (fail-closed on an
    //    unknown predicate via UnknownAir, on a failed proof via StarkInvalid).
    let proof_tier = dregg_circuit::ProofTier::Production;

    // Tier is informational only. If the STARK verified cryptographically, the
    // proof is valid. Structural stubs cannot reach this point because they cannot
    // produce valid STARK proofs for any known AIR.

    Ok(VerifiedPresentation {
        tier: proof_tier,
        action: expected_action.to_string(),
        resource: expected_resource.to_string(),
        federation_root: *federation_root,
    })
}

/// Verify a presentation proof cryptographically (convenience wrapper).
///
/// Equivalent to `verify_presentation_full` with:
/// - No action predicate check (`expected_action = None`)
/// - No timestamp freshness check (uses timestamp 0 and max_age of i64::MAX)
///
/// **DEPRECATED**: This function skips action binding and freshness checks.
/// Use [`verify_proof_complete`] instead, which checks EVERYTHING.
///
/// **SECURITY WARNING**: The `federation_root` parameter MUST come from an external
/// trusted source (e.g., the verifier's own configuration, a pinned trust anchor,
/// or a federation registry the verifier operates). It MUST NOT be extracted from
/// the proof being verified (e.g., `proof.federation_root`), as that is circular
/// and provides no security guarantee.
#[deprecated(
    note = "Use verify_proof_complete() which checks action binding, freshness, and composition. This function skips critical security checks."
)]
pub fn verify_presentation(proof: &BridgePresentationProof, federation_root: &[u8; 32]) -> bool {
    // Delegate to the BabyBear-root path (the descriptor flip made the two identical apart from the
    // root encoding). A real STARK proof is required — the mock/structural path returns false there.
    verify_presentation_bb(proof, bb_from_bytes(federation_root))
}

/// Verify a presentation proof against a BabyBear-encoded federation root.
///
/// This is the lower-level verification function used when the federation root
/// is already known as a BabyBear field element (e.g., computed from a synthetic
/// Merkle path in tests, or stored directly alongside the federation tree).
///
/// **SECURITY WARNING**: The `expected_root` MUST come from an external trusted source.
/// Do NOT pass a value derived from the proof itself.
pub fn verify_presentation_bb(proof: &BridgePresentationProof, expected_root: BabyBear) -> bool {
    if let Some(ref real) = proof.real_stark_proof {
        // Verify BOTH committed descriptors (the flip off the legacy hand-StarkProof).
        let (bound_pis, blinded_pis) = match verify_presentation_descriptor_wires(real) {
            Some(v) => v,
            None => return false,
        };
        use dregg_circuit::blinded_membership_witness::PI_ROOT_4ARY;
        use dregg_circuit::bound_presentation_witness::FEDERATION_ROOT as BOUND_FED_ROOT;
        // The blinded ring-membership root AND the bound-presentation summary federation_root must
        // both equal the (externally trusted) expected root.
        blinded_pis.get(PI_ROOT_4ARY).copied() == Some(expected_root)
            && bound_pis.get(BOUND_FED_ROOT).copied() == Some(expected_root)
    } else {
        false
    }
}

/// Verify a presentation proof (legacy API, checks only structural validity).
///
/// **DEPRECATED**: This only checks the prover-set `verification` field and provides
/// no cryptographic guarantee. Use `verify_presentation()` with a federation root instead.
#[deprecated(
    note = "Use verify_presentation(proof, federation_root) for cryptographic verification"
)]
pub fn verify_presentation_structural(proof: &BridgePresentationProof) -> bool {
    proof.is_valid()
}

/// Verify a presentation's fold chain.
///
/// Validated-IVC fold-chain proofs (chain STARK + per-step Merkle membership STARKs) were retired
/// with the descriptor-wire flip; the fold chain is now bound via the composition commitment
/// checked in [`verify_proof_complete`] / [`verify_presentation_complete`]. There is no separate
/// validated-IVC proof to check here, so this returns `false` (fail-closed).
pub fn verify_fold_chain(_proof: &BridgePresentationProof) -> bool {
    // Validated-IVC fold-chain proofs were retired with the descriptor-wire flip. The fold chain
    // is now bound via the composition commitment (recomputed and checked in
    // `verify_proof_complete` / `verify_presentation_complete`), not a separate validated-IVC
    // proof. With no such proof to check, this reports unverified (fail-closed).
    false
}

/// Verify a wire presentation proof's fold chain.
///
/// Validated-IVC fold-chain proofs were retired; there is no separate fold-chain proof on the
/// wire form to check, so this returns `false` (fail-closed). The fold chain is bound via the
/// composition commitment checked by [`verify_proof_complete`].
pub fn verify_wire_fold_chain(_proof: &WirePresentationProof) -> bool {
    false
}

/// Full cryptographic verification of a presentation proof: issuer + fold chain.
///
/// This verifies issuer membership (via `verify_presentation()`) and, for multi-step chains,
/// the fold chain binding via the composition commitment (recomputed from the fold-step roots +
/// derivation state root and checked against the committed value).
///
/// Returns `true` only if BOTH:
/// 1. The issuer membership descriptor verifies against `federation_root`
/// 2. Either the token is single-step, or the composition commitment binding the fold chain
///    recomputes to the committed value.
///
/// # Arguments
///
/// * `proof` - The presentation proof to verify.
/// * `federation_root` - The 32-byte federation root of trust (external trust anchor).
#[allow(deprecated)] // verify_presentation is deprecated in favor of verify_proof_complete
pub fn verify_presentation_complete(
    proof: &BridgePresentationProof,
    federation_root: &[u8; 32],
) -> bool {
    // 1. Verify issuer membership STARK.
    if !verify_presentation(proof, federation_root) {
        return false;
    }

    // 2. Check whether the proof is complete:
    //    - chain_length <= 1: no fold chain to prove (single-step token).
    //    - real_stark_proof with non-zero composition_commitment: the descriptor-wire proof
    //      binds the fold chain via the composition_commitment (recomputed below from the
    //      fold-step roots + derivation state root). This is the standard prove() path for
    //      multi-step chains; the composition_commitment ensures no sub-proof substitution.
    if proof.chain_length <= 1 {
        return true;
    }

    // For multi-step chains without IVC, accept if we have a real STARK proof
    // with a valid (non-zero) composition commitment binding the fold chain.
    // SECURITY: We MUST recompute the composition commitment from the sub-proof
    // data and verify it matches the claimed value. Without this, an attacker
    // could forge an arbitrary non-zero commitment that passes the non-zero check.
    let real = match proof.real_stark_proof.as_ref() {
        Some(r) => r,
        None => return false,
    };

    if proof.composition_commitment.is_zero() {
        return false;
    }

    // Recompute composition commitment from the sub-proof data.
    let fold_chain_commitment = if real.fold_step_roots.is_empty() {
        BabyBear::ZERO
    } else {
        let fold_roots: Vec<BabyBear> = real
            .fold_step_roots
            .iter()
            .flat_map(|r| [r[0], r[1]])
            .collect();
        poseidon2::hash_many(&fold_roots)
    };
    let derivation_state_root = real.derivation_state_root;
    let presentation_tag = proof.circuit_proof.public_inputs.presentation_tag;
    // The circuit PI already stores the narrow (single-element) presentation tag,
    // which is compute_presentation_tag_narrow(). Use it directly — no re-hashing.
    let recomputed = WideHash::from_poseidon2(
        "dregg-composition-v1",
        &[
            fold_chain_commitment,
            derivation_state_root,
            presentation_tag,
        ],
    );

    if recomputed != proof.composition_commitment {
        return false;
    }
    // (The composition value formerly rode the hand-STARK public inputs; with the descriptor flip
    //  the sub-proof binding is the recomputed-vs-stored check above, computed from `real`'s fold
    //  and derivation sub-proofs.)

    true
}

// =============================================================================
// Predicate Proofs
// =============================================================================

/// A predicate that can be proven about a private token attribute.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum Predicate {
    /// Prove `attribute >= threshold`.
    Gte(u32),
    /// Prove `attribute <= threshold`.
    Lte(u32),
    /// Prove `attribute > threshold`.
    Gt(u32),
    /// Prove `attribute < threshold`.
    Lt(u32),
    /// Prove `attribute != target`.
    Neq(u32),
    /// Prove `low <= attribute <= high`.
    InRange(u32, u32),
}

/// A predicate proof over a token attribute, ready for verification.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct BridgePredicateProof {
    /// The predicate that was proven.
    pub predicate: Predicate,
    /// The underlying circuit proof(s).
    pub proof: BridgePredicateProofInner,
    /// The fact commitment (public input -- binds the proof to a specific token state).
    pub fact_commitment: BabyBear,
    /// The DECOMMITMENT: the per-presentation [`Blinding`] used to build `fact_commitment`
    /// (`hash_4_to_1([fact_hash, state_root, blinding, 0])`).
    ///
    /// # Why this must travel with the proof
    ///
    /// [`verify_predicate_proof`] pins `expected_fact_commitment` as the descriptor's `pi[1]`, and
    /// that parameter is sound only if the verifier DERIVES it from token state it trusts. With the
    /// blinding drawn fresh per proof and then discarded, no verifier can reproduce the commitment
    /// for a fact it trusts — the parameter has no sound source at all, and the only feed that ever
    /// "works" is the proof's own commitment, i.e. the `x != x` gate that accepts everything. The
    /// blinding is the missing half of the opening.
    ///
    /// # Why publishing it costs no soundness
    ///
    /// The prover already chooses the blinding freely; handing it over adds no freedom. A verifier
    /// derives `commitment_of(TRUSTED_value, blinding)` — the blinding comes from the prover, but
    /// the VALUE does not, so matching a forged value's commitment would need a Poseidon2 collision.
    /// Per the [`Blinding`] doc: blinding rerandomizes WHICH commitment names a fact; it cannot
    /// change WHICH fact is named.
    ///
    /// # What it costs privacy
    ///
    /// Nothing against the parties unlinkability is for. Deriving requires already holding the
    /// fact's value, so anyone who can use this decommitment to correlate two showings could
    /// equally correlate them from the trusted state they must already hold. Parties who do not
    /// hold the proof still see only unlinkable commitments.
    ///
    /// Stored as the raw field element rather than [`Blinding`] because the circuit-side newtype
    /// carries no serde derives; [`Blinding`] is reconstructed at the derivation site.
    pub blinding: BabyBear,
}

/// Inner proof representation -- single proof for simple predicates, pair for InRange.
///
/// Each arm carries the `postcard`-encoded IR-v2 descriptor batch proof
/// (`dregg_circuit::descriptor_ir2::Ir2BatchProof`), not the retired hand-STARK
/// proof type. Only the ≥ (`Gte`) predicate has an emitted descriptor
/// (`dregg-predicate-arith-ge::threshold-v1`); the `Range` / `CommittedThreshold`
/// arms have no IR-v2 descriptor yet and are fail-closed at verify.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub enum BridgePredicateProofInner {
    /// A single predicate proof (only `Gte` has a descriptor). `postcard(Ir2BatchProof)`.
    Single(Vec<u8>),
    /// A pair of proofs for InRange (lower bound + upper bound). No descriptor (fail-closed).
    Range(Vec<u8>, Vec<u8>),
    /// A committed-threshold proof where both value and threshold are hidden. No descriptor
    /// (fail-closed).
    CommittedThreshold(Vec<u8>),
}

/// Generate a predicate proof for a specific fact attribute in a token state.
///
/// This is the primary predicate proof entry point. The prover specifies:
/// - `private_value`: The actual value of the attribute (kept private).
/// - `fact_hash`: The Poseidon2 hash of the fact containing the attribute.
/// - `state_root`: The Poseidon2 root of the token state containing the fact.
/// - `predicate`: The statement to prove.
///
/// The verifier will receive only:
/// - The predicate type and threshold (public).
/// - The fact_commitment = Poseidon2(fact_hash, state_root) (public).
/// - The proof (cryptographic).
///
/// They learn that "some value in the committed fact satisfies the predicate"
/// without learning the actual value.
///
/// # Returns
///
/// `Some(BridgePredicateProof)` if the statement is true and the proof generates
/// successfully, `None` if the statement is false or proof generation fails.
/// The caller-facing identity of a fact a predicate speaks about: everything the fact commitment
/// covers EXCEPT the value (which is `terms[0]`, supplied alongside) and the state root (which the
/// proving chain supplies, not the caller).
///
/// This replaces the old `fact_hash: BabyBear` parameter. A hash is opaque: passing it beside a
/// value let the two name different facts, and for `≥` the circuit did not relate them, so the
/// mispairing was a provable forgery rather than a caller mistake. Terms are not opaque — the hash
/// is derived, so the pairing cannot come apart.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FactTerms {
    /// The predicate symbol (`hash_fact`'s first argument).
    pub predicate_sym: BabyBear,
    /// The fact's second term (`terms[1]`).
    pub term1: BabyBear,
    /// The fact's third term (`terms[2]`).
    pub term2: BabyBear,
}

impl FactTerms {
    /// Bind these terms to a state root, yielding the circuit-level [`FactBinding`].
    pub fn bind(self, state_root: BabyBear) -> FactBinding {
        FactBinding {
            predicate_sym: self.predicate_sym,
            term1: self.term1,
            term2: self.term2,
            state_root,
        }
    }
}

pub fn prove_predicate_for_fact(
    private_value: u32,
    fact: FactBinding,
    blinding: Blinding,
    predicate: &Predicate,
) -> Option<BridgePredicateProof> {
    use dregg_circuit::descriptor_by_name::descriptor_by_name;
    use dregg_circuit::descriptor_ir2::{MemBoundaryWitness, prove_vm_descriptor2};
    use dregg_circuit::predicate_arith_witness::{PREDICATE_ARITH_NAME, predicate_arith_witness};
    use dregg_circuit::predicate_comparison_witness::{
        PREDICATE_ARITH_GT_NAME, PREDICATE_ARITH_LE_NAME, PREDICATE_ARITH_LT_NAME,
        PREDICATE_ARITH_NEQ_NAME, predicate_gt_witness, predicate_le_witness, predicate_lt_witness,
        predicate_neq_witness,
    };

    let v = private_value as u64;
    // The fact commitment is DERIVED from the value being proved about — it is not a caller-supplied
    // parameter that could name a different value's fact. Every descriptor in the family now ALSO
    // welds this relation INSIDE the circuit (the two Poseidon2 legs), so the derivation is checked,
    // not merely performed here: this value is what each builder independently recomputes.
    //
    // The commitment is BLINDED: leg 2 is an arity-4 chip lookup over
    // `[fact_hash, state_root, blinding, 0]`, so a fresh `blinding` per presentation makes two
    // showings of the SAME fact carry different commitments (unlinkable) while leg 1 keeps each
    // bound to the value compared. `prove_with_disclosure` draws it fresh; a caller passing
    // `Blinding::NONE` gets the sound-but-correlatable degenerate case.
    let fact_commitment = fact.commitment_of(BabyBear::from_u64(v), blinding);

    // Prove ONE single-bound witness against `desc_name`; `None` when the witness cannot be built or
    // the comparison is FALSE (prove refuses — the false-statement pole, per-op range / nonzero tooth).
    let prove_one = |desc_name: &str,
                     built: Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String>|
     -> Option<Vec<u8>> {
        let desc = descriptor_by_name(desc_name)?;
        let (trace, pis) = built.ok()?;
        let proof =
            prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[]).ok()?;
        postcard::to_allocvec(&proof).ok()
    };

    // Each comparison now has an emitted IR-v2 descriptor. Single-bound ops emit a `Single` proof;
    // `InRange(low, high)` emits a `Range` pair — `value ≥ low` (the `≥` descriptor) and
    // `value ≤ high` (the `≤` descriptor), both pinned to the same `fact_commitment`.
    let inner = match predicate {
        Predicate::Gte(t) => BridgePredicateProofInner::Single(prove_one(
            PREDICATE_ARITH_NAME,
            predicate_arith_witness(v, *t as u64, fact, blinding, 2),
        )?),
        Predicate::Lte(t) => BridgePredicateProofInner::Single(prove_one(
            PREDICATE_ARITH_LE_NAME,
            predicate_le_witness(v, *t as u64, fact, blinding, 2),
        )?),
        Predicate::Gt(t) => BridgePredicateProofInner::Single(prove_one(
            PREDICATE_ARITH_GT_NAME,
            predicate_gt_witness(v, *t as u64, fact, blinding, 2),
        )?),
        Predicate::Lt(t) => BridgePredicateProofInner::Single(prove_one(
            PREDICATE_ARITH_LT_NAME,
            predicate_lt_witness(v, *t as u64, fact, blinding, 2),
        )?),
        Predicate::Neq(t) => BridgePredicateProofInner::Single(prove_one(
            PREDICATE_ARITH_NEQ_NAME,
            predicate_neq_witness(v, *t as u64, fact, blinding, 2),
        )?),
        Predicate::InRange(low, high) => {
            let low_proof = prove_one(
                PREDICATE_ARITH_NAME,
                predicate_arith_witness(v, *low as u64, fact, blinding, 2),
            )?;
            let high_proof = prove_one(
                PREDICATE_ARITH_LE_NAME,
                predicate_le_witness(v, *high as u64, fact, blinding, 2),
            )?;
            BridgePredicateProofInner::Range(low_proof, high_proof)
        }
    };
    Some(BridgePredicateProof {
        predicate: predicate.clone(),
        proof: inner,
        fact_commitment,
        // The opening a trusted-state verifier needs to reproduce `fact_commitment`. Without it the
        // commitment is unreproducible and the verifier's gate has nothing sound to compare against.
        blinding: blinding.as_field(),
    })
}

/// Verify a predicate proof.
///
/// The verifier provides:
/// - The proof to verify.
/// - The expected fact_commitment (which the verifier must independently derive
///   from the token state they trust).
///
/// Returns `true` if the proof is valid for the given commitment.
pub fn verify_predicate_proof(
    proof: &BridgePredicateProof,
    expected_fact_commitment: BabyBear,
) -> bool {
    if proof.fact_commitment != expected_fact_commitment {
        return false;
    }

    use dregg_circuit::descriptor_by_name::descriptor_by_name;
    use dregg_circuit::descriptor_ir2::{DreggStarkConfig, Ir2BatchProof, verify_vm_descriptor2};
    use dregg_circuit::predicate_arith_witness::PREDICATE_ARITH_NAME;
    use dregg_circuit::predicate_comparison_witness::{
        PREDICATE_ARITH_GT_NAME, PREDICATE_ARITH_LE_NAME, PREDICATE_ARITH_LT_NAME,
        PREDICATE_ARITH_NEQ_NAME,
    };

    // Verify ONE single-bound proof against `desc_name`, pinning PIs `[bound, fact_commitment]`. A
    // proof committed to a different bound / fact, or a witness that violates the comparison, is UNSAT.
    let verify_one = |desc_name: &str, bound: u32, bytes: &[u8]| -> bool {
        let desc = match descriptor_by_name(desc_name) {
            Some(d) => d,
            None => return false,
        };
        let batch: Ir2BatchProof<DreggStarkConfig> = match postcard::from_bytes(bytes) {
            Ok(p) => p,
            Err(_) => return false,
        };
        let pis = vec![BabyBear::new(bound), expected_fact_commitment];
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            verify_vm_descriptor2(&desc, &batch, &pis).is_ok()
        }))
        .unwrap_or(false)
    };

    // The predicate operator selects the descriptor; the wire shape must match (single vs range).
    // Any shape mismatch, or a `CommittedThreshold` inner (its own descriptor path), fails closed.
    match (&proof.predicate, &proof.proof) {
        (Predicate::Gte(t), BridgePredicateProofInner::Single(inner)) => {
            verify_one(PREDICATE_ARITH_NAME, *t, inner)
        }
        (Predicate::Lte(t), BridgePredicateProofInner::Single(inner)) => {
            verify_one(PREDICATE_ARITH_LE_NAME, *t, inner)
        }
        (Predicate::Gt(t), BridgePredicateProofInner::Single(inner)) => {
            verify_one(PREDICATE_ARITH_GT_NAME, *t, inner)
        }
        (Predicate::Lt(t), BridgePredicateProofInner::Single(inner)) => {
            verify_one(PREDICATE_ARITH_LT_NAME, *t, inner)
        }
        (Predicate::Neq(t), BridgePredicateProofInner::Single(inner)) => {
            verify_one(PREDICATE_ARITH_NEQ_NAME, *t, inner)
        }
        (
            Predicate::InRange(low, high),
            BridgePredicateProofInner::Range(low_proof, high_proof),
        ) => {
            // `low ≤ value ≤ high` = `value ≥ low` (≥ descriptor) AND `value ≤ high` (≤ descriptor),
            // both pinned to the same `fact_commitment`. Either failing ⇒ reject.
            verify_one(PREDICATE_ARITH_NAME, *low, low_proof)
                && verify_one(PREDICATE_ARITH_LE_NAME, *high, high_proof)
        }
        _ => false,
    }
}

// =============================================================================
// Committed-Threshold Proofs (private threshold from verifier)
// =============================================================================

/// A committed-threshold proof: proves `value >= threshold` without revealing
/// either value or threshold to third-party verifiers.
///
/// The verifier commits to their threshold: `Poseidon2(threshold, blinding)`.
/// The prover proves: value >= threshold AND the commitment is correct.
/// Public inputs are only the two commitments (threshold + fact).
#[derive(Clone, Debug)]
pub struct BridgeCommittedThresholdProof {
    /// The circuit-level proof (`postcard`-encoded IR-v2 batch proof). No IR-v2
    /// committed-threshold descriptor is emitted yet, so this is currently unpopulated.
    pub proof: Vec<u8>,
    /// The threshold commitment (for verifier cross-check).
    pub threshold_commitment: BabyBear,
    /// The fact commitment (binding to token state).
    pub fact_commitment: BabyBear,
}

/// Generate a committed-threshold proof for a specific fact attribute.
///
/// This is the primary entry point for the committed-threshold protocol.
///
/// # Arguments
///
/// - `private_value`: The prover's private attribute value (kept hidden from verifier).
/// - `threshold`: The verifier's threshold (received from verifier via secure channel).
/// - `blinding`: The verifier's blinding factor (received from verifier via secure channel).
/// - `fact_hash`: Poseidon2 hash of the fact containing the attribute.
/// - `state_root`: Poseidon2 root of the token state containing the fact.
///
/// # Returns
///
/// `Some(BridgeCommittedThresholdProof)` if value >= threshold and proof succeeds,
/// `None` if the statement is false or proof generation fails.
///
/// # Privacy
///
/// Third-party verifiers see only:
/// - `threshold_commitment = Poseidon2(threshold, blinding)` — hides the threshold.
/// - `fact_commitment = Poseidon2(fact_hash, state_root)` — hides the value.
///
/// They learn ONLY that "the committed value satisfies the committed threshold."
pub fn prove_committed_threshold(
    private_value: u32,
    threshold: u32,
    blinding: u32,
    fact_hash: BabyBear,
    state_root: BabyBear,
) -> Option<BridgeCommittedThresholdProof> {
    // The committed-threshold (hidden value + hidden threshold) predicate has no
    // emitted IR-v2 descriptor, so no proof can be produced (the retired hand-AIR
    // gadget is gone). Fail-closed: no proof.
    let _ = (private_value, threshold, blinding, fact_hash, state_root);
    None
}

/// Verify a committed-threshold proof.
///
/// # For the verifier (who knows their threshold):
///
/// ```ignore
/// let expected_commitment = dregg_circuit::compute_threshold_commitment(
///     BabyBear::new(my_threshold), BabyBear::new(my_blinding)
/// );
/// let valid = verify_committed_threshold_proof(&proof, expected_commitment, fact_commitment);
/// ```
///
/// # For third-party auditors (who know neither value nor threshold):
///
/// They verify against the commitments they received from the protocol participants.
/// They learn only: "this proof is valid for these commitments" (1 bit).
pub fn verify_committed_threshold_proof(
    proof: &BridgeCommittedThresholdProof,
    expected_threshold_commitment: BabyBear,
    expected_fact_commitment: BabyBear,
) -> bool {
    // No emitted IR-v2 committed-threshold descriptor — fail closed rather than
    // accept an unverified claim.
    let _ = (
        proof,
        expected_threshold_commitment,
        expected_fact_commitment,
    );
    false
}

// =============================================================================
// Programmable Predicate Programs
// =============================================================================

/// An opaque programmable-predicate program proof: the `postcard`-encoded IR-v2
/// batch proof(s) for the compiled program. No IR-v2 descriptor is emitted for the
/// programmable-predicate compiler yet, so this currently carries no producible
/// proof (the proving entry points are fail-closed).
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct ProgramProof {
    /// The serialized proof payload (empty until a program descriptor is emitted).
    pub bytes: Vec<u8>,
}

/// Error from the predicate program proving pipeline.
#[derive(Clone, Debug)]
pub enum ProgramProveError {
    /// Compilation failed.
    CompileError(dregg_circuit::predicate_program::CompileError),
    /// Proof generation failed.
    ProveError(dregg_circuit::predicate_program::ProveError),
    /// The compiled program has no emitted IR-v2 descriptor, so no proof can be produced.
    Unsupported(String),
}

impl std::fmt::Display for ProgramProveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::CompileError(e) => write!(f, "compile error: {e}"),
            Self::ProveError(e) => write!(f, "prove error: {e}"),
            Self::Unsupported(m) => write!(f, "unsupported: {m}"),
        }
    }
}

impl From<dregg_circuit::predicate_program::CompileError> for ProgramProveError {
    fn from(e: dregg_circuit::predicate_program::CompileError) -> Self {
        Self::CompileError(e)
    }
}

impl From<dregg_circuit::predicate_program::ProveError> for ProgramProveError {
    fn from(e: dregg_circuit::predicate_program::ProveError) -> Self {
        Self::ProveError(e)
    }
}

/// Compile and prove a predicate program in one step.
///
/// This is the primary bridge-level entry point for the programmable predicates
/// pipeline. It takes a high-level program specification and private values,
/// compiles the program to AIR(s), and generates the appropriate proof(s).
///
/// # Arguments
///
/// * `program` - The predicate program to prove.
/// * `private_values` - Map from attribute names to private values.
/// * `state_root` - The Poseidon2 root of the current token state.
///
/// # Returns
///
/// A `ProgramProof` that can be verified by anyone knowing the public inputs,
/// or a `ProgramProveError` if compilation or proof generation fails.
///
/// # Example
///
/// ```ignore
/// use dregg_circuit::predicate_program::{PredicateExpr, PredicateProgram};
/// use dregg_circuit::dsl::predicates::PredicateType;
/// use dregg_circuit::BabyBear;
/// use std::collections::HashMap;
///
/// let program = PredicateProgram::with_default_depth(PredicateExpr::Range {
///     attribute: "balance".to_string(),
///     predicate_type: PredicateType::Gte,
///     threshold: 1000,
/// });
///
/// let mut values = HashMap::new();
/// values.insert("balance".to_string(), 5000u64);
///
/// let proof = dregg_bridge::prove_predicate_program(
///     &program, &values, BabyBear::new(99999),
/// ).unwrap();
/// ```
pub fn prove_predicate_program(
    program: &dregg_circuit::predicate_program::PredicateProgram,
    private_values: &std::collections::HashMap<String, u64>,
    state_root: BabyBear,
) -> Result<ProgramProof, ProgramProveError> {
    use dregg_circuit::predicate_program::compile_predicate;

    // Compilation still validates the program shape; but the compiled plan has no
    // emitted IR-v2 descriptor, so no proof can be produced (the retired hand-AIR
    // program prover is gone). Fail-closed.
    compile_predicate(program)?;
    let _ = (private_values, state_root);
    Err(ProgramProveError::Unsupported(
        "programmable predicate programs have no emitted IR-v2 descriptor yet".to_string(),
    ))
}

/// Compile and prove a predicate program with full private state (including temporal history).
///
/// This is the extended version of [`prove_predicate_program`] that supports
/// temporal predicates by accepting full [`PrivateState`] including historical
/// values and state roots.
pub fn prove_predicate_program_full(
    program: &dregg_circuit::predicate_program::PredicateProgram,
    private_state: &dregg_circuit::predicate_program::PrivateState,
    state_root: BabyBear,
) -> Result<ProgramProof, ProgramProveError> {
    use dregg_circuit::predicate_program::compile_predicate;

    compile_predicate(program)?;
    let _ = (private_state, state_root);
    Err(ProgramProveError::Unsupported(
        "programmable predicate programs have no emitted IR-v2 descriptor yet".to_string(),
    ))
}

/// Verify a predicate program proof.
///
/// The verifier provides:
/// - The program (they know what was proven).
/// - The proof to verify.
/// - Expected fact commitments for each attribute.
/// - The state root the proofs are bound to.
///
/// Returns `true` if the proof is valid.
pub fn verify_predicate_program(
    program: &dregg_circuit::predicate_program::PredicateProgram,
    proof: &ProgramProof,
    expected_commitments: &std::collections::HashMap<String, BabyBear>,
    state_root: BabyBear,
) -> bool {
    // No emitted IR-v2 descriptor for the programmable-predicate compiler — fail
    // closed rather than accept an unverified program proof.
    let _ = (program, proof, expected_commitments, state_root);
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_circuit::ConstraintProver;
    use dregg_circuit::merkle_types::MerkleAir;

    fn test_key() -> [u8; 32] {
        let mut key = [0u8; 32];
        key[0] = 0x42;
        key[1] = 0x13;
        key[31] = 0xFF;
        key
    }

    fn test_federation_root() -> [u8; 32] {
        let mut root = [0u8; 32];
        root[0] = 0xFE;
        root[1] = 0xDE;
        root[31] = 0x01;
        root
    }

    #[test]
    fn test_builder_state_transitions() {
        let key = test_key();
        let mut builder = BridgePresentationBuilder::new(key, test_federation_root());
        assert_eq!(builder.chain_length(), 0);

        let token = MacaroonToken::mint(key, b"kid-1", "dregg.fg-goose.online");
        builder.set_root_token(token);
        assert_eq!(builder.chain_length(), 1);
        assert!(builder.final_state().is_some());

        let att = Attenuation {
            apps: vec![("my-app".into(), "rw".into())],
            ..Default::default()
        };
        assert!(builder.add_attenuation(&att));
        assert_eq!(builder.chain_length(), 2);

        let att2 = Attenuation {
            confine_user: Some("alice".into()),
            ..Default::default()
        };
        assert!(builder.add_attenuation(&att2));
        assert_eq!(builder.chain_length(), 3);
        assert!(builder.verify_chain());
    }

    #[test]
    fn test_builder_empty_attenuation_fails() {
        let key = test_key();
        let mut builder = BridgePresentationBuilder::new(key, test_federation_root());
        let token = MacaroonToken::mint(key, b"kid-1", "dregg.fg-goose.online");

        builder.set_root_token(token);

        let att = Attenuation::default();
        assert!(!builder.add_attenuation(&att));
    }

    #[test]
    fn test_builder_attenuation_without_root_fails() {
        let key = test_key();
        let mut builder = BridgePresentationBuilder::new(key, test_federation_root());

        let att = Attenuation {
            apps: vec![("my-app".into(), "rw".into())],
            ..Default::default()
        };
        assert!(!builder.add_attenuation(&att));
    }

    #[test]
    fn test_bytes_to_babybear_vec() {
        // Multi-limb encoding should preserve all 32 bytes.
        let mut bytes = [0u8; 32];
        bytes[0] = 1;
        bytes[31] = 0xFF;
        let limbs = bytes_to_babybear_vec(&bytes);
        assert_eq!(limbs.len(), 8);
        // First limb encodes bytes[0..4]: value 1
        assert_eq!(limbs[0], BabyBear::new(1));
        // Last limb encodes bytes[28..32]: 0xFF000000 = 4278190080, mod p
        let expected_last = BabyBear::new(0xFF000000u32);
        assert_eq!(limbs[7], expected_last);
    }

    #[test]
    fn test_bytes_to_babybear_hash() {
        // Poseidon2-compressed hash should be deterministic and non-trivial.
        let bytes = [0u8; 32];
        let h1 = bytes_to_babybear(&bytes);
        let h2 = bytes_to_babybear(&bytes);
        assert_eq!(h1, h2);

        // Different inputs should produce different hashes.
        let mut bytes2 = [0u8; 32];
        bytes2[16] = 1; // Change a byte in the middle (was invisible to old 4-byte truncation).
        let h3 = bytes_to_babybear(&bytes2);
        assert_ne!(
            h1, h3,
            "bytes differing only beyond byte 3 must produce different hashes"
        );
    }

    #[test]
    fn test_hash_index_deterministic() {
        let key = test_key();
        let h1 = hash_index(0, 0, &key);
        let h2 = hash_index(0, 0, &key);
        assert_eq!(h1, h2);

        let h3 = hash_index(0, 1, &key);
        assert_ne!(h1, h3); // Different sibling index should give different hash.
    }

    #[test]
    fn test_build_issuer_membership_rejects_wrong_root() {
        // With an arbitrary federation_root that doesn't match the synthetic
        // Merkle path, the builder should return IssuerNotInFederation.
        let key = test_key();
        let builder = BridgePresentationBuilder::new(key, test_federation_root());
        let issuer_hash = bytes_to_babybear(&key);

        let result = builder.build_issuer_membership_poseidon2(issuer_hash);
        assert!(
            result.is_err(),
            "Synthetic proof should fail against an unrelated federation root"
        );
        assert_eq!(result.unwrap_err(), AuthError::IssuerNotInFederation);
    }

    #[test]
    fn test_build_issuer_membership_accepts_matching_root() {
        let key = test_key();
        let issuer_hash = bytes_to_babybear(&key);
        let depth = 8;

        // Linear Merkle AIR path.
        let mut current = issuer_hash;
        for i in 0..depth {
            let position = (i % 4) as u8;
            let siblings = [
                BabyBear::new(hash_index(i, 0, &key)),
                BabyBear::new(hash_index(i, 1, &key)),
                BabyBear::new(hash_index(i, 2, &key)),
            ];
            current = compute_parent_poseidon2(current, position, &siblings);
        }
        let expected_root_bb_poseidon2 = current;

        let builder = BridgePresentationBuilder::new_with_root_bb(
            key,
            test_federation_root(),
            expected_root_bb_poseidon2,
        );
        let result = builder.build_issuer_membership_poseidon2(issuer_hash);
        assert!(
            result.is_ok(),
            "Poseidon2 membership should succeed with matching root"
        );

        let witness = result.unwrap();
        assert_eq!(witness.leaf_hash, issuer_hash);
        assert_eq!(witness.levels.len(), 8);
        assert_eq!(witness.expected_root, expected_root_bb_poseidon2);

        // The Merkle AIR should verify this witness.
        let air = MerkleAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "Issuer membership Merkle proof should verify"
        );

        // Poseidon2 path.
        let mut current = issuer_hash;
        for i in 0..depth {
            let position = (i % 4) as u8;
            let siblings = [
                BabyBear::new(hash_index(i, 0, &key)),
                BabyBear::new(hash_index(i, 1, &key)),
                BabyBear::new(hash_index(i, 2, &key)),
            ];
            current = compute_parent_poseidon2(current, position, &siblings);
        }
        let expected_root_bb_poseidon2 = current;

        let builder = BridgePresentationBuilder::new_with_root_bb(
            key,
            test_federation_root(),
            expected_root_bb_poseidon2,
        );
        let result = builder.build_issuer_membership_poseidon2(issuer_hash);
        assert!(
            result.is_ok(),
            "Poseidon2 membership should succeed with matching root"
        );

        let witness = result.unwrap();
        assert_eq!(witness.leaf_hash, issuer_hash);
        assert_eq!(witness.levels.len(), 8);
        assert_eq!(witness.expected_root, expected_root_bb_poseidon2);
    }

    #[test]
    fn test_prove_real_poseidon2() {
        // Compute the Poseidon2-based federation root for the test key.
        let key = test_key();
        let issuer_hash = bytes_to_babybear(&key);
        let depth = 8;
        let mut current = issuer_hash;
        for i in 0..depth {
            let position = (i % 4) as u8;
            let siblings = [
                BabyBear::new(hash_index(i, 0, &key)),
                BabyBear::new(hash_index(i, 1, &key)),
                BabyBear::new(hash_index(i, 2, &key)),
            ];
            current = compute_parent_poseidon2(current, position, &siblings);
        }
        let fed_root_bb = current;
        let mut fed_root_bytes = [0u8; 32];
        fed_root_bytes[..4].copy_from_slice(&fed_root_bb.0.to_le_bytes());

        let mut builder =
            BridgePresentationBuilder::new_with_root_bb(key, fed_root_bytes, fed_root_bb);
        let token = MacaroonToken::mint(key, b"kid-p2", "dregg.fg-goose.online");
        builder.set_root_token(token);

        // Use unrestricted token (no attenuations) to avoid pre-existing
        // fold chain constraint failures. The UNRESTRICTED rule (rule 3)
        // will fire, allowing authorization without fold steps.
        let request = AuthRequest {
            action: Some("anything".into()),
            ..Default::default()
        };

        let proof = builder.prove(&request);
        assert!(
            proof.is_ok(),
            "prove() with Poseidon2 should succeed: {:?}",
            proof.err()
        );

        let proof = proof.unwrap();
        assert!(
            proof.has_real_stark_proof(),
            "Should have a real STARK proof"
        );

        // Verify the issuer-membership proof cryptographically against the
        // (external) federation root via the retained presentation verifier.
        assert!(
            verify_presentation_bb(&proof, fed_root_bb),
            "Poseidon2 issuer-membership proof should verify against the federation root"
        );
    }

    /// Task #163 fail-closed regression: every verify entry point in this
    /// module must REFUSE a proof whose AIR name does not resolve to a
    /// registered circuit descriptor — never fall back to a guessed circuit.
    /// A cryptographically valid proof is relabeled with an unregistered AIR
    /// name; verification must refuse loudly (typed `VerifyError::UnknownAir`
    /// on the Result path, `false` on the bool paths).
    #[test]
    fn test_unknown_air_refused_all_verify_paths() {
        // Build a real proof (same setup as test_prove_real_poseidon2).
        let key = test_key();
        let issuer_hash = bytes_to_babybear(&key);
        let depth = 8;
        let mut current = issuer_hash;
        for i in 0..depth {
            let position = (i % 4) as u8;
            let siblings = [
                BabyBear::new(hash_index(i, 0, &key)),
                BabyBear::new(hash_index(i, 1, &key)),
                BabyBear::new(hash_index(i, 2, &key)),
            ];
            current = compute_parent_poseidon2(current, position, &siblings);
        }
        let fed_root_bb = current;
        let mut fed_root_bytes = [0u8; 32];
        fed_root_bytes[..4].copy_from_slice(&fed_root_bb.0.to_le_bytes());

        let mut builder =
            BridgePresentationBuilder::new_with_root_bb(key, fed_root_bytes, fed_root_bb);
        let token = MacaroonToken::mint(key, b"kid-163", "dregg.fg-goose.online");
        builder.set_root_token(token);

        let request = AuthRequest {
            action: Some("anything".into()),
            ..Default::default()
        };
        let mut proof = builder.prove(&request).expect("prove should succeed");

        // Baseline: the honest proof verifies on every retained path.
        assert!(
            verify_presentation_bb(&proof, fed_root_bb),
            "baseline: honest proof must verify via verify_presentation_bb"
        );

        // Relabel the blinded ring-membership descriptor with an unregistered predicate identity
        // (the descriptor-flip analog of relabeling the retired hand-STARK air-name).
        proof
            .real_stark_proof
            .as_mut()
            .unwrap()
            .blinded_membership
            .predicate = "evil-unregistered-air-v0".to_string();

        // verify_presentation_bb (bool path): refusal.
        assert!(
            !verify_presentation_bb(&proof, fed_root_bb),
            "verify_presentation_bb must refuse an unknown descriptor predicate"
        );

        // verify_proof_complete (typed path): VerifyError::UnknownAir.
        let wire = proof.into_wire_proof();
        let complete = verify_proof_complete(&wire, "anything", "", &fed_root_bytes, 0, 0);
        assert!(
            matches!(complete, Err(VerifyError::UnknownAir(ref n)) if n == "evil-unregistered-air-v0"),
            "verify_proof_complete must refuse an unknown descriptor predicate with typed VerifyError::UnknownAir, got {:?}",
            complete
        );
    }

    /// Known AIR names still flow through verify_proof_complete unchanged
    /// (no behavior change for registered identifiers).
    #[test]
    fn test_known_air_still_verifies_proof_complete() {
        let key = test_key();
        let issuer_hash = bytes_to_babybear(&key);
        let depth = 8;
        let mut current = issuer_hash;
        for i in 0..depth {
            let position = (i % 4) as u8;
            let siblings = [
                BabyBear::new(hash_index(i, 0, &key)),
                BabyBear::new(hash_index(i, 1, &key)),
                BabyBear::new(hash_index(i, 2, &key)),
            ];
            current = compute_parent_poseidon2(current, position, &siblings);
        }
        let fed_root_bb = current;
        let mut fed_root_bytes = [0u8; 32];
        fed_root_bytes[..4].copy_from_slice(&fed_root_bb.0.to_le_bytes());

        let mut builder =
            BridgePresentationBuilder::new_with_root_bb(key, fed_root_bytes, fed_root_bb);
        let token = MacaroonToken::mint(key, b"kid-163b", "dregg.fg-goose.online");
        builder.set_root_token(token);

        let request = AuthRequest {
            action: Some("anything".into()),
            ..Default::default()
        };
        let proof = builder.prove(&request).expect("prove should succeed");
        let wire = proof.into_wire_proof();
        let complete = verify_proof_complete(&wire, "anything", "", &fed_root_bytes, 0, 0);
        assert!(
            complete.is_ok(),
            "known AIR must continue to verify via verify_proof_complete, got {:?}",
            complete.err()
        );
    }

    #[test]
    fn test_ring_membership_unlinkable() {
        // Same issuer, two presentations: verify blinded_leaf is different (unlinkable).
        let key = test_key();
        let issuer_hash = bytes_to_babybear(&key);

        // Compute the Poseidon2-based federation root.
        let depth = 8;
        let mut current = issuer_hash;
        for i in 0..depth {
            let position = (i % 4) as u8;
            let siblings = [
                BabyBear::new(hash_index(i, 0, &key)),
                BabyBear::new(hash_index(i, 1, &key)),
                BabyBear::new(hash_index(i, 2, &key)),
            ];
            current = compute_parent_poseidon2(current, position, &siblings);
        }
        let fed_root_bb = current;
        let mut fed_root_bytes = [0u8; 32];
        fed_root_bytes[..4].copy_from_slice(&fed_root_bb.0.to_le_bytes());

        // Generate two proofs from the same issuer.
        let mut builder1 =
            BridgePresentationBuilder::new_with_root_bb(key, fed_root_bytes, fed_root_bb);
        let token1 = MacaroonToken::mint(key, b"kid-ring1", "dregg.fg-goose.online");
        builder1.set_root_token(token1);

        let mut builder2 =
            BridgePresentationBuilder::new_with_root_bb(key, fed_root_bytes, fed_root_bb);
        let token2 = MacaroonToken::mint(key, b"kid-ring2", "dregg.fg-goose.online");
        builder2.set_root_token(token2);

        let request = AuthRequest {
            action: Some("ring-test".into()),
            ..Default::default()
        };

        let proof1 = builder1.prove(&request).expect("proof1 should succeed");
        let proof2 = builder2.prove(&request).expect("proof2 should succeed");

        // Both should have real STARK proofs.
        assert!(proof1.has_real_stark_proof());
        assert!(proof2.has_real_stark_proof());

        // Both should verify successfully against the federation root.
        assert!(
            verify_presentation_bb(&proof1, fed_root_bb),
            "proof1 should verify against the federation root"
        );
        assert!(
            verify_presentation_bb(&proof2, fed_root_bb),
            "proof2 should verify against the federation root"
        );

        // The blinded ring-membership PIs are [blinded_leaf, root]. The blinded_leaf (pi[0]) should
        // be DIFFERENT between the two proofs — this is the unlinkability property!
        let pi1 = dregg_circuit::presentation::descriptor_wire_pis(
            &proof1
                .real_stark_proof
                .as_ref()
                .unwrap()
                .blinded_membership
                .vk,
        )
        .expect("blinded ring-membership vk decodes");
        let pi2 = dregg_circuit::presentation::descriptor_wire_pis(
            &proof2
                .real_stark_proof
                .as_ref()
                .unwrap()
                .blinded_membership
                .vk,
        )
        .expect("blinded ring-membership vk decodes");
        assert_ne!(
            pi1[0], pi2[0],
            "Same issuer's two presentations must have different blinded_leaf (unlinkable)"
        );

        // But the federation root (pi[1]) should be the SAME.
        assert_eq!(
            pi1[1], pi2[1],
            "Both proofs should have the same federation root"
        );

        // The descriptor predicate should be the blinded ring-membership family.
        assert!(
            proof1
                .real_stark_proof
                .as_ref()
                .unwrap()
                .blinded_membership
                .predicate
                .starts_with(dregg_circuit::blinded_membership_witness::BLINDED_4ARY_NAME_PREFIX),
            "Proof should use the blinded ring-membership descriptor"
        );
    }

    #[test]
    fn test_ring_membership_verifies_against_federation_root() {
        // A blinded proof should verify against the correct federation root.
        let key = test_key();
        let issuer_hash = bytes_to_babybear(&key);

        let depth = 8;
        let mut current = issuer_hash;
        for i in 0..depth {
            let position = (i % 4) as u8;
            let siblings = [
                BabyBear::new(hash_index(i, 0, &key)),
                BabyBear::new(hash_index(i, 1, &key)),
                BabyBear::new(hash_index(i, 2, &key)),
            ];
            current = compute_parent_poseidon2(current, position, &siblings);
        }
        let fed_root_bb = current;
        let mut fed_root_bytes = [0u8; 32];
        fed_root_bytes[..4].copy_from_slice(&fed_root_bb.0.to_le_bytes());

        let mut builder =
            BridgePresentationBuilder::new_with_root_bb(key, fed_root_bytes, fed_root_bb);
        let token = MacaroonToken::mint(key, b"kid-verify", "dregg.fg-goose.online");
        builder.set_root_token(token);

        let request = AuthRequest {
            action: Some("verify-test".into()),
            ..Default::default()
        };

        let proof = builder.prove(&request).expect("proof should succeed");

        // Verify against correct root succeeds.
        assert!(
            verify_presentation_bb(&proof, fed_root_bb),
            "Blinded proof should verify against correct federation root"
        );

        // Verify against wrong root fails.
        assert!(
            !verify_presentation_bb(&proof, BabyBear::new(99999)),
            "Blinded proof should fail against wrong federation root"
        );
    }

    #[test]
    fn test_ring_membership_invalid_issuer_fails() {
        // An issuer NOT in the tree should fail proof generation.
        let key = test_key();
        let wrong_root = test_federation_root(); // This won't match the synthetic path

        let mut builder = BridgePresentationBuilder::new(key, wrong_root);
        let token = MacaroonToken::mint(key, b"kid-invalid", "dregg.fg-goose.online");
        builder.set_root_token(token);

        let request = AuthRequest {
            action: Some("invalid-test".into()),
            ..Default::default()
        };

        // prove() should fail because the issuer is not in the federation
        // (wrong_root doesn't match the synthetic Poseidon2 path).
        let result = builder.prove(&request);
        assert!(
            result.is_err(),
            "Proof generation should fail for non-member issuer"
        );
    }

    #[test]
    fn test_compute_revealed_facts_commitment_empty() {
        // Empty facts should produce ZERO commitment.
        let commitment = super::compute_revealed_facts_commitment(&[]);
        assert!(commitment.is_zero());
    }

    #[test]
    fn test_compute_revealed_facts_commitment_deterministic() {
        use dregg_trace::{Fact, Term, symbol_from_str};

        let facts = vec![
            Fact::new(
                symbol_from_str("service"),
                vec![Term::Const(symbol_from_str("dns"))],
            ),
            Fact::new(
                symbol_from_str("action"),
                vec![Term::Const(symbol_from_str("read"))],
            ),
        ];

        let c1 = super::compute_revealed_facts_commitment(&facts);
        let c2 = super::compute_revealed_facts_commitment(&facts);
        assert_eq!(c1, c2, "commitment must be deterministic");
        assert!(
            !c1.is_zero(),
            "non-empty facts must produce non-zero commitment"
        );
    }

    #[test]
    fn test_compute_revealed_facts_commitment_different_facts_differ() {
        use dregg_trace::{Fact, Term, symbol_from_str};

        let facts_a = vec![Fact::new(
            symbol_from_str("service"),
            vec![Term::Const(symbol_from_str("dns"))],
        )];
        let facts_b = vec![Fact::new(
            symbol_from_str("service"),
            vec![Term::Const(symbol_from_str("storage"))],
        )];

        let ca = super::compute_revealed_facts_commitment(&facts_a);
        let cb = super::compute_revealed_facts_commitment(&facts_b);
        assert_ne!(ca, cb, "different facts must produce different commitments");
    }

    #[test]
    fn test_verify_revealed_facts_commitment_matches() {
        use dregg_trace::{Fact, Term, symbol_from_str};

        let facts = vec![Fact::new(
            symbol_from_str("app"),
            vec![Term::Const(symbol_from_str("myapp"))],
        )];

        let commitment = super::compute_revealed_facts_commitment(&facts);
        assert!(
            super::verify_revealed_facts_commitment(&facts, commitment),
            "same facts should verify against their own commitment"
        );
    }

    #[test]
    fn test_verify_revealed_facts_commitment_rejects_wrong_facts() {
        use dregg_trace::{Fact, Term, symbol_from_str};

        let real_facts = vec![Fact::new(
            symbol_from_str("app"),
            vec![Term::Const(symbol_from_str("myapp"))],
        )];
        let fake_facts = vec![Fact::new(
            symbol_from_str("app"),
            vec![Term::Const(symbol_from_str("evil"))],
        )];

        let commitment = super::compute_revealed_facts_commitment(&real_facts);
        assert!(
            !super::verify_revealed_facts_commitment(&fake_facts, commitment),
            "different facts must NOT verify against the original commitment"
        );
    }

    #[test]
    fn test_verify_revealed_facts_commitment_order_sensitive() {
        use dregg_trace::{Fact, Term, symbol_from_str};

        let facts_ab = vec![
            Fact::new(
                symbol_from_str("a"),
                vec![Term::Const(symbol_from_str("x"))],
            ),
            Fact::new(
                symbol_from_str("b"),
                vec![Term::Const(symbol_from_str("y"))],
            ),
        ];
        let facts_ba = vec![
            Fact::new(
                symbol_from_str("b"),
                vec![Term::Const(symbol_from_str("y"))],
            ),
            Fact::new(
                symbol_from_str("a"),
                vec![Term::Const(symbol_from_str("x"))],
            ),
        ];

        let ca = super::compute_revealed_facts_commitment(&facts_ab);
        let cb = super::compute_revealed_facts_commitment(&facts_ba);
        // Order matters since Poseidon2 sponge is sequential.
        assert_ne!(
            ca, cb,
            "different ordering should produce different commitments"
        );
    }

    #[test]
    fn test_presentation_tag_unlinkable_multi_show() {
        // Phase 2 unlinkability test: same cipherclerk, same token, two presentations
        // must produce different presentation_tags. Both proofs must verify.
        let key = test_key();
        let issuer_hash = bytes_to_babybear(&key);

        // Compute the Poseidon2-based federation root.
        let depth = 8;
        let mut current = issuer_hash;
        for i in 0..depth {
            let position = (i % 4) as u8;
            let siblings = [
                BabyBear::new(hash_index(i, 0, &key)),
                BabyBear::new(hash_index(i, 1, &key)),
                BabyBear::new(hash_index(i, 2, &key)),
            ];
            current = compute_parent_poseidon2(current, position, &siblings);
        }
        let fed_root_bb = current;
        let mut fed_root_bytes = [0u8; 32];
        fed_root_bytes[..4].copy_from_slice(&fed_root_bb.0.to_le_bytes());

        // Generate two presentations from the SAME token (same cipherclerk, same key).
        let mut builder1 =
            BridgePresentationBuilder::new_with_root_bb(key, fed_root_bytes, fed_root_bb);
        let token1 = MacaroonToken::mint(key, b"kid-tag-test", "dregg.fg-goose.online");
        builder1.set_root_token(token1);

        let mut builder2 =
            BridgePresentationBuilder::new_with_root_bb(key, fed_root_bytes, fed_root_bb);
        let token2 = MacaroonToken::mint(key, b"kid-tag-test", "dregg.fg-goose.online");
        builder2.set_root_token(token2);

        let request = AuthRequest {
            action: Some("tag-unlinkable".into()),
            ..Default::default()
        };

        let proof1 = builder1.prove(&request).expect("proof1 should succeed");
        let proof2 = builder2.prove(&request).expect("proof2 should succeed");

        // Both proofs should be cryptographically valid.
        assert!(proof1.has_real_stark_proof());
        assert!(proof2.has_real_stark_proof());

        // Both should verify against the federation root.
        assert!(
            verify_presentation_bb(&proof1, fed_root_bb),
            "proof1 should verify against federation root"
        );
        assert!(
            verify_presentation_bb(&proof2, fed_root_bb),
            "proof2 should verify against federation root"
        );

        // UNLINKABILITY: The presentation_tags must be DIFFERENT.
        // Same token, same action, but fresh randomness per presentation.
        let tag1 = proof1.circuit_proof.public_inputs.presentation_tag;
        let tag2 = proof2.circuit_proof.public_inputs.presentation_tag;
        assert_ne!(
            tag1, tag2,
            "Same token, two presentations must produce different presentation_tags (unlinkable)"
        );

        // ALSO: the blinded_leaf in the ring-membership descriptor should differ (unlinkability).
        let stark_pi1 = dregg_circuit::presentation::descriptor_wire_pis(
            &proof1
                .real_stark_proof
                .as_ref()
                .unwrap()
                .blinded_membership
                .vk,
        )
        .expect("blinded ring-membership vk decodes");
        let stark_pi2 = dregg_circuit::presentation::descriptor_wire_pis(
            &proof2
                .real_stark_proof
                .as_ref()
                .unwrap()
                .blinded_membership
                .vk,
        )
        .expect("blinded ring-membership vk decodes");
        assert_ne!(
            stark_pi1[0], stark_pi2[0],
            "Same issuer's two presentations must have different blinded_leaf"
        );

        // But the federation root (pi[1]) should be the same.
        assert_eq!(
            stark_pi1[1], stark_pi2[1],
            "Both proofs should have the same federation root"
        );
    }
}

// =============================================================================
// Gate-3 RUNTIME round-trip: the `StarkProof` → `Ir2BatchProof` wire flip for the
// bridge issuer-membership producer, consumed through THIS cluster's verifiers.
// =============================================================================
#[cfg(test)]
mod ir2_issuer_wire_roundtrip {
    //! The build cannot see this flip: the issuer-membership proof blob is an
    //! OPAQUE `Vec<u8>`, so the byte-format change (`stark::proof_to_bytes(StarkProof)`
    //! → `postcard(Ir2BatchProof)`) and the air-name→predicate dispatch are invisible
    //! to `cargo build`. This is the gate the build can't provide: a REAL
    //! [`prove_issuer_membership_ir2`] proof, serialized, then consumed/verified
    //! through the deployed `verify_vm_descriptor2` via the FLIPPED
    //! [`crate::verifier::StarkProofVerifier`]/[`crate::verifier::DslAwareProofVerifier`]
    //! `verify_with_predicate` route (which delegates to
    //! [`crate::verifier::DescriptorDispatchVerifier`]). Honest ACCEPT, and every
    //! wrong case (missing predicate, unknown predicate, cross-kind descriptor,
    //! forged root, tampered blob, malformed VK) REJECTED — non-vacuous.

    use super::*;
    use crate::verifier::{DescriptorDispatchVerifier, DslAwareProofVerifier, StarkProofVerifier};
    use dregg_circuit::membership_descriptor_4ary::membership_root_4ary;
    use dregg_turn::ProofVerifier;
    use std::sync::Arc;

    /// A deterministic depth-`d` 4-ary authentication path: fixed leaf, distinct
    /// siblings, cycling positions ∈ {0,1,2,3}. Returns `(leaf, siblings, positions, root)`
    /// where `root` is the deployed `hash_4_to_1`-chained root.
    fn fixture(depth: usize) -> (BabyBear, Vec<[BabyBear; 3]>, Vec<u8>, BabyBear) {
        let leaf = BabyBear::new(0xABCD);
        let siblings: Vec<[BabyBear; 3]> = (0..depth)
            .map(|i| {
                let b = 1000 + (i as u32) * 3;
                [BabyBear::new(b), BabyBear::new(b + 1), BabyBear::new(b + 2)]
            })
            .collect();
        let positions: Vec<u8> = (0..depth).map(|i| (i % 4) as u8).collect();
        let root = membership_root_4ary(leaf, &siblings, &positions);
        (leaf, siblings, positions, root)
    }

    /// PRIMARY GATE — a real IR-v2 issuer-membership proof, wired producer→consumer
    /// through the FLIPPED `StarkProofVerifier`/`DslAwareProofVerifier`
    /// `verify_with_predicate`. Honest ACCEPT + every wrong case REJECTED.
    #[test]
    fn issuer_membership_ir2_wire_accepts_honest_rejects_wrong() {
        let depth = 4usize;
        let (leaf, siblings, positions, root) = fixture(depth);

        // PRODUCER: real prove → `postcard(Ir2BatchProof)` blob + predicate + VK.
        let wire = prove_issuer_membership_ir2(leaf, &siblings, &positions)
            .expect("honest issuer membership must prove");
        assert_eq!(
            wire.predicate, "merkle-membership::poseidon2-4ary-general-depth4",
            "descriptor identity names the 4-ary depth-general family + depth"
        );
        // VK is exactly `[leaf, root]` as canonical LE-u32 limbs.
        let mut expected_vk = Vec::new();
        expected_vk.extend_from_slice(&leaf.0.to_le_bytes());
        expected_vk.extend_from_slice(&root.0.to_le_bytes());
        assert_eq!(wire.vk, expected_vk, "VK commits [leaf, root]");

        let stark_v = StarkProofVerifier::new();
        let dsl_v = DslAwareProofVerifier::new(Arc::new(dregg_dsl_runtime::ProgramRegistry::new()));
        let desc_v = DescriptorDispatchVerifier::new();

        // ACCEPT — the flipped StarkProofVerifier consumer, keyed on predicate identity.
        assert!(
            stark_v.verify_with_predicate(&wire.predicate, &wire.blob, "read", "res", &wire.vk),
            "StarkProofVerifier::verify_with_predicate must ACCEPT the honest IR-v2 proof"
        );
        // ACCEPT — the flipped DslAwareProofVerifier consumer.
        assert!(
            dsl_v.verify_with_predicate(&wire.predicate, &wire.blob, "read", "res", &wire.vk),
            "DslAwareProofVerifier::verify_with_predicate must ACCEPT the honest IR-v2 proof"
        );
        // ACCEPT — the reference descriptor-dispatch consumer directly.
        assert!(
            desc_v.verify_with_predicate(&wire.predicate, &wire.blob, "read", "res", &wire.vk),
            "DescriptorDispatchVerifier must ACCEPT the honest IR-v2 proof"
        );

        // REJECT — legacy predicate-LESS path: the Ir2 blob is not a StarkProof, and
        // without a predicate there is no descriptor to name. This is the load-bearing
        // contrast: the SAME blob the predicate path accepts is refused here, proving the
        // threaded predicate is what makes descriptor verification possible.
        assert!(
            !stark_v.verify(&wire.blob, "read", "res", &wire.vk),
            "StarkProofVerifier::verify (no predicate) must REJECT the IR-v2 blob"
        );

        // REJECT — unknown predicate (fail-closed dispatch miss, never silent accept).
        assert!(
            !stark_v.verify_with_predicate(
                "no-such-predicate::v0",
                &wire.blob,
                "read",
                "res",
                &wire.vk
            ),
            "an unknown predicate must fail closed at dispatch"
        );

        // REJECT — cross-KIND: a real but WRONG descriptor name.
        assert!(
            !stark_v.verify_with_predicate(
                "dfa-routing-toggle-2state::poseidon2-v1",
                &wire.blob,
                "read",
                "res",
                &wire.vk
            ),
            "the IR-v2 proof under the wrong-KIND descriptor must be REJECTED"
        );

        // REJECT — forged expected root (leaf is not a member under this root).
        let mut forged_vk = Vec::new();
        forged_vk.extend_from_slice(&leaf.0.to_le_bytes());
        forged_vk.extend_from_slice(&BabyBear::new_canonical(root.0 ^ 1).0.to_le_bytes());
        assert!(
            !stark_v.verify_with_predicate(&wire.predicate, &wire.blob, "read", "res", &forged_vk),
            "a forged expected root must be REJECTED"
        );

        // REJECT — tampered blob (bit-flip in the postcard bytes).
        let mut tampered = wire.blob.clone();
        let mid = tampered.len() / 2;
        tampered[mid] ^= 0xFF;
        assert!(
            !stark_v.verify_with_predicate(&wire.predicate, &tampered, "read", "res", &wire.vk),
            "a tampered blob must be REJECTED"
        );

        // REJECT — malformed VK (not a positive multiple of 4 bytes).
        assert!(
            !stark_v.verify_with_predicate(&wire.predicate, &wire.blob, "read", "res", &[1, 2, 3]),
            "a malformed VK must be REJECTED"
        );

        // Object-safety: the flipped route survives `Box<dyn ProofVerifier>` — the
        // exact shape the executor stores.
        let boxed: Box<dyn ProofVerifier> = Box::new(StarkProofVerifier::new());
        assert!(
            boxed.verify_with_predicate(&wire.predicate, &wire.blob, "read", "res", &wire.vk),
            "trait-object dispatch must ACCEPT the honest IR-v2 proof"
        );
    }

    /// THE ACTUAL PRESENT PATH — the real [`BridgePresentationBuilder`] issuer
    /// `MerkleWitness` (its synthetic depth-8 4-ary federation path) is re-expressed
    /// as the IR-v2 wire and verified through the flipped consumer. Proves the
    /// producer is fed by the genuine present-side membership construction, and that
    /// the IR-v2 root is byte-equal to the federation root the builder committed.
    #[test]
    fn builder_issuer_membership_ir2_wire_roundtrips() {
        // Reproduce the builder's synthetic depth-8 federation root (same
        // `compute_parent_poseidon2` chain the synthetic membership path validates).
        let key = [7u8; 32];
        let issuer_hash = bytes_to_babybear(&key);
        let mut current = issuer_hash;
        for i in 0..8usize {
            let position = (i % 4) as u8;
            let siblings = [
                BabyBear::new(hash_index(i, 0, &key)),
                BabyBear::new(hash_index(i, 1, &key)),
                BabyBear::new(hash_index(i, 2, &key)),
            ];
            current = compute_parent_poseidon2(current, position, &siblings);
        }
        let fed_root_bb = current;
        let fed_root_bytes = bb_to_bytes(fed_root_bb);

        let builder = BridgePresentationBuilder::new_with_root_bb(key, fed_root_bytes, fed_root_bb);

        // PRODUCER: the real builder issuer witness → IR-v2 wire.
        let wire = builder
            .prove_issuer_membership_ir2_wire()
            .expect("builder issuer membership must prove");
        assert_eq!(
            wire.predicate, "merkle-membership::poseidon2-4ary-general-depth8",
            "synthetic federation path is depth 8"
        );

        // The IR-v2 root (VK's second limb) is BYTE-EQUAL to the federation root
        // the builder committed — the binding the migration must preserve.
        let root_limb = u32::from_le_bytes([wire.vk[4], wire.vk[5], wire.vk[6], wire.vk[7]]);
        assert_eq!(
            BabyBear::new_canonical(root_limb),
            fed_root_bb,
            "IR-v2 membership root must equal the committed federation root"
        );

        // CONSUMER: honest ACCEPT through the flipped StarkProofVerifier route.
        let stark_v = StarkProofVerifier::new();
        assert!(
            stark_v.verify_with_predicate(&wire.predicate, &wire.blob, "read", "res", &wire.vk),
            "the real builder's IR-v2 issuer proof must ACCEPT"
        );

        // Non-vacuous: a forged federation root is REJECTED.
        let mut forged_vk = wire.vk.clone();
        forged_vk[4] ^= 0x01;
        assert!(
            !stark_v.verify_with_predicate(&wire.predicate, &wire.blob, "read", "res", &forged_vk),
            "a forged federation root must be REJECTED"
        );
    }

    /// End-to-end prove+verify for EVERY comparison operator now that each has an emitted descriptor.
    /// A TRUE statement proves and verifies; a FALSE statement either fails to prove (`None`) or
    /// produces a proof that fails to verify — non-vacuous both poles. This exercises the wired
    /// `prove_predicate_for_fact` / `verify_predicate_proof` onto the new descriptors.
    #[test]
    fn comparison_predicates_prove_and_verify_end_to_end() {
        let terms = FactTerms {
            predicate_sym: BabyBear::new(0xABCD),
            term1: BabyBear::new(0x11),
            term2: BabyBear::new(0x22),
        };
        let state_root = BabyBear::new(0x1234);
        let binding = terms.bind(state_root);

        // (value, predicate, expected-true).
        let cases: &[(u32, Predicate, bool)] = &[
            (100, Predicate::Gte(40), true),
            (30, Predicate::Gte(40), false),
            (40, Predicate::Lte(100), true),
            (110, Predicate::Lte(100), false),
            (101, Predicate::Gt(40), true),
            (40, Predicate::Gt(40), false),
            (40, Predicate::Lt(101), true),
            (101, Predicate::Lt(101), false),
            (41, Predicate::Neq(40), true),
            (40, Predicate::Neq(40), false),
            (40, Predicate::InRange(10, 100), true),
            (5, Predicate::InRange(10, 100), false),
            (150, Predicate::InRange(10, 100), false),
        ];

        for (value, predicate, expect_true) in cases {
            println!("-- case: value={value} {predicate:?} expect_true={expect_true}");
            // A fresh per-showing blinding, as production draws it.
            let blinding = fresh_predicate_blinding();
            // The commitment a verifier derives from token state for THIS value's fact, opened with
            // the blinding the proof carries. It is value-dependent: that dependence is the weld.
            let fc = binding.commitment_of(BabyBear::from_u64(*value as u64), blinding);
            let proof = prove_predicate_for_fact(*value, binding, blinding, predicate);
            if *expect_true {
                let proof = proof
                    .unwrap_or_else(|| panic!("true statement {value} {predicate:?} must PROVE"));
                assert!(
                    verify_predicate_proof(&proof, fc),
                    "true statement {value} {predicate:?} must VERIFY"
                );
                // Non-vacuity: a forged expected fact commitment REJECTS.
                assert!(
                    !verify_predicate_proof(&proof, BabyBear::new(0xDEAD)),
                    "a forged fact commitment must REJECT for {predicate:?}"
                );
            } else {
                // A false statement either cannot be proved, or its proof fails to verify.
                let rejected = match proof {
                    None => true,
                    Some(p) => !verify_predicate_proof(&p, fc),
                };
                assert!(
                    rejected,
                    "false statement {value} {predicate:?} must be REJECTED"
                );
            }
        }
    }
}
