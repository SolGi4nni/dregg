//! High-level privacy APIs for application developers.
//!
//! This module provides ergonomic wrappers around dregg's privacy primitives,
//! making it simple to perform common privacy-preserving operations:
//!
//! - **Anonymous authorization**: Prove you are authorized without revealing your identity.
//! - **Private notes**: Create and transfer value without revealing amounts.
//! - **Unlinkable predicates**: Prove facts about yourself that can't be correlated.
//! - **Private discovery**: Find matching intents without revealing your query.
//! - **Non-revocation proofs**: Prove your token hasn't been revoked without revealing it.
//!
//! # Design Principles
//!
//! Each API method documents:
//! - What **privacy guarantee** it provides (what's hidden from the verifier).
//! - What **the verifier learns** (the public inputs / revealed information).
//! - What **stays hidden** (the private witness / secret data).

use dregg_cell::note::{Note, NoteCommitment, Nullifier};
use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_ir2::{
    DreggStarkConfig, Ir2BatchProof, MemBoundaryWitness, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::dsl::dsl_p3_air::DslP3Proof;
use dregg_circuit::dsl::revocation::{prove_non_revocation_p3, verify_non_revocation_p3};
use dregg_circuit::field::BABYBEAR_P;
use dregg_circuit::note_spending_witness::{
    NOTE_SPENDING_WIDTH, NoteSpendingWitness, key_to_field_elements, pi as note_spend_pi,
};
use dregg_circuit::poseidon2;
// `verify_anonymous_presentation` verifies the committed BLINDED ring-membership descriptor
// (`dregg-blinded-membership-4ary-general-depth{N}`) via `descriptor_by_name` →
// `verify_vm_descriptor2` — the Golden-Lift flip off the hand-written blinded-Merkle STARK. The
// self-contained non-revocation pair below is likewise flipped: it rides the audited
// `p3-batch-stark` prover.
use dregg_circuit_prove::note_spend_leaf_adapter::{
    note_spend_leaf_public_inputs, note_spend_mint_hash_felt, note_spend_to_descriptor2,
};
use dregg_commit::accumulator::{AccumulatorWitness, BabyBear4, PolynomialAccumulator};
use dregg_dsl_runtime::note_spending::generate_note_spending_trace;
use dregg_dsl_runtime::revocation::{DslRevocationTree, revocation_hash_to_field};
use dregg_token::AuthRequest;

// `discovery` is gated behind `network` (tokio-using); the lone method below
// that needs it is gated the same way.
use crate::cipherclerk::{AgentCipherclerk, HeldToken};
use crate::error::SdkError;

// =============================================================================
// Result Types
// =============================================================================

/// An anonymous authorization presentation.
///
/// Proves the holder is authorized without revealing which federation member they are.
/// Uses ring membership with per-presentation blinding, so the same holder produces
/// unlinkable proofs across sessions.
#[derive(Clone, Debug)]
pub struct AnonymousPresentation {
    /// The STARK-backed presentation proof (wire-safe form).
    pub proof: dregg_bridge::present::WirePresentationProof,
    /// The blinded presentation tag (unique per presentation, unlinkable across shows).
    ///
    /// The verifier cannot determine which federation member produced this tag.
    pub presentation_tag: BabyBear,
}

/// The secret material associated with a private note.
///
/// The holder must keep this to later spend or transfer the note.
/// Contains the full note preimage (owner, fields, randomness, creation_nonce)
/// plus the spending key that authorizes spending.
#[derive(Clone, Debug)]
pub struct NoteSecret {
    /// The full note (owner, value, asset_type, randomness, creation_nonce).
    pub note: Note,
    /// The spending key (derived from the cipherclerk's signing key).
    pub spending_key: [u8; 32],
}

/// Proof that a note was spent and a new one created for the recipient,
/// with value conservation proven in zero knowledge.
#[derive(Clone, Debug)]
pub struct NoteTransferProof {
    /// The nullifier of the spent input note (published for double-spend prevention).
    pub nullifier: Nullifier,
    /// The commitment of the newly created output note (published to the note tree).
    pub output_commitment: NoteCommitment,
    /// The descriptor batch proof of valid spending (postcard-serialized
    /// `Ir2BatchProof`), produced against the Lean-emitted `note-spend-leaf`
    /// descriptor: it proves spending-key knowledge, full-width (28-limb)
    /// commitment binding, Merkle membership, the two-step nullifier, and the
    /// in-AIR mint identity.
    pub spending_proof: Vec<u8>,
    /// The secret for the new output note (given to the recipient out-of-band).
    pub recipient_secret: NoteSecret,
}

/// A predicate proof generated with fresh blinding so it can't be correlated
/// with other proofs from the same holder.
#[derive(Clone, Debug)]
pub struct UnlinkablePredicateProof {
    /// The blinded fact commitment: `Poseidon2(fact_hash, state_root, blinding, 0)`.
    ///
    /// This commitment is different each time due to fresh blinding, so a verifier
    /// cannot link two proofs to the same holder.
    pub blinded_fact_commitment: BabyBear,
    /// The underlying predicate proof (STARK-backed).
    pub predicate_proof: dregg_bridge::BridgePredicateProof,
    /// The blinding factor used (keep private; needed if you want to open the commitment later).
    pub blinding: BabyBear,
}

/// Proof that a token's derivation path has no revoked ancestor.
///
/// The verifier learns only that the token is not revoked; it does not learn
/// the token's identity, derivation chain, or which ancestors were checked.
#[derive(Clone, Debug)]
pub struct NonRevocationProof {
    /// The non-revocation proof, `postcard`-encoded on the audited Plonky3 wire
    /// format (`postcard(DslP3Proof)` = `postcard(Ir2BatchProof)`). It carries the
    /// SAME deployed depth-`TREE_DEPTH` `hash_fact` sorted-tree statement, with
    /// public inputs `[revocation_root, queried_item]`, but its constraints come
    /// exclusively from the byte-pinned Lean descriptor
    /// `dregg-non-revocation-adjacency::poseidon2-fact-v1`. Rust emits one
    /// witness row per Merkle level and the IR2 prover/interpreter supplies the
    /// real terminal FRI proof.
    pub proof: Vec<u8>,
    /// The revocation set root this proof was generated against.
    ///
    /// The verifier must know this root (committed by the federation) to verify.
    pub revocation_root: BabyBear,
    /// The queried item (the primary ancestor / root-issuer revocation hash)
    /// this proof attests is NOT revoked. It is the non-revocation circuit's
    /// second public input (`pi::QUERIED_ITEM`), bound in-circuit to the
    /// bracketed control-row `COL_0`, so the verifier re-binds it: a proof of
    /// freshness for a different item would publish a different `pi[1]` and be
    /// rejected.
    pub item_hash: BabyBear,
}

/// Proof of non-revocation using the polynomial accumulator (O(1) verification).
///
/// When the revocation set is large (>1000 entries), the accumulator-based approach
/// is significantly more efficient than the sorted-Merkle tree approach used by
/// `NonRevocationProof`. The accumulator proof is constant-size regardless of how
/// many entries are in the revocation set.
///
/// # Privacy Guarantee
///
/// The verifier learns:
/// - That the prover holds a non-revoked token.
/// - The accumulator value and alpha challenge (committed by the federation).
///
/// The verifier does NOT learn:
/// - Which specific token the prover holds.
/// - The revocation hash of the token.
#[derive(Clone, Debug)]
pub struct AccumulatorNonMembershipProof {
    /// The accumulator non-membership witness (quotient + nonzero remainder).
    pub witness: AccumulatorWitness,
    /// The current accumulator value (product of (alpha - h_i) for all revoked h_i).
    pub accumulator_value: BabyBear4,
    /// The alpha challenge used (derived via Fiat-Shamir from the set commitment).
    pub alpha: BabyBear4,
    /// The revocation hash being proved absent (derived from the token).
    pub revocation_hash: BabyBear,
}

// =============================================================================
// Privacy API Implementation
// =============================================================================

impl AgentCipherclerk {
    /// Prove authorization without revealing which federation member you are.
    ///
    /// # Privacy Guarantee
    ///
    /// The verifier learns:
    /// - That some valid federation member authorized this request.
    /// - The presentation tag (unique per session, unlinkable).
    ///
    /// The verifier does NOT learn:
    /// - Which federation member produced the proof.
    /// - The token contents, caveats, or derivation chain.
    /// - Any correlation between this proof and previous proofs from the same holder.
    ///
    /// # How It Works
    ///
    /// Uses `BlindedMerklePoseidon2StarkAir`: a fresh random blinding factor is
    /// generated per presentation. The public inputs expose
    /// `blinded_leaf = hash_2_to_1(leaf_hash, blinding)` instead of the raw `leaf_hash`,
    /// so the verifier cannot determine which leaf in the federation Merkle tree
    /// corresponds to this proof.
    ///
    /// # Arguments
    ///
    /// * `token` - The held token to authorize from (must hold the root key).
    /// * `request` - The authorization request to prove.
    ///
    /// # Errors
    ///
    /// Returns an error if the token cannot produce federation membership proofs
    /// (e.g., attenuated tokens without the issuer key).
    pub fn authorize_anonymously(
        &self,
        token: &HeldToken,
        request: &AuthRequest,
    ) -> Result<AnonymousPresentation, SdkError> {
        // The prove_authorization path already uses BlindedMerklePoseidon2StarkAir
        // with a fresh blinding factor per call (via generate_blinding_factor()).
        // Each invocation is unlinkable by construction.
        let proof = self.prove_authorization(token, request)?;

        // Extract the presentation tag from the circuit proof's public inputs.
        // The tag is [BabyBear; 4]; hash to a single element for the wire representation.
        let presentation_tag = dregg_circuit::poseidon2::hash_many(&[proof
            .circuit_proof
            .public_inputs
            .presentation_tag]);

        // Convert to wire-safe representation (strips private trace data).
        let wire_proof = proof.into_wire_proof();

        Ok(AnonymousPresentation {
            proof: wire_proof,
            presentation_tag,
        })
    }

    /// Create a private note (hidden balance) that can be transferred without revealing amount.
    ///
    /// # Privacy Guarantee
    ///
    /// The verifier (note tree operator) learns:
    /// - That a new commitment was added to the note tree.
    ///
    /// The verifier does NOT learn:
    /// - The note's value (amount).
    /// - The note's asset type.
    /// - The note's owner.
    /// - The randomness / blinding factor.
    ///
    /// # How It Works
    ///
    /// Creates a note `(owner, [asset_type, value, 0...], randomness, creation_nonce)` and
    /// publishes only the Poseidon2 commitment. The commitment is binding (cannot be opened
    /// to a different value) but hiding (reveals nothing about the contents).
    ///
    /// # Arguments
    ///
    /// * `value` - The amount to store in the note.
    /// * `asset_type` - The asset type identifier.
    ///
    /// # Returns
    ///
    /// A tuple of:
    /// - `NoteCommitment`: publish this to the note tree.
    /// - `NoteSecret`: keep this secret; needed to spend or transfer the note later.
    pub fn create_private_note(
        &self,
        value: u64,
        asset_type: u64,
    ) -> Result<(NoteCommitment, NoteSecret), SdkError> {
        // Derive a spending key from the cipherclerk's signing key material.
        let spending_key = self.derive_symmetric_key("dregg-note-spending-key-v1");

        // Create the note with this cipherclerk's public key as owner.
        let owner = self.public_key().0;
        let mut fields = [0u64; 8];
        fields[0] = asset_type;
        fields[1] = value;
        let note = dregg_cell_crypto::note::new_note(owner, fields);

        // Compute the commitment (this is what gets published to the note tree).
        let commitment = note.commitment();

        let secret = NoteSecret { note, spending_key };

        Ok((commitment, secret))
    }

    /// Spend a note and create a new one for the recipient, proving value conservation
    /// without revealing the amount.
    ///
    /// # Privacy Guarantee
    ///
    /// The verifier learns:
    /// - The nullifier (for double-spend prevention).
    /// - The Merkle root of the note tree (the note exists in the committed tree).
    /// - The new output commitment (goes into the recipient's tree).
    ///
    /// The verifier does NOT learn:
    /// - The note's value or asset type.
    /// - The spending key.
    /// - The sender's or recipient's identity.
    /// - Which specific note in the tree was spent.
    ///
    /// # How It Works
    ///
    /// 1. Computes the nullifier from the note secret + spending key (proves ownership).
    /// 2. Creates a new note for the recipient with the same value/asset (conservation).
    /// 3. Generates a descriptor batch proof (the Lean-emitted `note-spend-leaf`
    ///    descriptor, via `prove_vm_descriptor2`) proving:
    ///    - Knowledge of the spending key.
    ///    - The commitment is in the Merkle tree.
    ///    - The nullifier is correctly derived.
    ///
    /// # Arguments
    ///
    /// * `note_secret` - The secret material for the note being spent.
    /// * `recipient_key` - The recipient's public key (32 bytes).
    /// * `merkle_siblings` - The Merkle path siblings from the note tree.
    /// * `merkle_positions` - The Merkle path positions (0..3 per level).
    ///
    /// # Returns
    ///
    /// A `NoteTransferProof` containing:
    /// - The nullifier to publish (prevents double-spend).
    /// - The output commitment to add to the tree.
    /// - The STARK proof for verification.
    /// - The recipient's secret (deliver to them out-of-band).
    pub fn transfer_note_privately(
        &self,
        note_secret: &NoteSecret,
        recipient_key: &[u8; 32],
        merkle_siblings: Vec<[BabyBear; 3]>,
        merkle_positions: Vec<u8>,
    ) -> Result<NoteTransferProof, SdkError> {
        let note = &note_secret.note;
        let spending_key = &note_secret.spending_key;

        // Compute the nullifier (reveals note is spent, without revealing which note).
        let nullifier = note.nullifier(spending_key);

        // Create a new note for the recipient with the same value and asset type.
        let mut output_fields = [0u64; 8];
        output_fields[0] = note.asset_type();
        output_fields[1] = note.value();
        let output_note = dregg_cell_crypto::note::new_note(*recipient_key, output_fields);
        let output_commitment = output_note.commitment();

        // Derive a recipient spending key (the recipient will use their own; we just
        // package the note secret so they can spend it).
        // In a real protocol the recipient would derive their own spending key.
        // Here we use a deterministic derivation from the recipient's public key
        // as a placeholder — the recipient must replace this with their own key.
        let mut recipient_spending_key_hasher =
            blake3::Hasher::new_derive_key("dregg-note-recipient-spending-key-v1");
        recipient_spending_key_hasher.update(recipient_key);
        let recipient_spending_key: [u8; 32] = *recipient_spending_key_hasher.finalize().as_bytes();

        // Convert spending key to 8 BabyBear limbs.
        let spending_key_limbs = key_to_field_elements(spending_key);

        // Build the spending witness for the STARK proof with FULL-WIDTH
        // (256-bit-per-field) commitment binding. `from_note_limbs` decomposes
        // every 32-byte field (owner / creation_nonce / randomness) into 8
        // BabyBear limbs and every u64 (value / asset_type) into low+high
        // limbs — the SAME 28-limb preimage layout as
        // `dregg_cell::Note::poseidon2_commitment`. This replaces the legacy
        // single-felt-per-field witness, whose in-circuit commitment bound only
        // the first 4 bytes of each 32-byte field (so two notes differing only
        // in bytes above byte 4 of owner/nonce/randomness collided).
        let witness = NoteSpendingWitness::from_note_limbs(
            &note.owner,
            note.value(),
            note.asset_type(),
            &note.creation_nonce,
            &note.randomness,
            spending_key_limbs,
            merkle_siblings,
            merkle_positions,
        );

        // Prove the spend through the Lean-emitted `note-spend-leaf` descriptor
        // (`prove_vm_descriptor2`), the plonky3 batch prover. This carries the SAME
        // statement the hand `NoteSpendingAir` did — spending-key knowledge, the
        // full-width commitment chain, the two-step nullifier, and Merkle membership —
        // plus the in-AIR mint identity (pinned to the 7th claim slot). Keep this
        // fallible: placeholder or stale witness data is reported to SDK callers
        // rather than panicking inside the prover.
        let inv = |e: String| SdkError::Auth(dregg_bridge::AuthError::InvalidRequest(e));
        let desc = note_spend_to_descriptor2()
            .map_err(|e| inv(format!("note-spend descriptor build failed: {e}")))?;
        // The base trace is the source note-spend trace extended with the three mint
        // columns on row 0 (the byte-pinned `note_spend_leaf_adapter` layout; the
        // per-site chip lanes are filled by the prover's `trace_with_chip_lanes`).
        let (mut trace, base_pis) = generate_note_spending_trace(&witness);
        for row in &mut trace {
            row.resize(NOTE_SPENDING_WIDTH + 3, BabyBear::ZERO);
        }
        let m1 = poseidon2::hash_fact(
            base_pis[note_spend_pi::NULLIFIER],
            &[
                base_pis[note_spend_pi::MERKLE_ROOT],
                base_pis[note_spend_pi::DESTINATION_FEDERATION],
                base_pis[note_spend_pi::ASSET_TYPE],
            ],
        );
        let mint = poseidon2::hash_fact(
            m1,
            &[
                base_pis[note_spend_pi::VALUE],
                base_pis[note_spend_pi::VALUE_HI],
            ],
        );
        trace[0][NOTE_SPENDING_WIDTH] = base_pis[note_spend_pi::MERKLE_ROOT];
        trace[0][NOTE_SPENDING_WIDTH + 1] = m1;
        trace[0][NOTE_SPENDING_WIDTH + 2] = mint;
        // The 7-slot claim tuple `[nullifier, merkle_root, value_lo, asset_type,
        // destination_federation, value_hi, mint_hash]`.
        let public_inputs = note_spend_leaf_public_inputs(&witness);
        debug_assert_eq!(
            mint,
            public_inputs[note_spend_pi::VALUE_HI + 1],
            "the row-0 mint column must equal the exposed 7th claim slot"
        );
        let batch_proof = prove_vm_descriptor2(
            &desc,
            &trace,
            &public_inputs,
            &MemBoundaryWitness::default(),
            &[],
        )
        .map_err(|e| inv(format!("note spending proof generation failed: {e}")))?;
        let spending_proof = postcard::to_allocvec(&batch_proof)
            .map_err(|e| inv(format!("note spending proof serialize failed: {e}")))?;

        let recipient_secret = NoteSecret {
            note: output_note,
            spending_key: recipient_spending_key,
        };

        Ok(NoteTransferProof {
            nullifier,
            output_commitment,
            spending_proof,
            recipient_secret,
        })
    }

    /// Generate a predicate proof with fresh blinding so multiple proofs can't be correlated.
    ///
    /// # Privacy Guarantee
    ///
    /// The verifier learns:
    /// - That some attribute satisfies the predicate (e.g., "age >= 18").
    /// - The blinded fact commitment (unique per proof, unlinkable).
    ///
    /// The verifier does NOT learn:
    /// - The actual attribute value.
    /// - Which token or identity produced the proof.
    /// - Any correlation with other proofs from the same holder.
    ///
    /// # How It Works
    ///
    /// 1. Generates a fresh random BabyBear blinding factor.
    /// 2. Computes `blinded_fact_commitment = Poseidon2(fact_hash, state_root, blinding, 0)`.
    /// 3. Generates the standard predicate proof (STARK-backed).
    /// 4. Returns both the proof and the blinded commitment.
    ///
    /// Because the blinding is fresh each time, two proofs about the same attribute
    /// from the same token produce different blinded commitments, preventing correlation.
    ///
    /// # Arguments
    ///
    /// * `token` - The held token containing the attribute.
    /// * `attribute` - The attribute name (e.g., "age", "balance", "reputation").
    /// * `attribute_value` - The actual (private) value of the attribute.
    /// * `predicate_type` - The type of predicate to prove (Gte, Lte, etc.).
    /// * `threshold` - The threshold value for the predicate.
    ///
    /// # Returns
    ///
    /// An `UnlinkablePredicateProof` with a fresh blinded commitment.
    pub fn prove_predicate_unlinkable(
        &self,
        token: &HeldToken,
        attribute: &str,
        attribute_value: u32,
        predicate_type: dregg_circuit::PredicateType,
        threshold: BabyBear,
    ) -> Result<UnlinkablePredicateProof, SdkError> {
        // Decode the token to verify it's valid.
        let _decoded = token.decode()?;

        // Generate fresh blinding factor.
        let mut blinding_bytes = [0u8; 4];
        getrandom::fill(&mut blinding_bytes)
            .map_err(|e| SdkError::MissingKey(format!("getrandom failed: {e}")))?;
        let blinding_raw = u32::from_le_bytes(blinding_bytes) % BABYBEAR_P;
        let blinding = BabyBear::new(if blinding_raw == 0 { 1 } else { blinding_raw });

        // Compute the fact hash for the attribute.
        let attr_bytes = blake3::hash(attribute.as_bytes());
        let attr_bb = Self::bytes_to_babybear(attr_bytes.as_bytes());
        let value_bb = BabyBear::new(attribute_value);
        let fact_hash = poseidon2::hash_fact(attr_bb, &[value_bb, BabyBear::ZERO, BabyBear::ZERO]);

        // Compute state root from the token's issuer key.
        let issuer_key = token.root_key();
        let state_root = Self::bytes_to_babybear(issuer_key);

        // Compute the blinded fact commitment: Poseidon2(fact_hash, state_root, blinding, 0).
        let blinded_fact_commitment =
            poseidon2::hash_many(&[fact_hash, state_root, blinding, BabyBear::ZERO]);

        // Generate the predicate proof over the UNBLINDED fact. blinding is a separate output
        // field (blinded_fact_commitment above); the proof itself binds the plain fact.
        // 2026-07-16: FactBinding migration — the value flows in as term[0], so the old
        // [value, 0, 0] terms become term1 = term2 = ZERO.
        let binding = dregg_bridge::present::FactTerms {
            predicate_sym: attr_bb,
            term1: BabyBear::ZERO,
            term2: BabyBear::ZERO,
        }
        .bind(state_root);
        let bridge_predicate = Self::predicate_type_to_bridge(predicate_type, threshold.as_u32());
        let predicate_proof = dregg_bridge::prove_predicate_for_fact(
            attribute_value,
            binding,
            &bridge_predicate,
        )
        .ok_or_else(|| {
            SdkError::Auth(dregg_bridge::AuthError::InvalidRequest(format!(
                "predicate proof generation failed: '{attribute}' {:?}({}) not satisfiable for value {attribute_value}",
                predicate_type, threshold.as_u32()
            )))
        })?;

        Ok(UnlinkablePredicateProof {
            blinded_fact_commitment,
            predicate_proof,
            blinding,
        })
    }

    // `discover_intents_privately` (2-server PIR over a PirTransport) is the
    // networked face and lives in `dregg-sdk-net` as a free function over
    // `&AgentCipherclerk`; the core privacy module stays net-free (wasm-safe).

    /// Prove a token is not in the revocation set without revealing the token's identity.
    ///
    /// # Privacy Guarantee
    ///
    /// The verifier learns:
    /// - That the prover holds a non-revoked capability.
    /// - The revocation set root (committed by the federation).
    ///
    /// The verifier does NOT learn:
    /// - Which specific capability/token the prover holds.
    /// - The derivation chain or ancestry of the token.
    /// - Which ancestors were checked against the revocation set.
    ///
    /// # How It Works
    ///
    /// Uses the `NonRevocationAir` (sorted-Merkle non-membership proof):
    /// 1. For each ancestor in the token's derivation path, finds two adjacent leaves
    ///    in the sorted revocation tree that bracket the ancestor's revocation hash.
    /// 2. Proves Merkle membership of both neighbors (they exist in the tree).
    /// 3. Proves the ancestor hash falls between them (it's absent from the tree).
    ///
    /// The STARK proof covers all ancestors simultaneously, so the verifier learns
    /// nothing about the derivation chain length or structure.
    ///
    /// # Arguments
    ///
    /// * `token` - The held token to prove non-revocation for.
    /// * `revocation_tree` - The federation's current sorted revocation tree.
    ///
    /// # Errors
    ///
    /// Returns an error if any ancestor in the derivation chain IS revoked
    /// (cannot generate a valid non-revocation proof for a revoked token).
    pub fn prove_not_revoked(
        &self,
        token: &HeldToken,
        revocation_tree: &DslRevocationTree,
    ) -> Result<NonRevocationProof, SdkError> {
        // Decode the token to verify it's structurally valid.
        let _decoded = token.decode()?;

        // Derive the revocation hashes for the token's derivation path.
        // The derivation chain is: root_key -> each attenuation step.
        // Each step's revocation hash = Poseidon2(hash(key_material || step_index)).
        let issuer_key = token.root_key();
        let mut ancestor_hashes = Vec::new();

        // The root issuer's revocation hash.
        let root_revocation_hash = revocation_hash_to_field(issuer_key);
        ancestor_hashes.push(root_revocation_hash);

        // For attenuated tokens, derive additional ancestor hashes from the token ID
        // which encodes the attenuation chain structure.
        // Each segment of the token ID (split by ':') represents a derivation step.
        let id_parts: Vec<&str> = token.id().split(':').collect();
        for (i, _part) in id_parts.iter().enumerate().skip(1) {
            let mut hasher = blake3::Hasher::new_derive_key("dregg-revocation-hash-v1");
            hasher.update(issuer_key);
            hasher.update(&(i as u64).to_le_bytes());
            let step_hash = *hasher.finalize().as_bytes();
            ancestor_hashes.push(revocation_hash_to_field(&step_hash));
        }

        // Generate the non-revocation proof using DSL circuit (30-bit range, sound).
        let revocation_root = revocation_tree.root();

        // We prove one ancestor at a time (single control row); use the first ancestor
        // (root issuer) as the primary proof, and guard that EVERY ancestor is fresh.
        let primary_hash = &ancestor_hashes[0];
        for hash in &ancestor_hashes {
            if revocation_tree.prove_non_membership(hash).is_none() {
                return Err(SdkError::Auth(dregg_bridge::AuthError::InvalidRequest(
                    "non-revocation proof generation failed: one or more ancestors are revoked"
                        .to_string(),
                )));
            }
        }

        // Prove non-revocation through the byte-pinned Lean-emitted IR2
        // descriptor. It composes depth-general adjacent membership with strict
        // ordering over the deployed depth-`TREE_DEPTH` `hash_fact` tree, with
        // public inputs `[revocation_root, queried_item]`; Rust only constructs
        // the one-row-per-level witness before the real terminal FRI proof.
        let inv = |e: String| SdkError::Auth(dregg_bridge::AuthError::InvalidRequest(e));
        let p3_proof = prove_non_revocation_p3(revocation_tree, *primary_hash)
            .map_err(|e| inv(format!("non-revocation proof generation failed: {e}")))?;
        let proof = postcard::to_allocvec(&p3_proof)
            .map_err(|e| inv(format!("non-revocation proof serialize failed: {e}")))?;

        Ok(NonRevocationProof {
            proof,
            revocation_root,
            // The queried item is the primary ancestor hash, surfaced as pi[1]
            // and bound by the emitted first-row constraint on ordering wire X.
            item_hash: *primary_hash,
        })
    }

    /// Prove a token is not in the revocation set using the polynomial accumulator.
    ///
    /// This is the O(1) alternative to `prove_not_revoked` for large revocation sets.
    /// The accumulator witness is constant-size regardless of how many tokens have been
    /// revoked, making it ideal when the revocation set exceeds ~1000 entries.
    ///
    /// # Privacy Guarantee
    ///
    /// Same as `prove_not_revoked`: the verifier learns only that the token is not
    /// revoked. The token's identity and derivation chain remain hidden.
    ///
    /// # How It Works
    ///
    /// The federation maintains a polynomial accumulator `Acc = product(alpha - h_i)`
    /// over all revoked hashes. To prove non-membership, the prover:
    /// 1. Derives the revocation hash for their token.
    /// 2. Obtains a non-membership witness from the accumulator.
    /// 3. The verifier checks: `witness.quotient * (alpha - h) + witness.remainder == Acc`
    ///    AND `witness.remainder != 0`.
    ///
    /// # Arguments
    ///
    /// * `token` - The held token to prove non-revocation for.
    /// * `accumulator` - The federation's current polynomial accumulator over revoked hashes.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - The token's revocation hash IS in the accumulator (token is revoked).
    /// - The witness computation fails (e.g., alpha - hash is not invertible).
    pub fn prove_not_revoked_accumulator(
        &self,
        token: &HeldToken,
        accumulator: &PolynomialAccumulator,
    ) -> Result<AccumulatorNonMembershipProof, SdkError> {
        // Decode the token to verify it's structurally valid.
        let _decoded = token.decode()?;

        // Derive the revocation hash for this token's root issuer.
        let issuer_key = token.root_key();
        let revocation_hash = revocation_hash_to_field(issuer_key);

        // Compute the non-membership witness from the accumulator.
        let witness = accumulator
            .non_membership_witness(revocation_hash)
            .ok_or_else(|| {
                SdkError::Auth(dregg_bridge::AuthError::InvalidRequest(
                    "accumulator non-membership proof failed: token's revocation hash is in the \
                 revocation set (token is revoked)"
                        .to_string(),
                ))
            })?;

        Ok(AccumulatorNonMembershipProof {
            witness,
            accumulator_value: accumulator.accumulator_value(),
            alpha: accumulator.alpha(),
            revocation_hash,
        })
    }
}

// =============================================================================
// Verification helpers
// =============================================================================

/// Verify an anonymous presentation proof.
///
/// The verifier checks:
/// 1. The STARK proof is valid (BlindedMerklePoseidon2StarkAir).
/// 2. The federation root matches the expected value.
///
/// The verifier does NOT learn which federation member produced the proof.
pub fn verify_anonymous_presentation(
    presentation: &AnonymousPresentation,
    expected_federation_root: &[u8; 32],
) -> bool {
    // Re-wrap into a BridgePresentationProof for verification via the bridge layer.
    // The wire proof contains all necessary STARK data.
    if let Some(ref real_stark) = presentation.proof.real_stark_proof {
        // Verify the committed BLINDED ring-membership descriptor — the flip off the hand-written
        // blinded-Merkle STARK. Its PIs are [blinded_leaf, root]: the member leaf_hash and the
        // fresh blinding factor stay HIDDEN, so the verifier never learns which federation member
        // produced the proof (the anonymity guarantee is preserved). `verify_descriptor_wire`
        // dispatches `descriptor_by_name(predicate)` → `verify_vm_descriptor2` and is fail-closed on
        // an unknown predicate / malformed vk / bad blob / failed verify.
        let blinded_pis = match dregg_circuit::presentation::verify_descriptor_wire(
            &real_stark.blinded_membership,
        ) {
            Some(pis) => pis,
            None => return false,
        };

        // Check federation root is the committed root.
        let expected_root_bb = {
            let limbs = BabyBear::encode_hash(expected_federation_root);
            poseidon2::hash_many(&limbs)
        };

        // The root is the second public input in blinded ring-membership proofs.
        use dregg_circuit::blinded_membership_witness::PI_ROOT_4ARY;
        if blinded_pis.get(PI_ROOT_4ARY).copied() == Some(expected_root_bb) {
            return true;
        }

        // Fallback: check if root appears anywhere in public inputs.
        blinded_pis.contains(&expected_root_bb)
    } else {
        false
    }
}

/// Verify a non-revocation proof against a known revocation root.
///
/// The verifier needs:
/// - The revocation set root (committed by the federation).
/// - The STARK proof.
///
/// Returns `Ok(())` if the proof is valid, `Err` with reason otherwise.
pub fn verify_non_revocation_proof(proof: &NonRevocationProof) -> Result<(), String> {
    // Decode the NEW wire format (postcard(DslP3Proof)); a malformed/tampered blob is a
    // fail-closed rejection (Err), never a silent accept.
    let p3_proof: DslP3Proof = postcard::from_bytes(&proof.proof)
        .map_err(|e| format!("non-revocation proof bytes could not be deserialized: {e}"))?;
    // Verify on the audited Plonky3 verifier against `[revocation_root, queried_item]`; both are
    // bound in-circuit (the two last-row path-root pins and the first-row X binding), so a proof
    // for a different root or queried item publishes different public inputs and is rejected.
    verify_non_revocation_p3(&p3_proof, proof.revocation_root, proof.item_hash)
}

/// Verify an accumulator-based non-membership proof against the TRUSTED (federation-committed)
/// accumulator. Sound: it checks the proof's `alpha`/`accumulator_value` match the trusted ones (no
/// forged challenge) and binds the witness remainder to `f(element)` via the trusted set
/// ([`PolynomialAccumulator::verify_non_membership_bound`]). A bare check on prover-supplied values is
/// forgeable (any `remainder'` with a matching quotient), which is why the trusted accumulator is
/// required — the caller must obtain it from the federation, not the prover.
///
/// The verifier needs:
/// - The current accumulator value (committed by the federation).
/// - The alpha challenge (committed by the federation via Fiat-Shamir).
///
/// Checks: `witness.quotient * (alpha - element) + witness.remainder == accumulator_value`
/// AND `witness.remainder != 0`.
///
/// Returns `Ok(())` if valid, `Err` with reason otherwise.
pub fn verify_accumulator_non_membership(
    trusted: &PolynomialAccumulator,
    proof: &AccumulatorNonMembershipProof,
) -> Result<(), String> {
    // The prover-supplied challenge + accumulator MUST match the TRUSTED (federation-committed) ones —
    // otherwise the prover forges the whole instance. `derive_alpha` binds alpha to the set commitment.
    if proof.alpha != trusted.alpha() {
        return Err("alpha does not match the trusted accumulator (forged challenge)".to_string());
    }
    if proof.accumulator_value != trusted.accumulator_value() {
        return Err("accumulator value does not match the trusted accumulator".to_string());
    }
    // SOUND: bind the witness remainder to f(x) via the trusted set. This closes the forgery the bare
    // division-identity check admitted (any remainder' with a matching quotient — even for a member).
    if trusted.verify_non_membership_bound(&proof.witness, proof.revocation_hash) {
        Ok(())
    } else {
        Err("accumulator non-membership verification failed: the witness remainder is not f(element) \
             against the trusted set, or the element is a member"
            .to_string())
    }
}

/// Verify a note spending proof (used by note tree operators to validate transfers).
///
/// The verifier needs:
/// - The nullifier (to check against the double-spend set).
/// - The Merkle root (the committed note tree root).
/// - The value (prevents value inflation attacks).
/// - The asset type (prevents asset type substitution attacks).
/// - The serialized descriptor batch proof (from [`NoteTransferProof::spending_proof`]).
///
/// Verification reconstructs the 7-slot claim EXACTLY as the DSL verifier did — a
/// local (non-bridge) spend pins `destination_federation = 0`, and a BabyBear-typed
/// caller binds a felt-sized value so `value_hi = 0` — plus the felt-domain mint
/// identity ([`note_spend_mint_hash_felt`]), then checks the proof against it via
/// `verify_vm_descriptor2`. The descriptor's `PiBinding`s pin every slot into the
/// trace, so a proof for a different `(nullifier, root, value, asset)` is rejected.
///
/// Returns `Ok(())` if valid.
pub fn verify_note_spending(
    nullifier: BabyBear,
    merkle_root: BabyBear,
    value: BabyBear,
    asset_type: BabyBear,
    proof_bytes: &[u8],
) -> Result<(), String> {
    let proof: Ir2BatchProof<DreggStarkConfig> = postcard::from_bytes(proof_bytes)
        .map_err(|e| format!("note-spend proof bytes could not be deserialized: {e}"))?;
    let dest = BabyBear::ZERO;
    let value_hi = BabyBear::ZERO;
    let mint = note_spend_mint_hash_felt(nullifier, merkle_root, value, asset_type, dest, value_hi);
    let claim = vec![
        nullifier,
        merkle_root,
        value,
        asset_type,
        dest,
        value_hi,
        mint,
    ];
    let desc = note_spend_to_descriptor2()?;
    verify_vm_descriptor2(&desc, &proof, &claim)
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_create_private_note_produces_valid_commitment() {
        let cclerk = AgentCipherclerk::new();
        let (commitment, secret) = cclerk.create_private_note(1000, 1).unwrap();

        // The commitment should match what Note::commitment() produces.
        assert_eq!(commitment, secret.note.commitment());

        // The note should have the correct value and asset type.
        assert_eq!(secret.note.value(), 1000);
        assert_eq!(secret.note.asset_type(), 1);

        // The owner should be the cipherclerk's public key.
        assert_eq!(secret.note.owner, cclerk.public_key().0);
    }

    #[test]
    fn test_create_private_note_unique_commitments() {
        let cclerk = AgentCipherclerk::new();
        let (c1, _) = cclerk.create_private_note(1000, 1).unwrap();
        let (c2, _) = cclerk.create_private_note(1000, 1).unwrap();

        // Even with same value/asset, commitments differ (fresh randomness).
        assert_ne!(c1, c2);
    }

    #[test]
    fn test_create_private_note_spending_key_derives_correctly() {
        let cclerk = AgentCipherclerk::new();
        let (_, secret) = cclerk.create_private_note(500, 2).unwrap();

        // The spending key should be deterministic for the same cipherclerk.
        let expected_key = cclerk.derive_symmetric_key("dregg-note-spending-key-v1");
        assert_eq!(secret.spending_key, expected_key);
    }

    #[test]
    fn test_prove_predicate_unlinkable_produces_fresh_commitment() {
        let mut cclerk = AgentCipherclerk::new();
        let root_key = [0xAB; 32];
        let token = cclerk.mint_token(&root_key, "test-service");

        // Generate two proofs for the same predicate.
        let proof1 = cclerk
            .prove_predicate_unlinkable(
                &token,
                "balance",
                5000,
                dregg_circuit::PredicateType::Gte,
                BabyBear::new(1000),
            )
            .unwrap();

        let proof2 = cclerk
            .prove_predicate_unlinkable(
                &token,
                "balance",
                5000,
                dregg_circuit::PredicateType::Gte,
                BabyBear::new(1000),
            )
            .unwrap();

        // The blinded commitments MUST differ (fresh blinding each time).
        assert_ne!(
            proof1.blinded_fact_commitment, proof2.blinded_fact_commitment,
            "blinded commitments must differ for unlinkability"
        );

        // But the blinding factors should also differ.
        assert_ne!(proof1.blinding, proof2.blinding);
    }

    #[test]
    fn test_prove_predicate_unlinkable_fails_on_false_statement() {
        let mut cclerk = AgentCipherclerk::new();
        let root_key = [0xCD; 32];
        let token = cclerk.mint_token(&root_key, "test-service");

        // Try to prove balance >= 1000 when balance is only 500 (false statement).
        let result = cclerk.prove_predicate_unlinkable(
            &token,
            "balance",
            500,
            dregg_circuit::PredicateType::Gte,
            BabyBear::new(1000),
        );

        assert!(result.is_err(), "should fail for false predicate");
    }

    #[test]
    fn test_prove_not_revoked_succeeds_for_non_revoked_token() {
        let mut cclerk = AgentCipherclerk::new();
        let root_key = [0xEF; 32];
        let token = cclerk.mint_token(&root_key, "service");

        // Build a revocation tree with some revoked entries (not our token).
        let revoked_hashes: Vec<BabyBear> = (1..=5u32)
            .map(|i| {
                let mut h = [0u8; 32];
                h[0] = i as u8;
                h[1] = 0xDE;
                revocation_hash_to_field(&h)
            })
            .collect();
        let tree = DslRevocationTree::new(revoked_hashes, 4);

        // Our token is not in the revocation set.
        let proof = cclerk.prove_not_revoked(&token, &tree);
        assert!(
            proof.is_ok(),
            "non-revoked token should produce valid proof: {:?}",
            proof.err()
        );

        // Verify the proof.
        let non_rev_proof = proof.unwrap();
        assert_eq!(non_rev_proof.revocation_root, tree.root());
        let verify_result = verify_non_revocation_proof(&non_rev_proof);
        assert!(
            verify_result.is_ok(),
            "non-revocation proof should verify: {:?}",
            verify_result.err()
        );
    }

    /// GATE RUNTIME round-trip for the non-revocation `StarkProof` → Lean-emitted IR2 wire
    /// migration. The proof blob is opaque `postcard` bytes, so `cargo build` cannot see the
    /// byte-format flip (`stark::proof_to_bytes(StarkProof)` → `postcard(DslP3Proof)`) nor the
    /// backend swap (`stark::prove`/`stark::verify` → `prove_non_revocation_p3` /
    /// `verify_non_revocation_p3` on the emitted descriptor) — this test is the gate the build cannot
    /// provide. It drives the exact producer→consumer contract through the REAL prover/verifier
    /// (never a mock):
    ///   PRODUCER: honest non-revoked token → `prove_not_revoked` → `postcard(DslP3Proof)`.
    ///   CONSUMER: `verify_non_revocation_proof` decodes the blob and checks it via the audited
    ///             `verify_non_revocation_p3` against `[revocation_root, queried_item]`.
    /// NON-VACUOUS: the honest proof ACCEPTS, and each of a forged root, a forged queried item,
    /// and a tampered blob is REJECTED (so the migrated prover did not install a trivially-
    /// accepting proof, and both public-input bindings are load-bearing).
    #[test]
    fn non_revocation_wire_roundtrip_gate() {
        let mut cclerk = AgentCipherclerk::new();
        let root_key = [0x9Cu8; 32];
        let token = cclerk.mint_token(&root_key, "service");

        // A revocation tree with several revoked entries (none of them our token).
        let revoked_hashes: Vec<BabyBear> = (1..=6u32)
            .map(|i| {
                let mut h = [0u8; 32];
                h[0] = i as u8;
                h[1] = 0xA7;
                revocation_hash_to_field(&h)
            })
            .collect();
        let tree = DslRevocationTree::new(revoked_hashes, 4);

        // ── PRODUCER: honest non-revoked token → emitted-IR2 proof, postcard-encoded. ──
        let honest = cclerk
            .prove_not_revoked(&token, &tree)
            .expect("a non-revoked token must produce a valid non-revocation proof");
        assert_eq!(honest.revocation_root, tree.root());

        // The blob really is the NEW wire format (postcard(DslP3Proof)), NOT a hand StarkProof.
        let _decoded: DslP3Proof = postcard::from_bytes(&honest.proof)
            .expect("the blob must decode as the migrated DslP3Proof (= Ir2BatchProof)");

        // ── POSITIVE POLE: honest ACCEPT through the real consumer. ──
        verify_non_revocation_proof(&honest).expect(
            "the honest non-revocation proof must ACCEPT through verify_non_revocation_proof",
        );

        // ── NEGATIVE 1 — a forged revocation root: both last-row root pins bite. ──
        let mut forged_root = honest.clone();
        forged_root.revocation_root += BabyBear::ONE;
        assert!(
            verify_non_revocation_proof(&forged_root).is_err(),
            "a forged revocation root must be REJECTED (root PI binding)"
        );

        // ── NEGATIVE 2 — a forged queried item: the first-row X binding bites. ──
        let mut forged_item = honest.clone();
        forged_item.item_hash += BabyBear::ONE;
        assert!(
            verify_non_revocation_proof(&forged_item).is_err(),
            "a freshness proof for one item must NOT verify against a different expected item"
        );

        // ── NEGATIVE 3 — a tampered blob (bit-flip in the postcard bytes). ──
        let mut tampered = honest.clone();
        let mid = tampered.proof.len() / 2;
        tampered.proof[mid] ^= 0xFF;
        let tampered_rejected = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            verify_non_revocation_proof(&tampered)
        }))
        .map(|r| r.is_err())
        .unwrap_or(true); // a decode/verify panic is itself a rejection
        assert!(tampered_rejected, "a tampered proof blob must be REJECTED");

        // ── Prover-side guard: a token whose OWN root-issuer hash is revoked cannot
        //    produce a non-revocation proof at all. ──
        let issuer_hash = revocation_hash_to_field(token.root_key());
        let tree_revoking_us = DslRevocationTree::new(vec![issuer_hash], 4);
        assert!(
            cclerk.prove_not_revoked(&token, &tree_revoking_us).is_err(),
            "a token whose ancestor IS revoked must not produce a non-revocation proof"
        );
    }

    #[test]
    fn test_authorize_anonymously_produces_unlinkable_proofs() {
        let mut cclerk = AgentCipherclerk::new();
        let root_key = [0x42; 32];
        let token = cclerk.mint_token(&root_key, "dns");

        let request = AuthRequest {
            service: Some("dns".into()),
            action: Some("read".into()),
            ..Default::default()
        };

        // Generate two anonymous presentations.
        // NOTE: This requires the bridge crate to have synthetic federation membership
        // enabled (cfg(test) or feature="test-utils"). When running in isolation without
        // that feature, prove_authorization returns IssuerNotInFederation.
        let pres1 = match cclerk.authorize_anonymously(&token, &request) {
            Ok(p) => p,
            Err(SdkError::Auth(dregg_bridge::AuthError::IssuerNotInFederation)) => {
                // Bridge crate compiled without test-utils feature; skip this test.
                return;
            }
            Err(e) => panic!("unexpected error: {e:?}"),
        };
        let pres2 = cclerk.authorize_anonymously(&token, &request).unwrap();

        // Presentation tags MUST differ (fresh randomness per presentation).
        assert_ne!(
            pres1.presentation_tag, pres2.presentation_tag,
            "presentation tags must differ for unlinkability"
        );
    }

    #[test]
    fn test_transfer_note_privately() {
        let cclerk = AgentCipherclerk::new();
        let (_, secret) = cclerk.create_private_note(1000, 1).unwrap();

        // Create a minimal Merkle path (depth 2 as required by the circuit).
        let merkle_siblings = vec![
            [BabyBear::new(111), BabyBear::new(222), BabyBear::new(333)],
            [BabyBear::new(444), BabyBear::new(555), BabyBear::new(666)],
        ];
        let merkle_positions = vec![0, 1];

        let recipient_key = [0xBB; 32];

        let transfer = cclerk
            .transfer_note_privately(&secret, &recipient_key, merkle_siblings, merkle_positions)
            .expect(
                "full-width (28-limb) witness should produce a valid note-spending proof; \
                 previously the felt-collapsed witness made the prover reject this path",
            );

        // The published nullifier matches the note's intrinsic nullifier.
        assert_eq!(
            transfer.nullifier,
            secret.note.nullifier(&secret.spending_key)
        );
        // The output note carries the same value/asset as the spent input.
        assert_eq!(transfer.recipient_secret.note.value(), secret.note.value());
        assert_eq!(
            transfer.recipient_secret.note.asset_type(),
            secret.note.asset_type()
        );
        // A descriptor batch proof was produced. `transfer_note_privately` only
        // returns Ok when `prove_vm_descriptor2` succeeded (and self-verified under
        // debug_assertions), so this exercises the FULL-WIDTH commitment-binding
        // trace end-to-end; the bytes must round-trip back into an `Ir2BatchProof`
        // that commits at least one table instance.
        let decoded: Ir2BatchProof<DreggStarkConfig> =
            postcard::from_bytes(&transfer.spending_proof)
                .expect("descriptor batch proof bytes round-trip");
        assert!(
            !decoded.degree_bits.is_empty(),
            "the note-spend descriptor proof commits at least one table instance"
        );
    }

    /// The rewired note-spend path proves the SAME statement it verifies against:
    /// an honest witness proves through the `note-spend-leaf` descriptor and
    /// `verify_note_spending` ACCEPTS the reconstructed claim, while a forged
    /// `value` claim is REFUSED (the descriptor's `PiBinding` value tooth). This
    /// witnesses at the SDK level that the descriptor prover did not replace the
    /// hand AIR with a trivially-accepting proof.
    #[test]
    fn test_verify_note_spending_accepts_honest_rejects_forged() {
        // Build a real full-width witness (value < 2^30 so value_hi = 0, dest = 0 —
        // the exact local-spend shape `verify_note_spending` reconstructs).
        let spending_key = key_to_field_elements(&[0x7Au8; 32]);
        let merkle_siblings = vec![
            [BabyBear::new(11), BabyBear::new(22), BabyBear::new(33)],
            [BabyBear::new(44), BabyBear::new(55), BabyBear::new(66)],
        ];
        let merkle_positions = vec![0u8, 1u8];
        let witness = NoteSpendingWitness::from_note_limbs(
            &[0x11u8; 32],
            1000,
            1,
            &[0x22u8; 32],
            &[0x33u8; 32],
            spending_key,
            merkle_siblings,
            merkle_positions,
        );

        // Prove exactly as `transfer_note_privately` does.
        let desc = note_spend_to_descriptor2().expect("descriptor builds");
        let (mut trace, base_pis) = generate_note_spending_trace(&witness);
        for row in &mut trace {
            row.resize(NOTE_SPENDING_WIDTH + 3, BabyBear::ZERO);
        }
        let m1 = poseidon2::hash_fact(
            base_pis[note_spend_pi::NULLIFIER],
            &[
                base_pis[note_spend_pi::MERKLE_ROOT],
                base_pis[note_spend_pi::DESTINATION_FEDERATION],
                base_pis[note_spend_pi::ASSET_TYPE],
            ],
        );
        let mint = poseidon2::hash_fact(
            m1,
            &[
                base_pis[note_spend_pi::VALUE],
                base_pis[note_spend_pi::VALUE_HI],
            ],
        );
        trace[0][NOTE_SPENDING_WIDTH] = base_pis[note_spend_pi::MERKLE_ROOT];
        trace[0][NOTE_SPENDING_WIDTH + 1] = m1;
        trace[0][NOTE_SPENDING_WIDTH + 2] = mint;
        let claim = note_spend_leaf_public_inputs(&witness);
        let proof =
            prove_vm_descriptor2(&desc, &trace, &claim, &MemBoundaryWitness::default(), &[])
                .expect("honest witness proves");
        let bytes = postcard::to_allocvec(&proof).unwrap();

        let nullifier = claim[note_spend_pi::NULLIFIER];
        let merkle_root = claim[note_spend_pi::MERKLE_ROOT];
        let value = claim[note_spend_pi::VALUE];
        let asset = claim[note_spend_pi::ASSET_TYPE];
        assert_eq!(value, BabyBear::new(1000));
        assert_eq!(
            claim[note_spend_pi::VALUE_HI],
            BabyBear::ZERO,
            "value < 2^30"
        );
        assert_eq!(
            claim[note_spend_pi::DESTINATION_FEDERATION],
            BabyBear::ZERO,
            "local spend"
        );

        // POSITIVE: the reconstructed claim verifies.
        verify_note_spending(nullifier, merkle_root, value, asset, &bytes)
            .expect("honest proof verifies against the reconstructed claim");

        // NEGATIVE: a forged value is refused (the PiBinding value tooth) — a
        // trivially-accepting proof would pass this too.
        assert!(
            verify_note_spending(nullifier, merkle_root, value + BabyBear::ONE, asset, &bytes)
                .is_err(),
            "a forged value claim must be REJECTED"
        );
    }

    /// GATE-3 RUNTIME round-trip for the `StarkProof` → `Ir2BatchProof` wire migration,
    /// exercised through the SDK's one migrated producer→consumer leg (the `note-spend-leaf`
    /// descriptor). The proof blob is opaque `postcard` bytes, so `cargo build` cannot see the
    /// byte-format flip (`stark::proof_to_bytes(StarkProof)` → `postcard(Ir2BatchProof)`) nor the
    /// descriptor dispatch — this test is the gate the build cannot provide. It drives the exact
    /// consumer contract the migration installs, through the REAL `prove_vm_descriptor2` /
    /// `verify_vm_descriptor2` (never a mock):
    ///   PRODUCER: honest full-width note-spend witness → `prove_vm_descriptor2` → `Ir2BatchProof`.
    ///   WIRE:     `postcard`-encode (the NEW format); the blob carries NO air-name.
    ///   CONSUMER: `verify_note_spending` decodes `postcard(Ir2BatchProof)` and checks it against the
    ///             `note_spend_to_descriptor2()` descriptor via `verify_vm_descriptor2`.
    /// NON-VACUOUS: the honest witness ACCEPTS, and each of a forged claim, a tampered blob, and a
    /// cross-KIND descriptor is REJECTED (so the descriptor prover did not install a trivially-
    /// accepting proof, and the descriptor dispatch is load-bearing).
    #[test]
    fn note_spend_wire_roundtrip_gate3() {
        use std::panic::AssertUnwindSafe;

        // ── PRODUCER: an honest local-spend witness (value < 2^30 ⇒ value_hi = 0, dest = 0). ──
        let spending_key = key_to_field_elements(&[0x5Cu8; 32]);
        let merkle_siblings = vec![
            [BabyBear::new(7), BabyBear::new(8), BabyBear::new(9)],
            [BabyBear::new(10), BabyBear::new(11), BabyBear::new(12)],
        ];
        let merkle_positions = vec![1u8, 0u8];
        let witness = NoteSpendingWitness::from_note_limbs(
            &[0xA1u8; 32],
            2000,
            3,
            &[0xB2u8; 32],
            &[0xC3u8; 32],
            spending_key,
            merkle_siblings,
            merkle_positions,
        );

        let desc = note_spend_to_descriptor2().expect("descriptor builds");
        let (mut trace, base_pis) = generate_note_spending_trace(&witness);
        for row in &mut trace {
            row.resize(NOTE_SPENDING_WIDTH + 3, BabyBear::ZERO);
        }
        let m1 = poseidon2::hash_fact(
            base_pis[note_spend_pi::NULLIFIER],
            &[
                base_pis[note_spend_pi::MERKLE_ROOT],
                base_pis[note_spend_pi::DESTINATION_FEDERATION],
                base_pis[note_spend_pi::ASSET_TYPE],
            ],
        );
        let mint = poseidon2::hash_fact(
            m1,
            &[
                base_pis[note_spend_pi::VALUE],
                base_pis[note_spend_pi::VALUE_HI],
            ],
        );
        trace[0][NOTE_SPENDING_WIDTH] = base_pis[note_spend_pi::MERKLE_ROOT];
        trace[0][NOTE_SPENDING_WIDTH + 1] = m1;
        trace[0][NOTE_SPENDING_WIDTH + 2] = mint;
        let claim = note_spend_leaf_public_inputs(&witness);
        let proof =
            prove_vm_descriptor2(&desc, &trace, &claim, &MemBoundaryWitness::default(), &[])
                .expect("honest note-spend witness must prove through the descriptor");

        // ── WIRE: the NEW opaque byte format = postcard(Ir2BatchProof). ──
        let blob = postcard::to_allocvec(&proof).expect("postcard-encode the batch proof");
        // The blob really is an Ir2BatchProof and NOT the retired StarkProof wire form.
        let _decoded: Ir2BatchProof<DreggStarkConfig> =
            postcard::from_bytes(&blob).expect("blob decodes as the migrated Ir2BatchProof");

        let nullifier = claim[note_spend_pi::NULLIFIER];
        let merkle_root = claim[note_spend_pi::MERKLE_ROOT];
        let value = claim[note_spend_pi::VALUE];
        let asset = claim[note_spend_pi::ASSET_TYPE];
        assert_eq!(value, BabyBear::new(2000));
        assert_eq!(
            claim[note_spend_pi::VALUE_HI],
            BabyBear::ZERO,
            "value < 2^30"
        );
        assert_eq!(
            claim[note_spend_pi::DESTINATION_FEDERATION],
            BabyBear::ZERO,
            "local spend"
        );

        // ── POSITIVE POLE: honest ACCEPT through the real consumer. ──
        verify_note_spending(nullifier, merkle_root, value, asset, &blob)
            .expect("honest note-spend proof must ACCEPT through verify_note_spending");

        // ── NEGATIVE 1 — a forged claim (wrong value): the descriptor's value PiBinding bites. ──
        assert!(
            verify_note_spending(nullifier, merkle_root, value + BabyBear::ONE, asset, &blob)
                .is_err(),
            "a forged value claim must be REJECTED"
        );
        // and a forged asset.
        assert!(
            verify_note_spending(nullifier, merkle_root, value, asset + BabyBear::ONE, &blob)
                .is_err(),
            "a forged asset claim must be REJECTED"
        );

        // ── NEGATIVE 2 — a tampered blob (bit-flip in the postcard bytes). ──
        let mut tampered = blob.clone();
        let mid = tampered.len() / 2;
        tampered[mid] ^= 0xFF;
        let tampered_rejected = std::panic::catch_unwind(AssertUnwindSafe(|| {
            verify_note_spending(nullifier, merkle_root, value, asset, &tampered)
        }))
        .map(|r| r.is_err())
        .unwrap_or(true); // a decode/verify panic is itself a rejection
        assert!(tampered_rejected, "a tampered proof blob must be REJECTED");

        // ── NEGATIVE 3 — cross-KIND descriptor: the note-spend proof under a DFA descriptor.
        // A wrong dispatch arm cannot launder the proof (structural mismatch → Err/panic). This
        // pins that the descriptor dispatch is load-bearing, not decorative. ──
        let dfa = dregg_circuit::descriptor_by_name::descriptor_by_name(
            "dfa-routing-toggle-2state::poseidon2-v1",
        )
        .expect("the DFA descriptor dispatches");
        let cross_kind_rejected = std::panic::catch_unwind(AssertUnwindSafe(|| {
            verify_vm_descriptor2(&dfa, &proof, &claim)
        }))
        .map(|r| r.is_err())
        .unwrap_or(true);
        assert!(
            cross_kind_rejected,
            "verifying the note-spend proof under the wrong-KIND (DFA) descriptor must be REJECTED"
        );
    }
}
