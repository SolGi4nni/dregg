//! High-level privacy APIs for application developers.
//!
//! This module provides ergonomic wrappers around dregg's privacy primitives,
//! making it simple to perform common privacy-preserving operations:
//!
//! - **Anonymous authorization**: Prove you are authorized without revealing your identity.
//! - **Private notes**: Create and transfer value without revealing amounts.
//! - **Unlinkable predicates**: Prove facts about yourself that can't be correlated.
//! - **Private discovery**: Find matching intents without revealing your query.
//! - **Non-revocation proofs**: Prove your token hasn't been revoked without revealing it
//!   (the polynomial-accumulator rail; the 1-felt sorted-tree rail is RETIRED —
//!   felt-width #11 fold-in).
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
use dregg_circuit::field::BABYBEAR_P;
use dregg_circuit::note_spending_witness::{
    NOTE_SPENDING_WIDTH, NoteSpendingWitness, key_to_field_elements, pi as note_spend_pi,
};
use dregg_circuit::poseidon2;
// `verify_anonymous_presentation` verifies the committed BLINDED ring-membership descriptor
// (`dregg-blinded-membership-4ary-general-depth{N}`) via `descriptor_by_name` →
// `verify_vm_descriptor2` — the Golden-Lift flip off the hand-written blinded-Merkle STARK.
pub use dregg_circuit_prove::faithful_note_spend::{FaithfulNoteOpening, FaithfulNoteSpendPublic};
use dregg_circuit_prove::faithful_note_spend::{FaithfulNoteSpendClaim, prove_zk};
use dregg_circuit_prove::note_spend_leaf_adapter::{
    note_spend_leaf_public_inputs, note_spend_mint_hash_felt, note_spend_to_descriptor2,
};
use dregg_commit::accumulator::{AccumulatorWitness, BabyBear4, PolynomialAccumulator};
pub use dregg_commit::poseidon2_tree::Poseidon2NoteProof16;
use dregg_dsl_runtime::note_spending::generate_note_spending_trace;
use dregg_token::AuthRequest;
use dregg_turn::faithful_note_spend::FaithfulNoteSpendProofCarrier;

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

/// Exact faithful-v2 hidden-note spend artifact ready for `Effect::NoteSpend`.
///
/// The inner proof is always produced by the Lean-emitted FNO2/FNC2/FNF2
/// relation under HidingFRI, then wrapped in the strict FNSP-v2 carrier.  The
/// verifier learns the fields in [`FaithfulNoteSpendPublic`] (including value
/// and asset type); the owner address, spending key, nonce, randomness,
/// commitment, and membership path stay private.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FaithfulHiddenSpendProof {
    /// Public statement reconstructed by the predicate-specific verifier.
    pub public: FaithfulNoteSpendPublic,
    /// Strict carrier for the existing `NoteSpend::spending_proof` byte field.
    pub carrier: FaithfulNoteSpendProofCarrier,
}

impl FaithfulHiddenSpendProof {
    /// Consume this proved artifact into the exact clear-value `NoteSpend`
    /// effect accepted by the faithful-v2 executor path.
    ///
    /// FNSP-v2 publicly binds `value` and `asset_type`, so this constructor
    /// always sets `value_commitment` to `None`.  Offering a committed-mode
    /// switch here would create a value statement the v2 AIR does not prove.
    pub fn into_note_spend_effect(self) -> dregg_turn::Effect {
        dregg_turn::Effect::NoteSpend {
            nullifier: Nullifier(self.public.nullifier),
            note_tree_root: root8_to_bytes(self.public.historical_note_root),
            value: self.public.value,
            asset_type: self.public.asset_type,
            spending_proof: self.carrier.encode(),
            value_commitment: None,
        }
    }
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

// (The 1-felt sorted-tree `NonRevocationProof` + `prove_not_revoked` +
// `verify_non_revocation_proof` are RETIRED — felt-width #11 fold-in. Spend
// freshness is in-circuit on the rotated note-spend leg; delegation-ancestor
// revocation is the limb-37 `.absent` open. The accumulator rail below stays.)

/// Proof of non-revocation using the polynomial accumulator (O(1) verification).
///
/// The accumulator proof is constant-size regardless of how many entries are in
/// the revocation set. (The retired 1-felt sorted-Merkle `NonRevocationProof`
/// alternative is gone — felt-width #11 fold-in.)
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

/// Build the exact faithful-v2 hidden-note spend proof used by finalization.
///
/// `historical_note_root` is `(authenticated height, faithful root8)`.  The
/// planned successor root must be computed from the durable nullifier frontier
/// plus this spend before calling this function; the executor recomputes it and
/// requires exact equality.  There is deliberately no legacy descriptor or
/// non-hiding fallback.
///
/// This API proves consumption of one existing note.  It does **not** create an
/// output note and does not attempt to derive a recipient secret from a public
/// key.  Output-note ownership must be established by the recipient-owned
/// shielded address/encryption flow.
pub fn build_faithful_hidden_spend_proof(
    opening: &FaithfulNoteOpening,
    membership: &Poseidon2NoteProof16,
    historical_note_root: (u64, [u32; 8]),
    planned_successor_nullifier_root: [u32; 8],
) -> Result<FaithfulHiddenSpendProof, SdkError> {
    let claim = FaithfulNoteSpendClaim {
        root_height: historical_note_root.0,
        historical_note_root: historical_note_root.1,
        successor_nullifier_root: planned_successor_nullifier_root,
    };
    let (proof, public) = prove_zk(opening, membership, claim)
        .map_err(|error| SdkError::InvalidWitness(format!("faithful hidden spend: {error}")))?;
    let inner_proof_bytes = proof.to_postcard().map_err(|error| {
        SdkError::InvalidWitness(format!("faithful hidden spend proof encoding: {error}"))
    })?;
    package_faithful_hidden_spend_proof(public, inner_proof_bytes)
}

fn package_faithful_hidden_spend_proof(
    public: FaithfulNoteSpendPublic,
    inner_proof_bytes: Vec<u8>,
) -> Result<FaithfulHiddenSpendProof, SdkError> {
    public
        .validate()
        .map_err(|error| SdkError::InvalidWitness(format!("faithful hidden spend: {error}")))?;
    let successor_nullifier_root = root8_to_bytes(public.successor_nullifier_root);
    let carrier = FaithfulNoteSpendProofCarrier::new(
        public.root_height,
        successor_nullifier_root,
        inner_proof_bytes,
    )
    .map_err(|error| SdkError::InvalidWitness(format!("faithful hidden spend carrier: {error}")))?;
    Ok(FaithfulHiddenSpendProof { public, carrier })
}

fn root8_to_bytes(root: [u32; 8]) -> [u8; 32] {
    let mut bytes = [0u8; 32];
    for (lane, value) in root.into_iter().enumerate() {
        bytes[4 * lane..4 * lane + 4].copy_from_slice(&value.to_le_bytes());
    }
    bytes
}

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
        // A FRESH blinding factor per proof: the fact commitment is
        // `hash_4_to_1([fact_hash, state_root, blinding, 0])`, so two showings of the same attribute
        // emit DIFFERENT commitments (unlinkable) while the in-circuit weld keeps each bound to the
        // value compared (sound).
        let predicate_proof = dregg_bridge::prove_predicate_for_fact(
            attribute_value,
            binding,
            dregg_bridge::present::fresh_predicate_blinding(),
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

    // (`prove_not_revoked` — the 1-felt sorted-tree delegation-ancestor rail — is
    // RETIRED; use `prove_not_revoked_accumulator` below, or rely on the in-circuit
    // limb-37 delegation-ancestor open on spend turns.)

    /// Convert a 32-byte revocation hash to the BabyBear field element the
    /// accumulator rail keys on: Poseidon2 over the byte-encoded limbs
    /// (matches `commit::poseidon2_tree::commitment_to_field`). (Home moved
    /// here from the retired `dsl::revocation` module.)
    fn revocation_hash_to_field(hash: &[u8; 32]) -> BabyBear {
        let elements = BabyBear::encode_hash(hash);
        poseidon2::hash_many(&elements)
    }

    /// Prove a token is not in the revocation set using the polynomial accumulator.
    ///
    /// The accumulator witness is constant-size regardless of how many tokens have been
    /// revoked, making it ideal when the revocation set exceeds ~1000 entries.
    ///
    /// # Privacy Guarantee
    ///
    /// The verifier learns only that the token is not revoked. The token's
    /// identity and derivation chain remain hidden.
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
        let revocation_hash = Self::revocation_hash_to_field(issuer_key);

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

/// Verify an [`UnlinkablePredicateProof`] the way a verifier holding the presented
/// (fresh-blinded) commitment does: run the REAL predicate STARK
/// ([`dregg_bridge::present::verify_predicate_proof`]), pinned to the commitment the
/// proof carries.
///
/// This is the missing sibling of [`AgentCipherclerk::prove_predicate_unlinkable`] —
/// proving had no verify entry in the SDK, so every consumer (the Discord
/// `/credential verify` path) had to reach into the bridge itself. It returns `true`
/// iff the value welded into `proof.predicate_proof.fact_commitment` satisfies the
/// predicate.
///
/// # What this establishes — and what it does NOT (read before relying on it)
///
/// - **Establishes:** the committed value satisfies the predicate, and the proof is
///   bound to the exact commitment it presents — the in-circuit blinded weld means a
///   proof does not verify against a different commitment
///   (`teasting/tests/privacy_unlinkability.rs`). Two proofs of the same fact carry
///   DIFFERENT `blinded_fact_commitment`s, so a party seeing only commitments cannot
///   correlate them (the unlinkability guarantee).
/// - **Does NOT establish** that the commitment opens to a THIRD-PARTY-ISSUED
///   credential. That is the attestation rung
///   ([`dregg_bridge::present::verify_predicate_proof_third_party`], which requires a
///   trusted `facts_root`); here the prover presents its own commitment, so the check
///   is sound against a prover who does not control the value (the custodial holder
///   proving about its own state) but says nothing about issuer provenance.
/// - **Inherits the deployed STARK/FRI soundness floor**
///   (`project-fri-soundness-reality`): it is a real proof, not an on-chain-settled
///   fact.
///
/// # ⚠ SAFETY — this is a SELF-COMMITMENT check, not a NON-CUSTODIAL verification
///
/// `expected_fact_commitment` is read off the proof (`x == x`), so a passing result
/// means only: *"the value the prover committed to satisfies the predicate."* It does
/// NOT mean the prover holds a matching issued credential — a malicious prover can
/// invent a fact, commit to it, and prove a TRUE statement about the invention. This
/// is sound ONLY where the caller already trusts the prover to have committed to the
/// real value: the CUSTODIAL flow, where the SAME party mints the proof about state it
/// controls and immediately checks it (the deployed `/credential verify` path reads the
/// value out of the subject's own held credential, so the commitment is trustworthy by
/// custody, not by this function).
///
/// A NON-CUSTODIAL verifier — one accepting an `UnlinkablePredicateProof` from an
/// untrusted party — MUST NOT treat a `true` here as evidence of credential possession.
/// The sound path for that is
/// [`crate::verify::verify_disclosure_presentation_third_party`] /
/// [`dregg_bridge::present::verify_predicate_proof_third_party`], which pins the
/// expected commitment via a `BridgeFactAttestation` under a `facts_root` the verifier
/// TRUSTS. This shape carries no attestation and no such root, so that binding is not
/// available here; closing it end-to-end additionally needs the presentation STARK to
/// expose `facts_root` as a public input (a Lean-authored AIR change, out of scope).
pub fn verify_predicate_unlinkable(proof: &UnlinkablePredicateProof) -> bool {
    dregg_bridge::present::verify_predicate_proof(
        &proof.predicate_proof,
        proof.predicate_proof.fact_commitment,
    )
}

// (`verify_non_revocation_proof` RETIRED with the 1-felt rail — felt-width #11
// fold-in.)

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
    fn faithful_hidden_spend_packages_exact_v2_carrier_without_a_second_proof() {
        let public = FaithfulNoteSpendPublic {
            root_height: 0x1122_3344_5566_7788,
            historical_note_root: core::array::from_fn(|lane| 0x1000 + lane as u32),
            nullifier: core::array::from_fn(|lane| 0x80u8.wrapping_add(lane as u8)),
            value: 0x0123_4567_89ab_cdef,
            asset_type: 0x8899_aabb_ccdd_eeff,
            successor_nullifier_root: core::array::from_fn(|lane| 0x2000 + lane as u32),
        };
        let inner = vec![0xa5, 0x5a, 0x11];
        let artifact = package_faithful_hidden_spend_proof(public, inner.clone())
            .expect("canonical public statement packages");

        assert_eq!(artifact.public, public);
        assert_eq!(artifact.carrier.root_height(), public.root_height);
        assert_eq!(
            artifact.carrier.successor_nullifier_root(),
            root8_to_bytes(public.successor_nullifier_root)
        );
        assert_eq!(artifact.carrier.inner_proof_bytes(), inner);
        assert_eq!(
            FaithfulNoteSpendProofCarrier::decode(&artifact.carrier.encode()),
            Ok(artifact.carrier.clone())
        );

        let encoded_carrier = artifact.carrier.encode();
        match artifact.into_note_spend_effect() {
            dregg_turn::Effect::NoteSpend {
                nullifier,
                note_tree_root,
                value,
                asset_type,
                spending_proof,
                value_commitment,
            } => {
                assert_eq!(nullifier.0, public.nullifier);
                assert_eq!(note_tree_root, root8_to_bytes(public.historical_note_root));
                assert_eq!(value, public.value);
                assert_eq!(asset_type, public.asset_type);
                assert_eq!(spending_proof, encoded_carrier);
                assert_eq!(value_commitment, None);
            }
            other => panic!("faithful spend lowered to the wrong effect: {other:?}"),
        }
    }

    #[test]
    fn faithful_hidden_spend_refuses_hostile_statement_before_proving() {
        let opening = FaithfulNoteOpening {
            owner: [0; 32],
            value: 7,
            asset_type: 9,
            creation_nonce: [0x44; 32],
            randomness: [0x55; 32],
            spending_key: [0x66; 32],
        };
        let membership = Poseidon2NoteProof16 {
            leaf: [BabyBear::ZERO; 16],
            siblings: vec![[[BabyBear::ZERO; 8]; 3]; 16],
            positions: vec![0; 16],
        };

        // The native preflight derives FNO2 and refuses this mismatched owner
        // before constructing the 1023-column trace or entering HidingFRI.
        let error = build_faithful_hidden_spend_proof(&opening, &membership, (5, [0; 8]), [0; 8])
            .expect_err("an address unrelated to the hidden key must refuse");
        assert!(error.to_string().contains("owner is not the FNO2 address"));

        // Root lanes are strict canonical BabyBear encodings, never reduced.
        let mut noncanonical = [0; 8];
        noncanonical[3] = BABYBEAR_P;
        let error =
            build_faithful_hidden_spend_proof(&opening, &membership, (5, noncanonical), [0; 8])
                .expect_err("a noncanonical historical root must refuse");
        assert!(error.to_string().contains("noncanonical for BabyBear"));
    }

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

    /// GATE for the new [`verify_predicate_unlinkable`] entry: an honest proof
    /// ACCEPTS, and two independent forgeries are REFUSED — so the verifier is not a
    /// trivial `true`. The forgeries are (1) relabeling a `≥1000` proof as `≥1_000_000`
    /// (the bound is a bound public input, so the STARK is re-checked against the new
    /// `pi` and fails) and (2) a bit-flip in the proof blob.
    #[test]
    fn test_verify_predicate_unlinkable_accepts_honest_rejects_forged() {
        let mut cclerk = AgentCipherclerk::new();
        let root_key = [0x5Au8; 32];
        let token = cclerk.mint_token(&root_key, "verify-svc");

        // Honest: 5000 >= 1000 is TRUE, so a real proof is produced and must verify.
        let proof = cclerk
            .prove_predicate_unlinkable(
                &token,
                "balance",
                5000,
                dregg_circuit::PredicateType::Gte,
                BabyBear::new(1000),
            )
            .expect("a TRUE predicate produces a real proof");
        assert!(
            verify_predicate_unlinkable(&proof),
            "an honest unlinkable predicate proof must verify"
        );

        // Forged 1 — relabel the SAME proof as proving a threshold it never proved.
        let mut forged_bound = proof.clone();
        forged_bound.predicate_proof.predicate = dregg_bridge::present::Predicate::Gte(1_000_000);
        assert!(
            !verify_predicate_unlinkable(&forged_bound),
            "a ≥1000 proof relabeled as ≥1_000_000 must be REJECTED (bound is a public input)"
        );

        // Forged 2 — tamper the proof bytes (a decode/verify failure is a rejection).
        let mut tampered = proof.clone();
        if let dregg_bridge::present::BridgePredicateProofInner::Single(ref mut b) =
            tampered.predicate_proof.proof
        {
            let mid = b.len() / 2;
            b[mid] ^= 0xFF;
        }
        let tampered_rejected = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            verify_predicate_unlinkable(&tampered)
        }))
        .map(|verified| !verified)
        .unwrap_or(true);
        assert!(
            tampered_rejected,
            "a tampered predicate proof blob must be REJECTED"
        );
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

    // (`test_prove_not_revoked_succeeds_for_non_revoked_token` +
    // `non_revocation_wire_roundtrip_gate` RETIRED with the 1-felt rail — felt-width
    // #11 fold-in. The in-circuit freshness teeth live in
    // `sdk/src/full_turn_proof.rs` (`freshness_in_circuit_*`) and
    // `circuit/tests/vk_epoch_notes_light_client_binding.rs`.)

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
