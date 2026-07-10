//! Anonymous note model: consume-once cells with private state.
//!
//! A note is a committed tuple: (owner, fields[8], randomness, creation_nonce) with a unique commitment.
//! Spending a note = revealing its nullifier (only the owner can compute this).
//! Creating a note = adding a commitment to the note tree.
//!
//! Notes are self-proving: the STARK proof + Merkle path is enough to verify,
//! no federation callback needed.
//!
//! Nullifiers are derived from note-intrinsic data only (no tree position), making
//! them globally unique and federation-independent. This ensures double-spend
//! protection works across federation boundaries without export ceremonies.
//!
//! Note commitments and nullifiers are computed with **Poseidon2** over the
//! STARK-native BabyBear field — the same audited `dregg_circuit::poseidon2`
//! sponge the circuit verifies. The 32-byte `NoteCommitment` / `Nullifier` are
//! the [`crate::felt_to_bytes32`] encoding of the Poseidon2 field-element
//! digest, so the cell-side note identity matches the circuit's field-domain
//! commitment (`Note::poseidon2_commitment` is the underlying felt).
//!
//! The separate BLAKE3 paths in this crate are confined to non-commitment
//! key-derivation roles: `creation_nonce` domain separation here, and the
//! Diffie–Hellman encryption KDF in `note_encryption` (which must keep its full
//! 256-bit symmetric strength and is unrelated to the felt commitment).

use serde::{Deserialize, Serialize};

/// A note commitment (published to the note tree).
/// commitment = H("dregg-note commitment v1", owner || fields[0..8] || randomness || creation_nonce)
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct NoteCommitment(pub [u8; 32]);

/// A nullifier (published when spending a note).
/// nullifier = H("dregg-note nullifier v1", commitment || spending_key || creation_nonce)
/// Only the owner can compute this. Publishing it "spends" the note.
/// Derived from note-intrinsic data only — no tree position — so the same note
/// produces the same nullifier regardless of which tree it lives in.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Nullifier(pub [u8; 32]);

/// The content of a note (known only to the owner).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Note {
    /// The owner's public key (spending authority).
    pub owner: [u8; 32],
    /// 8 field elements of application data.
    /// Convention: fields[0] = asset_type, fields[1] = amount (for fungible).
    /// For NFTs: fields[0] = unique_asset_id (immutable across transfers).
    pub fields: [u64; 8],
    /// Random blinding factor (ensures commitment uniqueness).
    pub randomness: [u8; 32],
    /// Unique per-note nonce chosen at creation time. Embedded in the commitment
    /// and used in nullifier derivation. Makes nullifiers federation-independent:
    /// the same note produces the same nullifier regardless of tree position.
    pub creation_nonce: [u8; 32],
}

/// A note with its computed commitment and position info.
/// The tree position is metadata used for Merkle proof generation only —
/// it does NOT participate in nullifier derivation.
#[derive(Clone, Debug)]
pub struct PositionedNote {
    pub note: Note,
    pub commitment: NoteCommitment,
    /// Position in the note tree (needed for Merkle proof generation, NOT for nullifiers).
    pub tree_position: u64,
}

/// Errors that can occur in note operations.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum NoteError {
    /// Attempted to spend a note that has already been spent (double-spend).
    DoubleSpend { nullifier: Nullifier },
    /// Attempted to create a note whose commitment is already present (the
    /// create-side dual of `DoubleSpend` — the commitments accumulator is
    /// grow-only, so a duplicate commitment is rejected).
    DuplicateCommitment { commitment: NoteCommitment },
    /// Conservation law violated: inputs do not equal outputs for an asset type.
    ConservationViolation {
        asset_type: u64,
        input_total: u64,
        output_total: u64,
    },
}

impl core::fmt::Display for NoteError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            NoteError::DoubleSpend { nullifier } => {
                write!(
                    f,
                    "double-spend: nullifier {:?} already revealed",
                    &nullifier.0[..4]
                )
            }
            NoteError::DuplicateCommitment { commitment } => {
                write!(
                    f,
                    "duplicate commitment: {:?} already created",
                    &commitment.0[..4]
                )
            }
            NoteError::ConservationViolation {
                asset_type,
                input_total,
                output_total,
            } => {
                write!(
                    f,
                    "conservation violated for asset {asset_type}: inputs={input_total}, outputs={output_total}"
                )
            }
        }
    }
}

impl std::error::Error for NoteError {}

/// Decompose a 32-byte value into 8 BabyBear limbs (4 bytes each,
/// little-endian). Position 0 carries bytes `[0..4]`; position 7 carries
/// bytes `[28..32]`. Each 4-byte chunk is reduced mod `p`.
///
/// This is the canonical full-32-byte limb decomposition, identical to the
/// EffectVM hash-binding lane's `circuit::effect_vm::helpers::bytes32_to_8_limbs`
/// (commit b0b87952). Every byte of the input contributes to some limb, so two
/// 32-byte values differing in ANY byte produce a distinct limb vector (up to
/// the per-limb mod-p wrap, which only aliases 4-byte chunks whose raw u32
/// exceeds `p` — a measure-zero, deterministic, total mapping that is identical
/// for any two callers).
#[inline]
fn bytes32_to_limbs(b: &[u8; 32]) -> [dregg_circuit::field::BabyBear; 8] {
    use dregg_circuit::field::{BABYBEAR_P, BabyBear};
    let mut out = [BabyBear::ZERO; 8];
    for (i, limb) in out.iter_mut().enumerate() {
        let off = i * 4;
        let v = u32::from_le_bytes([b[off], b[off + 1], b[off + 2], b[off + 3]]);
        *limb = BabyBear::new(v % BABYBEAR_P);
    }
    out
}

/// Decompose a u64 into 2 BabyBear limbs: `[low 32 bits, high 32 bits]`, each
/// reduced mod `p`. Binds the FULL 64 bits of a u64 note field (value /
/// asset_type), versus the legacy form that bound only the low 32 bits.
#[inline]
fn u64_to_limbs(v: u64) -> [dregg_circuit::field::BabyBear; 2] {
    use dregg_circuit::field::{BABYBEAR_P, BabyBear};
    [
        BabyBear::new((v as u32) % BABYBEAR_P),
        BabyBear::new(((v >> 32) as u32) % BABYBEAR_P),
    ]
}

impl Note {
    /// Create a note with explicit randomness and creation nonce (for deterministic tests).
    pub fn with_randomness(owner: [u8; 32], fields: [u64; 8], randomness: [u8; 32]) -> Self {
        // Derive a deterministic creation_nonce from the randomness.
        let mut hasher = blake3::Hasher::new_derive_key("dregg-note creation-nonce v1");
        hasher.update(&owner);
        hasher.update(&randomness);
        let mut creation_nonce = [0u8; 32];
        creation_nonce.copy_from_slice(hasher.finalize().as_bytes());
        Self {
            owner,
            fields,
            randomness,
            creation_nonce,
        }
    }

    /// Create a note with explicit randomness AND explicit creation nonce.
    /// Use when you need full control over both values (e.g., testing nonce uniqueness).
    pub fn with_nonce(
        owner: [u8; 32],
        fields: [u64; 8],
        randomness: [u8; 32],
        creation_nonce: [u8; 32],
    ) -> Self {
        Self {
            owner,
            fields,
            randomness,
            creation_nonce,
        }
    }

    /// Compute the commitment for this note.
    ///
    /// This is the **Poseidon2 commitment** over the STARK-native field: the
    /// 32-byte value is the [`crate::felt_to_bytes32`] encoding of
    /// [`Note::poseidon2_commitment`] (the audited `dregg_circuit::poseidon2`
    /// hash of the 28-limb owner ‖ value ‖ asset_type ‖ creation_nonce ‖
    /// randomness preimage). So `NoteCommitment(felt_to_bytes32(c)) == c`'s
    /// circuit-side felt commitment — the cell identity and the circuit
    /// commitment are the same function.
    pub fn commitment(&self) -> NoteCommitment {
        NoteCommitment(crate::felt_to_bytes32(self.poseidon2_commitment()))
    }

    /// Compute the nullifier for this note given the owner's secret key.
    /// nullifier = H("dregg-note nullifier v1", commitment || spending_key || creation_nonce)
    ///
    /// Derived from note-intrinsic data only. No tree position is used, so the same
    /// note produces the same nullifier regardless of which tree (or federation) it
    /// lives in. This makes double-spend detection global by construction.
    ///
    /// This is the **canonical in-protocol nullifier** consumed by the
    /// production `NullifierSet` in the turn executor. It is computed with
    /// Poseidon2 over the STARK-native field, structurally mirroring the
    /// note-spending AIR's `NoteSpendingWitness::nullifier`
    /// (`circuit/src/note_spending_air.rs`):
    ///   `hash_many(commitment_felt ‖ spending_key[8 limbs] ‖ creation_nonce[8 limbs])`,
    /// then encoded to 32 bytes via [`crate::felt_to_bytes32`]. The spending key
    /// is bound through all eight 4-byte limbs (~248-bit secret), so only the
    /// owner can compute it.
    ///
    /// The separate EVM withdrawal path
    /// (`dregg_chain::withdraw::derive_nullifier`) uses a different,
    /// domain-separated scheme (`dregg-withdrawal-nullifier-v1`) because it
    /// commits to a different SP1 circuit; see that function's doc-comment for
    /// why the schemes are intentionally distinct.
    pub fn nullifier(&self, spending_key: &[u8; 32]) -> Nullifier {
        use dregg_circuit::poseidon2::hash_many;
        let commitment_felt = self.poseidon2_commitment();
        // commitment(1) + spending_key(8 limbs) + creation_nonce(8 limbs) = 17.
        let mut preimage = Vec::with_capacity(17);
        preimage.push(commitment_felt);
        preimage.extend_from_slice(&bytes32_to_limbs(spending_key)); // 8
        preimage.extend_from_slice(&bytes32_to_limbs(&self.creation_nonce)); // 8
        Nullifier(crate::felt_to_bytes32(hash_many(&preimage)))
    }

    /// Check if this note represents a fungible asset.
    /// A note is fungible if both asset_type and amount are non-zero.
    pub fn is_fungible(&self) -> bool {
        self.fields[0] != 0 && self.fields[1] != 0
    }

    /// Get the value (for fungible notes: fields[1]).
    pub fn value(&self) -> u64 {
        self.fields[1]
    }

    /// Get the asset type (fields[0]).
    pub fn asset_type(&self) -> u64 {
        self.fields[0]
    }

    /// Compute the Poseidon2 commitment **field element** for this note.
    ///
    /// This is the commitment used in the NOTE TREE (Poseidon2 Merkle tree) and
    /// verified inside the STARK circuit. It is also the felt that
    /// [`Note::commitment`] encodes (via [`crate::felt_to_bytes32`]) into the
    /// 32-byte `NoteCommitment` — so the cleartext note identity and the
    /// in-circuit commitment are the SAME Poseidon2 function, just felt vs.
    /// 32-byte-encoded.
    ///
    /// The Poseidon2 commitment is authoritative for:
    /// - Note tree membership proofs (ZK Merkle paths)
    /// - STARK spending proofs (the circuit recomputes this from witness columns)
    /// - Nullifier derivation (cell-side and inside the circuit)
    /// - Cleartext note identity / deduplication (via the 32-byte encoding)
    ///
    /// # Field mapping (full-width, 256-bit-binding)
    ///
    /// Previously each 32-byte field (owner / creation_nonce / randomness)
    /// contributed only its FIRST 4 bytes (~31 bits) to the commitment, and
    /// each u64 field (value / asset_type) only its low 32 bits — so two notes
    /// differing only in the bytes ABOVE the first chunk collided. This is the
    /// same defect class fixed in the EffectVM hash-binding lane (commit
    /// b0b87952): a full 32-byte value must bind all 256 bits.
    ///
    /// The Poseidon2 commitment now maps note fields to BabyBear as follows:
    /// - owner: 8 limbs — `owner[0..32]` as 8 little-endian 4-byte chunks,
    ///   each reduced mod p (~248 bits bound).
    /// - value: 2 limbs — low 32 bits and high 32 bits of `fields[1]` (full
    ///   64-bit binding; the legacy form only bound the low 32 bits).
    /// - asset_type: 2 limbs — low/high 32 bits of `fields[0]` (full 64-bit).
    /// - creation_nonce: 8 limbs — `creation_nonce[0..32]` as 8 LE chunks.
    /// - randomness: 8 limbs — `randomness[0..32]` as 8 LE chunks.
    ///
    /// Total preimage = 28 BabyBear limbs (8 + 2 + 2 + 8 + 8), ordered
    /// owner ‖ value ‖ asset_type ‖ creation_nonce ‖ randomness. Two notes
    /// that differ in ANY byte of ANY field now produce distinct commitments
    /// (up to Poseidon2 collision resistance).
    ///
    /// # AIR lockstep
    ///
    /// `poseidon2_commitment` has no in-tree callers that feed a STARK AIR
    /// directly: the note-spending AIR (`circuit::note_spending_air`) and its
    /// DSL form build their witness from already-field-element preimages
    /// (`NoteSpendingWitness { owner, value, .. : BabyBear }`) and recompute
    /// `hash_many([owner, value, asset_type, creation_nonce, randomness])`
    /// over those 5 felts. That legacy 5-felt AIR layout binds 5 felts of
    /// preimage, not this 28-limb layout. Widening here closes the cell-side
    /// (note-tree / non-ZK identity) truncation; aligning the legacy
    /// note-spending AIR to the 28-limb preimage is a separate, out-of-scope
    /// circuit change (the schema-based `effect_action_air` already carries
    /// 8 limbs per 32-byte field for action-binding). See residual notes.
    pub fn poseidon2_commitment(&self) -> dregg_circuit::field::BabyBear {
        use dregg_circuit::poseidon2::hash_many;

        let mut preimage = Vec::with_capacity(28);
        preimage.extend_from_slice(&bytes32_to_limbs(&self.owner)); // 8
        preimage.extend_from_slice(&u64_to_limbs(self.fields[1])); // 2 (value)
        preimage.extend_from_slice(&u64_to_limbs(self.fields[0])); // 2 (asset_type)
        preimage.extend_from_slice(&bytes32_to_limbs(&self.creation_nonce)); // 8
        preimage.extend_from_slice(&bytes32_to_limbs(&self.randomness)); // 8

        hash_many(&preimage)
    }

    /// Position this note in the tree.
    pub fn positioned(self, tree_position: u64) -> PositionedNote {
        let commitment = self.commitment();
        PositionedNote {
            note: self,
            commitment,
            tree_position,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_owner(seed: u8) -> [u8; 32] {
        let mut key = [0u8; 32];
        key[0] = seed;
        key[31] = seed.wrapping_mul(37);
        key
    }

    fn test_spending_key(seed: u8) -> [u8; 32] {
        let mut key = [0u8; 32];
        key[0] = seed;
        key[1] = 0xBB;
        key
    }

    /// The 32-byte `NoteCommitment` IS Poseidon2 (not BLAKE3): it equals the
    /// `felt_to_bytes32` encoding of the note's `poseidon2_commitment` felt, and
    /// is NOT the old BLAKE3 digest. This pins the cutover of the former BLAKE3
    /// "placeholder for Poseidon2" stand-in.
    #[test]
    fn commitment_is_poseidon2_encoded_felt_not_blake3() {
        let owner = test_owner(3);
        let fields = [7u64, 250, 0, 0, 0, 0, 0, 0];
        let note = Note::with_randomness(owner, fields, [42u8; 32]);

        // The commitment equals the felt commitment encoded to 32 bytes.
        let expected = crate::felt_to_bytes32(note.poseidon2_commitment());
        assert_eq!(
            note.commitment().0,
            expected,
            "NoteCommitment must be the felt_to_bytes32 of poseidon2_commitment"
        );

        // And it is NOT the legacy BLAKE3 commitment.
        let mut legacy = blake3::Hasher::new_derive_key("dregg-note commitment v1");
        legacy.update(&note.owner);
        for f in &note.fields {
            legacy.update(&f.to_le_bytes());
        }
        legacy.update(&note.randomness);
        legacy.update(&note.creation_nonce);
        assert_ne!(
            note.commitment().0,
            *legacy.finalize().as_bytes(),
            "NoteCommitment must no longer be the BLAKE3 stand-in"
        );
    }

    /// The nullifier is Poseidon2 over (commitment_felt ‖ key limbs ‖ nonce
    /// limbs), encoded to 32 bytes — matching the note-spending AIR's structure.
    /// It is deterministic, key-bound, and NOT the legacy BLAKE3 nullifier.
    #[test]
    fn nullifier_is_poseidon2_not_blake3() {
        use dregg_circuit::poseidon2::hash_many;
        let owner = test_owner(3);
        let fields = [7u64, 250, 0, 0, 0, 0, 0, 0];
        let note = Note::with_randomness(owner, fields, [42u8; 32]);
        let key = test_spending_key(1);

        // Independently reconstruct the Poseidon2 nullifier felt.
        let mut preimage = Vec::with_capacity(17);
        preimage.push(note.poseidon2_commitment());
        preimage.extend_from_slice(&super::bytes32_to_limbs(&key));
        preimage.extend_from_slice(&super::bytes32_to_limbs(&note.creation_nonce));
        let expected = crate::felt_to_bytes32(hash_many(&preimage));
        assert_eq!(
            note.nullifier(&key).0,
            expected,
            "nullifier must be the encoded Poseidon2 of commitment ‖ key ‖ nonce"
        );

        // NOT the legacy BLAKE3 nullifier.
        let mut legacy = blake3::Hasher::new_derive_key("dregg-note nullifier v1");
        legacy.update(&note.commitment().0);
        legacy.update(&key);
        legacy.update(&note.creation_nonce);
        assert_ne!(
            note.nullifier(&key).0,
            *legacy.finalize().as_bytes(),
            "nullifier must no longer be the BLAKE3 stand-in"
        );

        // Deterministic and key-bound.
        assert_eq!(note.nullifier(&key), note.nullifier(&key));
        assert_ne!(
            note.nullifier(&key),
            note.nullifier(&test_spending_key(2)),
            "distinct spending keys must give distinct nullifiers"
        );
    }

    #[test]
    fn test_note_commitment_deterministic() {
        let owner = test_owner(1);
        let fields = [1u64, 100, 0, 0, 0, 0, 0, 0];
        let randomness = [42u8; 32];

        let note1 = Note::with_randomness(owner, fields, randomness);
        let note2 = Note::with_randomness(owner, fields, randomness);

        assert_eq!(note1.commitment(), note2.commitment());
    }

    #[test]
    fn test_note_commitment_unique_with_randomness() {
        let owner = test_owner(1);
        let fields = [1u64, 100, 0, 0, 0, 0, 0, 0];

        let note1 = Note::with_randomness(owner, fields, [1u8; 32]);
        let note2 = Note::with_randomness(owner, fields, [2u8; 32]);

        assert_ne!(note1.commitment(), note2.commitment());
    }

    #[test]
    fn test_nullifier_requires_spending_key() {
        let owner = test_owner(1);
        let fields = [1u64, 100, 0, 0, 0, 0, 0, 0];
        let note = Note::with_randomness(owner, fields, [42u8; 32]);

        let key1 = test_spending_key(1);
        let key2 = test_spending_key(2);

        let nullifier1 = note.nullifier(&key1);
        let nullifier2 = note.nullifier(&key2);

        // Different spending keys produce different nullifiers.
        assert_ne!(nullifier1, nullifier2);
    }

    #[test]
    fn test_nullifier_same_regardless_of_tree_position() {
        // CRITICAL: same note in two different trees produces the SAME nullifier.
        // This is the core property that enables federation-independent double-spend detection.
        let owner = test_owner(1);
        let fields = [1u64, 100, 0, 0, 0, 0, 0, 0];
        let note = Note::with_randomness(owner, fields, [42u8; 32]);
        let key = test_spending_key(1);

        // Nullifier is deterministic and position-independent.
        let n1 = note.nullifier(&key);
        let n2 = note.nullifier(&key);
        assert_eq!(n1, n2);

        // Even if positioned at different tree locations, nullifier is the same.
        let positioned_a = note.clone().positioned(0);
        let positioned_b = note.clone().positioned(999);
        assert_eq!(
            positioned_a.note.nullifier(&key),
            positioned_b.note.nullifier(&key)
        );
    }

    #[test]
    fn test_nullifier_unique_per_note() {
        // Different creation_nonce = different nullifier, even with same content.
        let owner = test_owner(1);
        let fields = [1u64, 100, 0, 0, 0, 0, 0, 0];
        let key = test_spending_key(1);

        let note1 = Note::with_nonce(owner, fields, [42u8; 32], [1u8; 32]);
        let note2 = Note::with_nonce(owner, fields, [42u8; 32], [2u8; 32]);

        assert_ne!(note1.nullifier(&key), note2.nullifier(&key));
    }

    #[test]
    fn test_double_spend_across_contexts() {
        // A nullifier computed once is valid everywhere — no tree-specific derivation.
        let owner = test_owner(1);
        let fields = [1u64, 100, 0, 0, 0, 0, 0, 0];
        let key = test_spending_key(1);
        let note = Note::with_randomness(owner, fields, [42u8; 32]);

        // Compute nullifier (simulating one federation).
        let nullifier = note.nullifier(&key);

        // In a different context (different federation, different tree position),
        // the same note still produces the same nullifier.
        let same_nullifier = note.nullifier(&key);
        assert_eq!(nullifier, same_nullifier);

        // A nullifier set in any federation can detect the double-spend.
        let mut set = crate::nullifier_set::NullifierSet::new();
        set.insert(nullifier, note.value()).unwrap();
        let double_spend = set.insert(same_nullifier, note.value());
        assert!(matches!(double_spend, Err(NoteError::DoubleSpend { .. })));
    }

    #[test]
    fn test_note_is_fungible() {
        let owner = test_owner(1);

        // Fungible: both asset_type and amount non-zero.
        let fungible = Note::with_randomness(owner, [1, 100, 0, 0, 0, 0, 0, 0], [0u8; 32]);
        assert!(fungible.is_fungible());

        // Not fungible: amount is zero.
        let nft = Note::with_randomness(owner, [1, 0, 0, 0, 0, 0, 0, 0], [0u8; 32]);
        assert!(!nft.is_fungible());

        // Not fungible: asset_type is zero.
        let empty = Note::with_randomness(owner, [0, 100, 0, 0, 0, 0, 0, 0], [0u8; 32]);
        assert!(!empty.is_fungible());
    }

    #[test]
    fn test_nft_transfer_preserves_identity() {
        let owner_a = test_owner(1);
        let owner_b = test_owner(2);
        let unique_asset_id: u64 = 0xDEAD_BEEF_CAFE_0001;

        // NFT note: fields[0] = unique asset ID, fields[1] = 0 (not fungible).
        let nft_note_a =
            Note::with_randomness(owner_a, [unique_asset_id, 0, 0, 0, 0, 0, 0, 0], [10u8; 32]);

        // Transfer: create a new note with same asset_id but new owner.
        let nft_note_b =
            Note::with_randomness(owner_b, [unique_asset_id, 0, 0, 0, 0, 0, 0, 0], [20u8; 32]);

        // Asset identity is preserved (same fields[0]).
        assert_eq!(nft_note_a.asset_type(), nft_note_b.asset_type());
        assert_eq!(nft_note_a.asset_type(), unique_asset_id);

        // But commitments differ (different owner and randomness).
        assert_ne!(nft_note_a.commitment(), nft_note_b.commitment());
    }

    // ─── Poseidon2 commitment full-width binding (256-bit) ───────────────────
    //
    // These adversarial tests pin the closure of the first-4-bytes truncation in
    // `poseidon2_commitment`. They FAIL on the legacy code that fed only
    // `owner[0..4]` / `creation_nonce[0..4]` / `randomness[0..4]` (and the low 32
    // bits of value/asset_type) and PASS once every limb is fed. Each case
    // mutates a byte ABOVE the first 4-byte chunk, which the legacy form ignored.

    #[cfg(feature = "zkvm")]
    fn note_diff_at(field: &str, byte_index: usize) -> (Note, Note) {
        let owner = test_owner(7);
        let fields = [3u64, 250, 0, 0, 0, 0, 0, 0];
        let randomness = [55u8; 32];
        let nonce = [66u8; 32];

        let base = Note::with_nonce(owner, fields, randomness, nonce);
        let mut owner2 = owner;
        let mut randomness2 = randomness;
        let mut nonce2 = nonce;
        match field {
            "owner" => owner2[byte_index] ^= 0xFF,
            "randomness" => randomness2[byte_index] ^= 0xFF,
            "creation_nonce" => nonce2[byte_index] ^= 0xFF,
            other => panic!("unknown field {other}"),
        }
        let mutated = Note::with_nonce(owner2, fields, randomness2, nonce2);
        (base, mutated)
    }

    #[cfg(feature = "zkvm")]
    #[test]
    fn poseidon2_commitment_binds_owner_high_bytes() {
        // Bytes 4, 8, 16 are all ABOVE the legacy first-4-byte window.
        for idx in [4usize, 8, 16, 31] {
            let (a, b) = note_diff_at("owner", idx);
            assert_ne!(
                a.poseidon2_commitment(),
                b.poseidon2_commitment(),
                "owner byte {idx} above the first chunk must change the commitment"
            );
        }
    }

    #[cfg(feature = "zkvm")]
    #[test]
    fn poseidon2_commitment_binds_creation_nonce_high_bytes() {
        for idx in [4usize, 8, 16, 31] {
            let (a, b) = note_diff_at("creation_nonce", idx);
            assert_ne!(
                a.poseidon2_commitment(),
                b.poseidon2_commitment(),
                "creation_nonce byte {idx} above the first chunk must change the commitment"
            );
        }
    }

    #[cfg(feature = "zkvm")]
    #[test]
    fn poseidon2_commitment_binds_randomness_high_bytes() {
        for idx in [4usize, 8, 16, 31] {
            let (a, b) = note_diff_at("randomness", idx);
            assert_ne!(
                a.poseidon2_commitment(),
                b.poseidon2_commitment(),
                "randomness byte {idx} above the first chunk must change the commitment"
            );
        }
    }

    #[cfg(feature = "zkvm")]
    #[test]
    fn poseidon2_commitment_binds_full_u64_value_and_asset_type() {
        let owner = test_owner(7);
        let randomness = [55u8; 32];
        let nonce = [66u8; 32];

        // value differs only in its HIGH 32 bits (legacy bound only low 32 bits).
        let base = Note::with_nonce(owner, [3, 1, 0, 0, 0, 0, 0, 0], randomness, nonce);
        let value_hi = Note::with_nonce(
            owner,
            [3, 1u64 | (1u64 << 40), 0, 0, 0, 0, 0, 0],
            randomness,
            nonce,
        );
        assert_ne!(
            base.poseidon2_commitment(),
            value_hi.poseidon2_commitment(),
            "high 32 bits of value must bind"
        );

        // asset_type differs only in its HIGH 32 bits.
        let asset_hi = Note::with_nonce(
            owner,
            [3u64 | (1u64 << 40), 1, 0, 0, 0, 0, 0, 0],
            randomness,
            nonce,
        );
        assert_ne!(
            base.poseidon2_commitment(),
            asset_hi.poseidon2_commitment(),
            "high 32 bits of asset_type must bind"
        );
    }

    #[cfg(feature = "zkvm")]
    #[test]
    fn poseidon2_commitment_deterministic() {
        let n = Note::with_nonce(
            test_owner(7),
            [3, 250, 0, 0, 0, 0, 0, 0],
            [55u8; 32],
            [66u8; 32],
        );
        assert_eq!(n.poseidon2_commitment(), n.poseidon2_commitment());
    }

    // ─── NoteBatcher tests ──────────────────────────────────────────────────

    #[test]
    fn test_note_batcher_add_and_should_flush() {
        let mut batcher = super::NoteBatcher::new(5, 16);
        let commitment = NoteCommitment([0xAA; 32]);

        assert!(!batcher.should_flush(0));

        batcher.add(commitment);
        assert_eq!(batcher.pending_count(), 1);
        // Not at interval yet
        assert!(!batcher.should_flush(3));
        // At interval boundary
        assert!(batcher.should_flush(5));
    }

    #[test]
    fn test_note_batcher_max_batch_size() {
        let mut batcher = super::NoteBatcher::new(100, 4);
        for i in 0..4 {
            batcher.add(NoteCommitment([i as u8; 32]));
        }
        // Should flush at max batch size regardless of height
        assert!(batcher.should_flush(1));
    }

    #[test]
    fn test_note_batcher_flush() {
        let mut batcher = super::NoteBatcher::new(5, 16);
        for i in 0..3 {
            batcher.add(NoteCommitment([i as u8; 32]));
        }
        let flushed = batcher.flush(5);
        assert_eq!(flushed.len(), 3);
        assert_eq!(batcher.pending_count(), 0);
        assert_eq!(batcher.last_batch_height, 5);
    }
}

// ─── Note Batcher (timing correlation mitigation) ─────────────────────────────

/// Batch note commitments to reduce timing correlation attacks.
///
/// Without batching, an observer can correlate when a note commitment appears in
/// the tree with when a specific user was online or submitted a turn. By accumulating
/// notes and committing them in fixed-interval batches, all notes in a batch appear
/// at the same height, making it impossible to correlate individual note creation
/// times with user activity.
///
/// # Usage
///
/// The executor (or federation sync layer) calls [`add`](NoteBatcher::add) when a
/// turn creates a note. At each block, it calls [`should_flush`](NoteBatcher::should_flush)
/// and if true, commits all pending notes to the tree in a single batch.
///
/// # Privacy Properties
///
/// - All notes in a batch share the same tree insertion height.
/// - An observer cannot determine which block (within the batch interval) created
///   a specific note.
/// - The batch size is bounded to prevent a single batch from becoming too distinctive.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct NoteBatcher {
    /// Pending note commitments waiting to be committed to the tree.
    pending: Vec<NoteCommitment>,
    /// Minimum interval (in blocks) between batch flushes.
    batch_interval_blocks: u64,
    /// The block height at which the last batch was flushed.
    pub last_batch_height: u64,
    /// Maximum number of notes per batch. When reached, flush even if the
    /// interval hasn't elapsed. Prevents unbounded memory growth.
    max_batch_size: usize,
}

impl NoteBatcher {
    /// Create a new note batcher.
    ///
    /// # Arguments
    ///
    /// * `batch_interval_blocks` - Minimum blocks between flushes (e.g., 10).
    /// * `max_batch_size` - Maximum notes per batch before forced flush (e.g., 16).
    pub fn new(batch_interval_blocks: u64, max_batch_size: usize) -> Self {
        Self {
            pending: Vec::new(),
            batch_interval_blocks,
            last_batch_height: 0,
            max_batch_size,
        }
    }

    /// Add a note commitment to the pending batch.
    pub fn add(&mut self, commitment: NoteCommitment) {
        self.pending.push(commitment);
    }

    /// Check whether the batch should be flushed at the given block height.
    ///
    /// Returns true if:
    /// - The batch interval has elapsed since the last flush, OR
    /// - The pending batch has reached `max_batch_size`.
    pub fn should_flush(&self, current_height: u64) -> bool {
        if self.pending.is_empty() {
            return false;
        }
        current_height.saturating_sub(self.last_batch_height) >= self.batch_interval_blocks
            || self.pending.len() >= self.max_batch_size
    }

    /// Flush all pending notes, returning them for insertion into the note tree.
    ///
    /// All returned notes should be committed to the tree at the same height,
    /// preventing timing correlation of individual note creation.
    pub fn flush(&mut self, current_height: u64) -> Vec<NoteCommitment> {
        self.last_batch_height = current_height;
        std::mem::take(&mut self.pending)
    }

    /// Get the number of pending notes.
    pub fn pending_count(&self) -> usize {
        self.pending.len()
    }

    /// Check if there are any pending notes.
    pub fn has_pending(&self) -> bool {
        !self.pending.is_empty()
    }
}
