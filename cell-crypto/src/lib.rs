//! # dregg-cell-crypto
//!
//! The cryptographic capability/note/value machinery that operates over the
//! crypto-free types in [`dregg_cell`]. Splitting this out keeps `dregg-cell` a
//! pure types crate: a consumer that only needs `CellState` / capability /
//! delegation / ledger types depends on `dregg-cell`; a consumer that signs,
//! seals, encrypts, or proves over cells additionally depends on this crate.
//!
//! This holds the bulletproofs / dalek / chacha / merlin stack plus the two
//! crypto constructors that previously lived as methods on `dregg-cell` core
//! types (now free functions: [`note::new_note`] and
//! [`delegation::verify_parent_signature`]).

pub mod capability_proof;
pub mod note_bridge;
pub mod note_encryption;
pub mod oblivious_transfer;
pub mod peer_exchange;
pub mod read_cap;
pub mod seal;
pub mod stealth;
pub mod value_commitment;
pub mod value_link_zk;

/// The crypto constructor for [`dregg_cell::note::Note`] (moved off the type so
/// `dregg-cell` carries no `getrandom` dependency).
pub mod note {
    use dregg_cell::note::Note;

    /// Create a new note with cryptographically random blinding and a unique creation nonce.
    ///
    /// The randomness field is filled with OS randomness via `getrandom` to ensure
    /// the blinding factor is cryptographically unpredictable. The creation_nonce is
    /// derived from the randomness for domain separation. Two calls at the same
    /// nanosecond will produce distinct notes.
    pub fn new_note(owner: [u8; 32], fields: [u64; 8]) -> Note {
        // Use OS randomness for the blinding factor — MUST be cryptographically random.
        let mut randomness = [0u8; 32];
        getrandom::fill(&mut randomness).expect("getrandom failed");

        // Derive creation_nonce from randomness (independent domain separation).
        let mut nonce_hasher = blake3::Hasher::new_derive_key("dregg-note creation-nonce v1");
        nonce_hasher.update(&owner);
        nonce_hasher.update(&randomness);
        let mut creation_nonce = [0u8; 32];
        creation_nonce.copy_from_slice(nonce_hasher.finalize().as_bytes());

        // Reuse the deterministic constructor with the freshly-sampled randomness;
        // it re-derives the same creation_nonce from (owner, randomness).
        Note::with_randomness(owner, fields, randomness)
    }
}

/// The crypto verifier for [`dregg_cell::delegation::DelegatedRef`] (moved off
/// the type so `dregg-cell` carries no `ed25519-dalek` dependency).
pub mod delegation {
    use dregg_cell::delegation::DelegatedRef;

    /// Verify the parent's signature over this delegation.
    ///
    /// Returns `true` if the signature is valid for the given parent public key.
    pub fn verify_parent_signature(d: &DelegatedRef, parent_pubkey: &[u8; 32]) -> bool {
        use ed25519_dalek::{Signature, VerifyingKey};

        let message =
            DelegatedRef::signing_message(&d.clist_commitment, d.delegation_epoch, &d.child);
        let signature = Signature::from_bytes(&d.parent_signature);

        if let Ok(vk) = VerifyingKey::from_bytes(parent_pubkey) {
            vk.verify_strict(&message, &signature).is_ok()
        } else {
            false
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Re-exports (mirroring what `dregg-cell` previously re-exported under the
// `crypto` feature, so `dregg_cell_crypto::<Item>` resolves the same names).
// ─────────────────────────────────────────────────────────────────────────────

pub use capability_proof::{
    CAP_PROOF_PQ_CTX, CapabilityExerciseRequest, CapabilityExerciseResponse, CapabilityProof,
    CapabilityProofData, CapabilityProofError, MlDsaCapKey, PeerEffect, VerificationContext,
    enrolled_ml_dsa_pubkey, ml_dsa_cap_verify, sign_capability_proof,
};
pub use note_bridge::{
    BridgeDestination, BridgeError, BridgeReceipt, BridgeState, BridgedNullifierSet, PendingBridge,
    PendingBridgeSet, PortableNoteProof, cancel_bridge, create_portable_note, finalize_bridge,
    initiate_bridge, verify_bridge_receipt, verify_portable_note,
};
pub use note_encryption::{NoteDecryptError, NotePlaintext, decrypt_note, encrypt_note_to};
pub use oblivious_transfer::{
    OtError, OtReceiver, OtReceiverResponse, OtSender, OtSenderPayload, OtSenderSetup, ot_1_of_n,
};
pub use peer_exchange::{PeerCellView, PeerExchange, PeerExchangeError, PeerStateTransition};
pub use read_cap::{
    EncryptedSlot, EncryptedState, FieldSet, ReadCap, ReadCapError, SlotOpening, ViewKey,
    is_read_attenuation,
};
pub use seal::{SealError, SealPair, SealedBox, SealerPublic, test_seal_pair};
pub use stealth::{StealthAddress, StealthAnnouncement, StealthKeys, StealthMetaAddress};
pub use value_commitment::{
    AssetEqualityError, AssetEqualityProof, BulletproofRangeProof, CommittedNote,
    CommittedNoteOpening, ConservationError, ConservationProof, FullConservationError,
    FullConservationProof, ValueCommitment, ValueCommitmentBytes, asset_tag_generator,
    prove_asset_conservation, prove_asset_equality, prove_asset_equality_with_message,
    prove_conservation, prove_conservation_with_range, verify_asset_conservation,
    verify_asset_equality, verify_asset_equality_with_message, verify_conservation,
    verify_conservation_with_range,
};
pub use value_link_zk::{
    LinkLegBindingProof, VALUE_BITS, ZkLeafLegLink, ZkValueLinkError, ZkValueLinkProof,
    prove_link_leg_binding, prove_zk_leaf_leg_link, prove_zk_value_link, value_binding_pi_bytes,
    verify_link_leg_binding, verify_zk_leaf_leg_link, verify_zk_value_link,
};
