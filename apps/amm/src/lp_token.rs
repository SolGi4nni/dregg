//! LP token minting and burning via the note model.
//!
//! LP tokens are represented as Notes with:
//! - `fields[0]` = LP asset type (derived from pool ID)
//! - `fields[1]` = amount
//!
//! Minting creates new notes; burning spends them (reveals nullifiers).

use pyana_cell::note::{Note, NoteCommitment, Nullifier};

use crate::pool::PoolId;

/// LP token identity derived from pool ID.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LpTokenId {
    /// The asset_type value stored in note fields[0].
    asset_type: u64,
    /// Source pool ID.
    pool_id: PoolId,
}

impl LpTokenId {
    /// Derive an LP token ID from a pool ID.
    pub fn new(pool_id: &PoolId) -> Self {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"LP");
        hasher.update(pool_id);
        let hash = hasher.finalize();
        let bytes: [u8; 8] = hash.as_bytes()[..8].try_into().unwrap();
        let asset_type = u64::from_le_bytes(bytes);

        Self {
            asset_type,
            pool_id: *pool_id,
        }
    }

    /// Get the asset type value for note fields[0].
    pub fn as_asset_type(&self) -> u64 {
        self.asset_type
    }

    /// Get the source pool ID.
    pub fn pool_id(&self) -> &PoolId {
        &self.pool_id
    }
}

/// Create a new LP token note (minting).
///
/// The owner receives `amount` LP tokens as a new note commitment.
pub fn mint_lp_note(owner: [u8; 32], lp_id: &LpTokenId, amount: u64, nonce: [u8; 32]) -> Note {
    let mut fields = [0u64; 8];
    fields[0] = lp_id.as_asset_type();
    fields[1] = amount;

    // Randomness for commitment uniqueness
    let mut randomness = [0u8; 32];
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"pyana-lp-mint-randomness");
    hasher.update(&owner);
    hasher.update(&amount.to_le_bytes());
    hasher.update(&nonce);
    let hash = hasher.finalize();
    randomness.copy_from_slice(hash.as_bytes());

    Note {
        owner,
        fields,
        randomness,
        creation_nonce: nonce,
    }
}

/// Compute the commitment for an LP token note.
pub fn lp_note_commitment(note: &Note) -> NoteCommitment {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"pyana-note commitment v1");
    hasher.update(&note.owner);
    for field in &note.fields {
        hasher.update(&field.to_le_bytes());
    }
    hasher.update(&note.randomness);
    hasher.update(&note.creation_nonce);
    NoteCommitment(*hasher.finalize().as_bytes())
}

/// Compute the nullifier for spending an LP token note.
pub fn lp_note_nullifier(note: &Note, spending_key: &[u8; 32]) -> Nullifier {
    let commitment = lp_note_commitment(note);
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"pyana-note nullifier v1");
    hasher.update(&commitment.0);
    hasher.update(spending_key);
    hasher.update(&note.creation_nonce);
    Nullifier(*hasher.finalize().as_bytes())
}

/// Validate that a note is an LP token for a specific pool.
pub fn validate_lp_note(note: &Note, lp_id: &LpTokenId) -> bool {
    note.fields[0] == lp_id.as_asset_type()
}

/// Get the LP amount from a note.
pub fn lp_amount(note: &Note) -> u64 {
    note.fields[1]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lp_token_id_deterministic() {
        let pool_id = [42u8; 32];
        let id1 = LpTokenId::new(&pool_id);
        let id2 = LpTokenId::new(&pool_id);
        assert_eq!(id1.as_asset_type(), id2.as_asset_type());
    }

    #[test]
    fn test_mint_and_validate() {
        let pool_id = [1u8; 32];
        let lp_id = LpTokenId::new(&pool_id);
        let owner = [99u8; 32];
        let nonce = [7u8; 32];

        let note = mint_lp_note(owner, &lp_id, 500, nonce);
        assert!(validate_lp_note(&note, &lp_id));
        assert_eq!(lp_amount(&note), 500);
    }

    #[test]
    fn test_nullifier_requires_key() {
        let pool_id = [1u8; 32];
        let lp_id = LpTokenId::new(&pool_id);
        let owner = [99u8; 32];
        let nonce = [7u8; 32];
        let note = mint_lp_note(owner, &lp_id, 100, nonce);

        let key1 = [10u8; 32];
        let key2 = [20u8; 32];
        let n1 = lp_note_nullifier(&note, &key1);
        let n2 = lp_note_nullifier(&note, &key2);
        assert_ne!(n1, n2);
    }
}
