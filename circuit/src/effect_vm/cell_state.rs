//! The `CellState` struct: the cell state that flows between AIR rows.
//!
//! Includes the canonical state-commitment tree (used by AIR_DESCRIPTOR
//! and the per-row state_commit continuity column) and the widened
//! 4-felt commitment used in PI[OLD/NEW_COMMIT_BASE].

use crate::field::BabyBear;
use crate::poseidon2::hash_4_to_1;

use super::{split_u64, state};

/// Cell state that flows between rows.
#[derive(Clone, Debug)]
pub struct CellState {
    /// Balance as u64 (split into lo/hi for BabyBear encoding).
    pub balance: u64,
    /// Monotonic nonce.
    pub nonce: u32,
    /// 8 custom field values.
    pub fields: [BabyBear; 8],
    /// Capability list Merkle root.
    pub capability_root: BabyBear,
    /// Running state commitment.
    pub state_commitment: BabyBear,
    /// Sealed field mask: bit i set means field i is sealed against mutation.
    pub sealed_field_mask: u32,
    /// Mode flag: 0 = managed, 1 = sovereign.
    pub mode_flag: u32,
}

impl CellState {
    /// Create a new cell state with default values.
    pub fn new(balance: u64, nonce: u32) -> Self {
        let fields = [BabyBear::ZERO; 8];
        let capability_root = BabyBear::ZERO;
        // Initial state commitment is hash of all state elements.
        let state_commitment = Self::compute_commitment(balance, nonce, &fields, capability_root);
        Self {
            balance,
            nonce,
            fields,
            capability_root,
            state_commitment,
            sealed_field_mask: 0,
            mode_flag: 0,
        }
    }

    /// Compute the state commitment from all state components using a
    /// constrainable tree of hash_4_to_1 calls.
    ///
    /// Tree structure:
    ///   inter1 = hash_4_to_1(balance_lo, balance_hi, nonce, field[0])
    ///   inter2 = hash_4_to_1(field[1], field[2], field[3], field[4])
    ///   inter3 = hash_4_to_1(field[5], field[6], field[7], cap_root)
    ///   commitment = hash_4_to_1(inter1, inter2, inter3, ZERO)
    ///
    /// The fourth input to the root hash is ZERO (reserved for future use).
    /// This structure is directly constrainable because each hash_4_to_1 can be
    /// verified by the evaluator at each trace row.
    pub fn compute_commitment(
        balance: u64,
        nonce: u32,
        fields: &[BabyBear; 8],
        capability_root: BabyBear,
    ) -> BabyBear {
        let (lo, hi) = split_u64(balance);
        let inter1 = hash_4_to_1(&[lo, hi, BabyBear::new(nonce), fields[0]]);
        let inter2 = hash_4_to_1(&[fields[1], fields[2], fields[3], fields[4]]);
        let inter3 = hash_4_to_1(&[fields[5], fields[6], fields[7], capability_root]);
        hash_4_to_1(&[inter1, inter2, inter3, BabyBear::ZERO])
    }

    /// Stage 1: compute the 4-felt state commitment for the public input layout.
    ///
    /// Position 0 matches [`compute_commitment`] exactly (the in-trace
    /// continuity column). Positions 1..3 are 3 additional independent
    /// Poseidon2 compressions of the same intermediates with different
    /// "salt" felts. The result is bound at row-0 / last-row boundaries
    /// (position 0 in-trace; positions 1..3 via PI matching against the
    /// executor's independently-computed canonical form).
    ///
    /// AUDIT[stage1-pi-only-bound]: positions 1..3 are constrained only by
    /// the executor's PI-matching loop (see `turn/src/executor.rs::verify_proof_carrying_turn`)
    /// — they bind the proof to the verifier's view of cell state but not
    /// to the trace. Stage 2 may add aux columns to extend the in-trace
    /// continuity binding to all 4 felts.
    pub fn compute_commitment_4(
        balance: u64,
        nonce: u32,
        fields: &[BabyBear; 8],
        capability_root: BabyBear,
    ) -> [BabyBear; 4] {
        let (lo, hi) = split_u64(balance);
        let inter1 = hash_4_to_1(&[lo, hi, BabyBear::new(nonce), fields[0]]);
        let inter2 = hash_4_to_1(&[fields[1], fields[2], fields[3], fields[4]]);
        let inter3 = hash_4_to_1(&[fields[5], fields[6], fields[7], capability_root]);
        [
            hash_4_to_1(&[inter1, inter2, inter3, BabyBear::ZERO]),
            hash_4_to_1(&[inter1, inter2, inter3, BabyBear::ONE]),
            hash_4_to_1(&[inter1, inter2, inter3, BabyBear::new(2)]),
            hash_4_to_1(&[inter1, inter2, inter3, BabyBear::new(3)]),
        ]
    }

    /// Compute the three intermediate hashes for the state commitment tree.
    /// Returns (inter1, inter2, inter3) which are needed as witness values.
    pub fn compute_commitment_intermediates(
        balance: u64,
        nonce: u32,
        fields: &[BabyBear; 8],
        capability_root: BabyBear,
    ) -> (BabyBear, BabyBear, BabyBear) {
        let (lo, hi) = split_u64(balance);
        let inter1 = hash_4_to_1(&[lo, hi, BabyBear::new(nonce), fields[0]]);
        let inter2 = hash_4_to_1(&[fields[1], fields[2], fields[3], fields[4]]);
        let inter3 = hash_4_to_1(&[fields[5], fields[6], fields[7], capability_root]);
        (inter1, inter2, inter3)
    }

    /// Recompute and update the state commitment.
    pub fn refresh_commitment(&mut self) {
        self.state_commitment =
            Self::compute_commitment(self.balance, self.nonce, &self.fields, self.capability_root);
    }

    /// Encode state into trace columns (14 elements).
    pub(super) fn to_trace_cols(&self) -> Vec<BabyBear> {
        let (lo, hi) = split_u64(self.balance);
        let mut cols = Vec::with_capacity(state::SIZE);
        cols.push(lo); // balance_lo
        cols.push(hi); // balance_hi
        cols.push(BabyBear::new(self.nonce)); // nonce
        cols.extend_from_slice(&self.fields); // field_values[0..8]
        cols.push(self.capability_root); // cap_root
        cols.push(self.state_commitment); // state_commit
        cols.push(BabyBear::new(
            self.sealed_field_mask | (self.mode_flag << 8),
        )); // reserved: sealed_mask | mode_flag
        assert_eq!(cols.len(), state::SIZE);
        cols
    }
}
