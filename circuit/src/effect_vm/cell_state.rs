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
    /// Record digest: a single Poseidon2 felt folding ALL authority-bearing cell
    /// state that the balance/nonce/fields/cap_root limbs do NOT carry —
    /// permissions, verification key, lifecycle, deathCert, delegate, delegation,
    /// program, mode, sealed-field mask, visibility, the side-table roots, and
    /// `fields[8..]`. This is the EffectVM analog of the canonical commitment's
    /// authority residue (cell-side `dregg_cell::compute_authority_digest_felt`
    /// and the Lean `recStateCommit`'s `RH`/`record_digest` rest-hash limb).
    ///
    /// It is ABSORBED as the fourth input of the state-commitment root hash
    /// (replacing the old literal `ZERO`), so `OLD_COMMIT`/`NEW_COMMIT` bind the
    /// FULL cell state, not the lossy `(balance, nonce, fields, cap_root)` subset
    /// (audit P0-2 — `cell/src/commitment.rs`, `REVIEW[circuit-fix-coordination]`).
    ///
    /// A cell with no authority residue beyond the carried limbs uses
    /// [`crate::cap_root::empty_record_digest`] — a cell-independent constant —
    /// so the absorption is a uniform no-op for such cells (structurally mirroring
    /// the Lean `legacyReferenceCommitS` / `emptySystemRootsDigest` no-op fold).
    pub record_digest: BabyBear,
    /// Running state commitment.
    pub state_commitment: BabyBear,
    /// Sealed field mask: bit i set means field i is sealed against mutation.
    pub sealed_field_mask: u32,
    /// Mode flag: 0 = managed, 1 = sovereign.
    pub mode_flag: u32,
}

impl CellState {
    /// Create a new cell state with default values. The `capability_root` is
    /// seeded with the EMPTY c-list root ([`crate::cap_root::empty_capability_root`])
    /// — the openable sorted-Poseidon2 root of a cell holding no capabilities —
    /// NOT `BabyBear::ZERO`. This is the cap Phase A seed: a fresh actor cell's
    /// circuit `cap_root` now equals its cell-side
    /// `compute_canonical_capability_root`, instead of the disjoint ZERO that
    /// tied the circuit to nothing. For a cell that already holds capabilities,
    /// the prover seeds the real root via [`CellState::with_capability_root`].
    pub fn new(balance: u64, nonce: u32) -> Self {
        // The deployed `cap_root` column is the 1-felt LANE-0 of the native 8-felt
        // cap-tree root (Phase H-CAP-8). The full 8 felts ride the rotated cap-open
        // appendix's root-pins (limb 25 ‖ headroom 51..57); this carried column seeds
        // lane 0. The VK epoch: lane-0's VALUE moves (node8 lane-0 ≠ old 1-felt cap_node).
        Self::with_capability_root(balance, nonce, crate::cap_root::empty_capability_root()[0])
    }

    /// Create a new cell state seeding `capability_root` from a caller-supplied
    /// value — the cell's real canonical capability root
    /// (`dregg_cell::compute_canonical_capability_root_felt`). The node /
    /// cipherclerk prover paths use this so a turn over a cell that holds
    /// capabilities binds the SAME `cap_root` the cell commits to (cap Phase A).
    pub fn with_capability_root(balance: u64, nonce: u32, capability_root: BabyBear) -> Self {
        Self::with_capability_root_and_record_digest(
            balance,
            nonce,
            capability_root,
            crate::cap_root::empty_record_digest(),
        )
    }

    /// Create a new cell state seeding BOTH `capability_root` and `record_digest`
    /// from caller-supplied values — the cell's real canonical capability root
    /// and its authority-residue digest (`dregg_cell::compute_authority_digest_felt`).
    /// A cell carrying authority state beyond the welded limbs (permissions / VK /
    /// lifecycle / …) seeds the real digest here so its circuit `state_commit` binds
    /// the FULL cell state (audit P0-2).
    pub fn with_capability_root_and_record_digest(
        balance: u64,
        nonce: u32,
        capability_root: BabyBear,
        record_digest: BabyBear,
    ) -> Self {
        let fields = [BabyBear::ZERO; 8];
        // Initial state commitment is hash of all state elements.
        let state_commitment =
            Self::compute_commitment(balance, nonce, &fields, capability_root, record_digest);
        Self {
            balance,
            nonce,
            fields,
            capability_root,
            record_digest,
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
    ///   commitment = hash_4_to_1(inter1, inter2, inter3, record_digest)
    ///
    /// The fourth input to the root hash is the `record_digest` — the single
    /// Poseidon2 felt folding ALL authority-bearing state the other limbs do not
    /// carry (permissions / VK / lifecycle / deathCert / delegate / delegation /
    /// program / mode / visibility / side-table roots / `fields[8..]`). This makes
    /// the commitment (and `OLD_COMMIT`/`NEW_COMMIT`) bind the FULL cell state,
    /// closing audit P0-2 (`cell/src/commitment.rs`,
    /// `REVIEW[circuit-fix-coordination]`), structurally mirroring the Lean
    /// `recStateCommit = cmb(cellDigest, RH)` (the rest-hash limb) and
    /// `cellCommitS = compressN(rest ++ [systemRootsDigest])` (one absorbed digest
    /// limb). A residue-free cell carries [`crate::cap_root::empty_record_digest`]
    /// (`ZERO`), so the absorption is byte-identical to the legacy lossy form for
    /// such cells — the no-op cutover.
    ///
    /// This structure is directly constrainable because each hash_4_to_1 can be
    /// verified by the evaluator at each trace row.
    pub fn compute_commitment(
        balance: u64,
        nonce: u32,
        fields: &[BabyBear; 8],
        capability_root: BabyBear,
        record_digest: BabyBear,
    ) -> BabyBear {
        let (lo, hi) = split_u64(balance);
        let inter1 = hash_4_to_1(&[lo, hi, BabyBear::new(nonce), fields[0]]);
        let inter2 = hash_4_to_1(&[fields[1], fields[2], fields[3], fields[4]]);
        let inter3 = hash_4_to_1(&[fields[5], fields[6], fields[7], capability_root]);
        hash_4_to_1(&[inter1, inter2, inter3, record_digest])
    }

    /// Phase C: compute the 8-felt state commitment for the public input layout.
    ///
    /// THE FLOOR this closes (`docs/FAITHFUL-STATE-COMMITMENT.md`): a 4-felt
    /// BabyBear Poseidon2 digest has ~62-bit COLLISION resistance (half the
    /// ~124-bit digest width) — below the system's FRI ~128-bit soundness. Eight
    /// genuine, independent Poseidon2 squeeze felts give ~124-bit collision
    /// resistance, matching the FRI floor.
    ///
    /// All 8 felts are GENUINE Poseidon2 outputs — NEVER 4 real + 4 zero-padded
    /// (zero-padding keeps the same ~62-bit floor). Position 0 matches
    /// [`compute_commitment`] exactly (the in-trace continuity column, root of
    /// the constrainable hash tree). Positions 1..7 are 7 further independent
    /// Poseidon2 compressions of the SAME three intermediates plus the
    /// record_digest, each carrying a distinct salt felt (1..7), so every felt
    /// is a full-state squeeze.
    ///
    /// AUDIT[stage1-pi-only-bound]: positions 1..7 are constrained only by the
    /// executor's PI-matching loop (see
    /// `turn/src/executor.rs::verify_proof_carrying_turn`) — they bind the proof
    /// to the verifier's independently-computed canonical commitment, not to the
    /// trace. The in-trace continuity binding (the AIR's STATE_COMMIT column +
    /// Lean `saCol STATE_COMMIT` piBinding) pins position 0; the off-AIR PI match
    /// over all 8 felts is what raises the collision floor to ~124 bits.
    pub fn compute_commitment_8(
        balance: u64,
        nonce: u32,
        fields: &[BabyBear; 8],
        capability_root: BabyBear,
        record_digest: BabyBear,
    ) -> [BabyBear; 8] {
        let (lo, hi) = split_u64(balance);
        let inter1 = hash_4_to_1(&[lo, hi, BabyBear::new(nonce), fields[0]]);
        let inter2 = hash_4_to_1(&[fields[1], fields[2], fields[3], fields[4]]);
        let inter3 = hash_4_to_1(&[fields[5], fields[6], fields[7], capability_root]);
        // Position 0 matches `compute_commitment` exactly (absorbs `record_digest`
        // as the fourth root input). The remaining 7 felts salt-compress the SAME
        // three intermediates AND the record_digest with distinct salts 1..7, so
        // all 8 felts are genuine independent squeezes binding the full state.
        let inter4 = hash_4_to_1(&[inter1, inter2, inter3, record_digest]);
        let mut out = [BabyBear::ZERO; 8];
        out[0] = inter4;
        for (i, slot) in out.iter_mut().enumerate().skip(1) {
            *slot = hash_4_to_1(&[
                inter4,
                record_digest,
                BabyBear::new(i as u32),
                BabyBear::ZERO,
            ]);
        }
        out
    }

    /// Backward-compat 4-felt form: the first 4 felts of [`compute_commitment_8`].
    /// Retained for callers/tests that only need the legacy 4-felt prefix; the
    /// values are byte-identical to the first 4 entries of the 8-felt form.
    pub fn compute_commitment_4(
        balance: u64,
        nonce: u32,
        fields: &[BabyBear; 8],
        capability_root: BabyBear,
        record_digest: BabyBear,
    ) -> [BabyBear; 4] {
        let c8 = Self::compute_commitment_8(balance, nonce, fields, capability_root, record_digest);
        [c8[0], c8[1], c8[2], c8[3]]
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
        self.state_commitment = Self::compute_commitment(
            self.balance,
            self.nonce,
            &self.fields,
            self.capability_root,
            self.record_digest,
        );
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

#[cfg(test)]
mod tests {
    use super::*;

    /// **P0-2 (audit `cell/src/commitment.rs`, REVIEW[circuit-fix-coordination]).**
    /// Two cells differing ONLY in their authority residue (`record_digest`) — same
    /// balance, nonce, fields, cap_root — must produce DIFFERENT state commitments.
    /// This is the gap the old `hash_4_to_1(inter1, inter2, inter3, ZERO)` left open:
    /// permissions / VK / lifecycle lived ONLY in `record_digest`, which the lossy form
    /// dropped, so a locked-down cell and a wide-open one collided. Absorbing
    /// `record_digest` as the fourth root input closes it.
    #[test]
    fn record_digest_binds_commitment_p0_2() {
        let balance = 1_000u64;
        let nonce = 7u32;
        let fields = [BabyBear::new(3); 8];
        // The legacy v1 1-felt commitment takes a single cap-root felt; use the
        // lane-0 projection of the faithful 8-felt empty root.
        let cap_root = crate::cap_root::empty_capability_root()[0];

        // Same carried state, two DIFFERENT authority residues.
        let rd_a = BabyBear::new(11);
        let rd_b = BabyBear::new(22);

        let c_a = CellState::compute_commitment(balance, nonce, &fields, cap_root, rd_a);
        let c_b = CellState::compute_commitment(balance, nonce, &fields, cap_root, rd_b);
        assert_ne!(
            c_a, c_b,
            "two cells differing only in authority residue must commit differently (P0-2)"
        );

        // The 4-felt PI form must distinguish them too (OLD_COMMIT/NEW_COMMIT).
        let c4_a = CellState::compute_commitment_4(balance, nonce, &fields, cap_root, rd_a);
        let c4_b = CellState::compute_commitment_4(balance, nonce, &fields, cap_root, rd_b);
        assert_ne!(c4_a, c4_b, "4-felt commitment must bind record_digest");
        // Position 0 of the 4-felt form equals the scalar commitment.
        assert_eq!(c4_a[0], c_a);
    }

    /// A residue-free cell (`empty_record_digest()` = ZERO) must commit byte-identically
    /// to the legacy lossy form `hash_4_to_1(inter1, inter2, inter3, ZERO)` — the no-op
    /// cutover (no flag-day for cells carrying no authority residue beyond the welded
    /// limbs). Structurally mirrors the Lean `legacyReferenceCommitS` no-op fold.
    #[test]
    fn empty_record_digest_is_legacy_noop() {
        let balance = 500u64;
        let nonce = 2u32;
        let fields = [BabyBear::new(9); 8];
        // The legacy v1 1-felt commitment takes a single cap-root felt; use the
        // lane-0 projection of the faithful 8-felt empty root.
        let cap_root = crate::cap_root::empty_capability_root()[0];

        let with_empty = CellState::compute_commitment(
            balance,
            nonce,
            &fields,
            cap_root,
            crate::cap_root::empty_record_digest(),
        );
        // The legacy form: literal ZERO fourth input.
        let (lo, hi) = split_u64(balance);
        let inter1 = hash_4_to_1(&[lo, hi, BabyBear::new(nonce), fields[0]]);
        let inter2 = hash_4_to_1(&[fields[1], fields[2], fields[3], fields[4]]);
        let inter3 = hash_4_to_1(&[fields[5], fields[6], fields[7], cap_root]);
        let legacy = hash_4_to_1(&[inter1, inter2, inter3, BabyBear::ZERO]);
        assert_eq!(
            with_empty, legacy,
            "empty_record_digest must reproduce the legacy lossy commitment (no-op cutover)"
        );
    }
}
