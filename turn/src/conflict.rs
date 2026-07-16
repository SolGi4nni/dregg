//! Conflict set: probabilistic structure for detecting turn conflicts without revealing content.
//!
//! Two turns conflict if and only if they access overlapping cells. A conflict set is a
//! Bloom filter over the read and write sets of a turn. The federation can detect potential
//! conflicts from these filters alone, without seeing the actual cell IDs.
//!
//! # Properties
//!
//! - **No false negatives**: If two turns truly conflict, their Bloom filters will overlap.
//! - **False positives**: Two non-conflicting turns may appear to conflict (conservative/safe).
//! - **Privacy**: The filter reveals the approximate size of the access set but not specific cells.
//!
//! # Conflict Detection
//!
//! Two conflict sets overlap if the bitwise AND of their filters is non-zero. This is a
//! necessary (but not sufficient) condition for a true conflict.

use dregg_cell::CellId;
use serde::{Deserialize, Serialize};

/// Number of hash functions (k) for the Bloom filter.
const BLOOM_K: usize = 8;

/// Size of the Bloom filter in bits (m). 256 bits = 32 bytes.
/// With k=8 and expected n=4 cells, false positive rate is ~0.002.
/// With n=16 cells, false positive rate rises to ~0.17.
const BLOOM_BITS: usize = 256;

/// Size of the Bloom filter in bytes.
const BLOOM_BYTES: usize = BLOOM_BITS / 8;

/// A conflict set represented as a Bloom filter over accessed cell IDs.
///
/// The federation uses this to detect potential conflicts between turns without
/// seeing the turn content. Two turns with non-overlapping conflict sets can be
/// safely parallelized.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConflictSet {
    /// The Bloom filter bits (256 bits = 32 bytes).
    pub filter: [u8; BLOOM_BYTES],
    /// Number of cells inserted (for estimating false positive rate).
    /// This is public metadata — it reveals access set size.
    pub cell_count: u16,
}

impl ConflictSet {
    /// Create an empty conflict set.
    pub fn new() -> Self {
        Self {
            filter: [0u8; BLOOM_BYTES],
            cell_count: 0,
        }
    }

    /// Insert a cell ID into the conflict set.
    pub fn insert(&mut self, cell_id: &CellId) {
        let positions = Self::hash_positions(cell_id);
        for pos in positions {
            let byte_idx = pos / 8;
            let bit_idx = pos % 8;
            self.filter[byte_idx] |= 1 << bit_idx;
        }
        self.cell_count += 1;
    }

    /// Check if this conflict set might overlap with another.
    ///
    /// Returns `true` if there is ANY bit set in both filters (potential conflict).
    /// Returns `false` if the filters are completely disjoint (definitely no conflict).
    pub fn may_conflict_with(&self, other: &ConflictSet) -> bool {
        for i in 0..BLOOM_BYTES {
            if self.filter[i] & other.filter[i] != 0 {
                return true;
            }
        }
        false
    }

    /// Compute the Bloom filter bit positions for a cell ID using BLAKE3 keyed hashing.
    ///
    /// We use k=8 positions derived from a BLAKE3 hash of the cell ID with different
    /// domain separators. Each position is in [0, BLOOM_BITS).
    fn hash_positions(cell_id: &CellId) -> [usize; BLOOM_K] {
        let cell_bytes = cell_id.as_bytes();
        let hash = blake3::hash(cell_bytes);
        let hash_bytes = hash.as_bytes();

        let mut positions = [0usize; BLOOM_K];
        for i in 0..BLOOM_K {
            // Use 4 bytes per position (mod BLOOM_BITS)
            let offset = i * 4;
            let val = u32::from_le_bytes([
                hash_bytes[offset],
                hash_bytes[offset + 1],
                hash_bytes[offset + 2],
                hash_bytes[offset + 3],
            ]);
            positions[i] = (val as usize) % BLOOM_BITS;
        }
        positions
    }

    /// Compute the commitment hash of this conflict set.
    ///
    /// This is included in the encrypted turn submission so the federation can
    /// verify the conflict set wasn't tampered with after the validity proof was generated.
    pub fn commitment(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"dregg-conflict-set-v1");
        hasher.update(&self.filter);
        hasher.update(&self.cell_count.to_le_bytes());
        *hasher.finalize().as_bytes()
    }

    /// Estimated false positive probability for the current filter state.
    ///
    /// Formula: (1 - e^(-kn/m))^k where k=hash functions, n=insertions, m=bits.
    pub fn estimated_fpr(&self) -> f64 {
        let k = BLOOM_K as f64;
        let n = self.cell_count as f64;
        let m = BLOOM_BITS as f64;
        (1.0 - (-k * n / m).exp()).powf(k)
    }

    /// Count the number of set bits in the filter.
    pub fn popcount(&self) -> u32 {
        self.filter.iter().map(|b| b.count_ones()).sum()
    }
}

impl Default for ConflictSet {
    fn default() -> Self {
        Self::new()
    }
}

/// Build a conflict set from a turn's read and write sets.
///
/// The read set includes all cells whose state is read (precondition checks, authorization).
/// The write set includes all cells whose state is modified (effects).
///
/// Both sets are combined into a single Bloom filter — we don't distinguish read-write
/// conflicts from write-write conflicts at this level. This is conservative: two turns
/// that only READ the same cell don't truly conflict, but our filter will flag them.
/// A future refinement could use separate filters for reads and writes.
pub fn build_conflict_set(read_cells: &[CellId], write_cells: &[CellId]) -> ConflictSet {
    let mut cs = ConflictSet::new();
    for cell_id in read_cells {
        cs.insert(cell_id);
    }
    for cell_id in write_cells {
        cs.insert(cell_id);
    }
    cs
}

/// Extract the read and write sets from a Turn.
///
/// The read set is: {agent} ∪ {action.target for each action}
/// The write set is: {agent} ∪ {cells modified by effects}
///
/// This is a conservative over-approximation — the actual conflict depends on
/// which effects succeed, but we assume all declared effects will execute.
pub fn extract_access_sets(turn: &crate::turn::Turn) -> (Vec<CellId>, Vec<CellId>) {
    let mut read_set = Vec::new();
    let mut write_set = Vec::new();

    // The agent cell is always both read and written (nonce + fee).
    read_set.push(turn.agent);
    write_set.push(turn.agent);

    // Walk the call forest to find all accessed cells.
    for root in &turn.call_forest.roots {
        extract_tree_access(root, &mut read_set, &mut write_set);
    }

    // Deduplicate (Bloom filter handles duplicates fine, but this keeps counts accurate).
    read_set.sort_by_key(|id| *id.as_bytes());
    read_set.dedup();
    write_set.sort_by_key(|id| *id.as_bytes());
    write_set.dedup();

    (read_set, write_set)
}

/// Recursively extract access sets from a call tree.
fn extract_tree_access(
    tree: &crate::forest::CallTree,
    read_set: &mut Vec<CellId>,
    write_set: &mut Vec<CellId>,
) {
    use crate::action::Effect;

    let action = &tree.action;

    // The action target is always read (preconditions, authorization check).
    read_set.push(action.target);

    // Effects determine the write set.
    for effect in &action.effects {
        match effect {
            Effect::SetField { cell, .. } => {
                write_set.push(*cell);
            }
            Effect::Transfer { from, to, .. } => {
                write_set.push(*from);
                write_set.push(*to);
            }
            Effect::GrantCapability { from, to, .. } => {
                read_set.push(*from);
                write_set.push(*to);
            }
            Effect::RevokeCapability { cell, .. } => {
                write_set.push(*cell);
            }
            Effect::IncrementNonce { cell } => {
                write_set.push(*cell);
            }
            Effect::CreateCell {
                public_key,
                token_id,
                ..
            } => {
                let id = CellId::derive_raw(public_key, token_id);
                write_set.push(id);
            }
            Effect::SetPermissions { cell, .. } => {
                write_set.push(*cell);
            }
            Effect::SetVerificationKey { cell, .. } => {
                write_set.push(*cell);
            }
            Effect::SetProgram { cell, .. } => {
                write_set.push(*cell);
            }
            Effect::EmitEvent { cell, .. } => {
                read_set.push(*cell);
            }

            Effect::ExerciseViaCapability { inner_effects, .. } => {
                // Inner effects also access cells.
                for inner in inner_effects {
                    match inner {
                        Effect::SetField { cell, .. } => write_set.push(*cell),
                        Effect::Transfer { from, to, .. } => {
                            write_set.push(*from);
                            write_set.push(*to);
                        }
                        Effect::IncrementNonce { cell } => write_set.push(*cell),
                        _ => {}
                    }
                }
            }
            // A custom transition ADVANCES the sovereign commitment of `cell`, so
            // it conflicts with any concurrent turn touching that cell — the
            // scheduler must serialize them. (An empty write-set here would let two
            // custom turns racing the same sovereign root be scheduled concurrently.)
            Effect::Custom { cell, .. } => {
                write_set.push(*cell);
            }
            // Note effects, bridge effects, obligation effects don't target specific cells
            // beyond what's already captured by the action target.
            _ => {}
        }
    }

    // Balance change modifies the target cell.
    if action.balance_change.is_some() {
        write_set.push(action.target);
    }

    // Recurse into children.
    for child in &tree.children {
        extract_tree_access(child, read_set, write_set);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_cell_id(seed: u8) -> CellId {
        let mut bytes = [0u8; 32];
        bytes[0] = seed;
        CellId::from_bytes(bytes)
    }

    #[test]
    fn empty_sets_dont_conflict() {
        let cs1 = ConflictSet::new();
        let cs2 = ConflictSet::new();
        assert!(!cs1.may_conflict_with(&cs2));
    }

    #[test]
    fn same_cell_conflicts() {
        let cell = make_cell_id(1);
        let mut cs1 = ConflictSet::new();
        let mut cs2 = ConflictSet::new();
        cs1.insert(&cell);
        cs2.insert(&cell);
        assert!(cs1.may_conflict_with(&cs2));
    }

    #[test]
    fn disjoint_cells_no_conflict() {
        // `may_conflict_with` is a pure function of the two cell IDs (keyed
        // BLAKE3 → k=8 fixed bit positions), so for a FIXED pair it either
        // collides or it does not; there is no probability left to hedge
        // against and the answer can simply be asserted.
        //
        // The previous version computed the answer, dropped it with `let _`,
        // and asserted NOTHING — it would have passed if `may_conflict_with`
        // returned `true` unconditionally (i.e. if the scheduler had declared
        // every pair of turns conflicting and serialized the whole chain). It
        // declined to assert on the grounds that the false-positive rate was
        // "(1 - e^(-8/256))^8 ≈ 0.00000009". That number is WRONG for this
        // function — see `false_positive_rate_matches_the_any_bit_overlap_design`,
        // which measures the real rate at ~22.7%. The old note quoted the
        // standard Bloom FPR (the chance ALL k bits of a queried element are
        // set); `may_conflict_with` reports a conflict when ANY single bit
        // overlaps, which is ~11 orders of magnitude more likely.
        let cell_a = make_cell_id(1);
        let cell_b = make_cell_id(200);
        let mut cs1 = ConflictSet::new();
        let mut cs2 = ConflictSet::new();
        cs1.insert(&cell_a);
        cs2.insert(&cell_b);
        assert!(
            !cs1.may_conflict_with(&cs2),
            "these two specific disjoint cells must not be reported as conflicting"
        );
        // Symmetric: conflict is a relation on the pair, not on the order.
        assert!(
            !cs2.may_conflict_with(&cs1),
            "may_conflict_with must be symmetric"
        );
        // Deterministic: the property the old comment promised and never checked.
        assert_eq!(
            cs1.may_conflict_with(&cs2),
            cs1.may_conflict_with(&cs2),
            "may_conflict_with must be deterministic"
        );
    }

    /// ⚑ THE LOAD-BEARING DIRECTION: no FALSE NEGATIVES.
    ///
    /// A false positive costs throughput (two independent turns get serialized);
    /// a false negative costs CORRECTNESS (two turns touching the same cell are
    /// declared independent and may be reordered/parallelized). Only this
    /// direction is a soundness property, so it is asserted with zero tolerance
    /// over a swept set rather than on the single pair `same_cell_conflicts`
    /// checks.
    #[test]
    fn shared_cells_always_conflict_across_a_swept_set() {
        let ids: Vec<CellId> = (0u8..64).map(make_cell_id).collect();
        for shared in &ids {
            for other in &ids {
                let mut cs1 = ConflictSet::new();
                let mut cs2 = ConflictSet::new();
                // Both sets contain `shared`; cs2 additionally contains `other`.
                cs1.insert(shared);
                cs2.insert(shared);
                cs2.insert(other);
                assert!(
                    cs1.may_conflict_with(&cs2),
                    "FALSE NEGATIVE: sets sharing cell {shared:?} were reported independent \
                     (cs2 also held {other:?}) — the scheduler would run conflicting turns \
                     concurrently"
                );
            }
        }
    }

    /// Pins the PRECISION of the filter to its actual design.
    ///
    /// `may_conflict_with` ORs together k=8 bits per cell over m=256 and reports
    /// a conflict on ANY overlap, so two unrelated single-cell sets collide with
    /// probability 1 - C(248,8)/C(256,8) ≈ 0.227 — NOT the ≈1e-7 the old
    /// `disjoint_cells_no_conflict` comment claimed. This measures the real rate
    /// over every unordered pair of a fixed 64-cell set and pins it to a band
    /// around the analytic value.
    ///
    /// The band is a genuine gate in both directions: a filter that saturates
    /// (every pair conflicts → the scheduler serializes everything) blows the
    /// upper bound, and one that never sets bits (every pair independent → false
    /// negatives) blows the lower bound. Widening k or shrinking m moves the rate
    /// and reds here, which is the point — the number stops being folklore.
    #[test]
    fn false_positive_rate_matches_the_any_bit_overlap_design() {
        let sets: Vec<ConflictSet> = (0u8..64)
            .map(|s| {
                let mut cs = ConflictSet::new();
                cs.insert(&make_cell_id(s));
                cs
            })
            .collect();
        let mut pairs = 0usize;
        let mut collisions = 0usize;
        for i in 0..sets.len() {
            for j in (i + 1)..sets.len() {
                pairs += 1;
                if sets[i].may_conflict_with(&sets[j]) {
                    collisions += 1;
                }
            }
        }
        let rate = collisions as f64 / pairs as f64;
        // Analytic: 1 - C(248,8)/C(256,8) ≈ 0.2271. Band allows sampling spread
        // over 2016 pairs while still catching a saturated or dead filter.
        assert!(
            (0.12..0.34).contains(&rate),
            "single-cell false-conflict rate {rate:.4} ({collisions}/{pairs}) is outside the \
             band the k=8/m=256 any-bit-overlap design predicts (≈0.227). Above it: the filter \
             is saturating and the scheduler serializes independent turns. Below it: too few \
             bits are being set, which threatens the false-negative direction."
        );
    }

    #[test]
    fn commitment_is_deterministic() {
        let cell = make_cell_id(42);
        let mut cs1 = ConflictSet::new();
        let mut cs2 = ConflictSet::new();
        cs1.insert(&cell);
        cs2.insert(&cell);
        assert_eq!(cs1.commitment(), cs2.commitment());
    }

    #[test]
    fn popcount_tracks_insertions() {
        let mut cs = ConflictSet::new();
        assert_eq!(cs.popcount(), 0);
        cs.insert(&make_cell_id(1));
        // With k=8, at most 8 bits set (could be fewer due to collisions).
        assert!(cs.popcount() <= 8);
        assert!(cs.popcount() > 0);
    }

    #[test]
    fn build_conflict_set_from_cells() {
        let reads = vec![make_cell_id(1), make_cell_id(2)];
        let writes = vec![make_cell_id(3)];
        let cs = build_conflict_set(&reads, &writes);
        assert_eq!(cs.cell_count, 3);
    }
}
