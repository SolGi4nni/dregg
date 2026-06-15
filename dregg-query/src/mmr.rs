//! The receipt-index MMR — the Rust embodiment of
//! `metatheory/Dregg2/Lightclient/MMR.lean`.
//!
//! The Lean module proves the theory this file implements:
//!
//! - peaks are PERFECT binary trees; `push` is the binary carry
//!   (`peaksOf_mountains`: heights strictly increase from the youngest —
//!   the binary decomposition of the log length);
//! - the root bags the peaks youngest-outward (`mroot = bag (peaksOf L)`)
//!   and BINDS the whole log (`mroot_injective` — tamper / truncate /
//!   extend / reorder each move the root);
//! - range answers need NO gap openings: positions are DENSE, so the client
//!   checks a COUNT (pinned by the committed length, which the root pins via
//!   the peak heights) plus per-slot openings — `RVerifies`, and
//!   `server_cannot_omit_position`: a verifying answer is EXACTLY the
//!   genuine range.
//!
//! [`verify_range`] is the client-side `RVerifies` check, with two Rust-side
//! teeth the model justifies:
//!
//! 1. the committed length is RECOMPUTED from the root-pinned peak heights
//!    (`Σ 2^h` — the mountains shape), never trusted from the server;
//! 2. Merkle directions are DERIVED from the slot's dense offset, never
//!    carried in the proof — a path cannot be replayed at another position.
//!
//! ## The hash floor (UNVERIFIED equivalence — stated, not proved)
//!
//! The Lean model's one crypto premise is a collision-resistant sponge with
//! ARITY-separated domains (`Poseidon2SpongeCR`; arities 0/1/2 keep
//! empty/leaf/node-and-bag apart). [`Blake3Mmr`] realizes the same contract
//! with explicit domain tags over blake3 — the hash the receipt chain
//! already uses (`dregg_turn::TurnReceipt::receipt_hash`,
//! `b"dregg-receipt-v3"` domain). The in-circuit instantiation (the
//! `CommitBindsMMR` weld riding THE ROTATION — `iroot` as `recStateCommit`'s
//! last limb) will be Poseidon2; this trait is the seam where the two
//! instantiations meet, and the blake3↔Poseidon2 correspondence is a named,
//! unverified assumption of this crate, not of the model.

use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::hexutil::{serde_hex32, serde_vec_vec_hex32};

/// The arity-domain-separated hash contract of the model
/// (`Poseidon2SpongeCR`'s shape, instantiated). All four domains MUST be
/// mutually disjoint for the root to bind the log.
pub trait MmrHasher {
    /// The empty bag (Lean `hash []`).
    fn empty(&self) -> [u8; 32];
    /// A leaf over one log entry (Lean `hash [v]`).
    fn leaf(&self, v: &[u8; 32]) -> [u8; 32];
    /// An interior node (Lean `hash [l, r]`).
    fn node(&self, l: &[u8; 32], r: &[u8; 32]) -> [u8; 32];
    /// One bagging step (Lean `hash [peakHash, bagOfRest]`). Domain-distinct
    /// from `node` (the model separates them by sponge position; here, by tag).
    fn bag(&self, peak: &[u8; 32], rest: &[u8; 32]) -> [u8; 32];
}

/// The default hasher: blake3 with explicit domain tags, one per arity-domain
/// of the model. Leaf values are the 32-byte receipt commitments
/// (`TurnReceipt::receipt_hash`), so the MMR composes with the hash the
/// chain already speaks.
#[derive(Clone, Copy, Debug, Default)]
pub struct Blake3Mmr;

const TAG_EMPTY: &[u8] = b"dregg-query-mmr-v1:empty";
const TAG_LEAF: &[u8] = b"dregg-query-mmr-v1:leaf";
const TAG_NODE: &[u8] = b"dregg-query-mmr-v1:node";
const TAG_BAG: &[u8] = b"dregg-query-mmr-v1:bag";

fn b3(parts: &[&[u8]]) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    for p in parts {
        h.update(p);
    }
    *h.finalize().as_bytes()
}

impl MmrHasher for Blake3Mmr {
    fn empty(&self) -> [u8; 32] {
        b3(&[TAG_EMPTY])
    }
    fn leaf(&self, v: &[u8; 32]) -> [u8; 32] {
        b3(&[TAG_LEAF, v])
    }
    fn node(&self, l: &[u8; 32], r: &[u8; 32]) -> [u8; 32] {
        b3(&[TAG_NODE, l, r])
    }
    fn bag(&self, peak: &[u8; 32], rest: &[u8; 32]) -> [u8; 32] {
        b3(&[TAG_BAG, peak, rest])
    }
}

/// One peak of the frontier: its height and its hash. Wire order is
/// OLDEST-FIRST (heights strictly DECREASING — the reverse of the Lean
/// youngest-first list; same mountains invariant).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Peak {
    pub height: u8,
    #[serde(with = "serde_hex32")]
    pub hash: [u8; 32],
}

/// A positional range opening: the peak frontier plus one bottom-up sibling
/// path per answered slot. NO direction bits travel — the verifier derives
/// them from each slot's dense offset (positional binding). NO length
/// travels — the verifier derives it from the peak heights, which the root
/// pins.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RangeOpening {
    /// The frontier, oldest-first, heights strictly decreasing.
    pub peaks: Vec<Peak>,
    /// `paths[j]` is the sibling path (bottom-up) of position `lo + j`
    /// inside its covering peak; its length must equal that peak's height.
    #[serde(with = "serde_vec_vec_hex32")]
    pub paths: Vec<Vec<[u8; 32]>>,
}

/// The verification failures — each is a Lean FALSE-witness, §7 of the model
/// (skipped ⇒ `CountMismatch`; substituted/reordered ⇒ `SlotMismatch`;
/// tamper/truncate/extend/reorder of the log ⇒ `RootMismatch`).
#[derive(Debug, Error, PartialEq, Eq)]
pub enum MmrError {
    #[error("peak frontier is not mountains-shaped (heights must strictly decrease, < 64)")]
    BadFrontier,
    #[error("frontier does not bag to the committed root")]
    RootMismatch,
    #[error(
        "answer count {got} != committed in-range count {want} (positions are dense; omission breaks the count)"
    )]
    CountMismatch { got: usize, want: usize },
    #[error(
        "slot {slot}: opening path does not recompute its peak (wrong value, wrong position, or wrong path)"
    )]
    SlotMismatch { slot: usize },
    #[error("slot {slot}: path length {got} != covering peak height {want}")]
    PathLength {
        slot: usize,
        got: usize,
        want: usize,
    },
    #[error("malformed opening: {0} paths for {1} values")]
    PathCount(usize, usize),
}

/// The committed in-range position count — Lean `rangeCount len lo hi =
/// min (hi+1) len - lo` (saturating). The whole non-omission argument is
/// that this number is forced by the root.
pub fn range_count(len: u64, lo: u64, hi: u64) -> u64 {
    (hi + 1).min(len).saturating_sub(lo)
}

/// The prover/builder side: the appendable log of receipt commitments.
/// The node holds this (its receipt chain IS the log, `chain_index` the
/// dense position); tests hold it offline. Append-only — `push` is the only
/// mutation, mirroring `appendLeaf`.
#[derive(Clone, Debug)]
pub struct Mmr<H: MmrHasher> {
    hasher: H,
    values: Vec<[u8; 32]>,
}

impl<H: MmrHasher> Mmr<H> {
    pub fn new(hasher: H) -> Self {
        Mmr {
            hasher,
            values: Vec::new(),
        }
    }

    pub fn from_values(hasher: H, values: Vec<[u8; 32]>) -> Self {
        Mmr { hasher, values }
    }

    /// Append one log entry (a receipt commitment). Returns its position.
    pub fn push(&mut self, v: [u8; 32]) -> u64 {
        self.values.push(v);
        (self.values.len() - 1) as u64
    }

    pub fn len(&self) -> u64 {
        self.values.len() as u64
    }

    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }

    /// The hash of the perfect subtree over `values[start .. start + 2^height]`.
    fn subtree(&self, start: usize, height: u8) -> [u8; 32] {
        if height == 0 {
            self.hasher.leaf(&self.values[start])
        } else {
            let half = 1usize << (height - 1);
            let l = self.subtree(start, height - 1);
            let r = self.subtree(start + half, height - 1);
            self.hasher.node(&l, &r)
        }
    }

    /// The peak frontier, oldest-first: one perfect peak per set bit of the
    /// length, highest bit first (`peaksOf_mountains`, reversed to wire
    /// order). Recomputation here IS the incremental push, by
    /// `peaksOf_append` — the model proves the two agree, so the simple
    /// recomputing form is the honest reference implementation.
    pub fn peaks(&self) -> Vec<Peak> {
        let mut out = Vec::new();
        let mut start = 0usize;
        let len = self.values.len();
        for height in (0..64u8).rev() {
            if len & (1usize << height) != 0 {
                out.push(Peak {
                    height,
                    hash: self.subtree(start, height),
                });
                start += 1usize << height;
            }
        }
        out
    }

    /// The committed root — Lean `mroot`: bag the peaks youngest-outward
    /// over the empty bag.
    pub fn root(&self) -> [u8; 32] {
        bag_peaks(&self.hasher, &self.peaks())
    }

    /// The sibling path (bottom-up) of `pos` inside its covering peak.
    fn path_of(&self, pos: u64) -> Vec<[u8; 32]> {
        let (peak_start, peak_height) =
            covering_peak(self.len(), pos).expect("position < len has a covering peak");
        let offset = (pos - peak_start) as usize;
        let mut path = Vec::with_capacity(peak_height as usize);
        for level in 0..peak_height {
            let sib_offset = (offset >> level) ^ 1;
            let sib_start = peak_start as usize + (sib_offset << level);
            path.push(self.subtree(sib_start, level));
        }
        path
    }

    /// Open the positional range `[lo, hi]` (clipped to the committed
    /// length): the answered values plus their [`RangeOpening`]. This is the
    /// honest prover of `exact_range_verifies` — its output ALWAYS verifies
    /// against `self.root()`.
    pub fn open_range(&self, lo: u64, hi: u64) -> (Vec<[u8; 32]>, RangeOpening) {
        let count = range_count(self.len(), lo, hi);
        let mut values = Vec::with_capacity(count as usize);
        let mut paths = Vec::with_capacity(count as usize);
        for j in 0..count {
            let pos = lo + j;
            values.push(self.values[pos as usize]);
            paths.push(self.path_of(pos));
        }
        (
            values,
            RangeOpening {
                peaks: self.peaks(),
                paths,
            },
        )
    }
}

/// Bag an oldest-first frontier into the root (youngest-outward fold —
/// Lean `bag`: `hash [peak, bagOfRest]`, empty = `hash []`).
pub fn bag_peaks<H: MmrHasher>(hasher: &H, peaks_oldest_first: &[Peak]) -> [u8; 32] {
    let mut acc = hasher.empty();
    for p in peaks_oldest_first {
        acc = hasher.bag(&p.hash, &acc);
    }
    acc
}

/// The covering peak of `pos` in a log of length `len`: returns
/// `(chunk_start, height)`. Peaks chunk the log by the binary decomposition
/// of `len`, highest bit (oldest chunk) first.
fn covering_peak(len: u64, pos: u64) -> Option<(u64, u8)> {
    if pos >= len {
        return None;
    }
    let mut start = 0u64;
    for height in (0..64u8).rev() {
        if len & (1u64 << height) != 0 {
            let size = 1u64 << height;
            if pos < start + size {
                return Some((start, height));
            }
            start += size;
        }
    }
    None
}

/// **The client-side acceptance — Lean `RVerifies`, root-pinned.**
///
/// Against a trusted `root` (and ONLY the root: length and peak hashes are
/// recomputed/pinned, never trusted), accept `values` as the answer to the
/// positional range query `[lo, hi]` iff:
///
/// 1. the supplied frontier is mountains-shaped and bags to `root`
///    (`mroot_injective`: this pins the whole log, including its length
///    `Σ 2^height`);
/// 2. `values.len()` equals the committed in-range count
///    (`rangeCount` — positions are dense, a skipped position breaks the
///    count: THE non-omission keystone, `range_complete`);
/// 3. each slot `j` opens position `lo + j`: its path, with directions
///    DERIVED from the dense offset, recomputes the covering peak's pinned
///    hash (`Opens` — soundness, and the slot-order pin that rejects
///    substituted/reordered answers).
///
/// Returns the root-pinned log length. By `server_cannot_omit_position`, a
/// `Ok` verdict means `values` is EXACTLY the genuine range — nothing
/// omitted, nothing forged, dense order.
pub fn verify_range<H: MmrHasher>(
    hasher: &H,
    root: &[u8; 32],
    lo: u64,
    hi: u64,
    values: &[[u8; 32]],
    opening: &RangeOpening,
) -> Result<u64, MmrError> {
    // (1a) mountains shape: heights strictly decreasing oldest-first, < 64.
    let mut len = 0u64;
    let mut prev: Option<u8> = None;
    for p in &opening.peaks {
        if p.height >= 64 {
            return Err(MmrError::BadFrontier);
        }
        if let Some(ph) = prev
            && p.height >= ph
        {
            return Err(MmrError::BadFrontier);
        }
        prev = Some(p.height);
        len += 1u64 << p.height;
    }
    // (1b) the frontier bags to the committed root — everything below is
    // now pinned: peak hashes, chunking, and the length.
    if bag_peaks(hasher, &opening.peaks) != *root {
        return Err(MmrError::RootMismatch);
    }
    // (2) the dense count — the non-omission tooth.
    let want = range_count(len, lo, hi);
    if values.len() as u64 != want {
        return Err(MmrError::CountMismatch {
            got: values.len(),
            want: want as usize,
        });
    }
    if opening.paths.len() != values.len() {
        return Err(MmrError::PathCount(opening.paths.len(), values.len()));
    }
    // (3) per-slot positional openings.
    let mut chunk_starts = Vec::with_capacity(opening.peaks.len());
    let mut start = 0u64;
    for p in &opening.peaks {
        chunk_starts.push(start);
        start += 1u64 << p.height;
    }
    for (j, (v, path)) in values.iter().zip(opening.paths.iter()).enumerate() {
        let pos = lo + j as u64;
        // locate the covering peak (pos < len is guaranteed by the count).
        let k = opening
            .peaks
            .iter()
            .zip(chunk_starts.iter())
            .position(|(p, s)| pos < s + (1u64 << p.height))
            .expect("pos < len implies a covering peak");
        let peak = &opening.peaks[k];
        let offset = (pos - chunk_starts[k]) as usize;
        if path.len() != peak.height as usize {
            return Err(MmrError::PathLength {
                slot: j,
                got: path.len(),
                want: peak.height as usize,
            });
        }
        let mut cur = hasher.leaf(v);
        for (level, sib) in path.iter().enumerate() {
            // Directions derived from the DENSE offset — the positional pin.
            cur = if (offset >> level) & 1 == 1 {
                hasher.node(sib, &cur)
            } else {
                hasher.node(&cur, sib)
            };
        }
        if cur != peak.hash {
            return Err(MmrError::SlotMismatch { slot: j });
        }
    }
    Ok(len)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn leaf_val(i: u8) -> [u8; 32] {
        let mut v = [0u8; 32];
        v[0] = i;
        v
    }

    /// The Lean §7 demo shape: 3 leaves → peak heights [1, 0] oldest-first
    /// (youngest-first [0, 1]); a 4th append carries to one height-2 peak.
    #[test]
    fn binary_decomposition_shape() {
        let mut m = Mmr::new(Blake3Mmr);
        for i in 0..3 {
            m.push(leaf_val(i));
        }
        let hs: Vec<u8> = m.peaks().iter().map(|p| p.height).collect();
        assert_eq!(hs, vec![1, 0]);
        m.push(leaf_val(3));
        let hs: Vec<u8> = m.peaks().iter().map(|p| p.height).collect();
        assert_eq!(hs, vec![2]);
    }

    /// Prefix stability: a later append leaves a prior range opening
    /// verifying VERBATIM against the OLD root, and the exact answer
    /// verifies against the new one (`append_preserves_range`).
    #[test]
    fn exact_answer_verifies_across_sizes() {
        for n in 1u64..=33 {
            let mut m = Mmr::new(Blake3Mmr);
            for i in 0..n {
                m.push(leaf_val(i as u8));
            }
            let root = m.root();
            let (vals, opening) = m.open_range(0, n - 1);
            let len = verify_range(&Blake3Mmr, &root, 0, n - 1, &vals, &opening).unwrap();
            assert_eq!(len, n);
            // an interior sub-range too
            let lo = n / 3;
            let hi = (2 * n / 3).max(lo);
            let (vals, opening) = m.open_range(lo, hi);
            verify_range(&Blake3Mmr, &root, lo, hi, &vals, &opening).unwrap();
        }
    }
}
