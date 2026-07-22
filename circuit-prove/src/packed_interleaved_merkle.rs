//! Dregg-owned prototype for packed, worker-interleaved Merkle layouts.
//!
//! This module isolates two ideas that are easy to conflate:
//!
//! 1. **Packing is canonical for the current MMCS.** For equal-height source
//!    matrices, Plonky3's `MerkleTreeMmcs` hashes the source rows in matrix
//!    order. Horizontally concatenating those rows into one tuple-valued leaf
//!    therefore preserves the Poseidon2 root and every authentication path.
//!    [`audit_canonical_packing_equivalence`] checks that executable contract.
//! 2. **Worker interleaving is not canonical.** Worker `w` owns logical rows
//!    `w, w + workers, w + 2 * workers, ...`; concatenating the worker-local
//!    subtrees changes the leaf order. The result is exposed only through
//!    [`PackedInterleavedCommitment`], whose external root is BLAKE3-domain-
//!    separated from every existing MMCS root and binds the complete layout.
//!
//! The physical order matches the locality idea in UltraFold: after the
//! one-time transpose, one worker can serve a leaf and its local subtree path.
//! This prototype does **not** implement BaseFold encoding, the all-to-all
//! transpose, a distributed transcript, worker authentication, malicious
//! accountability, or witness privacy. It is CPU-only and copies the full
//! matrix. Its purpose is to pin commitment semantics before a resident WGPU
//! or distributed implementation is allowed to optimize them.

use core::fmt;

use p3_baby_bear::{BabyBear, Poseidon2BabyBear, default_babybear_poseidon2_16};
use p3_commit::{BatchOpeningRef, Mmcs};
use p3_field::{Field, PrimeField32};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::{Dimensions, Matrix};
use p3_merkle_tree::{MerkleTree, MerkleTreeMmcs};
use p3_symmetric::{MerkleCap, PaddingFreeSponge, TruncatedPermutation};

const WIDTH: usize = 16;
const RATE: usize = 8;
const DIGEST_ELEMS: usize = 8;

type Perm = Poseidon2BabyBear<WIDTH>;
type LeafHash = PaddingFreeSponge<Perm, WIDTH, RATE, DIGEST_ELEMS>;
type Compress = TruncatedPermutation<Perm, 2, DIGEST_ELEMS, WIDTH>;
type InnerMmcs = MerkleTreeMmcs<
    <BabyBear as Field>::Packing,
    <BabyBear as Field>::Packing,
    LeafHash,
    Compress,
    2,
    DIGEST_ELEMS,
>;
type InnerTree = MerkleTree<BabyBear, BabyBear, RowMajorMatrix<BabyBear>, 2, DIGEST_ELEMS>;

/// Domain of the external alternate root.
///
/// The NUL terminator prevents prefix ambiguity with future textual domains.
/// The version is also encoded as a binary field in the preimage.
pub const PACKED_INTERLEAVED_ROOT_DOMAIN_V1: &[u8] =
    b"dregg.pcs.packed-interleaved-merkle.alternate-root\0";

/// Current binary layout/envelope version.
pub const PACKED_INTERLEAVED_LAYOUT_VERSION: u32 = 1;

/// Poseidon2 digest used by the physical, interleaved tree.
pub type PhysicalDigest = [BabyBear; DIGEST_ELEMS];

/// The physical tree's cap-height-zero commitment.
pub type PhysicalMerkleRoot = MerkleCap<BabyBear, PhysicalDigest>;

/// Errors are fail-closed at the layout boundary, before hashing when possible.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PackedInterleavedError {
    /// At least one source matrix is required.
    EmptySources,
    /// A zero-width source does not define a tuple component.
    ZeroSourceWidth { source: usize },
    /// All packed sources must describe the same logical row set.
    SourceHeightMismatch {
        source: usize,
        expected: usize,
        actual: usize,
    },
    /// This prototype pins the power-of-two BaseFold/FRI geometry.
    InvalidLogicalRows(usize),
    /// Worker count is part of the commitment and must fit the binary top tree.
    InvalidWorkerCount(usize),
    /// Every worker must own at least one full local subtree.
    TooManyWorkers { workers: usize, logical_rows: usize },
    /// Width addition overflowed the host index type.
    PackedWidthOverflow,
    /// The coordinator received too many or too few worker shards.
    WrongShardCount { expected: usize, actual: usize },
    /// Shards are accepted only in their committed worker-id order.
    ReorderedShard {
        position: usize,
        expected: usize,
        actual: usize,
    },
    /// A shard dropped, duplicated, or appended a physical row.
    WrongShardHeight {
        worker: usize,
        expected: usize,
        actual: usize,
    },
    /// A shard does not use the committed tuple schema.
    WrongShardWidth {
        worker: usize,
        expected: usize,
        actual: usize,
    },
    /// A logical query lies outside the committed row set.
    LogicalIndexOutOfBounds { index: usize, logical_rows: usize },
    /// The opening cannot select a different logical row than its caller asked for.
    OpeningIndexMismatch { expected: usize, actual: usize },
    /// The external root does not bind the supplied physical root and layout.
    AlternateRootMismatch,
    /// The cap-height-zero physical commitment had an impossible shape.
    WrongPhysicalRootCount(usize),
    /// The underlying Poseidon2 MMCS rejected an opening.
    PhysicalOpeningRejected(String),
    /// Packing changed the canonical root or opening path.
    CanonicalPackingMismatch { stage: &'static str },
}

impl fmt::Display for PackedInterleavedError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptySources => {
                f.write_str("packed Merkle layout needs at least one source matrix")
            }
            Self::ZeroSourceWidth { source } => {
                write!(f, "source matrix {source} has zero width")
            }
            Self::SourceHeightMismatch {
                source,
                expected,
                actual,
            } => write!(
                f,
                "source matrix {source} has height {actual}, expected {expected}"
            ),
            Self::InvalidLogicalRows(rows) => write!(
                f,
                "logical row count {rows} must be a non-zero power of two"
            ),
            Self::InvalidWorkerCount(workers) => {
                write!(f, "worker count {workers} must be a non-zero power of two")
            }
            Self::TooManyWorkers {
                workers,
                logical_rows,
            } => write!(
                f,
                "worker count {workers} exceeds logical row count {logical_rows}"
            ),
            Self::PackedWidthOverflow => f.write_str("packed tuple width overflows usize"),
            Self::WrongShardCount { expected, actual } => {
                write!(f, "received {actual} worker shards, expected {expected}")
            }
            Self::ReorderedShard {
                position,
                expected,
                actual,
            } => write!(
                f,
                "shard position {position} carries worker id {actual}, expected {expected}"
            ),
            Self::WrongShardHeight {
                worker,
                expected,
                actual,
            } => write!(
                f,
                "worker {worker} shard height {actual}, expected {expected}"
            ),
            Self::WrongShardWidth {
                worker,
                expected,
                actual,
            } => write!(
                f,
                "worker {worker} shard width {actual}, expected {expected}"
            ),
            Self::LogicalIndexOutOfBounds {
                index,
                logical_rows,
            } => write!(
                f,
                "logical index {index} is outside row count {logical_rows}"
            ),
            Self::OpeningIndexMismatch { expected, actual } => write!(
                f,
                "opening is for logical index {actual}, caller requested {expected}"
            ),
            Self::AlternateRootMismatch => {
                f.write_str("packed/interleaved alternate-root envelope mismatch")
            }
            Self::WrongPhysicalRootCount(roots) => write!(
                f,
                "physical Merkle commitment has {roots} roots, expected exactly one"
            ),
            Self::PhysicalOpeningRejected(error) => {
                write!(f, "physical Merkle opening rejected: {error}")
            }
            Self::CanonicalPackingMismatch { stage } => {
                write!(f, "canonical packing equivalence failed at {stage}")
            }
        }
    }
}

impl std::error::Error for PackedInterleavedError {}

/// Layout bound into every packed/interleaved alternate root.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackedInterleavedLayout {
    logical_rows: usize,
    worker_count: usize,
    source_widths: Vec<usize>,
    packed_width: usize,
}

impl PackedInterleavedLayout {
    /// Validate a layout reconstructed from protocol-visible dimensions.
    pub fn new(
        logical_rows: usize,
        worker_count: usize,
        source_widths: Vec<usize>,
    ) -> Result<Self, PackedInterleavedError> {
        if !logical_rows.is_power_of_two() {
            return Err(PackedInterleavedError::InvalidLogicalRows(logical_rows));
        }
        if !worker_count.is_power_of_two() {
            return Err(PackedInterleavedError::InvalidWorkerCount(worker_count));
        }
        if worker_count > logical_rows {
            return Err(PackedInterleavedError::TooManyWorkers {
                workers: worker_count,
                logical_rows,
            });
        }
        if source_widths.is_empty() {
            return Err(PackedInterleavedError::EmptySources);
        }
        let mut packed_width = 0usize;
        for (source, width) in source_widths.iter().copied().enumerate() {
            if width == 0 {
                return Err(PackedInterleavedError::ZeroSourceWidth { source });
            }
            packed_width = packed_width
                .checked_add(width)
                .ok_or(PackedInterleavedError::PackedWidthOverflow)?;
        }
        Ok(Self {
            logical_rows,
            worker_count,
            source_widths,
            packed_width,
        })
    }

    /// Number of canonical rows before worker interleaving.
    pub const fn logical_rows(&self) -> usize {
        self.logical_rows
    }

    /// Number of worker-local subtrees.
    pub const fn worker_count(&self) -> usize {
        self.worker_count
    }

    /// Width of every source row, in canonical source order.
    pub fn source_widths(&self) -> &[usize] {
        &self.source_widths
    }

    /// Number of field words in one packed tuple leaf.
    pub const fn packed_width(&self) -> usize {
        self.packed_width
    }

    /// Rows held by each worker.
    pub const fn rows_per_worker(&self) -> usize {
        self.logical_rows / self.worker_count
    }

    /// Convert a canonical row index into `(worker, worker-local row)`.
    pub fn worker_and_local_row(
        &self,
        logical_index: usize,
    ) -> Result<(usize, usize), PackedInterleavedError> {
        self.check_logical_index(logical_index)?;
        Ok((
            logical_index % self.worker_count,
            logical_index / self.worker_count,
        ))
    }

    /// Convert a canonical row index into the physical concatenated-tree index.
    pub fn physical_index(&self, logical_index: usize) -> Result<usize, PackedInterleavedError> {
        let (worker, local_row) = self.worker_and_local_row(logical_index)?;
        Ok(worker * self.rows_per_worker() + local_row)
    }

    /// Static operation counts. These are not benchmark results.
    pub fn cost_model(&self) -> PackedInterleavedCostModel {
        PackedInterleavedCostModel {
            total_field_words_copied: self.logical_rows * self.packed_width,
            field_words_per_worker: self.rows_per_worker() * self.packed_width,
            physical_leaf_hashes: self.logical_rows,
            physical_authentication_depth: self.logical_rows.trailing_zeros() as usize,
            coordinator_subtree_roots: self.worker_count,
            coordinator_top_compressions: self.worker_count.saturating_sub(1),
        }
    }

    fn check_logical_index(&self, index: usize) -> Result<(), PackedInterleavedError> {
        if index >= self.logical_rows {
            Err(PackedInterleavedError::LogicalIndexOutOfBounds {
                index,
                logical_rows: self.logical_rows,
            })
        } else {
            Ok(())
        }
    }
}

/// Exact operation counts implied by the layout.
///
/// They intentionally omit elapsed time, GPU occupancy, communication latency,
/// and BaseFold arithmetic. The current implementation performs the full copy
/// named by `total_field_words_copied` and then calls the CPU MMCS.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PackedInterleavedCostModel {
    /// Field words copied into worker-contiguous physical order.
    pub total_field_words_copied: usize,
    /// Field words retained by each equally sized worker.
    pub field_words_per_worker: usize,
    /// Tuple-valued leaves hashed across all subtrees.
    pub physical_leaf_hashes: usize,
    /// Full physical-tree authentication depth.
    pub physical_authentication_depth: usize,
    /// Worker-local roots sent to the coordinator in a distributed build.
    pub coordinator_subtree_roots: usize,
    /// Binary hashes in the coordinator's top tree.
    pub coordinator_top_compressions: usize,
}

/// One worker's tuple-packed, worker-local subtree leaves.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackedWorkerShard {
    worker_index: usize,
    rows: RowMajorMatrix<BabyBear>,
}

impl PackedWorkerShard {
    /// Construct a received shard. [`commit_ordered_worker_shards`] validates
    /// its id and exact dimensions against the committed layout.
    pub const fn new(worker_index: usize, rows: RowMajorMatrix<BabyBear>) -> Self {
        Self { worker_index, rows }
    }

    /// Protocol-visible worker id.
    pub const fn worker_index(&self) -> usize {
        self.worker_index
    }

    /// Tuple-packed local rows.
    pub const fn rows(&self) -> &RowMajorMatrix<BabyBear> {
        &self.rows
    }

    /// Consume the shard for transport or a backend-specific tree build.
    pub fn into_rows(self) -> RowMajorMatrix<BabyBear> {
        self.rows
    }
}

/// A strongly typed alternate root for the non-canonical interleaved tree.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackedInterleavedCommitment {
    layout: PackedInterleavedLayout,
    physical_root: PhysicalMerkleRoot,
    alternate_root: [u8; 32],
}

impl PackedInterleavedCommitment {
    /// Layout included in the root preimage.
    pub const fn layout(&self) -> &PackedInterleavedLayout {
        &self.layout
    }

    /// The physical Poseidon2 tree root. This is not a canonical PCS root and
    /// must never be observed directly into an existing transcript.
    pub const fn physical_root(&self) -> &PhysicalMerkleRoot {
        &self.physical_root
    }

    /// Domain-separated root that is safe to route under a distinct backend id.
    pub const fn alternate_root(&self) -> &[u8; 32] {
        &self.alternate_root
    }

    fn validate_envelope(&self) -> Result<(), PackedInterleavedError> {
        let actual = alternate_root(&self.layout, &self.physical_root)?;
        if actual == self.alternate_root {
            Ok(())
        } else {
            Err(PackedInterleavedError::AlternateRootMismatch)
        }
    }
}

/// Prover-side physical tree. It deliberately does not implement serialization;
/// a distributed implementation should retain worker-local subtrees instead.
pub struct PackedInterleavedProverData {
    layout: PackedInterleavedLayout,
    physical_tree: InnerTree,
}

impl fmt::Debug for PackedInterleavedProverData {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PackedInterleavedProverData")
            .field("layout", &self.layout)
            .field("physical_tree", &"<Poseidon2 Merkle tree>")
            .finish()
    }
}

impl PackedInterleavedProverData {
    /// Open a canonical logical row through its deterministic physical index.
    pub fn open(
        &self,
        logical_index: usize,
    ) -> Result<PackedInterleavedOpening, PackedInterleavedError> {
        let physical_index = self.layout.physical_index(logical_index)?;
        let opening = inner_mmcs().open_batch(physical_index, &self.physical_tree);
        let (mut opened_values, authentication_path) = opening.unpack();
        debug_assert_eq!(opened_values.len(), 1);
        Ok(PackedInterleavedOpening {
            logical_index,
            packed_values: opened_values.pop().expect("one physical matrix"),
            authentication_path,
        })
    }
}

/// Opening of one logical tuple leaf under the alternate layout.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PackedInterleavedOpening {
    logical_index: usize,
    packed_values: Vec<BabyBear>,
    authentication_path: Vec<PhysicalDigest>,
}

impl PackedInterleavedOpening {
    /// Canonical row index selected by this opening.
    pub const fn logical_index(&self) -> usize {
        self.logical_index
    }

    /// Concatenated source rows in canonical source order.
    pub fn packed_values(&self) -> &[BabyBear] {
        &self.packed_values
    }

    /// Physical Poseidon2 authentication path.
    pub fn authentication_path(&self) -> &[PhysicalDigest] {
        &self.authentication_path
    }
}

/// Result of checking the current MMCS's canonical tuple-packing contract.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CanonicalPackingAudit {
    /// Number of rows checked.
    pub logical_rows: usize,
    /// Width of the resulting tuple leaf.
    pub packed_width: usize,
    /// Number of authentication paths compared.
    pub checked_openings: usize,
    /// Common canonical Poseidon2 root.
    pub canonical_root: PhysicalMerkleRoot,
}

/// Build tuple-packed worker shards from equal-height canonical source matrices.
///
/// Shard vector position is the worker id; each shard contains logical rows
/// congruent to that id modulo `worker_count`.
pub fn prepare_worker_shards(
    sources: &[RowMajorMatrix<BabyBear>],
    worker_count: usize,
) -> Result<(PackedInterleavedLayout, Vec<PackedWorkerShard>), PackedInterleavedError> {
    let (layout, canonical_packed) = pack_canonical_sources(sources, worker_count)?;
    let rows_per_worker = layout.rows_per_worker();
    let mut shards = Vec::with_capacity(worker_count);
    for worker in 0..worker_count {
        let mut values = Vec::with_capacity(rows_per_worker * layout.packed_width);
        for local_row in 0..rows_per_worker {
            let logical_index = local_row * worker_count + worker;
            values.extend_from_slice(
                &canonical_packed
                    .row_slice(logical_index)
                    .expect("validated logical row"),
            );
        }
        shards.push(PackedWorkerShard::new(
            worker,
            RowMajorMatrix::new(values, layout.packed_width),
        ));
    }
    Ok((layout, shards))
}

/// Validate ordered worker shards and commit their physical concatenation.
///
/// Correct worker ids and dimensions are structural checks. Codeword
/// correctness remains the responsibility of the PCS relation; arbitrary data
/// with the right shape is still committed faithfully.
pub fn commit_ordered_worker_shards(
    layout: PackedInterleavedLayout,
    shards: Vec<PackedWorkerShard>,
) -> Result<(PackedInterleavedCommitment, PackedInterleavedProverData), PackedInterleavedError> {
    if shards.len() != layout.worker_count {
        return Err(PackedInterleavedError::WrongShardCount {
            expected: layout.worker_count,
            actual: shards.len(),
        });
    }

    let rows_per_worker = layout.rows_per_worker();
    let mut physical_values = Vec::with_capacity(layout.logical_rows * layout.packed_width);
    for (position, shard) in shards.into_iter().enumerate() {
        if shard.worker_index != position {
            return Err(PackedInterleavedError::ReorderedShard {
                position,
                expected: position,
                actual: shard.worker_index,
            });
        }
        if shard.rows.height() != rows_per_worker {
            return Err(PackedInterleavedError::WrongShardHeight {
                worker: position,
                expected: rows_per_worker,
                actual: shard.rows.height(),
            });
        }
        if shard.rows.width() != layout.packed_width {
            return Err(PackedInterleavedError::WrongShardWidth {
                worker: position,
                expected: layout.packed_width,
                actual: shard.rows.width(),
            });
        }
        physical_values.extend(shard.rows.values);
    }

    let physical_matrix = RowMajorMatrix::new(physical_values, layout.packed_width);
    let (physical_root, physical_tree) = inner_mmcs().commit_matrix(physical_matrix);
    let external_root = alternate_root(&layout, &physical_root)?;
    Ok((
        PackedInterleavedCommitment {
            layout: layout.clone(),
            physical_root,
            alternate_root: external_root,
        },
        PackedInterleavedProverData {
            layout,
            physical_tree,
        },
    ))
}

/// Prepare and commit the packed/interleaved layout in one call.
pub fn commit_packed_interleaved(
    sources: &[RowMajorMatrix<BabyBear>],
    worker_count: usize,
) -> Result<(PackedInterleavedCommitment, PackedInterleavedProverData), PackedInterleavedError> {
    let (layout, shards) = prepare_worker_shards(sources, worker_count)?;
    commit_ordered_worker_shards(layout, shards)
}

/// Verify one logical opening and split its tuple back into canonical source rows.
pub fn verify_packed_interleaved_opening(
    commitment: &PackedInterleavedCommitment,
    requested_logical_index: usize,
    opening: &PackedInterleavedOpening,
) -> Result<Vec<Vec<BabyBear>>, PackedInterleavedError> {
    commitment.validate_envelope()?;
    commitment
        .layout
        .check_logical_index(requested_logical_index)?;
    if opening.logical_index != requested_logical_index {
        return Err(PackedInterleavedError::OpeningIndexMismatch {
            expected: requested_logical_index,
            actual: opening.logical_index,
        });
    }
    if opening.packed_values.len() != commitment.layout.packed_width {
        return Err(PackedInterleavedError::WrongShardWidth {
            worker: requested_logical_index % commitment.layout.worker_count,
            expected: commitment.layout.packed_width,
            actual: opening.packed_values.len(),
        });
    }

    let physical_index = commitment.layout.physical_index(requested_logical_index)?;
    let opened_values = vec![opening.packed_values.clone()];
    inner_mmcs()
        .verify_batch(
            &commitment.physical_root,
            &[Dimensions {
                width: commitment.layout.packed_width,
                height: commitment.layout.logical_rows,
            }],
            physical_index,
            BatchOpeningRef::new(&opened_values, &opening.authentication_path),
        )
        .map_err(|error| PackedInterleavedError::PhysicalOpeningRejected(format!("{error:?}")))?;

    let mut unpacked = Vec::with_capacity(commitment.layout.source_widths.len());
    let mut offset = 0usize;
    for width in &commitment.layout.source_widths {
        unpacked.push(opening.packed_values[offset..offset + width].to_vec());
        offset += width;
    }
    Ok(unpacked)
}

/// Differentially check that horizontal tuple packing preserves the current
/// canonical MMCS root, opened values, and every authentication path.
///
/// This is an audit/prototype helper, not part of a proving hot path: it opens
/// every row under both representations.
pub fn audit_canonical_packing_equivalence(
    sources: &[RowMajorMatrix<BabyBear>],
) -> Result<CanonicalPackingAudit, PackedInterleavedError> {
    let (layout, packed) = pack_canonical_sources(sources, 1)?;
    let mmcs = inner_mmcs();
    let (source_root, source_tree) = mmcs.commit(sources.to_vec());
    let (packed_root, packed_tree) = mmcs.commit_matrix(packed);
    if source_root != packed_root {
        return Err(PackedInterleavedError::CanonicalPackingMismatch { stage: "root" });
    }

    for index in 0..layout.logical_rows {
        let source_opening = mmcs.open_batch(index, &source_tree);
        let packed_opening = mmcs.open_batch(index, &packed_tree);
        let source_values = source_opening
            .opened_values
            .iter()
            .flatten()
            .copied()
            .collect::<Vec<_>>();
        if source_values != packed_opening.opened_values[0] {
            return Err(PackedInterleavedError::CanonicalPackingMismatch {
                stage: "opened values",
            });
        }
        if source_opening.opening_proof != packed_opening.opening_proof {
            return Err(PackedInterleavedError::CanonicalPackingMismatch {
                stage: "authentication path",
            });
        }
    }

    Ok(CanonicalPackingAudit {
        logical_rows: layout.logical_rows,
        packed_width: layout.packed_width,
        checked_openings: layout.logical_rows,
        canonical_root: source_root,
    })
}

fn pack_canonical_sources(
    sources: &[RowMajorMatrix<BabyBear>],
    worker_count: usize,
) -> Result<(PackedInterleavedLayout, RowMajorMatrix<BabyBear>), PackedInterleavedError> {
    let Some(first) = sources.first() else {
        return Err(PackedInterleavedError::EmptySources);
    };
    let logical_rows = first.height();
    let source_widths = sources.iter().map(Matrix::width).collect::<Vec<_>>();
    let layout = PackedInterleavedLayout::new(logical_rows, worker_count, source_widths)?;
    for (source, matrix) in sources.iter().enumerate() {
        if matrix.height() != logical_rows {
            return Err(PackedInterleavedError::SourceHeightMismatch {
                source,
                expected: logical_rows,
                actual: matrix.height(),
            });
        }
    }

    let mut values = Vec::with_capacity(logical_rows * layout.packed_width);
    for row in 0..logical_rows {
        for source in sources {
            values.extend_from_slice(&source.row_slice(row).expect("validated equal height"));
        }
    }
    Ok((
        layout.clone(),
        RowMajorMatrix::new(values, layout.packed_width),
    ))
}

fn inner_mmcs() -> InnerMmcs {
    let perm = default_babybear_poseidon2_16();
    InnerMmcs::new(LeafHash::new(perm.clone()), Compress::new(perm), 0)
}

fn alternate_root(
    layout: &PackedInterleavedLayout,
    physical_root: &PhysicalMerkleRoot,
) -> Result<[u8; 32], PackedInterleavedError> {
    if physical_root.num_roots() != 1 {
        return Err(PackedInterleavedError::WrongPhysicalRootCount(
            physical_root.num_roots(),
        ));
    }
    let mut hasher = blake3::Hasher::new();
    hasher.update(PACKED_INTERLEAVED_ROOT_DOMAIN_V1);
    hasher.update(&PACKED_INTERLEAVED_LAYOUT_VERSION.to_le_bytes());
    hash_usize(&mut hasher, layout.logical_rows);
    hash_usize(&mut hasher, layout.worker_count);
    hash_usize(&mut hasher, layout.source_widths.len());
    for width in &layout.source_widths {
        hash_usize(&mut hasher, *width);
    }
    for word in &physical_root.roots()[0] {
        hasher.update(&word.as_canonical_u32().to_le_bytes());
    }
    Ok(*hasher.finalize().as_bytes())
}

fn hash_usize(hasher: &mut blake3::Hasher, value: usize) {
    hasher.update(&(value as u64).to_le_bytes());
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sources() -> Vec<RowMajorMatrix<BabyBear>> {
        let height = 16usize;
        let a = RowMajorMatrix::new(
            (0..height)
                .flat_map(|row| {
                    [
                        BabyBear::new(100 + row as u32),
                        BabyBear::new(200 + row as u32),
                    ]
                })
                .collect(),
            2,
        );
        let b = RowMajorMatrix::new(
            (0..height)
                .flat_map(|row| {
                    [
                        BabyBear::new(1_000 + row as u32),
                        BabyBear::new(2_000 + row as u32),
                        BabyBear::new(3_000 + row as u32),
                    ]
                })
                .collect(),
            3,
        );
        vec![a, b]
    }

    fn expected_rows(sources: &[RowMajorMatrix<BabyBear>], row: usize) -> Vec<Vec<BabyBear>> {
        sources
            .iter()
            .map(|source| source.row_slice(row).unwrap().to_vec())
            .collect()
    }

    #[test]
    fn canonical_tuple_packing_preserves_root_and_every_path() {
        let sources = sources();
        let audit = audit_canonical_packing_equivalence(&sources).unwrap();
        assert_eq!(audit.logical_rows, 16);
        assert_eq!(audit.packed_width, 5);
        assert_eq!(audit.checked_openings, 16);
        assert_eq!(audit.canonical_root.num_roots(), 1);
    }

    #[test]
    fn interleaved_openings_decode_to_canonical_rows() {
        let sources = sources();
        let (commitment, prover_data) = commit_packed_interleaved(&sources, 4).unwrap();
        assert_eq!(commitment.layout().rows_per_worker(), 4);
        assert_eq!(commitment.layout().physical_index(0).unwrap(), 0);
        assert_eq!(commitment.layout().physical_index(4).unwrap(), 1);
        assert_eq!(commitment.layout().physical_index(1).unwrap(), 4);
        assert_eq!(commitment.layout().physical_index(15).unwrap(), 15);

        for logical_index in 0..16 {
            let opening = prover_data.open(logical_index).unwrap();
            let decoded =
                verify_packed_interleaved_opening(&commitment, logical_index, &opening).unwrap();
            assert_eq!(decoded, expected_rows(&sources, logical_index));
        }

        let costs = commitment.layout().cost_model();
        assert_eq!(costs.total_field_words_copied, 80);
        assert_eq!(costs.field_words_per_worker, 20);
        assert_eq!(costs.physical_leaf_hashes, 16);
        assert_eq!(costs.physical_authentication_depth, 4);
        assert_eq!(costs.coordinator_subtree_roots, 4);
        assert_eq!(costs.coordinator_top_compressions, 3);
    }

    #[test]
    fn worker_reorder_and_drop_refuse_before_commit() {
        let sources = sources();
        let (layout, shards) = prepare_worker_shards(&sources, 4).unwrap();

        let mut reordered = shards.clone();
        reordered.swap(1, 2);
        assert_eq!(
            commit_ordered_worker_shards(layout.clone(), reordered).unwrap_err(),
            PackedInterleavedError::ReorderedShard {
                position: 1,
                expected: 1,
                actual: 2,
            }
        );

        let mut dropped_worker = shards.clone();
        dropped_worker.pop();
        assert_eq!(
            commit_ordered_worker_shards(layout.clone(), dropped_worker).unwrap_err(),
            PackedInterleavedError::WrongShardCount {
                expected: 4,
                actual: 3,
            }
        );

        let mut dropped_row = shards;
        let bad = dropped_row.remove(2);
        let mut values = bad.rows.values;
        values.truncate(values.len() - layout.packed_width());
        dropped_row.insert(
            2,
            PackedWorkerShard::new(2, RowMajorMatrix::new(values, layout.packed_width())),
        );
        assert_eq!(
            commit_ordered_worker_shards(layout, dropped_row).unwrap_err(),
            PackedInterleavedError::WrongShardHeight {
                worker: 2,
                expected: 4,
                actual: 3,
            }
        );
    }

    #[test]
    fn mutation_reordered_path_and_index_substitution_refuse() {
        let sources = sources();
        let (commitment, prover_data) = commit_packed_interleaved(&sources, 4).unwrap();
        let honest = prover_data.open(5).unwrap();

        assert_eq!(
            verify_packed_interleaved_opening(&commitment, 4, &honest).unwrap_err(),
            PackedInterleavedError::OpeningIndexMismatch {
                expected: 4,
                actual: 5,
            }
        );

        let mut reordered_path = honest.clone();
        reordered_path.authentication_path.swap(0, 1);
        assert!(matches!(
            verify_packed_interleaved_opening(&commitment, 5, &reordered_path),
            Err(PackedInterleavedError::PhysicalOpeningRejected(_))
        ));

        let mut changed_sources = sources.clone();
        changed_sources[0].values.swap(0, 2);
        let (changed_commitment, changed_data) =
            commit_packed_interleaved(&changed_sources, 4).unwrap();
        assert_ne!(
            changed_commitment.alternate_root(),
            commitment.alternate_root()
        );
        let changed_opening = changed_data.open(0).unwrap();
        assert!(matches!(
            verify_packed_interleaved_opening(&commitment, 0, &changed_opening),
            Err(PackedInterleavedError::PhysicalOpeningRejected(_))
        ));
    }

    #[test]
    fn alternate_root_binds_layout_and_is_not_the_canonical_root_api() {
        let sources = sources();
        let (mut commitment, prover_data) = commit_packed_interleaved(&sources, 4).unwrap();
        let opening = prover_data.open(7).unwrap();
        let canonical = audit_canonical_packing_equivalence(&sources).unwrap();

        // Packing alone preserved this root in the first test. The worker-
        // contiguous physical order does not: it must enter a new transcript
        // only through the separately typed/domain-separated alternate root.
        assert_ne!(commitment.physical_root(), &canonical.canonical_root);

        commitment.layout.worker_count = 2;
        assert_eq!(
            verify_packed_interleaved_opening(&commitment, 7, &opening).unwrap_err(),
            PackedInterleavedError::AlternateRootMismatch
        );

        assert_ne!(
            PACKED_INTERLEAVED_ROOT_DOMAIN_V1,
            b"dregg.pcs.canonical-merkle-root\0"
        );
    }
}
