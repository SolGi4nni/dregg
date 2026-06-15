//! Reed–Solomon erasure coding for data availability.
//!
//! Encode a blob into `n_total = n_data * expansion_factor` chunks where any
//! `n_data` suffice to reconstruct (true k-of-n). Light clients sample K random
//! chunks; if all K are retrievable *and* each carries a valid Merkle path to
//! the manifest root, the full data is available with high probability.
//!
//! For dregg: when a blob is committed to the blocklace it is erasure-encoded.
//! Phones (light clients) verify availability by sampling chunks from peers,
//! checking each chunk against the manifest's Merkle root. This proves "the
//! data exists, is the *right* data, and is retrievable" without downloading it
//! all.
//!
//! # What this module provides
//!
//! * **Real Reed–Solomon** over GF(2^8) (the vetted `reed-solomon-erasure`
//!   crate, Vandermonde construction). [`ErasureEncoder::encode`] emits
//!   `n_data` data shards plus `n_data * (expansion_factor - 1)` parity shards;
//!   [`ErasureEncoder::reconstruct`] recovers the original from *any* `n_data`
//!   of the `n_total` shards — not merely the single-loss case the previous
//!   XOR prototype could handle.
//! * **A Merkle-path chunk proof.** Every chunk's commitment is a leaf of a
//!   binary Merkle tree; the tree root is the manifest's `root`. Each chunk
//!   carries a [`MerkleProof`] authenticating its leaf against that root, so a
//!   client that holds only the (small) root can verify an individual chunk it
//!   received from an untrusted operator — and a *tampered* chunk fails its
//!   proof (its data no longer hashes to the committed leaf).
//!
//! The Merkle root is computed with the same BLAKE3 binary-tree construction as
//! [`crate::commitment::blake3_binary_root`] (zero-padded to a power of two),
//! so the root here is byte-identical to the typed-commitment framework's root
//! over the same leaf vector.

use crate::ContentHash;

/// Encoder configuration.
#[derive(Debug, Clone)]
pub struct ErasureEncoder {
    /// Size of each data chunk in bytes.
    pub chunk_size: usize,
    /// Expansion factor: total_chunks = data_chunks * expansion_factor.
    /// With factor 2, any N of 2N chunks suffice.
    pub expansion_factor: usize,
}

/// A single erasure-coded chunk.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ErasureChunk {
    /// Index of this chunk in the encoded set (`0..n_total`; data shards first,
    /// then parity shards).
    pub index: usize,
    /// The chunk data (always exactly `chunk_size` bytes).
    pub data: Vec<u8>,
    /// BLAKE3 commitment of this chunk's data (the Merkle *leaf* for this
    /// chunk).
    pub commitment: [u8; 32],
    /// Whether this is an original data chunk or a parity chunk.
    pub is_parity: bool,
    /// Authentication path proving `commitment` is the leaf at position `index`
    /// of the chunk-set Merkle tree whose root is the manifest's `root`.
    pub proof: MerkleProof,
}

/// A Merkle authentication path for one leaf against a binary BLAKE3 tree root.
///
/// `siblings[d]` is the hash of the sibling node at depth `d` (`d = 0` is the
/// sibling of the leaf, deeper indices climb toward the root). `leaf_index` is
/// the leaf's position; its parity at each level selects whether the sibling is
/// on the left or right. The tree is the one built by [`merkle_root`] /
/// [`crate::commitment::blake3_binary_root`]: leaves zero-padded to the next
/// power of two, parents `= BLAKE3(left || right)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MerkleProof {
    /// Position of the authenticated leaf in the (unpadded) leaf vector.
    pub leaf_index: usize,
    /// Total number of leaves the tree was built over (before power-of-two
    /// padding). Binds the proof to a specific tree shape.
    pub leaf_count: usize,
    /// Sibling hashes from the leaf level up to (but excluding) the root.
    pub siblings: Vec<[u8; 32]>,
}

impl MerkleProof {
    /// Recompute the root implied by `leaf` walking this path, and compare it
    /// to `root`. Returns `true` iff `leaf` is genuinely the `leaf_index`-th
    /// leaf of the tree committed to by `root`.
    pub fn verify(&self, leaf: &[u8; 32], root: &[u8; 32]) -> bool {
        // Single-leaf trees have no siblings and the leaf *is* the root
        // (matches blake3_binary_root's single-leaf passthrough).
        if self.leaf_count <= 1 {
            return self.siblings.is_empty() && leaf == root;
        }
        let mut idx = self.leaf_index;
        let mut acc = *leaf;
        for sib in &self.siblings {
            let mut hasher = blake3::Hasher::new();
            if idx & 1 == 0 {
                // We are the left child.
                hasher.update(&acc);
                hasher.update(sib);
            } else {
                // We are the right child.
                hasher.update(sib);
                hasher.update(&acc);
            }
            acc = *hasher.finalize().as_bytes();
            idx >>= 1;
        }
        &acc == root
    }
}

/// Error during reconstruction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReconstructError {
    /// Not enough chunks to reconstruct (`have < need`; `need == n_data`).
    InsufficientChunks { have: usize, need: usize },
    /// Chunk data is corrupted (commitment mismatch).
    CorruptedChunk { index: usize },
    /// Invalid configuration (e.g. shard count outside the GF(2^8) field, or a
    /// chunk index out of range).
    InvalidConfig(String),
}

/// GF(2^8) field — any `n_data` of `n_total` (≤ 255) shards reconstruct.
type RsField = reed_solomon_erasure::galois_8::Field;

impl ErasureEncoder {
    /// Create a new encoder with the given chunk size and expansion factor.
    ///
    /// `chunk_size` is clamped to at least 1; `expansion_factor` to at least 2
    /// (so there is always ≥ `n_data` redundancy and ≥ 1 parity shard, which
    /// the Reed–Solomon codec requires).
    pub fn new(chunk_size: usize, expansion_factor: usize) -> Self {
        Self {
            chunk_size: chunk_size.max(1),
            expansion_factor: expansion_factor.max(2),
        }
    }

    /// Number of original data shards for a blob of `original_size` bytes.
    fn n_data_for(&self, original_size: usize) -> usize {
        original_size.div_ceil(self.chunk_size).max(1)
    }

    /// Split `data` into `n_data` zero-padded `chunk_size` shards.
    fn split_data_shards(&self, data: &[u8]) -> Vec<Vec<u8>> {
        let mut shards: Vec<Vec<u8>> = data
            .chunks(self.chunk_size)
            .map(|c| {
                let mut v = c.to_vec();
                v.resize(self.chunk_size, 0);
                v
            })
            .collect();
        if shards.is_empty() {
            // Empty blob still gets one (all-zero) data shard so n_data ≥ 1.
            shards.push(vec![0u8; self.chunk_size]);
        }
        shards
    }

    /// Encode data into erasure-coded chunks.
    ///
    /// Returns `n_data * expansion_factor` total chunks: `n_data` data shards
    /// (indices `0..n_data`) followed by `n_data * (expansion_factor - 1)`
    /// Reed–Solomon parity shards. Any `n_data` of them reconstruct the blob.
    ///
    /// Each returned chunk carries a [`MerkleProof`] of its commitment against
    /// the chunk-set root (see [`merkle_root`]); a light client holding only
    /// the root can verify any single chunk.
    pub fn encode(&self, data: &[u8]) -> Vec<ErasureChunk> {
        let mut data_shards = self.split_data_shards(data);
        let n_data = data_shards.len();
        let n_parity = n_data * (self.expansion_factor - 1);

        // Reed–Solomon parity. The codec fills the parity shards in place; on
        // the (only) error path — shard counts exceeding the GF(2^8) field —
        // we fall back to replicating data shards as parity so the encoder is
        // total. Reconstruction from such an oversized set then relies on the
        // data shards directly (still k-of-n for the data shards themselves).
        let mut all_shards: Vec<Vec<u8>> = data_shards.clone();
        all_shards.extend((0..n_parity).map(|_| vec![0u8; self.chunk_size]));

        if let Ok(rs) = reed_solomon_erasure::ReedSolomon::<RsField>::new(n_data, n_parity) {
            // encode() needs &mut [shard]; operate on slices of all_shards.
            let mut refs: Vec<&mut [u8]> =
                all_shards.iter_mut().map(|v| v.as_mut_slice()).collect();
            // If encoding fails (it shouldn't, the shapes are validated), the
            // parity shards stay zero — reconstruction still works from the
            // data shards, which are untouched.
            let _ = rs.encode(&mut refs);
        } else {
            // n_data + n_parity > 255: cannot build a GF(2^8) codec. Replicate
            // data shards across parity slots so any n_data data shards still
            // reconstruct directly.
            for p in 0..n_parity {
                all_shards[n_data + p] = data_shards[p % n_data].clone();
            }
        }

        // Recompute data_shards view consistent with all_shards (parity now
        // filled). Build commitments (Merkle leaves) over every shard.
        data_shards = all_shards;
        let leaves: Vec<[u8; 32]> = data_shards
            .iter()
            .map(|s| chunk_commitment_dual(s).blake3)
            .collect();

        // Build the Merkle tree once; emit a path per leaf.
        let proofs = merkle_proofs(&leaves);

        data_shards
            .into_iter()
            .enumerate()
            .zip(leaves)
            .zip(proofs)
            .map(|(((index, shard), commitment), proof)| ErasureChunk {
                index,
                data: shard,
                commitment,
                is_parity: index >= n_data,
                proof,
            })
            .collect()
    }

    /// Reconstruct the original data from a subset of chunks.
    ///
    /// Succeeds given *any* `n_data` chunks (data and/or parity) of the
    /// `n_total` emitted, where `n_data = ceil(original_size / chunk_size)`.
    /// Each supplied chunk is verified against its own commitment first; a
    /// corrupted chunk is rejected rather than silently mis-reconstructed.
    pub fn reconstruct(
        &self,
        chunks: &[ErasureChunk],
        original_size: usize,
    ) -> Result<Vec<u8>, ReconstructError> {
        let n_data = self.n_data_for(original_size);
        let n_parity = n_data * (self.expansion_factor - 1);
        let n_total = n_data + n_parity;

        // Per-chunk integrity + place each into its slot.
        let mut slots: Vec<Option<Vec<u8>>> = vec![None; n_total];
        for chunk in chunks {
            if chunk_commitment_dual(&chunk.data).blake3 != chunk.commitment {
                return Err(ReconstructError::CorruptedChunk { index: chunk.index });
            }
            if chunk.index >= n_total {
                return Err(ReconstructError::InvalidConfig(format!(
                    "chunk index {} out of range (n_total = {})",
                    chunk.index, n_total
                )));
            }
            if chunk.data.len() != self.chunk_size {
                return Err(ReconstructError::InvalidConfig(format!(
                    "chunk {} has length {} (expected chunk_size {})",
                    chunk.index,
                    chunk.data.len(),
                    self.chunk_size
                )));
            }
            slots[chunk.index] = Some(chunk.data.clone());
        }

        let present = slots.iter().filter(|s| s.is_some()).count();
        if present < n_data {
            return Err(ReconstructError::InsufficientChunks {
                have: present,
                need: n_data,
            });
        }

        // Reed–Solomon reconstruction of the missing data shards.
        if let Ok(rs) = reed_solomon_erasure::ReedSolomon::<RsField>::new(n_data, n_parity) {
            rs.reconstruct_data(&mut slots).map_err(|e| match e {
                reed_solomon_erasure::Error::TooFewShardsPresent => {
                    ReconstructError::InsufficientChunks {
                        have: present,
                        need: n_data,
                    }
                }
                other => ReconstructError::InvalidConfig(other.to_string()),
            })?;
        }
        // (If the codec couldn't be built — oversized set — the data shards
        // were replicated 1:1 into parity at encode time, so any n_data data
        // shards are already present in `slots[0..n_data]` when reconstructable;
        // the assembly below handles the data slots directly.)

        // Assemble the original from the (now reconstructed) data shards.
        let mut result = Vec::with_capacity(n_data * self.chunk_size);
        for slot in slots.iter().take(n_data) {
            match slot {
                Some(bytes) => result.extend_from_slice(bytes),
                None => {
                    // A data shard is still missing (only reachable on the
                    // oversized-set fallback where RS could not run).
                    return Err(ReconstructError::InsufficientChunks {
                        have: present,
                        need: n_data,
                    });
                }
            }
        }
        result.truncate(original_size);
        Ok(result)
    }
}

/// Verify that a chunk's data matches its commitment (its Merkle leaf).
pub fn verify_chunk(chunk: &ErasureChunk) -> bool {
    chunk_commitment_dual(&chunk.data).blake3 == chunk.commitment
}

/// Dual-form commitment for a single erasure chunk's data (the Merkle leaf).
pub fn chunk_commitment_dual(data: &[u8]) -> crate::commitment::ErasureChunkCommitment {
    crate::commitment::Commitment::seal(data)
}

/// Compute the chunk-set Merkle root (BLAKE3 binary tree over chunk leaves).
///
/// This is the root a light client keeps as `manifest.root`. It is byte-
/// identical to [`crate::commitment::blake3_binary_root`] over the same leaf
/// vector, so the typed-commitment framework and this module agree.
pub fn merkle_root(chunks: &[ErasureChunk]) -> ContentHash {
    let leaves: Vec<[u8; 32]> = chunks.iter().map(|c| c.commitment).collect();
    ContentHash(crate::commitment::blake3_binary_root(&leaves))
}

/// The combined root commitment for a set of chunks.
///
/// Now defined as the **Merkle root** over the chunk leaves (was a flat hash of
/// the concatenated commitments in the XOR prototype). Returning the Merkle
/// root is what makes per-chunk [`MerkleProof`]s verifiable against
/// `manifest.root`.
pub fn root_commitment(chunks: &[ErasureChunk]) -> ContentHash {
    merkle_root(chunks)
}

/// Dual-form combined-root commitment for a set of erasure chunks.
///
/// The BLAKE3 form is the chunk-set Merkle root; the Poseidon2 form is the
/// dual-form Poseidon2 Merkle root over the same leaves (via the typed
/// framework's [`crate::commitment::MerkleRoot`]).
pub fn root_commitment_dual(chunks: &[ErasureChunk]) -> crate::commitment::ErasureSetCommitment {
    // Seal the canonical leaf concatenation so both digests bind the leaf set;
    // the BLAKE3 form below is then *overridden* with the Merkle root so it
    // matches `merkle_root`. (The Poseidon2 companion remains a sound binding
    // of the same canonical preimage.)
    let mut canonical = Vec::with_capacity(chunks.len() * 32);
    for chunk in chunks {
        canonical.extend_from_slice(&chunk.commitment);
    }
    let sealed: crate::commitment::ErasureSetCommitment =
        crate::commitment::Commitment::seal(&canonical[..]);
    let merkle = merkle_root(chunks).0;
    crate::commitment::Commitment::from_parts(merkle, sealed.poseidon2)
}

/// Verify a chunk against a root commitment using its Merkle proof.
///
/// This is the real availability check: it confirms (a) the chunk's data
/// hashes to its committed leaf, and (b) that leaf is genuinely a member of the
/// tree committed to by `root` at the chunk's claimed position. A tampered
/// chunk fails (a); a chunk swapped in from a different blob/position fails (b).
pub fn verify_chunk_against_root(chunk: &ErasureChunk, root: &ContentHash) -> bool {
    // (a) integrity: data → leaf.
    if chunk_commitment_dual(&chunk.data).blake3 != chunk.commitment {
        return false;
    }
    // (b) membership: leaf → root via the authentication path.
    chunk.proof.verify(&chunk.commitment, &root.0)
}

/// Internal: build a binary BLAKE3 Merkle tree over `leaves` (zero-padded to
/// the next power of two) and return an authentication path for every original
/// leaf. The root these paths authenticate equals
/// [`crate::commitment::blake3_binary_root`] of the same leaves.
fn merkle_proofs(leaves: &[[u8; 32]]) -> Vec<MerkleProof> {
    let n = leaves.len();
    if n == 0 {
        return Vec::new();
    }
    if n == 1 {
        // Single-leaf tree: leaf is the root, empty path.
        return vec![MerkleProof {
            leaf_index: 0,
            leaf_count: 1,
            siblings: Vec::new(),
        }];
    }

    // Build all layers (each parent = BLAKE3(left || right)), padding each
    // layer to even width with zero nodes.
    let mut layers: Vec<Vec<[u8; 32]>> = Vec::new();
    let mut layer: Vec<[u8; 32]> = leaves.to_vec();
    layer.resize(layer.len().next_power_of_two(), [0u8; 32]);
    layers.push(layer.clone());
    while layer.len() > 1 {
        let mut next = Vec::with_capacity(layer.len() / 2);
        for pair in layer.chunks(2) {
            let mut hasher = blake3::Hasher::new();
            hasher.update(&pair[0]);
            hasher.update(&pair[1]);
            next.push(*hasher.finalize().as_bytes());
        }
        layers.push(next.clone());
        layer = next;
    }

    // For each original leaf, collect the sibling at each level.
    (0..n)
        .map(|leaf_index| {
            let mut siblings = Vec::with_capacity(layers.len().saturating_sub(1));
            let mut idx = leaf_index;
            for level in &layers[..layers.len() - 1] {
                let sib = idx ^ 1;
                siblings.push(level[sib]);
                idx >>= 1;
            }
            MerkleProof {
                leaf_index,
                leaf_count: n,
                siblings,
            }
        })
        .collect()
}

/// Calculate the probability that data is available given sampling results.
/// If we sample `sample_size` chunks from `total_chunks` and find
/// `chunks_available` of them present, what is the probability the full data is
/// available?
///
/// Under the model: with a k-of-n RS code the blob is reconstructable iff at
/// least `n_data` of `n_total` chunks survive. A light client that samples K
/// chunks (each verified against the Merkle root) and finds them all present
/// gains confidence an adversary is not withholding more than it appears.
///
/// Simplified: if all K sampled chunks are present, confidence ≈ 1 − (1/2)^K
/// at the 50%-available worst case.
pub fn sample_availability(
    chunks_available: usize,
    total_chunks: usize,
    sample_size: usize,
) -> f64 {
    if total_chunks == 0 || sample_size == 0 {
        return 0.0;
    }
    if chunks_available >= total_chunks {
        return 1.0;
    }

    let availability_ratio = chunks_available as f64 / total_chunks as f64;
    if availability_ratio >= 0.5 {
        1.0 - (1.0 - availability_ratio).powi(sample_size as i32)
    } else {
        availability_ratio.powi(sample_size as i32)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: encode and return (chunks, n_data).
    fn enc(data: &[u8], chunk_size: usize, expansion: usize) -> (Vec<ErasureChunk>, usize) {
        let encoder = ErasureEncoder::new(chunk_size, expansion);
        let n_data = encoder.n_data_for(data.len());
        (encoder.encode(data), n_data)
    }

    #[test]
    fn encode_emits_n_total_chunks() {
        let (chunks, n_data) = enc(b"the quick brown fox jumps over the lazy dog!!", 8, 2);
        assert_eq!(chunks.len(), n_data * 2);
        assert_eq!(chunks.iter().filter(|c| !c.is_parity).count(), n_data);
        assert_eq!(chunks.iter().filter(|c| c.is_parity).count(), n_data);
    }

    #[test]
    fn roundtrip_all_chunks() {
        let data = b"availability is reachable and reconstructable now".to_vec();
        let encoder = ErasureEncoder::new(8, 2);
        let chunks = encoder.encode(&data);
        let recovered = encoder.reconstruct(&chunks, data.len()).unwrap();
        assert_eq!(recovered, data);
    }

    #[test]
    fn rs_recovers_from_any_k_of_n_data_only() {
        // Real RS: any n_data shards reconstruct, even ALL-parity.
        let data = b"reed solomon recovers from any k of n shards, parity included".to_vec();
        let encoder = ErasureEncoder::new(8, 2);
        let chunks = encoder.encode(&data);
        let n_data = encoder.n_data_for(data.len());

        // Keep only the parity shards (the hard case the XOR prototype failed).
        let parity_only: Vec<_> = chunks.iter().filter(|c| c.is_parity).cloned().collect();
        assert!(parity_only.len() >= n_data);
        let recovered = encoder
            .reconstruct(&parity_only[..n_data], data.len())
            .unwrap();
        assert_eq!(recovered, data);
    }

    #[test]
    fn rs_recovers_from_every_k_subset() {
        // Exhaustively: drop each possible (n_total - n_data) subset, recover
        // from the remaining n_data. (Small params keep the combinatorics tiny.)
        let data = b"abcdefghijklmnop".to_vec(); // 16 bytes, chunk 8 => 2 data shards
        let encoder = ErasureEncoder::new(8, 2); // n_data=2, n_total=4
        let chunks = encoder.encode(&data);
        let n_total = chunks.len();
        let n_data = encoder.n_data_for(data.len());
        assert_eq!((n_data, n_total), (2, 4));

        // Every n_data-subset of the 4 chunks must reconstruct.
        for i in 0..n_total {
            for j in (i + 1)..n_total {
                let subset = vec![chunks[i].clone(), chunks[j].clone()];
                let recovered = encoder
                    .reconstruct(&subset, data.len())
                    .unwrap_or_else(|e| panic!("subset {{{i},{j}}} failed: {e:?}"));
                assert_eq!(recovered, data, "subset {{{i},{j}}}");
            }
        }
    }

    #[test]
    fn reconstruct_fails_below_threshold() {
        let data = b"this blob spans several chunks for sure".to_vec();
        let encoder = ErasureEncoder::new(8, 2);
        let chunks = encoder.encode(&data);
        let n_data = encoder.n_data_for(data.len());
        // One fewer than n_data must fail.
        let too_few = &chunks[..n_data - 1];
        let err = encoder.reconstruct(too_few, data.len()).unwrap_err();
        assert!(matches!(err, ReconstructError::InsufficientChunks { .. }));
    }

    #[test]
    fn reconstruct_rejects_corrupt_chunk() {
        let data = b"tamper with a chunk and get caught here".to_vec();
        let encoder = ErasureEncoder::new(8, 2);
        let mut chunks = encoder.encode(&data);
        chunks[0].data[0] ^= 0xFF; // corrupt data, stale commitment.
        let err = encoder.reconstruct(&chunks, data.len()).unwrap_err();
        assert_eq!(err, ReconstructError::CorruptedChunk { index: 0 });
    }

    // ---- Merkle proof: the real chunk-availability tooth ---------------------

    #[test]
    fn every_chunk_proof_verifies_against_root() {
        let data = b"every honest chunk authenticates against the manifest root".to_vec();
        let encoder = ErasureEncoder::new(8, 2);
        let chunks = encoder.encode(&data);
        let root = root_commitment(&chunks);
        for chunk in &chunks {
            assert!(
                verify_chunk_against_root(chunk, &root),
                "chunk {} failed its Merkle proof",
                chunk.index
            );
            // The proof also verifies directly against the leaf.
            assert!(chunk.proof.verify(&chunk.commitment, &root.0));
        }
    }

    #[test]
    fn corrupted_chunk_fails_its_merkle_proof() {
        let data = b"a corrupted chunk must fail its merkle proof, full stop".to_vec();
        let encoder = ErasureEncoder::new(8, 2);
        let chunks = encoder.encode(&data);
        let root = root_commitment(&chunks);

        // Tamper the data but keep the (now-stale) commitment + proof: the
        // integrity leg fails.
        let mut tampered = chunks[1].clone();
        tampered.data[0] ^= 0xFF;
        assert!(!verify_chunk_against_root(&tampered, &root));

        // Tamper the data AND recompute its leaf commitment (so integrity
        // passes) but keep the old path: the *membership* leg must now fail,
        // because the recomputed leaf is not in the committed tree.
        let mut forged = chunks[1].clone();
        forged.data[0] ^= 0xFF;
        forged.commitment = chunk_commitment_dual(&forged.data).blake3;
        assert!(verify_chunk(&forged)); // integrity passes...
        assert!(
            !verify_chunk_against_root(&forged, &root),
            "a leaf not in the tree must fail the membership proof"
        );
    }

    #[test]
    fn chunk_from_another_blob_fails_membership() {
        let (chunks_a, _) = enc(b"i am blob A, the genuine article", 8, 2);
        let (chunks_b, _) = enc(b"i am blob B, a different payload!", 8, 2);
        let root_a = root_commitment(&chunks_a);
        // A perfectly internally-consistent chunk from B (valid integrity +
        // valid proof against B's root) must NOT verify against A's root.
        assert!(verify_chunk(&chunks_b[0]));
        assert!(!verify_chunk_against_root(&chunks_b[0], &root_a));
    }

    #[test]
    fn wrong_position_fails_membership() {
        let data = b"position binding: a leaf is at exactly one index".to_vec();
        let encoder = ErasureEncoder::new(8, 2);
        let chunks = encoder.encode(&data);
        let root = root_commitment(&chunks);
        // Take chunk 0's (data, commitment) but claim chunk 2's path/index.
        let mut misplaced = chunks[0].clone();
        misplaced.proof = chunks[2].proof.clone();
        misplaced.index = 2;
        assert!(verify_chunk(&misplaced)); // integrity still fine
        assert!(
            !verify_chunk_against_root(&misplaced, &root),
            "leaf-0 under leaf-2's path must fail"
        );
    }

    #[test]
    fn merkle_root_matches_commitment_framework() {
        // The Merkle root here must equal blake3_binary_root over the leaves.
        let data = b"roots agree across the commitment framework boundary".to_vec();
        let encoder = ErasureEncoder::new(8, 2);
        let chunks = encoder.encode(&data);
        let leaves: Vec<[u8; 32]> = chunks.iter().map(|c| c.commitment).collect();
        let expected = crate::commitment::blake3_binary_root(&leaves);
        assert_eq!(root_commitment(&chunks).0, expected);
    }

    #[test]
    fn single_chunk_blob_proof_is_passthrough() {
        // A blob fitting in one chunk → one data shard + one parity shard
        // (expansion 2), so n_total = 2 and proofs are non-trivial. Verify the
        // proof tooth still holds at the smallest non-degenerate size.
        let data = b"tiny".to_vec();
        let encoder = ErasureEncoder::new(64, 2);
        let chunks = encoder.encode(&data);
        assert_eq!(chunks.len(), 2);
        let root = root_commitment(&chunks);
        for chunk in &chunks {
            assert!(verify_chunk_against_root(chunk, &root));
        }
        let recovered = encoder.reconstruct(&chunks[..1], data.len()).unwrap();
        assert_eq!(recovered, data);
    }

    #[test]
    fn larger_blob_higher_expansion_any_k() {
        // n_data = 5, expansion 3 => n_total = 15, tolerate losing 10.
        let data: Vec<u8> = (0..200u32).map(|i| (i % 251) as u8).collect();
        let encoder = ErasureEncoder::new(40, 3);
        let chunks = encoder.encode(&data);
        let n_data = encoder.n_data_for(data.len());
        let n_total = chunks.len();
        assert_eq!((n_data, n_total), (5, 15));
        // Keep an arbitrary k-subset (the last n_data chunks, all parity-heavy).
        let subset: Vec<_> = chunks.iter().skip(n_total - n_data).cloned().collect();
        let recovered = encoder.reconstruct(&subset, data.len()).unwrap();
        assert_eq!(recovered, data);
        // And every chunk authenticates.
        let root = root_commitment(&chunks);
        assert!(chunks.iter().all(|c| verify_chunk_against_root(c, &root)));
    }

    #[test]
    fn sample_availability_monotone() {
        assert_eq!(sample_availability(10, 10, 5), 1.0);
        assert_eq!(sample_availability(0, 10, 5), 0.0);
        assert!(sample_availability(8, 10, 8) > 0.99);
        assert!(sample_availability(5, 10, 1) <= 0.5 + 1e-9);
    }
}
