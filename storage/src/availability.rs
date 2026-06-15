//! Availability route: bridge the content-addressed store to erasure coding.
//!
//! The [`erasure`](crate::erasure) module can encode a blob into chunks,
//! sample availability, and reconstruct — but, per the `ORGANS.md` §3 note,
//! those pieces were *unreachable from the store*: there was no entry-point
//! that took a blob the [`ContentStore`] already holds and produced its
//! erasure encoding + the manifest a light client needs to verify
//! availability and reconstruct.
//!
//! This module is that entry-point. It is deliberately a thin, side-effect-free
//! bridge over `ContentStore` + `erasure` so it composes with the existing
//! ownership / quota machinery without reaching into either's internals:
//!
//! * [`encode_for_availability`] reads a stored blob and returns its
//!   [`AvailabilityManifest`] (the small commitment a light client keeps) plus
//!   the chunk set an operator disseminates.
//! * [`AvailabilityManifest::confidence`] is the light-client sampler — given
//!   how many of the manifest's chunks a sampling pass found present, it
//!   reports the availability confidence (routes through
//!   [`erasure::sample_availability`]).
//! * [`reconstruct`] rebuilds the original blob from a surviving subset of
//!   chunks, verifying each chunk against its commitment and the recovered
//!   bytes against the blob's content hash (so a corrupt or wrong chunk set is
//!   rejected, not silently accepted).
//!
//! The manifest is content-addressed end-to-end: its `content_hash` is the
//! BLAKE3 of the original blob and its `root` is the erasure-set root
//! commitment, so possession of a manifest is enough to (a) sample
//! availability against an untrusted operator and (b) verify a reconstruction
//! is the *right* blob, not merely *a* blob.

use crate::content::ContentStore;
use crate::erasure::{self, ErasureChunk, ErasureEncoder, ReconstructError};
use crate::{ContentHash, StorageError};

/// The small, content-addressed record a light client keeps so it can sample
/// availability and verify a reconstruction without holding the blob.
///
/// A manifest is cheap (a few words + two 32-byte commitments) and is the unit
/// that travels to phones / light clients: given a manifest, a client can ask
/// arbitrary (untrusted) operators for chunks, check each against its
/// commitment, and reconstruct — confident the result is exactly the blob
/// named by `content_hash`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AvailabilityManifest {
    /// BLAKE3 content hash of the *original* blob. A reconstruction is only
    /// accepted if it hashes to this.
    pub content_hash: ContentHash,
    /// Erasure-set root commitment over all chunk commitments (binds the chunk
    /// set as a whole; see [`erasure::root_commitment`]).
    pub root: ContentHash,
    /// Size in bytes of the original blob (needed to truncate padding on
    /// reconstruction).
    pub original_size: usize,
    /// Chunk size used by the encoder.
    pub chunk_size: usize,
    /// Number of original *data* chunks (the reconstruction threshold).
    pub n_data: usize,
    /// Total number of chunks emitted (`n_data * expansion_factor`).
    pub n_total: usize,
}

impl AvailabilityManifest {
    /// Availability confidence given a sampling pass that found
    /// `chunks_found` of the manifest's `n_total` chunks present.
    ///
    /// Routes through [`erasure::sample_availability`]: if at least the
    /// reconstruction threshold's worth of chunks are present the blob is
    /// recoverable, and the returned value is the sampler's confidence that an
    /// adversary is not hiding more than it appears.
    pub fn confidence(&self, chunks_found: usize, sample_size: usize) -> f64 {
        erasure::sample_availability(chunks_found, self.n_total, sample_size)
    }

    /// The minimum number of chunks required to reconstruct (the data-chunk
    /// count `n_data`). With the real Reed–Solomon code, *any* `n_data` of the
    /// `n_total` chunks — data and/or parity, in any combination — suffice.
    pub fn reconstruction_threshold(&self) -> usize {
        self.n_data
    }

    /// The redundancy factor `n_total / n_data` (≥ 2). Reconstructed from the
    /// manifest so the encoder used by [`reconstruct`] matches the one that
    /// produced the chunks.
    pub fn expansion_factor(&self) -> usize {
        if self.n_data == 0 {
            2
        } else {
            (self.n_total / self.n_data).max(2)
        }
    }
}

/// Read a blob the store already holds and produce its erasure encoding.
///
/// Returns the [`AvailabilityManifest`] (kept by light clients) together with
/// the full chunk set (disseminated to operators). The blob is *not* mutated
/// or re-charged — this is a read-only availability route over content the
/// caller already owns.
///
/// `expansion_factor` is the redundancy: `n_total = n_data * expansion_factor`,
/// so any `n_data` of `n_total` chunks reconstruct (factor 2 ⇒ tolerate half
/// the chunks missing).
pub fn encode_for_availability(
    store: &ContentStore,
    hash: &ContentHash,
    chunk_size: usize,
    expansion_factor: usize,
) -> Result<(AvailabilityManifest, Vec<ErasureChunk>), StorageError> {
    let data = store.read(hash).ok_or(StorageError::NotFound(*hash))?;
    Ok(encode_bytes_for_availability(
        data,
        chunk_size,
        expansion_factor,
    ))
}

/// Encode raw bytes into chunks + manifest (the store-independent core of
/// [`encode_for_availability`], exposed for callers that already hold the
/// bytes, e.g. a relay encoding an in-flight payload).
pub fn encode_bytes_for_availability(
    data: &[u8],
    chunk_size: usize,
    expansion_factor: usize,
) -> (AvailabilityManifest, Vec<ErasureChunk>) {
    let encoder = ErasureEncoder::new(chunk_size, expansion_factor);
    let chunks = encoder.encode(data);
    // Derive n_data from the emitted set so it always matches the encoder
    // (e.g. an empty blob still yields one all-zero data shard ⇒ n_data ≥ 1).
    let n_data = chunks.len() / encoder.expansion_factor;
    let manifest = AvailabilityManifest {
        content_hash: ContentHash(*blake3::hash(data).as_bytes()),
        root: erasure::root_commitment(&chunks),
        original_size: data.len(),
        chunk_size: encoder.chunk_size,
        n_data,
        n_total: chunks.len(),
    };
    (manifest, chunks)
}

/// Errors from an availability reconstruction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AvailabilityError {
    /// Underlying erasure reconstruction failed (too few / wrong chunks).
    Reconstruct(ReconstructError),
    /// A supplied chunk failed its own commitment check.
    CorruptChunk { index: usize },
    /// A supplied chunk's Merkle proof did not authenticate against the
    /// manifest's root (the chunk is not a member of this manifest's tree at
    /// its claimed position).
    ChunkProofInvalid { index: usize },
    /// The reconstructed bytes did not hash to the manifest's content hash
    /// (the chunk set reconstructed *a* blob, but not the expected one).
    ContentHashMismatch,
    /// The supplied chunk set did not match this manifest's root commitment.
    RootMismatch,
}

/// Reconstruct the original blob from a surviving subset of its chunks,
/// verifying integrity *and Merkle membership* at every step.
///
/// Checks, in order:
/// 1. every supplied chunk verifies against its own commitment (integrity),
/// 2. every supplied chunk's Merkle proof authenticates against
///    `manifest.root` (membership — the chunk really belongs to this blob's
///    erasure set at its claimed position),
/// 3. Reed–Solomon reconstruction succeeds from the subset (any `n_data` of
///    `n_total` chunks suffice),
/// 4. the recovered bytes hash to `manifest.content_hash`.
///
/// Any failure is reported rather than returning unverified bytes. The caller
/// may pass any subset of the chunk set (including all-parity); reconstruction
/// succeeds when the subset meets the manifest's `n_data` threshold.
pub fn reconstruct(
    manifest: &AvailabilityManifest,
    chunks: &[ErasureChunk],
) -> Result<Vec<u8>, AvailabilityError> {
    // (1) per-chunk integrity + (2) per-chunk Merkle membership against the
    // manifest root. The membership check is what binds an operator's chunk to
    // *this* blob: a valid chunk from a different blob (or a forged leaf) is
    // rejected here, before it can influence reconstruction.
    for chunk in chunks {
        if !erasure::verify_chunk(chunk) {
            return Err(AvailabilityError::CorruptChunk { index: chunk.index });
        }
        if !erasure::verify_chunk_against_root(chunk, &manifest.root) {
            return Err(AvailabilityError::ChunkProofInvalid { index: chunk.index });
        }
    }

    // (3) Reed–Solomon reconstruction (k-of-n).
    let encoder = ErasureEncoder::new(manifest.chunk_size, manifest.expansion_factor());
    let recovered = encoder
        .reconstruct(chunks, manifest.original_size)
        .map_err(AvailabilityError::Reconstruct)?;

    // (4) content-hash binding: the recovered blob must be the expected one.
    if ContentHash(*blake3::hash(&recovered).as_bytes()) != manifest.content_hash {
        return Err(AvailabilityError::ContentHashMismatch);
    }

    Ok(recovered)
}

/// Verify that a chunk set matches a manifest's root commitment (i.e. these are
/// the chunks this manifest was issued over). A light client runs this before
/// trusting an operator's chunk advertisement.
pub fn chunks_match_manifest(manifest: &AvailabilityManifest, chunks: &[ErasureChunk]) -> bool {
    chunks.len() == manifest.n_total && erasure::root_commitment(chunks) == manifest.root
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::QuotaId;
    use crate::quota::SpaceBank;

    fn test_store(computrons: u64) -> (ContentStore, QuotaId) {
        let mut bank = SpaceBank::new(1, 50, 0.8);
        let owner = [0xCD; 32];
        let id = bank.allocate_quota(owner, computrons, None);
        (ContentStore::new(bank), id)
    }

    #[test]
    fn encode_route_reaches_a_stored_blob() {
        // The whole point of the §3 weld: a blob written to the store is now
        // reachable by the availability route.
        let (mut store, payer) = test_store(1_000_000);
        let data = b"availability is reachable from the store now!!!!".repeat(4);
        let hash = store.write(&data, &payer).unwrap();

        let (manifest, chunks) = encode_for_availability(&store, &hash, 16, 2).unwrap();
        assert_eq!(manifest.content_hash, hash);
        assert_eq!(manifest.original_size, data.len());
        assert_eq!(chunks.len(), manifest.n_total);
        assert!(chunks_match_manifest(&manifest, &chunks));
    }

    #[test]
    fn encode_route_rejects_unknown_blob() {
        let (store, _payer) = test_store(1_000);
        let missing = ContentHash([0x99; 32]);
        let err = encode_for_availability(&store, &missing, 16, 2).unwrap_err();
        assert_eq!(err, StorageError::NotFound(missing));
    }

    #[test]
    fn reconstruct_full_roundtrip_via_manifest() {
        let (mut store, payer) = test_store(1_000_000);
        let data = b"the quick brown fox jumps over the lazy availability dog".to_vec();
        let hash = store.write(&data, &payer).unwrap();

        let (manifest, chunks) = encode_for_availability(&store, &hash, 16, 2).unwrap();
        let recovered = reconstruct(&manifest, &chunks).unwrap();
        assert_eq!(recovered, data);
    }

    #[test]
    fn reconstruct_from_data_chunks_only() {
        let (manifest, chunks) =
            encode_bytes_for_availability(b"only the data chunks survive here", 16, 2);
        let data_only: Vec<_> = chunks.into_iter().filter(|c| !c.is_parity).collect();
        let recovered = reconstruct(&manifest, &data_only).unwrap();
        assert_eq!(recovered, b"only the data chunks survive here");
    }

    #[test]
    fn reconstruct_recovers_single_lost_chunk_from_parity() {
        // Drop exactly one data chunk; Reed–Solomon parity recovers it.
        let (manifest, chunks) =
            encode_bytes_for_availability(b"lose one chunk and recover it ok", 16, 2);
        // Keep all but the first data chunk, plus the parity chunks.
        let surviving: Vec<_> = chunks
            .into_iter()
            .filter(|c| c.index != 0 || c.is_parity)
            .collect();
        let recovered = reconstruct(&manifest, &surviving).unwrap();
        assert_eq!(recovered, b"lose one chunk and recover it ok");
    }

    #[test]
    fn reconstruct_recovers_from_any_k_of_n_including_all_parity() {
        // The real RS guarantee: any n_data of n_total chunks reconstruct —
        // even keeping ONLY parity shards (impossible under the old XOR scheme).
        let data = b"reed solomon at the availability layer recovers from any k subset".to_vec();
        let (manifest, chunks) = encode_bytes_for_availability(&data, 16, 2);
        let parity_only: Vec<_> = chunks.iter().filter(|c| c.is_parity).cloned().collect();
        assert!(parity_only.len() >= manifest.n_data);
        let recovered = reconstruct(&manifest, &parity_only[..manifest.n_data]).unwrap();
        assert_eq!(recovered, data);
    }

    #[test]
    fn reconstruct_rejects_corrupt_chunk() {
        let (manifest, mut chunks) =
            encode_bytes_for_availability(b"tamper with a chunk and get caught", 16, 2);
        chunks[0].data[0] ^= 0xFF; // corrupt, but leave the stale commitment.
        let err = reconstruct(&manifest, &chunks).unwrap_err();
        assert_eq!(err, AvailabilityError::CorruptChunk { index: 0 });
    }

    #[test]
    fn reconstruct_rejects_chunk_with_forged_leaf_via_merkle_proof() {
        // Stronger than the integrity check: re-derive a tampered chunk's leaf
        // commitment so it passes verify_chunk, then watch the Merkle proof
        // reject it — the forged leaf is not in manifest.root's tree.
        let (manifest, mut chunks) =
            encode_bytes_for_availability(b"forge a leaf but the root still catches you!", 16, 2);
        chunks[0].data[0] ^= 0xFF;
        chunks[0].commitment = erasure::chunk_commitment_dual(&chunks[0].data).blake3;
        assert!(erasure::verify_chunk(&chunks[0])); // integrity now passes...
        let err = reconstruct(&manifest, &chunks).unwrap_err();
        assert_eq!(err, AvailabilityError::ChunkProofInvalid { index: 0 });
    }

    #[test]
    fn reconstruct_rejects_wrong_blob_under_valid_chunks() {
        // Take a perfectly valid chunk set for blob B, but check it against a
        // manifest for blob A. Per-chunk commitments pass (they're internally
        // consistent), but the *Merkle membership* leg must reject every chunk:
        // B's leaves are not in A's tree, so they fail to authenticate against
        // manifest_a.root before reconstruction can even run.
        let (manifest_a, _) = encode_bytes_for_availability(b"i am blob A, the real one", 16, 2);
        let (_, chunks_b) = encode_bytes_for_availability(b"i am blob B, an impostor!", 16, 2);
        let err = reconstruct(&manifest_a, &chunks_b).unwrap_err();
        // The Merkle-root binding is the tooth here. (For pathological inputs
        // where shapes differ wildly a Reconstruct error is also acceptable.)
        assert!(matches!(
            err,
            AvailabilityError::ChunkProofInvalid { .. }
                | AvailabilityError::ContentHashMismatch
                | AvailabilityError::Reconstruct(_)
        ));
    }

    #[test]
    fn reconstruct_fails_below_threshold() {
        let (manifest, chunks) = encode_bytes_for_availability(
            b"this blob is long enough to span several chunks for sure yes",
            16,
            2,
        );
        let too_few = &chunks[..1];
        let err = reconstruct(&manifest, too_few).unwrap_err();
        assert!(matches!(err, AvailabilityError::Reconstruct(_)));
    }

    #[test]
    fn confidence_sampler_routes_through_erasure() {
        let (manifest, _chunks) = encode_bytes_for_availability(&[0u8; 256], 16, 2);
        // All chunks found => full confidence.
        assert_eq!(manifest.confidence(manifest.n_total, 8), 1.0);
        // None found => zero.
        assert_eq!(manifest.confidence(0, 8), 0.0);
        // Majority present, decent sample => high confidence.
        let found = manifest.n_total * 3 / 4;
        assert!(manifest.confidence(found, 12) > 0.9);
    }

    #[test]
    fn chunks_match_manifest_detects_wrong_set() {
        let (manifest, chunks) = encode_bytes_for_availability(b"matched set", 16, 2);
        assert!(chunks_match_manifest(&manifest, &chunks));
        // A truncated set must not match (wrong count).
        assert!(!chunks_match_manifest(
            &manifest,
            &chunks[..chunks.len() - 1]
        ));
    }
}
