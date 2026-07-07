//! Light-client retrieval over the erasure-coded availability layer.
//!
//! [`availability`](crate::availability) gives a light client the two ends of
//! the data-availability story — an [`AvailabilityManifest`] (the small,
//! content-addressed record it holds) and [`availability::reconstruct`] (verify
//! a chunk set against the manifest root and rebuild the blob). What was missing
//! was the *fetch loop* between them: pull `k`-of-`n` chunks from one or more
//! (untrusted) operators, Merkle-verify each against the manifest root, and
//! reconstruct — so a single node **withholding** the bytes no longer breaks
//! retrieval.
//!
//! This module is that loop, kept **peer-agnostic**: it talks to a
//! [`ChunkSource`] (one operator/peer that *may or may not* hold any given
//! chunk and is *not trusted* to return honest bytes). The HTTP wiring (a node
//! serving `GET /storage/chunk/{hash}/{index}`, a client adapter that hits one
//! peer's URL) lives in `dregg-node`; the trust-bearing logic — Merkle
//! membership per chunk, k-of-n threshold, content-hash binding, and the
//! data-availability sampling confidence — lives here, where it is exercised by
//! pure tests with synthetic peers (honest, withholding, and forging).
//!
//! # The retrieval guarantee
//!
//! Given a manifest verified against a commitment, [`retrieve`] returns the
//! original bytes iff at least `manifest.n_data` chunks are obtainable across
//! the supplied sources AND each obtained chunk authenticates against
//! `manifest.root`. Concretely:
//!
//! * a peer that **withholds** chunks (returns `None`) is simply skipped — as
//!   long as `n_data` chunks survive across all peers, retrieval succeeds
//!   (the k-of-n availability property);
//! * a peer that **forges** a chunk (tampered data, or a valid chunk from a
//!   different blob/position) is rejected by [`erasure::verify_chunk_against_root`]
//!   before it can influence reconstruction — a forged chunk never counts toward
//!   the threshold;
//! * the final reconstruction is content-hash bound (`availability::reconstruct`),
//!   so the recovered blob is provably the one named by the manifest.
//!
//! # Lean-proven spec
//!
//! The per-chunk acceptance predicate this loop gates on —
//! [`erasure::verify_chunk_against_root`], "the chunk opens against the
//! manifest root at its committed position" — is the client-side realization
//! of the PoR audit proven in `metatheory/Dregg2/Storage/Retrievability.lean`:
//!
//! * `por_sound` — an opening that verifies IS the genuine committed object at
//!   that position (reduces to `Dregg2/Storage/BucketCommitment.lean::read_sound`),
//!   and `por_holds_committed` — the whole passing set is genuine, which is why
//!   a gathered `n_data`-set reconstructs the committed blob and nothing else;
//! * `por_refuses_substitution` — an object *different* from the committed one
//!   at a position cannot produce a verifying opening, so a forged / tampered /
//!   wrong-position chunk NEVER counts toward the k-of-n threshold in
//!   [`retrieve`] nor toward the found-count in [`sample_das`].
//!
//! The `lean_*` tests below bind this loop to those theorems.

use crate::availability::{self, AvailabilityError, AvailabilityManifest};
use crate::erasure::{self, ErasureChunk};

/// One operator/peer a light client can ask for chunks. A source is **untrusted**:
/// it may withhold a chunk (`Ok(None)`), error, or return a forged chunk — the
/// retrieval loop verifies every returned chunk against the manifest root and
/// only accepts members of the committed tree.
///
/// The blanket retrieval logic is synchronous and source-agnostic; an async /
/// over-the-wire source (e.g. an HTTP peer) adapts by blocking or by pre-fetching
/// into an in-memory [`InMemorySource`]. The node's HTTP serving path
/// (`GET /storage/chunk/{hash}/{index}`) is the canonical real source.
pub trait ChunkSource {
    /// Attempt to fetch the chunk at `index` for the blob committed by `root`.
    /// `Ok(None)` means "I do not have it / I am withholding it" — a benign
    /// availability fault the loop routes around. `Err` is a transport failure,
    /// treated the same as a miss for liveness but surfaced for scoring.
    fn fetch_chunk(
        &self,
        root: &crate::ContentHash,
        index: usize,
    ) -> Result<Option<ErasureChunk>, ChunkFetchError>;
}

/// A transport-level failure fetching a chunk (distinct from an honest miss).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ChunkFetchError(pub String);

impl core::fmt::Display for ChunkFetchError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "chunk fetch failed: {}", self.0)
    }
}
impl std::error::Error for ChunkFetchError {}

/// Why a light-client retrieval failed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RetrievalError {
    /// Fewer than `n_data` valid chunks were obtainable across all sources —
    /// the data is being withheld beyond the erasure code's recovery threshold.
    Unavailable {
        /// Distinct valid chunks gathered.
        gathered: usize,
        /// Threshold required (`manifest.n_data`).
        need: usize,
    },
    /// Enough chunks were gathered, but the availability reconstruction failed
    /// (e.g. a content-hash mismatch — should not happen once every chunk has
    /// passed its Merkle membership check, but reported rather than hidden).
    Reconstruct(AvailabilityError),
}

impl core::fmt::Display for RetrievalError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            RetrievalError::Unavailable { gathered, need } => write!(
                f,
                "data unavailable: gathered {gathered} valid chunks, need {need} to reconstruct"
            ),
            RetrievalError::Reconstruct(e) => write!(f, "reconstruction failed: {e:?}"),
        }
    }
}
impl std::error::Error for RetrievalError {}

/// **THE RETRIEVAL LOOP** — fetch `k`-of-`n` Merkle-verified chunks from one or
/// more (untrusted) sources and reconstruct the blob behind `manifest`.
///
/// Walks every chunk index `0..manifest.n_total`, asking each source in turn
/// until one returns a chunk that **authenticates against `manifest.root`**
/// (integrity + Merkle membership at the claimed position). A withholding source
/// (`Ok(None)`/`Err`) is skipped; a forging source's chunk is rejected and not
/// counted. Stops as soon as `manifest.n_data` valid chunks are gathered (the
/// k-of-n threshold), then reconstructs via [`availability::reconstruct`] —
/// which re-checks integrity + membership and binds the result to the manifest's
/// content hash.
///
/// Returns the original bytes, or [`RetrievalError::Unavailable`] if fewer than
/// `n_data` valid chunks are obtainable across all sources (genuine
/// unavailability — the withholding exceeded the code's recovery budget).
pub fn retrieve<S: ChunkSource>(
    manifest: &AvailabilityManifest,
    sources: &[S],
) -> Result<Vec<u8>, RetrievalError> {
    let mut gathered: Vec<ErasureChunk> = Vec::with_capacity(manifest.n_data);
    let mut have: Vec<bool> = vec![false; manifest.n_total];

    'indices: for (index, slot) in have.iter_mut().enumerate() {
        if gathered.len() >= manifest.n_data {
            break;
        }
        for source in sources {
            match source.fetch_chunk(&manifest.root, index) {
                Ok(Some(chunk)) => {
                    // Only a chunk that is a genuine member of THIS manifest's
                    // tree at its claimed position counts. A forged chunk
                    // (tampered data, or a valid chunk from another blob) fails
                    // here and is discarded — it never reaches reconstruction.
                    if chunk.index == index
                        && !*slot
                        && erasure::verify_chunk_against_root(&chunk, &manifest.root)
                    {
                        *slot = true;
                        gathered.push(chunk);
                        continue 'indices;
                    }
                    // A returned-but-invalid chunk: try the next source for this
                    // same index (this peer is forging/buggy for this index).
                }
                Ok(None) | Err(_) => { /* withheld / transport fault: next source */ }
            }
        }
    }

    if gathered.len() < manifest.n_data {
        return Err(RetrievalError::Unavailable {
            gathered: gathered.len(),
            need: manifest.n_data,
        });
    }

    availability::reconstruct(manifest, &gathered).map_err(RetrievalError::Reconstruct)
}

/// The verdict of a data-availability sampling (DAS) pass.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct SamplingVerdict {
    /// Number of distinct sampled indices that returned a Merkle-valid chunk.
    pub found: usize,
    /// Number of indices sampled.
    pub sampled: usize,
    /// Confidence the full blob is available (`erasure::sample_availability`).
    pub confidence: f64,
}

impl SamplingVerdict {
    /// Whether the sampling pass clears a confidence threshold (e.g. `0.99`).
    pub fn is_available(&self, threshold: f64) -> bool {
        self.confidence >= threshold
    }
}

/// **THE DATA-AVAILABILITY SAMPLING LOOP** — sample `sample_size` random chunk
/// indices, fetch each from the source set, Merkle-verify it against
/// `manifest.root`, and report a confidence verdict — *without downloading the
/// whole blob*.
///
/// This is the live realization of the sampler whose confidence math already
/// existed (`erasure::sample_availability`) but which previously took a
/// pre-supplied found-count from nowhere. Here the found-count is *produced* by
/// actually fetching sampled chunks from peers and counting the ones that
/// authenticate. A withholding/forging peer drives the found-count (and hence
/// the confidence) DOWN, which is exactly the signal a light client wants: an
/// adversary hiding chunks cannot also make the sampler report them present,
/// because a chunk that does not Merkle-verify against the manifest root is not
/// counted.
///
/// `rng_seed` makes the sampled index set deterministic (a SplitMix64 walk over
/// `0..n_total`); pass a fresh seed per pass for independent samples. Each index
/// is asked of every source until one returns a valid chunk for it.
pub fn sample_das<S: ChunkSource>(
    manifest: &AvailabilityManifest,
    sources: &[S],
    sample_size: usize,
    rng_seed: u64,
) -> SamplingVerdict {
    let n = manifest.n_total.max(1);
    let sample_size = sample_size.min(manifest.n_total);

    // Deterministic distinct index sample (SplitMix64 → Fisher–Yates-lite).
    let mut indices: Vec<usize> = (0..manifest.n_total).collect();
    let mut state = rng_seed ^ 0x9E37_79B9_7F4A_7C15;
    let mut next = || {
        state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    };
    for i in (1..manifest.n_total).rev() {
        let j = (next() % ((i + 1) as u64)) as usize;
        indices.swap(i, j);
    }
    indices.truncate(sample_size);

    let mut found = 0usize;
    for &index in &indices {
        for source in sources {
            if let Ok(Some(chunk)) = source.fetch_chunk(&manifest.root, index)
                && chunk.index == index
                && erasure::verify_chunk_against_root(&chunk, &manifest.root)
            {
                found += 1;
                break;
            }
        }
    }

    let confidence = erasure::sample_availability(
        // Project the sampled found-rate onto the full chunk set so the
        // confidence reflects the population, not just the sample.
        ((found as f64 / sample_size.max(1) as f64) * n as f64).round() as usize,
        manifest.n_total,
        sample_size,
    );
    SamplingVerdict {
        found,
        sampled: sample_size,
        confidence,
    }
}

/// An in-memory [`ChunkSource`] holding a (possibly partial, possibly tampered)
/// subset of a blob's chunks. The reference source for tests and for a client
/// that pre-fetched chunks; the node's HTTP serving path is the real one.
#[derive(Debug, Default, Clone)]
pub struct InMemorySource {
    chunks: std::collections::HashMap<usize, ErasureChunk>,
}

impl InMemorySource {
    /// An empty source (a pure withholder).
    pub fn new() -> Self {
        Self {
            chunks: std::collections::HashMap::new(),
        }
    }

    /// A source holding exactly the supplied chunks.
    pub fn from_chunks(chunks: impl IntoIterator<Item = ErasureChunk>) -> Self {
        let mut s = Self::new();
        for c in chunks {
            s.chunks.insert(c.index, c);
        }
        s
    }

    /// Insert/replace a chunk this source will serve.
    pub fn insert(&mut self, chunk: ErasureChunk) {
        self.chunks.insert(chunk.index, chunk);
    }
}

impl ChunkSource for InMemorySource {
    fn fetch_chunk(
        &self,
        _root: &crate::ContentHash,
        index: usize,
    ) -> Result<Option<ErasureChunk>, ChunkFetchError> {
        Ok(self.chunks.get(&index).cloned())
    }
}

// =============================================================================
// HTTP light-client adapter — retrieve over the node's serving routes
// =============================================================================

/// Retrieve a blob over HTTP from one or more node base URLs, stitching k-of-n
/// chunks across them — the light-client entry point for "fetch the bytes behind
/// a commitment I verified".
///
/// Each node serves `GET {base}/chunk/{content_hash_hex}/{index}` returning a
/// JSON-encoded [`ErasureChunk`] (the `dregg-node` storage gateway's
/// `/storage/chunk/{hash}/{index}` route). `fetch` is the injected transport
/// (`Fn(url) -> Result<body_bytes, err_string>`) so this crate needs no HTTP
/// client; a wallet/browser/agent passes whatever stack it already carries. A
/// node that withholds (empty/404 body or transport error) is skipped; a node
/// that forges a chunk is rejected by [`retrieve`]'s Merkle check against
/// `manifest.root`. Returns the content-hash-bound original bytes, or
/// [`RetrievalError::Unavailable`] if fewer than `n_data` valid chunks are
/// obtainable across all nodes.
pub fn retrieve_via_http<F>(
    manifest: &AvailabilityManifest,
    node_base_urls: &[String],
    fetch: &F,
) -> Result<Vec<u8>, RetrievalError>
where
    F: Fn(&str) -> Result<Vec<u8>, String>,
{
    let content_hex: String = manifest
        .content_hash
        .0
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect();
    let sources: Vec<HttpChunkSource<'_, F>> = node_base_urls
        .iter()
        .map(|base| HttpChunkSource {
            base_url: base.clone(),
            content_hex: content_hex.clone(),
            fetch,
        })
        .collect();
    retrieve(manifest, &sources)
}

/// A [`ChunkSource`] backed by one node's `GET {base}/chunk/{hash}/{index}`
/// route, keyed by the blob's content hash (the node route key). The transport
/// is injected (a `Fn`) so no HTTP client is hard-wired. Constructed by
/// [`retrieve_via_http`]; the trust check (Merkle membership against the manifest
/// root) happens inside [`retrieve`], so a node serving garbage cannot poison the
/// result.
pub struct HttpChunkSource<'f, F>
where
    F: Fn(&str) -> Result<Vec<u8>, String>,
{
    base_url: String,
    content_hex: String,
    fetch: &'f F,
}

impl<F> ChunkSource for HttpChunkSource<'_, F>
where
    F: Fn(&str) -> Result<Vec<u8>, String>,
{
    fn fetch_chunk(
        &self,
        _root: &crate::ContentHash,
        index: usize,
    ) -> Result<Option<ErasureChunk>, ChunkFetchError> {
        let url = format!("{}/chunk/{}/{}", self.base_url, self.content_hex, index);
        match (self.fetch)(&url) {
            Ok(body) if body.is_empty() => Ok(None),
            // A non-chunk body (404 JSON, HTML error) is a miss, not fatal —
            // route around this node for this index.
            Ok(body) => Ok(serde_json::from_slice::<ErasureChunk>(&body).ok()),
            Err(e) => Err(ChunkFetchError(e)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::availability::encode_bytes_for_availability;

    /// Encode a blob and split its chunks across `n` in-memory peers
    /// round-robin (so each peer holds a disjoint slice and no single peer can
    /// serve the whole blob).
    fn shard_across_peers(
        data: &[u8],
        n_peers: usize,
    ) -> (AvailabilityManifest, Vec<InMemorySource>) {
        let (manifest, chunks) = encode_bytes_for_availability(data, 16, 2);
        let mut peers: Vec<InMemorySource> = (0..n_peers).map(|_| InMemorySource::new()).collect();
        for (i, chunk) in chunks.into_iter().enumerate() {
            peers[i % n_peers].insert(chunk);
        }
        (manifest, peers)
    }

    // ── THE BAR: retrieve the bytes behind a verified commitment ─────────────

    #[test]
    fn retrieves_blob_from_a_single_full_source() {
        let data = b"the light client retrieves the bytes behind a verified commitment".to_vec();
        let (manifest, chunks) = encode_bytes_for_availability(&data, 16, 2);
        let source = InMemorySource::from_chunks(chunks);
        let recovered = retrieve(&manifest, &[source]).expect("full source reconstructs");
        assert_eq!(recovered, data);
    }

    #[test]
    fn retrieves_across_multiple_peers_no_single_peer_has_it_all() {
        // Stage 2: chunks are spread across 4 peers; the loop stitches k-of-n
        // from whichever peers hold them. No single peer can serve the blob.
        let data = b"multi-peer chunk fetch: no one operator holds the whole blob here".to_vec();
        let (manifest, peers) = shard_across_peers(&data, 4);
        // Sanity: no peer alone meets the threshold.
        for p in &peers {
            assert!(
                p.chunks.len() < manifest.n_data,
                "no peer should be self-sufficient"
            );
        }
        let recovered = retrieve(&manifest, &peers).expect("k-of-n across peers reconstructs");
        assert_eq!(recovered, data);
    }

    #[test]
    fn withholding_n_minus_k_chunks_still_reconstructs() {
        // A withholder hides the first n_total - n_data chunks; the surviving
        // n_data (here, parity-heavy tail) still reconstruct.
        let data = b"a node withholding up to n-k chunks cannot break retrieval".to_vec();
        let (manifest, chunks) = encode_bytes_for_availability(&data, 16, 2);
        let withheld = manifest.n_total - manifest.n_data;
        let surviving: Vec<ErasureChunk> = chunks.into_iter().skip(withheld).collect();
        assert_eq!(surviving.len(), manifest.n_data, "exactly k chunks survive");
        let source = InMemorySource::from_chunks(surviving);
        let recovered = retrieve(&manifest, &[source]).expect("k survivors reconstruct");
        assert_eq!(recovered, data);
    }

    #[test]
    fn total_withholding_beyond_threshold_is_reported_unavailable() {
        // Only n_data - 1 chunks anywhere: below the recovery threshold ⇒ a
        // genuine, reported unavailability (not a silent wrong answer).
        let data = b"if more than n-k chunks vanish the data is genuinely unavailable".to_vec();
        let (manifest, chunks) = encode_bytes_for_availability(&data, 16, 2);
        let too_few: Vec<ErasureChunk> = chunks.into_iter().take(manifest.n_data - 1).collect();
        let source = InMemorySource::from_chunks(too_few);
        match retrieve(&manifest, &[source]) {
            Err(RetrievalError::Unavailable { gathered, need }) => {
                assert_eq!(gathered, manifest.n_data - 1);
                assert_eq!(need, manifest.n_data);
            }
            other => panic!("expected Unavailable, got {other:?}"),
        }
    }

    #[test]
    fn forged_chunk_is_rejected_and_does_not_count() {
        // A forging peer returns a chunk with a recomputed leaf (passes the
        // integrity check) but whose leaf is not in the manifest's tree — it
        // must NOT count toward the threshold. An honest peer holding the same
        // index lets retrieval still succeed.
        let data =
            b"a forged chunk is rejected by its merkle path against the manifest root".to_vec();
        let (manifest, chunks) = encode_bytes_for_availability(&data, 16, 2);

        // Forger: holds a tampered version of chunk 0.
        let mut forged = chunks[0].clone();
        forged.data[0] ^= 0xFF;
        forged.commitment = erasure::chunk_commitment_dual(&forged.data).blake3; // integrity passes
        assert!(erasure::verify_chunk(&forged));
        assert!(!erasure::verify_chunk_against_root(&forged, &manifest.root)); // membership fails
        let forger = InMemorySource::from_chunks(vec![forged]);

        // Honest peer: holds the genuine remaining chunks.
        let honest = InMemorySource::from_chunks(chunks.iter().skip(1).cloned());

        // forger first in the list — its forged chunk-0 must be skipped, and the
        // honest peer's chunks reconstruct.
        let recovered = retrieve(&manifest, &[forger, honest])
            .expect("forged chunk skipped, honest k-of-n wins");
        assert_eq!(recovered, data);
    }

    #[test]
    fn chunk_from_another_blob_does_not_count() {
        // A peer serving a perfectly valid chunk from a DIFFERENT blob: rejected
        // by Merkle membership against THIS manifest's root.
        let data_a = b"i am blob A, the one the manifest commits to, the real article".to_vec();
        let (manifest_a, _) = encode_bytes_for_availability(&data_a, 16, 2);
        let (_, chunks_b) =
            encode_bytes_for_availability(b"i am blob B, an impostor that should not count", 16, 2);
        // A source serving ONLY blob B's (internally valid) chunks.
        let impostor = InMemorySource::from_chunks(chunks_b);
        match retrieve(&manifest_a, &[impostor]) {
            Err(RetrievalError::Unavailable { gathered, .. }) => {
                assert_eq!(
                    gathered, 0,
                    "no impostor chunk authenticates against A's root"
                );
            }
            other => panic!("impostor chunks must yield Unavailable, got {other:?}"),
        }
    }

    // ── Lean-spec bindings: metatheory/Dregg2/Storage/Retrievability.lean ────
    //
    // These tests assert, at the retrieval/DAS loop, exactly what the Lean
    // theorems prove about the opening relation the loop gates on. A verify
    // that accepted a substituted opening makes the `gathered == 0` /
    // `found == 0` asserts RED.

    /// POSITIVE pole — `Dregg2/Storage/Retrievability.lean::por_sound` +
    /// `por_holds_committed`: every chunk the loop gathers is a verified
    /// opening, hence IS the committed chunk at its position — so across blob
    /// shapes and peer layouts, the reconstruction is the committed blob.
    #[test]
    fn lean_por_sound_retrieval_over_committed_openings_yields_the_blob() {
        for (len, n_peers) in [(37usize, 1usize), (200, 3), (513, 4), (1024, 5)] {
            let data: Vec<u8> = (0..len).map(|i| (i.wrapping_mul(97) % 251) as u8).collect();
            let (manifest, peers) = shard_across_peers(&data, n_peers);
            let recovered = retrieve(&manifest, &peers)
                .expect("committed openings must reconstruct (por_sound binding)");
            assert_eq!(recovered, data, "len={len} n_peers={n_peers}");
        }
    }

    /// NEGATIVE pole — `Dregg2/Storage/Retrievability.lean::por_refuses_substitution`:
    /// a provider serving an internally-consistent *different* object at EVERY
    /// position (each with a recomputed leaf, so an integrity-only check would
    /// pass) produces ZERO verifying openings — no substituted chunk ever
    /// counts toward the k-of-n threshold. `gathered > 0` here would mean the
    /// verify accepted a forgery: RED.
    #[test]
    fn lean_por_refuses_substitution_substituting_provider_gathers_nothing() {
        let data: Vec<u8> = (0..400usize)
            .map(|i| (i.wrapping_mul(11) % 251) as u8)
            .collect();
        let (manifest, chunks) = encode_bytes_for_availability(&data, 16, 2);
        let forged_all: Vec<ErasureChunk> = chunks
            .iter()
            .map(|c| {
                let mut f = c.clone();
                f.data[0] ^= 0xA5;
                f.commitment = erasure::chunk_commitment_dual(&f.data).blake3;
                assert!(erasure::verify_chunk(&f)); // a coherent different object
                f
            })
            .collect();
        let forger = InMemorySource::from_chunks(forged_all);
        match retrieve(&manifest, &[forger]) {
            Err(RetrievalError::Unavailable { gathered, need }) => {
                assert_eq!(
                    gathered, 0,
                    "por_refuses_substitution violated: a substituted chunk counted"
                );
                assert_eq!(need, manifest.n_data);
            }
            other => panic!("all-substituted provider must be Unavailable, got {other:?}"),
        }
    }

    /// NEGATIVE pole, wrong-position — `por_refuses_substitution` where the
    /// substituted object is the genuine committed object of a *different*
    /// position: a provider answering every challenge `i` with the committed
    /// object of position `i+1` (claiming position `i`) passes nothing.
    #[test]
    fn lean_por_refuses_substitution_wrong_position_openings_never_count() {
        let data: Vec<u8> = (0..300usize)
            .map(|i| (i.wrapping_mul(13) % 251) as u8)
            .collect();
        let (manifest, chunks) = encode_bytes_for_availability(&data, 16, 2);
        let rotated: Vec<ErasureChunk> = (0..chunks.len())
            .map(|i| {
                let j = (i + 1) % chunks.len();
                let mut c = chunks[j].clone();
                c.index = i;
                c.proof = chunks[i].proof.clone(); // claim position i
                // Genuine substitution: the committed objects differ.
                assert_ne!(c.commitment, chunks[i].commitment);
                c
            })
            .collect();
        let forger = InMemorySource::from_chunks(rotated);
        match retrieve(&manifest, &[forger]) {
            Err(RetrievalError::Unavailable { gathered, .. }) => {
                assert_eq!(
                    gathered, 0,
                    "por_refuses_substitution violated: a wrong-position opening counted"
                );
            }
            other => panic!("wrong-position provider must be Unavailable, got {other:?}"),
        }
    }

    /// The sampler counts EXACTLY the committed openings — both poles at once.
    /// Sampling every index against a peer holding a strict genuine subset:
    /// `found == |subset|` — every committed chunk served opens (`por_sound`)
    /// and nothing else counts (`por_refuses_substitution`).
    #[test]
    fn lean_por_sound_das_found_count_is_exactly_the_committed_openings() {
        let data: Vec<u8> = (0..400usize)
            .map(|i| (i.wrapping_mul(29) % 251) as u8)
            .collect();
        let (manifest, chunks) = encode_bytes_for_availability(&data, 16, 2);
        let keep = manifest.n_total / 3;
        let kept: Vec<ErasureChunk> = chunks.into_iter().take(keep).collect();
        let source = InMemorySource::from_chunks(kept);
        let verdict = sample_das(&manifest, &[source], manifest.n_total, 0x1EAF);
        assert_eq!(verdict.sampled, manifest.n_total);
        assert_eq!(
            verdict.found, keep,
            "found-count must equal the committed openings served: {verdict:?}"
        );
    }

    /// NEGATIVE pole at the DAS loop — `por_refuses_substitution`: a peer
    /// serving substituted versions of ALL chunks contributes NOTHING to the
    /// found-count; confidence collapses to zero. `found > 0` here would mean
    /// a substituted opening verified: RED.
    #[test]
    fn lean_por_refuses_substitution_das_counts_no_substituted_chunk() {
        let data: Vec<u8> = (0..400usize)
            .map(|i| (i.wrapping_mul(17) % 251) as u8)
            .collect();
        let (manifest, chunks) = encode_bytes_for_availability(&data, 16, 2);
        let forged_all: Vec<ErasureChunk> = chunks
            .iter()
            .map(|c| {
                let mut f = c.clone();
                f.data[0] ^= 0x3C;
                f.commitment = erasure::chunk_commitment_dual(&f.data).blake3;
                f
            })
            .collect();
        let forger = InMemorySource::from_chunks(forged_all);
        let verdict = sample_das(&manifest, &[forger], manifest.n_total, 0xF0E5);
        assert_eq!(
            verdict.found, 0,
            "por_refuses_substitution violated at the DAS loop: {verdict:?}"
        );
        assert_eq!(verdict.confidence, 0.0);
    }

    // ── Stage 3: the live DAS sampling loop ──────────────────────────────────

    #[test]
    fn das_full_availability_high_confidence() {
        let data = (0..400u32).map(|i| (i % 251) as u8).collect::<Vec<u8>>();
        let (manifest, chunks) = encode_bytes_for_availability(&data, 16, 2);
        let source = InMemorySource::from_chunks(chunks);
        let verdict = sample_das(&manifest, &[source], manifest.n_total.min(8), 0xDA5);
        assert_eq!(
            verdict.found, verdict.sampled,
            "every sampled chunk present"
        );
        assert!(
            verdict.is_available(0.99),
            "full availability ⇒ high confidence: {verdict:?}"
        );
    }

    // ── HTTP light-client adapter (multi-node stitch over the serving routes) ─

    use std::collections::HashMap;
    use std::sync::Mutex;

    /// A fake HTTP backend: chunk URL → JSON body. A node "withholds" a chunk by
    /// not holding its URL; records every URL fetched (to assert multi-peer).
    struct FakeNet {
        bodies: HashMap<String, Vec<u8>>,
        hits: Mutex<Vec<String>>,
    }
    impl FakeNet {
        fn fetch(&self, url: &str) -> Result<Vec<u8>, String> {
            self.hits.lock().unwrap().push(url.to_string());
            Ok(self.bodies.get(url).cloned().unwrap_or_default())
        }
    }
    fn chunk_url(base: &str, content_hash: &crate::ContentHash, index: usize) -> String {
        let hex: String = content_hash.0.iter().map(|b| format!("{b:02x}")).collect();
        format!("{base}/chunk/{hex}/{index}")
    }

    /// **THE LIGHT-CLIENT DA HEADLINE (HTTP).** A client holding a verified
    /// manifest RETRIEVES the bytes over HTTP from TWO nodes that each hold only
    /// a disjoint half of the chunks — so neither alone can serve it and k-of-n
    /// MUST stitch across both.
    #[test]
    fn retrieve_via_http_stitches_across_two_nodes() {
        let data =
            b"retrieve the bytes behind a verified commitment across two http nodes".to_vec();
        let (manifest, chunks) = encode_bytes_for_availability(&data, 16, 2);
        let mut bodies = HashMap::new();
        for chunk in &chunks {
            let base = if chunk.index % 2 == 0 {
                "http://node-a/storage"
            } else {
                "http://node-b/storage"
            };
            bodies.insert(
                chunk_url(base, &manifest.content_hash, chunk.index),
                serde_json::to_vec(chunk).unwrap(),
            );
        }
        let net = FakeNet {
            bodies,
            hits: Mutex::new(Vec::new()),
        };
        let bases = vec![
            "http://node-a/storage".into(),
            "http://node-b/storage".into(),
        ];
        let fetch = |u: &str| net.fetch(u);
        let recovered = retrieve_via_http(&manifest, &bases, &fetch).expect("k-of-n across nodes");
        assert_eq!(recovered, data);
        let hits = net.hits.lock().unwrap();
        assert!(hits.iter().any(|u| u.contains("node-a")));
        assert!(hits.iter().any(|u| u.contains("node-b")));
    }

    /// One node withholds everything; the honest node serves k-of-n. The
    /// withholder cannot block retrieval.
    #[test]
    fn retrieve_via_http_survives_a_withholding_node() {
        let data = b"one withholding http node cannot break light-client retrieval here".to_vec();
        let (manifest, chunks) = encode_bytes_for_availability(&data, 16, 2);
        let mut bodies = HashMap::new();
        for chunk in &chunks {
            bodies.insert(
                chunk_url("http://node-b/storage", &manifest.content_hash, chunk.index),
                serde_json::to_vec(chunk).unwrap(),
            );
        }
        let net = FakeNet {
            bodies,
            hits: Mutex::new(Vec::new()),
        };
        // node-a (the withholder) listed FIRST: every index asks it first.
        let bases = vec![
            "http://node-a/storage".into(),
            "http://node-b/storage".into(),
        ];
        let fetch = |u: &str| net.fetch(u);
        let recovered = retrieve_via_http(&manifest, &bases, &fetch).expect("honest node serves");
        assert_eq!(recovered, data);
    }

    /// A node serving a FORGED chunk over HTTP is rejected by its Merkle proof;
    /// the honest node's k-of-n still reconstructs.
    #[test]
    fn retrieve_via_http_rejects_a_forging_node() {
        let data =
            b"a forging http node cannot poison retrieval: the merkle root catches it".to_vec();
        let (manifest, chunks) = encode_bytes_for_availability(&data, 16, 2);
        let mut forged = chunks[0].clone();
        forged.data[0] ^= 0xFF;
        forged.commitment = erasure::chunk_commitment_dual(&forged.data).blake3;
        let mut bodies = HashMap::new();
        bodies.insert(
            chunk_url("http://node-a/storage", &manifest.content_hash, 0),
            serde_json::to_vec(&forged).unwrap(),
        );
        for chunk in &chunks {
            bodies.insert(
                chunk_url("http://node-b/storage", &manifest.content_hash, chunk.index),
                serde_json::to_vec(chunk).unwrap(),
            );
        }
        let net = FakeNet {
            bodies,
            hits: Mutex::new(Vec::new()),
        };
        let bases = vec![
            "http://node-a/storage".into(),
            "http://node-b/storage".into(),
        ];
        let fetch = |u: &str| net.fetch(u);
        let recovered = retrieve_via_http(&manifest, &bases, &fetch)
            .expect("forged chunk skipped, honest k-of-n wins");
        assert_eq!(recovered, data);
    }

    #[test]
    fn das_withheld_data_low_confidence() {
        // A peer set holding fewer than half the chunks: sampling finds gaps and
        // confidence stays low — the light client refuses to trust the root as
        // available.
        let data = (0..400u32).map(|i| (i % 251) as u8).collect::<Vec<u8>>();
        let (manifest, chunks) = encode_bytes_for_availability(&data, 16, 2);
        // Hold only a small minority of chunks.
        let kept: Vec<ErasureChunk> = chunks.into_iter().take(manifest.n_total / 4).collect();
        let source = InMemorySource::from_chunks(kept);
        let verdict = sample_das(&manifest, &[source], manifest.n_total, 0xBEEF);
        assert!(verdict.found < verdict.sampled, "gaps observed");
        assert!(
            !verdict.is_available(0.99),
            "withheld data ⇒ low confidence: {verdict:?}"
        );
    }
}
