//! Chunking for committee payloads that outgrow one sealed envelope.
//!
//! # The cap that actually binds
//!
//! Two limits sit on a committee message, and the smaller one is not the one
//! people quote. The TCP frame is capped at
//! [`super::relying_party::MAX_MESSAGE_BYTES`] (16 MiB), but the frame carries a
//! SEALED envelope, and the envelope's own plaintext ceiling is
//! [`crate::mpc_party::transport::MAX_NATIVE_PQ_AUXILIARY_BYTES`] — **8 MiB**.
//! That is the real wall.
//!
//! The commit-response body is the payload that reaches it. Per dealer it
//! carries `n` Pedersen row-commitment vectors (`n * moduli * degree * 32`
//! bytes) plus `t*t` RNS linear images, and the whole response carries one such
//! commitment per dealer, so it grows as `O(n^2 * degree)`. At `n = 3`,
//! `t = 2`, degree 4096 that is already ~7-8 MiB against an 8 MiB ceiling.
//! A fourth party, or degree 8192, does not fit — and the failure mode is a
//! refusal at seal time with the ceremony dead, not a graceful degradation.
//!
//! # What this module guarantees, stated narrowly
//!
//! **Exact reassembly, or a refusal.** The bytes a reassembler yields are
//! byte-identical to the bytes the sender chunked, or it returns an error and
//! yields nothing. That is proved by a digest over the whole payload carried in
//! every chunk and recomputed over the reassembly before it is handed back — so
//! a dropped, duplicated, resized, reordered-with-swapped-content, or truncated
//! chunk stream cannot produce a payload at all.
//!
//! **What it does NOT claim.** It is not an authenticity layer. Chunks travel
//! inside the committee's sealed, route-bound, dually-signed envelopes, and
//! that is what makes a chunk unforgeable and unattributable-to-the-wrong-party;
//! in-flight tampering fails the AEAD before a chunk is ever parsed here. The
//! stream digest is computed by the sender, so it binds a sender to its own
//! bytes — it does not make a lying sender honest. Whether the reassembled
//! payload is a TRUE statement is the job of the layer above (the VSS
//! commitment openings and the aggregate-row binding proofs), exactly as it was
//! when the payload fit in one envelope.

use sha2::{Digest, Sha256};

/// Payload bytes per chunk.
///
/// Half the 8 MiB envelope ceiling, so a chunk plus its 96-byte header plus the
/// envelope's own trailer (KEM ciphertext, nonce, AEAD tag, two signatures) has
/// room to spare. Raising this toward the ceiling buys round-trips and spends
/// the margin that keeps a header change from silently overflowing.
pub const CHUNK_PAYLOAD_BYTES: usize = 4 * 1024 * 1024;

/// A generous ceiling on chunk count, so a malformed header cannot make a
/// receiver reserve unbounded state. 4096 chunks is 16 GiB of payload.
const MAX_CHUNKS: usize = 4096;

const CHUNK_MAGIC: &[u8; 8] = b"FHCKv001";
const STREAM_DIGEST_DOMAIN: &[u8] = b"fhegg/threshold/chunked-stream/v1";
const HEADER_BYTES: usize = 8 + 32 + 32 + 8 + 8 + 8 + 8;

/// Fail-closed refusals from chunk reassembly.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ChunkError {
    /// Wrong magic, a truncated header, or trailing bytes.
    Malformed(&'static str),
    /// The chunk belongs to a different MESSAGE KIND than the reassembler was
    /// opened for (a commit-response chunk offered to a finalize reassembler).
    DomainMismatch,
    /// The chunk belongs to a different STREAM than the ones already accepted —
    /// its digest, total length, or chunk count disagrees. This is the
    /// two-payloads-spliced-together refusal.
    StreamMismatch,
    /// A chunk index at or past the declared count.
    IndexOutOfRange { index: usize, count: usize },
    /// The same index offered twice.
    DuplicateChunk { index: usize },
    /// A chunk whose length is not the one its position requires. Every chunk
    /// but the last is exactly [`CHUNK_PAYLOAD_BYTES`]; the last is the
    /// remainder. A resized chunk cannot shift the payload silently.
    WrongChunkLength {
        index: usize,
        found: usize,
        expected: usize,
    },
    /// The declared chunk count is zero or beyond the allowed ceiling.
    ImplausibleCount { count: usize },
    /// EVERY chunk arrived and the reassembled bytes still do not hash to the
    /// digest the stream declared. Reassembly was not exact; nothing is yielded.
    ReassemblyDigestMismatch,
}

impl std::fmt::Display for ChunkError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Malformed(what) => write!(f, "chunk is malformed: {what}"),
            Self::DomainMismatch => write!(f, "chunk belongs to a different message kind"),
            Self::StreamMismatch => write!(f, "chunk belongs to a different payload stream"),
            Self::IndexOutOfRange { index, count } => {
                write!(f, "chunk index {index} is past the declared count {count}")
            }
            Self::DuplicateChunk { index } => write!(f, "chunk {index} was offered twice"),
            Self::WrongChunkLength {
                index,
                found,
                expected,
            } => write!(
                f,
                "chunk {index} carries {found} bytes where its position requires {expected}"
            ),
            Self::ImplausibleCount { count } => write!(f, "implausible chunk count {count}"),
            Self::ReassemblyDigestMismatch => write!(
                f,
                "the reassembled payload does not match the digest every chunk declared"
            ),
        }
    }
}

impl std::error::Error for ChunkError {}

fn stream_digest(domain: &[u8; 32], payload: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(STREAM_DIGEST_DOMAIN);
    hasher.update(domain);
    hasher.update((payload.len() as u64).to_le_bytes());
    hasher.update(payload);
    hasher.finalize().into()
}

/// Domain-separate a message kind, so a chunk of one kind can never reassemble
/// as another even if both streams are the same length.
pub fn chunk_domain(label: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"fhegg/threshold/chunk-domain/v1");
    hasher.update((label.len() as u64).to_le_bytes());
    hasher.update(label);
    hasher.finalize().into()
}

fn chunk_count(total_len: usize) -> usize {
    // An empty payload is ONE empty chunk, never zero: a stream with no chunks
    // has nothing to carry its digest, so a receiver could not tell "empty" from
    // "nothing arrived".
    total_len.div_ceil(CHUNK_PAYLOAD_BYTES).max(1)
}

fn expected_chunk_len(index: usize, total_len: usize, count: usize) -> usize {
    if index + 1 < count {
        CHUNK_PAYLOAD_BYTES
    } else {
        total_len - index * CHUNK_PAYLOAD_BYTES
    }
}

/// SENDER: one payload, split into envelope-sized chunks.
///
/// Hold this for as long as the peer may still ask for a chunk; every chunk it
/// emits carries the same stream digest, so a receiver can tell a re-request
/// apart from a different payload.
pub struct ChunkStream {
    domain: [u8; 32],
    digest: [u8; 32],
    payload: Vec<u8>,
}

impl ChunkStream {
    pub fn new(domain: [u8; 32], payload: Vec<u8>) -> Self {
        let digest = stream_digest(&domain, &payload);
        Self {
            domain,
            digest,
            payload,
        }
    }

    pub fn count(&self) -> usize {
        chunk_count(self.payload.len())
    }

    pub fn total_len(&self) -> usize {
        self.payload.len()
    }

    pub fn digest(&self) -> [u8; 32] {
        self.digest
    }

    /// The encoded chunk at `index`, ready to be sealed. `None` past the end.
    pub fn chunk(&self, index: usize) -> Option<Vec<u8>> {
        let count = self.count();
        if index >= count {
            return None;
        }
        let start = index * CHUNK_PAYLOAD_BYTES;
        let end = (start + CHUNK_PAYLOAD_BYTES).min(self.payload.len());
        let body = &self.payload[start..end];

        let mut out = Vec::with_capacity(HEADER_BYTES + body.len());
        out.extend_from_slice(CHUNK_MAGIC);
        out.extend_from_slice(&self.domain);
        out.extend_from_slice(&self.digest);
        out.extend_from_slice(&(self.payload.len() as u64).to_le_bytes());
        out.extend_from_slice(&(count as u64).to_le_bytes());
        out.extend_from_slice(&(index as u64).to_le_bytes());
        out.extend_from_slice(&(body.len() as u64).to_le_bytes());
        out.extend_from_slice(body);
        Some(out)
    }
}

struct StreamShape {
    digest: [u8; 32],
    total_len: usize,
    count: usize,
}

/// RECEIVER: accumulate chunks until the payload is exactly reassembled.
///
/// Yields `Some(payload)` exactly once, on the chunk that completes the stream
/// AND only if the reassembly hashes to the declared digest. Every other
/// outcome is `None` (still incomplete) or an error.
pub struct ChunkReassembler {
    domain: [u8; 32],
    shape: Option<StreamShape>,
    slots: Vec<Option<Vec<u8>>>,
    have: usize,
}

impl ChunkReassembler {
    pub fn new(domain: [u8; 32]) -> Self {
        Self {
            domain,
            shape: None,
            slots: Vec::new(),
            have: 0,
        }
    }

    /// How many chunks this stream declared, once the first one has arrived.
    pub fn expected_count(&self) -> Option<usize> {
        self.shape.as_ref().map(|shape| shape.count)
    }

    /// Chunks still outstanding, once the first one has arrived.
    pub fn missing(&self) -> Option<usize> {
        self.shape.as_ref().map(|shape| shape.count - self.have)
    }

    pub fn accept(&mut self, bytes: &[u8]) -> Result<Option<Vec<u8>>, ChunkError> {
        if bytes.len() < HEADER_BYTES || &bytes[..8] != CHUNK_MAGIC.as_slice() {
            return Err(ChunkError::Malformed("header"));
        }
        let read = |at: usize| -> usize {
            u64::from_le_bytes(bytes[at..at + 8].try_into().expect("checked length")) as usize
        };
        if bytes[8..40] != self.domain {
            return Err(ChunkError::DomainMismatch);
        }
        let digest: [u8; 32] = bytes[40..72].try_into().expect("checked length");
        let total_len = read(72);
        let count = read(80);
        let index = read(88);
        let body_len = read(96);

        if count == 0 || count > MAX_CHUNKS {
            return Err(ChunkError::ImplausibleCount { count });
        }
        if bytes.len() != HEADER_BYTES + body_len {
            return Err(ChunkError::Malformed(
                "body length disagrees with the frame",
            ));
        }
        // The declared shape must be internally consistent BEFORE it is trusted
        // as this stream's shape, or a first chunk could name any geometry.
        if chunk_count(total_len) != count {
            return Err(ChunkError::Malformed(
                "chunk count is not the one this total length implies",
            ));
        }
        if index >= count {
            return Err(ChunkError::IndexOutOfRange { index, count });
        }
        let expected = expected_chunk_len(index, total_len, count);
        if body_len != expected {
            return Err(ChunkError::WrongChunkLength {
                index,
                found: body_len,
                expected,
            });
        }

        match &self.shape {
            None => {
                self.shape = Some(StreamShape {
                    digest,
                    total_len,
                    count,
                });
                self.slots = (0..count).map(|_| None).collect();
            }
            Some(shape) => {
                // Splicing a chunk of a DIFFERENT payload into this stream is
                // refused here rather than surfacing as a digest mismatch at the
                // end, so the caller learns which chunk was wrong.
                if shape.digest != digest || shape.total_len != total_len || shape.count != count {
                    return Err(ChunkError::StreamMismatch);
                }
            }
        }

        if self.slots[index].is_some() {
            return Err(ChunkError::DuplicateChunk { index });
        }
        self.slots[index] = Some(bytes[HEADER_BYTES..].to_vec());
        self.have += 1;

        let shape = self.shape.as_ref().expect("set above");
        if self.have < shape.count {
            return Ok(None);
        }

        let mut payload = Vec::with_capacity(shape.total_len);
        for slot in &self.slots {
            payload.extend_from_slice(slot.as_ref().expect("every slot filled"));
        }
        // THE EXACTNESS CHECK. Everything above pins the geometry; this pins the
        // CONTENT. If the bytes that came back are not the bytes that went in,
        // nothing is yielded.
        if payload.len() != shape.total_len || stream_digest(&self.domain, &payload) != shape.digest
        {
            return Err(ChunkError::ReassemblyDigestMismatch);
        }
        Ok(Some(payload))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn domain() -> [u8; 32] {
        chunk_domain(b"test/commit-response")
    }

    fn payload(len: usize) -> Vec<u8> {
        (0..len).map(|i| (i % 251) as u8).collect()
    }

    fn all_chunks(stream: &ChunkStream) -> Vec<Vec<u8>> {
        (0..stream.count())
            .map(|i| stream.chunk(i).expect("in range"))
            .collect()
    }

    fn reassemble(domain: [u8; 32], chunks: &[Vec<u8>]) -> Result<Option<Vec<u8>>, ChunkError> {
        let mut reassembler = ChunkReassembler::new(domain);
        let mut out = None;
        for chunk in chunks {
            if let Some(payload) = reassembler.accept(chunk)? {
                out = Some(payload);
            }
        }
        Ok(out)
    }

    #[test]
    fn reassembly_is_exact_across_sizes_and_orders() {
        for len in [
            0,
            1,
            CHUNK_PAYLOAD_BYTES - 1,
            CHUNK_PAYLOAD_BYTES,
            CHUNK_PAYLOAD_BYTES + 1,
            3 * CHUNK_PAYLOAD_BYTES + 12_345,
        ] {
            let original = payload(len);
            let stream = ChunkStream::new(domain(), original.clone());
            let chunks = all_chunks(&stream);
            assert_eq!(chunks.len(), len.div_ceil(CHUNK_PAYLOAD_BYTES).max(1));

            assert_eq!(
                reassemble(domain(), &chunks).expect("in-order reassembly"),
                Some(original.clone()),
                "in-order reassembly was not exact at len {len}"
            );

            // Arrival ORDER is not part of the guarantee: each chunk names its
            // own index, so a shuffled delivery must reassemble identically.
            let mut shuffled = chunks.clone();
            shuffled.reverse();
            assert_eq!(
                reassemble(domain(), &shuffled).expect("reverse-order reassembly"),
                Some(original),
                "reverse-order reassembly was not exact at len {len}"
            );
        }
    }

    #[test]
    fn a_dropped_chunk_never_yields_a_payload() {
        let original = payload(3 * CHUNK_PAYLOAD_BYTES + 99);
        let stream = ChunkStream::new(domain(), original);
        let chunks = all_chunks(&stream);
        assert!(chunks.len() >= 4);

        for dropped in 0..chunks.len() {
            let kept: Vec<Vec<u8>> = chunks
                .iter()
                .enumerate()
                .filter(|(i, _)| *i != dropped)
                .map(|(_, c)| c.clone())
                .collect();
            assert_eq!(kept.len(), chunks.len() - 1, "the drop was a no-op");
            assert_eq!(
                reassemble(domain(), &kept).expect("no error, just incomplete"),
                None,
                "dropping chunk {dropped} still produced a payload"
            );
        }
    }

    #[test]
    fn a_duplicated_chunk_is_refused_rather_than_standing_in_for_a_missing_one() {
        let stream = ChunkStream::new(domain(), payload(2 * CHUNK_PAYLOAD_BYTES + 7));
        let chunks = all_chunks(&stream);
        let mut spliced = vec![chunks[0].clone(), chunks[1].clone(), chunks[0].clone()];
        spliced.truncate(3);
        assert_eq!(
            reassemble(domain(), &spliced),
            Err(ChunkError::DuplicateChunk { index: 0 })
        );
    }

    #[test]
    fn a_tampered_chunk_body_is_refused_by_the_reassembly_digest() {
        let stream = ChunkStream::new(domain(), payload(2 * CHUNK_PAYLOAD_BYTES + 7));
        let mut chunks = all_chunks(&stream);

        let before = chunks[1].clone();
        let at = HEADER_BYTES + 4096;
        chunks[1][at] ^= 0xff;
        assert_ne!(
            before, chunks[1],
            "the mutation did not change the chunk; the refusal below would be vacuous"
        );

        assert_eq!(
            reassemble(domain(), &chunks),
            Err(ChunkError::ReassemblyDigestMismatch),
            "a tampered chunk body reassembled into a payload"
        );
    }

    #[test]
    fn a_chunk_carrying_another_chunks_content_under_this_index_is_refused() {
        // The sharp case: not a dropped or extra chunk, but chunk 1's body
        // relabelled as chunk 0. Every count and length still lines up; only the
        // CONTENT is in the wrong place.
        let stream = ChunkStream::new(domain(), payload(2 * CHUNK_PAYLOAD_BYTES));
        let chunks = all_chunks(&stream);

        let mut forged = chunks[0].clone();
        forged[HEADER_BYTES..].copy_from_slice(&chunks[1][HEADER_BYTES..]);
        assert_ne!(forged, chunks[0], "the swap was a no-op");

        assert_eq!(
            reassemble(domain(), &[forged, chunks[1].clone()]),
            Err(ChunkError::ReassemblyDigestMismatch),
            "a chunk carrying another chunk's content passed reassembly"
        );
    }

    #[test]
    fn chunks_of_two_different_payloads_cannot_be_spliced() {
        let a = ChunkStream::new(domain(), payload(2 * CHUNK_PAYLOAD_BYTES));
        let b = ChunkStream::new(domain(), payload(2 * CHUNK_PAYLOAD_BYTES + 1));
        assert_ne!(a.digest(), b.digest());
        assert_eq!(
            reassemble(
                domain(),
                &[
                    a.chunk(0).unwrap(),
                    b.chunk(1).unwrap(),
                    b.chunk(2).unwrap()
                ]
            ),
            Err(ChunkError::StreamMismatch)
        );
    }

    #[test]
    fn a_chunk_of_another_message_kind_is_refused() {
        let other = chunk_domain(b"test/finalize-request");
        assert_ne!(domain(), other);
        let stream = ChunkStream::new(other, payload(1024));
        assert_eq!(
            reassemble(domain(), &all_chunks(&stream)),
            Err(ChunkError::DomainMismatch)
        );
    }

    #[test]
    fn a_resized_or_relabelled_chunk_is_refused_before_any_reassembly() {
        let stream = ChunkStream::new(domain(), payload(2 * CHUNK_PAYLOAD_BYTES + 7));
        let chunks = all_chunks(&stream);

        // Truncating the body: the declared body length no longer matches the frame.
        let mut truncated = chunks[0].clone();
        truncated.truncate(truncated.len() - 1);
        assert_eq!(
            reassemble(domain(), &[truncated]),
            Err(ChunkError::Malformed(
                "body length disagrees with the frame"
            ))
        );

        // Relabelling the LAST chunk as a middle one: its length no longer
        // matches what that position requires.
        let mut relabelled = chunks[2].clone();
        relabelled[88..96].copy_from_slice(&0u64.to_le_bytes());
        assert!(matches!(
            reassemble(domain(), &[relabelled]),
            Err(ChunkError::WrongChunkLength { index: 0, .. })
        ));

        // An index past the declared count.
        let mut past_end = chunks[2].clone();
        past_end[88..96].copy_from_slice(&9u64.to_le_bytes());
        assert!(matches!(
            reassemble(domain(), &[past_end]),
            Err(ChunkError::IndexOutOfRange { index: 9, count: 3 })
        ));
    }

    #[test]
    fn a_stream_geometry_that_does_not_add_up_is_refused() {
        let stream = ChunkStream::new(domain(), payload(2 * CHUNK_PAYLOAD_BYTES + 7));
        let mut lying = stream.chunk(0).unwrap();
        // Claim a count that this total length does not imply.
        lying[80..88].copy_from_slice(&7u64.to_le_bytes());
        assert_eq!(
            reassemble(domain(), &[lying]),
            Err(ChunkError::Malformed(
                "chunk count is not the one this total length implies"
            ))
        );
    }
}
