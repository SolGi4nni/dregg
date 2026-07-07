//! Content-addressed blob store (nameless writes).
//!
//! Write returns hash. No allocation, no indirection.
//! Each write has a computron cost (proportional to size).
//! Each stored blob has an OWNER (quota cell that paid for it).
//! Deletion refunds a portion of the computron cost.
//!
//! # Lean-spec status
//!
//! No Lean theorem specifies `ContentStore` yet.
//! `metatheory/Dregg2/Storage/BucketCommitment.lean::read_sound` proves the
//! trustless read for the COMMITTED bucket store
//! ([`crate::bucket_commitment`] — an opening verified against a published
//! Poseidon2 content root); this module is a local, unilateral BLAKE3 blob
//! store with no openings to verify, so that theorem does not apply here
//! and is not claimed. The store's executable contract — deterministic,
//! collision-sensitive content addressing; read-integrity (a read returns
//! the exact preimage of the requested hash); owner-gated splice/delete —
//! is pinned by the `prop_*` tests below, ready to bind when a Lean spec
//! for the local store lands.

use std::collections::HashMap;

use crate::quota::SpaceBank;
use crate::{ComputronRefund, ContentHash, QuotaId, StorageError};

/// Metadata about a stored blob.
#[derive(Debug, Clone)]
struct BlobMeta {
    /// The quota cell that paid for this blob.
    owner: QuotaId,
    /// Size in bytes.
    size: u64,
    /// Original write cost (computrons charged).
    write_cost: u64,
    /// Reference count (for deduplication — same content, multiple owners).
    ref_count: u32,
}

/// Content-addressed store. Nameless writes: data in, hash out.
#[derive(Debug)]
pub struct ContentStore {
    /// Blob data keyed by content hash.
    blobs: HashMap<ContentHash, Vec<u8>>,
    /// Metadata keyed by content hash.
    meta: HashMap<ContentHash, BlobMeta>,
    /// The space bank governing quota.
    pub bank: SpaceBank,
}

impl ContentStore {
    /// Create a new content store with the given space bank.
    pub fn new(bank: SpaceBank) -> Self {
        Self {
            blobs: HashMap::new(),
            meta: HashMap::new(),
            bank,
        }
    }

    /// Hash data using blake3.
    fn hash(data: &[u8]) -> ContentHash {
        let h = blake3::hash(data);
        ContentHash(*h.as_bytes())
    }

    /// Write data to the store. Returns the content hash.
    /// The payer's quota is charged for the write.
    pub fn write(&mut self, data: &[u8], payer: &QuotaId) -> Result<ContentHash, StorageError> {
        let hash = Self::hash(data);
        let size = data.len() as u64;

        // If content already exists, handle deduplication.
        if let Some(meta) = self.meta.get_mut(&hash) {
            meta.ref_count += 1;
            // Still charge the payer (they're claiming storage under their quota).
            self.bank.charge_write(payer, size)?;
            return Ok(hash);
        }

        // Charge the payer.
        let cost = self.bank.charge_write(payer, size)?;

        // Store the data.
        self.blobs.insert(hash, data.to_vec());
        self.meta.insert(
            hash,
            BlobMeta {
                owner: *payer,
                size,
                write_cost: cost,
                ref_count: 1,
            },
        );

        Ok(hash)
    }

    /// Read data by content hash.
    pub fn read(&self, hash: &ContentHash) -> Option<&[u8]> {
        self.blobs.get(hash).map(|v| v.as_slice())
    }

    /// Splice: replace a subrange of an existing blob, producing a new blob.
    /// This is delete(old) + write(new) atomically.
    pub fn splice(
        &mut self,
        old_hash: &ContentHash,
        offset: usize,
        new_data: &[u8],
        payer: &QuotaId,
    ) -> Result<ContentHash, StorageError> {
        // Read old data.
        let old_data = self
            .blobs
            .get(old_hash)
            .ok_or(StorageError::NotFound(*old_hash))?
            .clone();

        // Verify ownership.
        let old_meta = self
            .meta
            .get(old_hash)
            .ok_or(StorageError::NotFound(*old_hash))?;
        if old_meta.owner != *payer {
            return Err(StorageError::NotOwner {
                hash: *old_hash,
                owner: old_meta.owner,
                caller: *payer,
            });
        }

        // Construct new data: old[..offset] + new_data + old[offset+new_data.len()..]
        let end = (offset + new_data.len()).min(old_data.len());
        let mut spliced = Vec::with_capacity(old_data.len());
        spliced.extend_from_slice(&old_data[..offset.min(old_data.len())]);
        spliced.extend_from_slice(new_data);
        if end < old_data.len() {
            spliced.extend_from_slice(&old_data[end..]);
        }

        // Delete old (with refund).
        self.delete(old_hash, payer)?;

        // Write new.
        self.write(&spliced, payer)
    }

    /// Delete a blob. Only the owner can delete. Returns a computron refund.
    pub fn delete(
        &mut self,
        hash: &ContentHash,
        owner: &QuotaId,
    ) -> Result<ComputronRefund, StorageError> {
        let meta = self
            .meta
            .get(hash)
            .ok_or(StorageError::NotFound(*hash))?
            .clone();

        if meta.owner != *owner {
            return Err(StorageError::NotOwner {
                hash: *hash,
                owner: meta.owner,
                caller: *owner,
            });
        }

        // Remove from store.
        if meta.ref_count <= 1 {
            self.blobs.remove(hash);
            self.meta.remove(hash);
        } else {
            if let Some(m) = self.meta.get_mut(hash) {
                m.ref_count -= 1;
            }
        }

        // Process refund through the bank.
        self.bank.process_refund(owner, meta.write_cost, meta.size)
    }

    /// Check if a blob exists.
    pub fn contains(&self, hash: &ContentHash) -> bool {
        self.blobs.contains_key(hash)
    }

    /// Get the size of a blob.
    pub fn blob_size(&self, hash: &ContentHash) -> Option<u64> {
        self.meta.get(hash).map(|m| m.size)
    }

    /// Total bytes stored in this content store.
    pub fn total_bytes(&self) -> u64 {
        self.meta.values().map(|m| m.size).sum()
    }

    /// Number of blobs stored.
    pub fn blob_count(&self) -> usize {
        self.blobs.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A store with two funded quota cells (alice, bob).
    fn store_with_two_cells() -> (ContentStore, QuotaId, QuotaId) {
        let mut bank = SpaceBank::new(1, 1, 0.5);
        let alice = bank.allocate_quota([0xA1; 32], 1_000_000, None);
        let bob = bank.allocate_quota([0xB0; 32], 1_000_000, None);
        (ContentStore::new(bank), alice, bob)
    }

    /// Content addressing is deterministic (same bytes → same address,
    /// across writes, across store instances, and equal to the raw BLAKE3
    /// of the data) and collision-sensitive (negative pole: every
    /// single-byte mutation of the data yields a DIFFERENT address).
    #[test]
    fn prop_content_addressing_deterministic_and_collision_sensitive() {
        let (mut s1, a1, _) = store_with_two_cells();
        let (mut s2, a2, _) = store_with_two_cells();
        let base: Vec<u8> = (0u8..32).collect();
        let h1 = s1.write(&base, &a1).unwrap();
        let h2 = s2.write(&base, &a2).unwrap();
        assert_eq!(
            h1, h2,
            "same bytes must address identically across instances"
        );
        assert_eq!(
            h1.0,
            *blake3::hash(&base).as_bytes(),
            "the content address must be the raw BLAKE3 of the data"
        );
        assert_eq!(
            s1.write(&base, &a1).unwrap(),
            h1,
            "a re-write of the same bytes must dedup to the same address"
        );
        for i in 0..base.len() {
            let mut mutated = base.clone();
            mutated[i] ^= 1;
            let hm = s1.write(&mutated, &a1).unwrap();
            assert_ne!(hm, h1, "byte {i} mutation must change the content address");
        }
    }

    /// Read integrity: `read(h)` returns EXACTLY the written bytes, whose
    /// BLAKE3 is `h` (the local analog of a sound read). Negative pole: a
    /// forged address — any single-byte perturbation of a genuine hash —
    /// reads as absent; the store never serves other content for it.
    #[test]
    fn prop_read_returns_the_preimage_and_forged_addresses_are_absent() {
        let (mut s, alice, _) = store_with_two_cells();
        let blobs: Vec<Vec<u8>> = vec![
            b"alpha".to_vec(),
            b"beta-beta".to_vec(),
            (0u8..64).collect(),
        ];
        let mut hashes = Vec::new();
        for blob in &blobs {
            hashes.push(s.write(blob, &alice).unwrap());
        }
        for (blob, h) in blobs.iter().zip(&hashes) {
            let served = s.read(h).expect("stored blob must read back");
            assert_eq!(
                served,
                &blob[..],
                "read must return the exact written bytes"
            );
            assert_eq!(
                *blake3::hash(served).as_bytes(),
                h.0,
                "the served bytes must be the preimage of the requested address"
            );
        }
        for h in &hashes {
            for i in 0..32 {
                let mut forged = h.0;
                forged[i] ^= 1;
                let fh = ContentHash(forged);
                assert!(
                    s.read(&fh).is_none(),
                    "forged address (byte {i}) must read as absent"
                );
                assert!(!s.contains(&fh), "forged address (byte {i}) must not exist");
            }
        }
    }

    /// Splice preserves content addressing: the returned hash is the
    /// BLAKE3 of the spliced bytes, the new content reads back exactly,
    /// and the old address no longer resolves (ref_count was 1).
    /// Negative pole: a non-owner splice is refused with `NotOwner` and
    /// leaves the original blob intact.
    #[test]
    fn prop_splice_rehashes_result_and_is_owner_gated() {
        let (mut s, alice, bob) = store_with_two_cells();
        let old = b"hello cruel world".to_vec();
        let h_old = s.write(&old, &alice).unwrap();

        // Negative pole: bob may not splice alice's blob.
        let refused = s.splice(&h_old, 6, b"kind!", &bob);
        assert!(
            matches!(refused, Err(StorageError::NotOwner { .. })),
            "non-owner splice must be refused with NotOwner, got {refused:?}"
        );
        assert_eq!(
            s.read(&h_old).unwrap(),
            &old[..],
            "a refused splice must leave the blob intact"
        );

        // Positive pole: alice splices; result is re-addressed by content.
        let h_new = s.splice(&h_old, 6, b"kind!", &alice).unwrap();
        let expected = b"hello kind! world".to_vec();
        assert_eq!(
            h_new.0,
            *blake3::hash(&expected).as_bytes(),
            "the spliced blob's address must be the BLAKE3 of the spliced bytes"
        );
        assert_eq!(s.read(&h_new).unwrap(), &expected[..]);
        assert!(
            !s.contains(&h_old),
            "the old address (ref_count 1) must be gone after splice"
        );
    }

    /// Owner-gated delete with dedup conservation: a non-owner delete is
    /// refused (`NotOwner`) and the blob stays readable — including for a
    /// deduplicating second writer, who does NOT gain delete rights
    /// (ownership stays with the first writer). The owner must then
    /// delete once per reference before the blob disappears.
    #[test]
    fn prop_delete_is_owner_gated_and_refcount_conserving() {
        let (mut s, alice, bob) = store_with_two_cells();
        let data = b"shared content".to_vec();
        let h = s.write(&data, &alice).unwrap();

        // bob dedup-writes the same content: same address, no ownership.
        assert_eq!(s.write(&data, &bob).unwrap(), h);
        let refused = s.delete(&h, &bob);
        assert!(
            matches!(refused, Err(StorageError::NotOwner { .. })),
            "dedup writer must not gain delete rights, got {refused:?}"
        );
        assert_eq!(
            s.read(&h).unwrap(),
            &data[..],
            "a refused delete must leave the blob intact"
        );

        // Owner deletes: first delete drops one reference, blob survives.
        s.delete(&h, &alice).unwrap();
        assert!(
            s.contains(&h),
            "with ref_count 2, one delete must conserve the blob"
        );
        // Second delete removes the last reference.
        s.delete(&h, &alice).unwrap();
        assert!(!s.contains(&h), "the last delete must remove the blob");
        assert!(s.read(&h).is_none());
    }
}
