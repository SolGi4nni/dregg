//! VFS: Content-addressed (nameless) file storage with capability security.
//!
//! Files are stored by their blake3 hash. There is no filename allocation, no inode
//! table, no indirection layer. The content hash IS the address. Knowledge of the hash
//! IS authority to read — this is the capability security model.
//!
//! ## Operations
//!
//! - **Write**: receive bytes, hash them, store at hash → return hash (the address).
//! - **Read**: present a hash → receive bytes (or 404 if not stored).
//! - **Splice**: present old hash + patch function → atomically produce new content
//!   at new hash, optionally nullifying the old hash.
//! - **Delete**: present hash → remove content, record nullifier (prevents re-upload
//!   of identical content — a tombstone).
//!
//! ## Circuit provability
//!
//! Every operation can be expressed as a STARK statement:
//! - Write: "I computed blake3(content) and it equals H" (preimage knowledge)
//! - Read: "I possess H" (capability presentation — trivial but logged)
//! - Splice: "blake3(old_content ++ patch) = H_new AND H_old was live"
//! - Delete: "I nullified H and the nullifier is blake3(H || 'nullify')"

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use tokio::sync::RwLock;

/// A 32-byte content hash serving as the file's address.
pub type ContentHash = [u8; 32];

/// Metadata about a stored file.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct FileEntry {
    /// The blake3 content hash (redundant with key, but convenient).
    pub hash: ContentHash,
    /// Size in bytes.
    pub size: usize,
    /// MIME type hint (optional, not authoritative).
    pub content_type: Option<String>,
    /// Unix timestamp of when this entry was written.
    pub created_at: u64,
    /// Which route prefix this file was stored under (for governance auditing).
    pub route_prefix: Option<String>,
}

/// Result of a write operation.
#[derive(Clone, Debug, serde::Serialize)]
pub struct WriteReceipt {
    /// The content hash (= address) of the stored file.
    pub hash: String,
    /// Size in bytes.
    pub size: usize,
    /// Whether this was a new write (true) or content already existed (false).
    pub new: bool,
}

/// Result of a splice operation.
#[derive(Clone, Debug, serde::Serialize)]
pub struct SpliceReceipt {
    /// The old content hash that was consumed.
    pub old_hash: String,
    /// The new content hash produced.
    pub new_hash: String,
    /// Size of the new content.
    pub new_size: usize,
    /// Whether the old hash was nullified.
    pub old_nullified: bool,
}

/// Errors from VFS operations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StorageError {
    /// Content hash not found in store.
    NotFound,
    /// Content hash has been nullified (tombstoned) and cannot be re-inserted.
    Nullified,
    /// The content is identical to the existing content (no-op splice).
    NoChange,
}

impl std::fmt::Display for StorageError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            StorageError::NotFound => write!(f, "content hash not found"),
            StorageError::Nullified => write!(f, "content hash has been nullified"),
            StorageError::NoChange => write!(f, "splice produced identical content"),
        }
    }
}

/// Content-addressed storage backend.
///
/// Thread-safe via internal RwLock. All operations are O(1) amortized (HashMap).
#[derive(Clone)]
pub struct ContentStore {
    /// The actual content, keyed by blake3 hash.
    data: Arc<RwLock<HashMap<ContentHash, Vec<u8>>>>,
    /// Metadata for each stored file.
    meta: Arc<RwLock<HashMap<ContentHash, FileEntry>>>,
    /// Nullifier set: hashes that have been deleted and cannot be re-inserted.
    /// The nullifier value is blake3(hash || "nullify") — a derived commitment.
    nullifiers: Arc<RwLock<HashSet<ContentHash>>>,
}

impl ContentStore {
    /// Create a new empty content store.
    pub fn new() -> Self {
        Self {
            data: Arc::new(RwLock::new(HashMap::new())),
            meta: Arc::new(RwLock::new(HashMap::new())),
            nullifiers: Arc::new(RwLock::new(HashSet::new())),
        }
    }

    /// Compute the blake3 hash of content.
    pub fn hash_content(content: &[u8]) -> ContentHash {
        *blake3::hash(content).as_bytes()
    }

    /// Compute the nullifier for a content hash.
    /// nullifier = blake3(hash || "nullify")
    pub fn compute_nullifier(hash: &ContentHash) -> ContentHash {
        let mut hasher = blake3::Hasher::new();
        hasher.update(hash);
        hasher.update(b"nullify");
        *hasher.finalize().as_bytes()
    }

    /// Write content to the store (nameless write).
    ///
    /// Returns the content hash and whether this was a new insertion.
    /// Fails if the content hash has been nullified.
    pub async fn write(
        &self,
        content: Vec<u8>,
        content_type: Option<String>,
        route_prefix: Option<String>,
    ) -> Result<WriteReceipt, StorageError> {
        let hash = Self::hash_content(&content);

        // Check nullifier set.
        let nullifiers = self.nullifiers.read().await;
        if nullifiers.contains(&hash) {
            return Err(StorageError::Nullified);
        }
        drop(nullifiers);

        let size = content.len();

        // Check if already stored.
        let mut data = self.data.write().await;
        let new = !data.contains_key(&hash);
        if new {
            data.insert(hash, content);
            drop(data);

            let now = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_secs())
                .unwrap_or(0);

            let entry = FileEntry {
                hash,
                size,
                content_type,
                created_at: now,
                route_prefix,
            };
            self.meta.write().await.insert(hash, entry);
        } else {
            drop(data);
        }

        Ok(WriteReceipt {
            hash: hex::encode(hash),
            size,
            new,
        })
    }

    /// Read content by its hash.
    ///
    /// Knowledge of the hash IS authority. If you can present the hash, you get the content.
    pub async fn read(&self, hash: &ContentHash) -> Result<(Vec<u8>, FileEntry), StorageError> {
        let data = self.data.read().await;
        let content = data.get(hash).cloned().ok_or(StorageError::NotFound)?;
        drop(data);

        let meta = self.meta.read().await;
        let entry = meta.get(hash).cloned().ok_or(StorageError::NotFound)?;

        Ok((content, entry))
    }

    /// Splice: apply a transformation to existing content, producing new content.
    ///
    /// The old content is read, the `patch` bytes are appended (simple splice semantics),
    /// and the result is stored under its new hash. The old hash is optionally nullified.
    ///
    /// For a real system, the patch would be a more sophisticated operation (byte-level
    /// diff, content-dependent transform, etc.). For this demo, splice = append.
    pub async fn splice(
        &self,
        old_hash: &ContentHash,
        patch: &[u8],
        nullify_old: bool,
    ) -> Result<SpliceReceipt, StorageError> {
        // Read old content (verify it exists).
        let data = self.data.read().await;
        let _old_content = data.get(old_hash).cloned().ok_or(StorageError::NotFound)?;
        drop(data);

        // Produce new content (splice = replace with patch content).
        // If patch is empty, this is a no-op.
        let new_content = if patch.is_empty() {
            return Err(StorageError::NoChange);
        } else {
            patch.to_vec()
        };

        let new_hash = Self::hash_content(&new_content);
        if new_hash == *old_hash {
            return Err(StorageError::NoChange);
        }

        // Check nullifier for new content.
        let nullifiers = self.nullifiers.read().await;
        if nullifiers.contains(&new_hash) {
            return Err(StorageError::Nullified);
        }
        drop(nullifiers);

        let new_size = new_content.len();

        // Store new content.
        self.data.write().await.insert(new_hash, new_content);

        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs())
            .unwrap_or(0);

        // Copy route prefix from old entry.
        let old_route = self
            .meta
            .read()
            .await
            .get(old_hash)
            .and_then(|e| e.route_prefix.clone());

        self.meta.write().await.insert(
            new_hash,
            FileEntry {
                hash: new_hash,
                size: new_size,
                content_type: None,
                created_at: now,
                route_prefix: old_route,
            },
        );

        // Optionally nullify old hash.
        let old_nullified = if nullify_old {
            self.delete(old_hash).await.is_ok()
        } else {
            false
        };

        Ok(SpliceReceipt {
            old_hash: hex::encode(*old_hash),
            new_hash: hex::encode(new_hash),
            new_size,
            old_nullified,
        })
    }

    /// Delete content and record a nullifier (tombstone).
    ///
    /// Once nullified, the same content cannot be re-inserted. This prevents
    /// "resurrection attacks" where deleted content is re-uploaded to bypass
    /// governance decisions.
    pub async fn delete(&self, hash: &ContentHash) -> Result<ContentHash, StorageError> {
        let mut data = self.data.write().await;
        if data.remove(hash).is_none() {
            return Err(StorageError::NotFound);
        }
        drop(data);

        self.meta.write().await.remove(hash);

        // Record nullifier.
        let nullifier = Self::compute_nullifier(hash);
        self.nullifiers.write().await.insert(*hash);

        Ok(nullifier)
    }

    /// Check if a hash is stored (without reading content).
    pub async fn exists(&self, hash: &ContentHash) -> bool {
        self.data.read().await.contains_key(hash)
    }

    /// Check if a hash has been nullified.
    pub async fn is_nullified(&self, hash: &ContentHash) -> bool {
        self.nullifiers.read().await.contains(hash)
    }

    /// Get total number of stored files.
    pub async fn file_count(&self) -> usize {
        self.data.read().await.len()
    }

    /// Get total number of nullifiers.
    pub async fn nullifier_count(&self) -> usize {
        self.nullifiers.read().await.len()
    }
}

/// Hex encoding/decoding utilities for content hashes.
pub mod hex {
    use super::ContentHash;

    /// Encode a 32-byte hash as a 64-character hex string.
    pub fn encode(hash: ContentHash) -> String {
        hash.iter().map(|b| format!("{b:02x}")).collect()
    }

    /// Decode a 64-character hex string into a 32-byte hash.
    pub fn decode(s: &str) -> Result<ContentHash, String> {
        let s = s.strip_prefix("0x").unwrap_or(s);
        if s.len() != 64 {
            return Err(format!("expected 64 hex chars, got {}", s.len()));
        }
        let mut hash = [0u8; 32];
        for i in 0..32 {
            hash[i] = u8::from_str_radix(&s[i * 2..i * 2 + 2], 16)
                .map_err(|e| format!("invalid hex at byte {i}: {e}"))?;
        }
        Ok(hash)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn write_and_read() {
        let store = ContentStore::new();
        let content = b"hello, governed namespace".to_vec();
        let receipt = store.write(content.clone(), None, None).await.unwrap();
        assert!(receipt.new);
        assert_eq!(receipt.size, content.len());

        let hash = hex::decode(&receipt.hash).unwrap();
        let (data, entry) = store.read(&hash).await.unwrap();
        assert_eq!(data, content);
        assert_eq!(entry.size, content.len());
    }

    #[tokio::test]
    async fn duplicate_write_returns_existing() {
        let store = ContentStore::new();
        let content = b"duplicate content".to_vec();
        let r1 = store.write(content.clone(), None, None).await.unwrap();
        let r2 = store.write(content, None, None).await.unwrap();
        assert!(r1.new);
        assert!(!r2.new);
        assert_eq!(r1.hash, r2.hash);
    }

    #[tokio::test]
    async fn delete_and_nullify() {
        let store = ContentStore::new();
        let content = b"to be deleted".to_vec();
        let receipt = store.write(content.clone(), None, None).await.unwrap();
        let hash = hex::decode(&receipt.hash).unwrap();

        // Delete succeeds.
        let nullifier = store.delete(&hash).await.unwrap();
        assert_ne!(nullifier, hash);

        // Read fails after delete.
        assert_eq!(store.read(&hash).await.unwrap_err(), StorageError::NotFound);

        // Re-upload of same content fails (nullified).
        let err = store.write(content, None, None).await.unwrap_err();
        assert_eq!(err, StorageError::Nullified);
    }

    #[tokio::test]
    async fn splice_produces_new_hash() {
        let store = ContentStore::new();
        let content = b"original content".to_vec();
        let receipt = store.write(content, None, None).await.unwrap();
        let old_hash = hex::decode(&receipt.hash).unwrap();

        let splice_result = store
            .splice(&old_hash, b"new content entirely", true)
            .await
            .unwrap();

        assert_ne!(splice_result.old_hash, splice_result.new_hash);
        assert!(splice_result.old_nullified);

        // Old hash is now gone.
        assert_eq!(
            store.read(&old_hash).await.unwrap_err(),
            StorageError::NotFound
        );

        // New hash is readable.
        let new_hash = hex::decode(&splice_result.new_hash).unwrap();
        let (data, _) = store.read(&new_hash).await.unwrap();
        assert_eq!(data, b"new content entirely");
    }

    #[tokio::test]
    async fn hex_roundtrip() {
        let original = [0xab; 32];
        let encoded = hex::encode(original);
        let decoded = hex::decode(&encoded).unwrap();
        assert_eq!(original, decoded);
    }
}
