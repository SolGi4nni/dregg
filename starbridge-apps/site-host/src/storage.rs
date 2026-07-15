//! Durable storage for the hosting data plane — the backbone under
//! [`crate::registry::SiteRegistry`].
//!
//! The registry used to be a pair of in-memory `Mutex<BTreeMap>`s plus an
//! `AtomicU64` sequence: a process restart erased every published site and every
//! receipt and reset the publish order to zero. That is a demo, not a hosting
//! service. This module introduces a [`StorageBackend`] the registry writes through,
//! with two implementations:
//!
//! * [`MemoryStore`] — the ephemeral in-process double (the free/local default and
//!   the test fixture). Fast, no disk, no durability — and it says so.
//! * [`FsStore`] — a filesystem backend: each site cell is an atomically-written JSON
//!   file, each site's receipts are an **append-only** JSONL log (full history, not
//!   just the latest), and the publish sequence is a crash-safe counter persisted by
//!   atomic temp-write + rename so the publish order survives a restart and never
//!   collides.
//!
//! Both keep the same `Send + Sync` object-safe surface so a handler is generic over
//! durability: a test binds a `MemoryStore`, a deployment binds an `FsStore` rooted
//! at a data directory (or, later, a replicated KV — the trait is the seam).

use std::collections::BTreeMap;
use std::fs;
use std::io::{BufRead, Write as _};
use std::path::{Path, PathBuf};
use std::sync::Mutex;
use std::sync::atomic::{AtomicU64, Ordering};

use crate::lock::lock_recover;
use crate::registry::{PublishReceipt, SiteCell};

/// Why a storage operation failed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StorageError {
    /// An underlying I/O error (path, message).
    Io(String),
    /// A stored record could not be (de)serialized — a corrupt or incompatible
    /// on-disk record.
    Corrupt(String),
    /// A name is not a safe storage key (path traversal / illegal characters).
    BadKey(String),
}

impl std::fmt::Display for StorageError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            StorageError::Io(m) => write!(f, "storage io error: {m}"),
            StorageError::Corrupt(m) => write!(f, "corrupt stored record: {m}"),
            StorageError::BadKey(k) => write!(f, "unsafe storage key `{k}`"),
        }
    }
}

impl std::error::Error for StorageError {}

/// The durable substrate the registry writes through: site cells, an append-only
/// receipt log per site, and a monotonic publish sequence.
///
/// Object-safe (`Arc<dyn StorageBackend>`) so a registry is generic over durability.
/// Implementations must be internally synchronized (the registry holds no lock of its
/// own around these calls).
pub trait StorageBackend: Send + Sync {
    /// Durably write (insert or replace) a site cell keyed by its `name`.
    fn put_cell(&self, cell: &SiteCell) -> Result<(), StorageError>;

    /// Read a site cell by name.
    fn get_cell(&self, name: &str) -> Result<Option<SiteCell>, StorageError>;

    /// Delete a site cell by name; returns whether it existed.
    fn delete_cell(&self, name: &str) -> Result<bool, StorageError>;

    /// The names of all stored cells (sorted).
    fn list_cells(&self) -> Result<Vec<String>, StorageError>;

    /// Append a receipt to the site's append-only history (retained for ALL
    /// publishes — signed or not, republish or delete).
    fn append_receipt(&self, receipt: &PublishReceipt) -> Result<(), StorageError>;

    /// The latest retained receipt for a site, if any.
    fn latest_receipt(&self, name: &str) -> Result<Option<PublishReceipt>, StorageError>;

    /// The full retained receipt history for a site, oldest first.
    fn receipt_history(&self, name: &str) -> Result<Vec<PublishReceipt>, StorageError>;

    /// Allocate the next publish sequence — strictly monotonic and, for a durable
    /// backend, crash-safe across restarts (never re-hands a value).
    fn next_seq(&self) -> Result<u64, StorageError>;

    /// Whether this backend is durable across process restarts (`false` for the
    /// in-memory double). Surfaced so an operator can assert durability at boot.
    fn is_durable(&self) -> bool;
}

// =============================================================================
// MemoryStore — the ephemeral in-process double.
// =============================================================================

/// The in-memory backend: the free/local default and the test double. **Not
/// durable** — a process restart erases it. Locks recover from poison (a panic
/// holding the lock does not brick every later access).
#[derive(Default)]
pub struct MemoryStore {
    cells: Mutex<BTreeMap<String, SiteCell>>,
    receipts: Mutex<BTreeMap<String, Vec<PublishReceipt>>>,
    seq: AtomicU64,
}

impl MemoryStore {
    /// A fresh empty in-memory store.
    pub fn new() -> MemoryStore {
        MemoryStore::default()
    }
}

impl StorageBackend for MemoryStore {
    fn put_cell(&self, cell: &SiteCell) -> Result<(), StorageError> {
        lock_recover(&self.cells).insert(cell.name.clone(), cell.clone());
        Ok(())
    }

    fn get_cell(&self, name: &str) -> Result<Option<SiteCell>, StorageError> {
        Ok(lock_recover(&self.cells).get(name).cloned())
    }

    fn delete_cell(&self, name: &str) -> Result<bool, StorageError> {
        Ok(lock_recover(&self.cells).remove(name).is_some())
    }

    fn list_cells(&self) -> Result<Vec<String>, StorageError> {
        Ok(lock_recover(&self.cells).keys().cloned().collect())
    }

    fn append_receipt(&self, receipt: &PublishReceipt) -> Result<(), StorageError> {
        lock_recover(&self.receipts)
            .entry(receipt.name.clone())
            .or_default()
            .push(receipt.clone());
        Ok(())
    }

    fn latest_receipt(&self, name: &str) -> Result<Option<PublishReceipt>, StorageError> {
        Ok(lock_recover(&self.receipts)
            .get(name)
            .and_then(|v| v.last().cloned()))
    }

    fn receipt_history(&self, name: &str) -> Result<Vec<PublishReceipt>, StorageError> {
        Ok(lock_recover(&self.receipts)
            .get(name)
            .cloned()
            .unwrap_or_default())
    }

    fn next_seq(&self) -> Result<u64, StorageError> {
        Ok(self.seq.fetch_add(1, Ordering::SeqCst))
    }

    fn is_durable(&self) -> bool {
        false
    }
}

// =============================================================================
// FsStore — the filesystem backend.
// =============================================================================

/// A filesystem-backed durable store rooted at a data directory.
///
/// Layout under `root`:
/// ```text
///   root/
///     seq              — the crash-safe publish counter (atomic temp+rename)
///     cells/<name>.json      — one site cell per file (atomic temp+rename)
///     receipts/<name>.jsonl  — append-only receipt history (one JSON per line)
/// ```
///
/// A single process-wide [`Mutex`] serializes mutations so the seq counter and the
/// append log stay consistent; reads take it too (cheap, and keeps the invariant
/// simple). Names are validated as safe single-label keys (no path traversal) before
/// they ever touch the filesystem.
pub struct FsStore {
    root: PathBuf,
    guard: Mutex<()>,
}

impl FsStore {
    /// Open (creating if absent) an `FsStore` rooted at `root`. Materializes the
    /// `cells/` and `receipts/` subdirectories.
    pub fn open(root: impl Into<PathBuf>) -> Result<FsStore, StorageError> {
        let root = root.into();
        fs::create_dir_all(root.join("cells")).map_err(io)?;
        fs::create_dir_all(root.join("receipts")).map_err(io)?;
        Ok(FsStore {
            root,
            guard: Mutex::new(()),
        })
    }

    fn cell_path(&self, name: &str) -> Result<PathBuf, StorageError> {
        Ok(self
            .root
            .join("cells")
            .join(format!("{}.json", safe_key(name)?)))
    }

    fn receipt_path(&self, name: &str) -> Result<PathBuf, StorageError> {
        Ok(self
            .root
            .join("receipts")
            .join(format!("{}.jsonl", safe_key(name)?)))
    }

    fn seq_path(&self) -> PathBuf {
        self.root.join("seq")
    }
}

impl StorageBackend for FsStore {
    fn put_cell(&self, cell: &SiteCell) -> Result<(), StorageError> {
        let _g = lock_recover(&self.guard);
        let path = self.cell_path(&cell.name)?;
        let bytes = serde_json::to_vec(cell).map_err(|e| StorageError::Corrupt(e.to_string()))?;
        atomic_write(&path, &bytes)
    }

    fn get_cell(&self, name: &str) -> Result<Option<SiteCell>, StorageError> {
        let _g = lock_recover(&self.guard);
        let path = self.cell_path(name)?;
        match fs::read(&path) {
            Ok(bytes) => {
                let cell = serde_json::from_slice(&bytes)
                    .map_err(|e| StorageError::Corrupt(e.to_string()))?;
                Ok(Some(cell))
            }
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(None),
            Err(e) => Err(io(e)),
        }
    }

    fn delete_cell(&self, name: &str) -> Result<bool, StorageError> {
        let _g = lock_recover(&self.guard);
        let path = self.cell_path(name)?;
        match fs::remove_file(&path) {
            Ok(()) => Ok(true),
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(false),
            Err(e) => Err(io(e)),
        }
    }

    fn list_cells(&self) -> Result<Vec<String>, StorageError> {
        let _g = lock_recover(&self.guard);
        let mut names = Vec::new();
        let dir = self.root.join("cells");
        for entry in fs::read_dir(&dir).map_err(io)? {
            let entry = entry.map_err(io)?;
            let file = entry.file_name();
            let file = file.to_string_lossy();
            if let Some(name) = file.strip_suffix(".json") {
                names.push(name.to_string());
            }
        }
        names.sort();
        Ok(names)
    }

    fn append_receipt(&self, receipt: &PublishReceipt) -> Result<(), StorageError> {
        let _g = lock_recover(&self.guard);
        let path = self.receipt_path(&receipt.name)?;
        let mut line =
            serde_json::to_vec(receipt).map_err(|e| StorageError::Corrupt(e.to_string()))?;
        line.push(b'\n');
        let mut f = fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(&path)
            .map_err(io)?;
        f.write_all(&line).map_err(io)?;
        f.flush().map_err(io)?;
        f.sync_all().map_err(io)?;
        Ok(())
    }

    fn latest_receipt(&self, name: &str) -> Result<Option<PublishReceipt>, StorageError> {
        Ok(self.receipt_history(name)?.pop())
    }

    fn receipt_history(&self, name: &str) -> Result<Vec<PublishReceipt>, StorageError> {
        let _g = lock_recover(&self.guard);
        let path = self.receipt_path(name)?;
        let file = match fs::File::open(&path) {
            Ok(f) => f,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(Vec::new()),
            Err(e) => return Err(io(e)),
        };
        let mut out = Vec::new();
        for line in std::io::BufReader::new(file).lines() {
            let line = line.map_err(io)?;
            if line.trim().is_empty() {
                continue;
            }
            let r: PublishReceipt =
                serde_json::from_str(&line).map_err(|e| StorageError::Corrupt(e.to_string()))?;
            out.push(r);
        }
        Ok(out)
    }

    fn next_seq(&self) -> Result<u64, StorageError> {
        let _g = lock_recover(&self.guard);
        let path = self.seq_path();
        let next = match fs::read_to_string(&path) {
            Ok(s) => s.trim().parse::<u64>().unwrap_or(0),
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => 0,
            Err(e) => return Err(io(e)),
        };
        // Persist `next + 1` BEFORE handing out `next`, atomically: a crash after the
        // rename never re-hands `next`; a crash before it just re-hands `next` to a
        // publish that had not yet committed a cell. Monotonic across restarts.
        atomic_write(&path, (next + 1).to_string().as_bytes())?;
        Ok(next)
    }

    fn is_durable(&self) -> bool {
        true
    }
}

/// Map an `io::Error` into a [`StorageError::Io`].
fn io(e: std::io::Error) -> StorageError {
    StorageError::Io(e.to_string())
}

/// Validate a name is a safe single-label storage key: non-empty, no path separators,
/// no `.`/`..` traversal, only the DNS-label alphabet the publish path already
/// enforces. Belt-and-braces against a caller that skipped [`crate::site::is_valid_name`].
fn safe_key(name: &str) -> Result<&str, StorageError> {
    let ok = !name.is_empty()
        && name.len() <= 63
        && !name.contains('/')
        && !name.contains('\\')
        && !name.contains('.')
        && name
            .bytes()
            .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'-');
    if ok {
        Ok(name)
    } else {
        Err(StorageError::BadKey(name.to_string()))
    }
}

/// Write `bytes` to `path` atomically: write a sibling temp file, fsync it, then
/// rename over the destination (a crash never leaves a half-written record).
fn atomic_write(path: &Path, bytes: &[u8]) -> Result<(), StorageError> {
    let tmp = tmp_sibling(path);
    {
        let mut f = fs::File::create(&tmp).map_err(io)?;
        f.write_all(bytes).map_err(io)?;
        f.flush().map_err(io)?;
        f.sync_all().map_err(io)?;
    }
    fs::rename(&tmp, path).map_err(io)?;
    Ok(())
}

/// A unique temp sibling path for an atomic write.
fn tmp_sibling(path: &Path) -> PathBuf {
    let pid = std::process::id();
    let n = TMP_CTR.fetch_add(1, Ordering::Relaxed);
    let mut ext = path
        .extension()
        .map(|e| e.to_string_lossy().into_owned())
        .unwrap_or_default();
    ext.push_str(&format!(".tmp.{pid}.{n}"));
    path.with_extension(ext)
}

static TMP_CTR: AtomicU64 = AtomicU64::new(0);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::registry::SiteCell;
    use crate::site::SiteContent;

    fn cell(name: &str, body: &str) -> SiteCell {
        SiteCell::new(
            name,
            "agent:alice",
            SiteContent::new().with("/index.html", body),
        )
    }

    fn receipt(name: &str, seq: u64) -> PublishReceipt {
        PublishReceipt {
            seq,
            name: name.to_string(),
            owner: "agent:alice".to_string(),
            content_root: "deadbeef".to_string(),
            asset_count: 1,
            deleted: false,
            attest: None,
        }
    }

    fn backends() -> Vec<(&'static str, Box<dyn StorageBackend>)> {
        let dir = std::env::temp_dir().join(format!(
            "site-host-fsstore-test-{}-{}",
            std::process::id(),
            TMP_CTR.fetch_add(1, Ordering::Relaxed)
        ));
        vec![
            ("memory", Box::new(MemoryStore::new())),
            ("fs", Box::new(FsStore::open(dir).unwrap())),
        ]
    }

    #[test]
    fn put_get_delete_and_list_round_trip_on_both_backends() {
        for (label, store) in backends() {
            store.put_cell(&cell("blog", "hi")).unwrap();
            store.put_cell(&cell("shop", "buy")).unwrap();
            assert_eq!(store.list_cells().unwrap(), vec!["blog", "shop"], "{label}");
            assert_eq!(
                store
                    .get_cell("blog")
                    .unwrap()
                    .unwrap()
                    .content
                    .resolve("/")
                    .unwrap()
                    .body,
                b"hi",
                "{label}"
            );
            assert!(store.get_cell("absent").unwrap().is_none(), "{label}");
            assert!(store.delete_cell("blog").unwrap(), "{label}");
            assert!(!store.delete_cell("blog").unwrap(), "{label}");
            assert_eq!(store.list_cells().unwrap(), vec!["shop"], "{label}");
        }
    }

    #[test]
    fn receipt_history_is_append_only_on_both_backends() {
        for (label, store) in backends() {
            store.append_receipt(&receipt("blog", 0)).unwrap();
            store.append_receipt(&receipt("blog", 1)).unwrap();
            store.append_receipt(&receipt("blog", 2)).unwrap();
            let hist = store.receipt_history("blog").unwrap();
            assert_eq!(hist.len(), 3, "{label}: full history retained");
            assert_eq!(
                hist.iter().map(|r| r.seq).collect::<Vec<_>>(),
                vec![0, 1, 2],
                "{label}"
            );
            assert_eq!(
                store.latest_receipt("blog").unwrap().unwrap().seq,
                2,
                "{label}"
            );
            assert!(
                store.receipt_history("absent").unwrap().is_empty(),
                "{label}"
            );
        }
    }

    #[test]
    fn seq_is_monotonic_and_unique() {
        for (label, store) in backends() {
            let seqs: Vec<u64> = (0..5).map(|_| store.next_seq().unwrap()).collect();
            assert_eq!(seqs, vec![0, 1, 2, 3, 4], "{label}");
        }
    }

    #[test]
    fn fs_seq_survives_reopen() {
        let dir = std::env::temp_dir().join(format!(
            "site-host-fsstore-seq-{}-{}",
            std::process::id(),
            TMP_CTR.fetch_add(1, Ordering::Relaxed)
        ));
        {
            let store = FsStore::open(&dir).unwrap();
            assert_eq!(store.next_seq().unwrap(), 0);
            assert_eq!(store.next_seq().unwrap(), 1);
        }
        // A "restart": a fresh handle on the same root resumes the sequence — no
        // collision back to 0.
        let store = FsStore::open(&dir).unwrap();
        assert_eq!(store.next_seq().unwrap(), 2, "seq survived the reopen");
    }

    #[test]
    fn fs_cells_and_receipts_survive_reopen() {
        let dir = std::env::temp_dir().join(format!(
            "site-host-fsstore-durable-{}-{}",
            std::process::id(),
            TMP_CTR.fetch_add(1, Ordering::Relaxed)
        ));
        {
            let store = FsStore::open(&dir).unwrap();
            store.put_cell(&cell("blog", "durable")).unwrap();
            store.append_receipt(&receipt("blog", 7)).unwrap();
        }
        let store = FsStore::open(&dir).unwrap();
        assert_eq!(
            store
                .get_cell("blog")
                .unwrap()
                .unwrap()
                .content
                .resolve("/")
                .unwrap()
                .body,
            b"durable"
        );
        assert_eq!(store.latest_receipt("blog").unwrap().unwrap().seq, 7);
        assert!(store.is_durable());
    }

    #[test]
    fn fs_rejects_unsafe_keys() {
        let dir = std::env::temp_dir().join(format!(
            "site-host-fsstore-badkey-{}-{}",
            std::process::id(),
            TMP_CTR.fetch_add(1, Ordering::Relaxed)
        ));
        let store = FsStore::open(dir).unwrap();
        assert!(matches!(
            store.get_cell("../etc/passwd"),
            Err(StorageError::BadKey(_))
        ));
        assert!(matches!(
            store.put_cell(&cell("a/b", "x")),
            Err(StorageError::BadKey(_))
        ));
    }
}
