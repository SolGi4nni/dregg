//! `SyncCellFs` — a `Send + Sync` cell-ledger filesystem over deos-zed's verified
//! [`OwnedSpine`](deos_zed::fs::OwnedSpine).
//!
//! # Why this exists
//!
//! Zed's [`fs::Fs`] trait is `Send + Sync` (its async methods return
//! `Pin<Box<dyn Future + Send>>`), and a real Zed `Project`/`Worktree` holds its
//! fs as `Arc<dyn fs::Fs>` shared across the gpui executor's threads.
//!
//! deos-zed's [`FirmamentFs`](deos_zed::FirmamentFs) is deliberately
//! single-threaded: it holds `Rc<dyn LedgerSpine>` + `RefCell` so it can SHARE
//! the cockpit's `Rc<RefCell<World>>` ledger (the editor-pane-over-the-live-World
//! seam). That makes it `!Send`/`!Sync` — perfect for the cockpit, unusable as a
//! Zed `Fs`.
//!
//! `SyncCellFs` keeps the SAME verified turn semantics — every save is a real
//! cap-gated `SetField` turn through deos-zed's [`OwnedSpine::commit_save`],
//! leaving a genuine [`TurnReceipt`] — but holds the spine behind an
//! `Arc<Mutex<OwnedSpine>>` and owns its own `Mutex`-guarded path→cell namespace.
//! `OwnedSpine` is `Send` (it has no `Rc`; just `RefCell`s and `Arc`s over the
//! `Ledger` + `TurnExecutor`), so `Arc<Mutex<OwnedSpine>>` is `Send + Sync`, and
//! so is `SyncCellFs`.
//!
//! Nothing here reimplements the turn: `install_file` (genesis seed),
//! `commit_save` (the verified cap-gated turn), `cell` (ledger snapshot),
//! `receipt_count`/`total_balance` are all deos-zed's `OwnedSpine` /
//! `LedgerSpine` code. `SyncCellFs` owns ONLY the path namespace + content
//! decode (the latter via deos-zed's exported `host_decode_content`).

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

use anyhow::{Result, anyhow};

use deos_zed::fs::{LedgerSpine, OwnedSpine, host_decode_content};

// The real verified cell id type — the same `dregg_cell::CellId` deos-zed's
// `LedgerSpine` trait returns (`install_file` → `Result<CellId>`).
use dregg_cell::CellId;

/// Lightweight metadata, mirroring deos-zed's `fs::Metadata` shape.
#[derive(Debug, Clone, Copy)]
pub struct CellMetadata {
    pub is_dir: bool,
    pub is_symlink: bool,
    pub len: u64,
}

/// A `Send + Sync` cell-ledger fs over deos-zed's verified `OwnedSpine`.
///
/// Holds the spine (the `Ledger` + `TurnExecutor` + editor author cell) behind a
/// `Mutex`, and a `Mutex`-guarded path→file-cell namespace. All save/seed
/// operations route through the spine's `LedgerSpine` methods — the same
/// verified turn logic deos-zed's single-threaded `FirmamentFs` uses.
pub struct SyncCellFs {
    spine: Arc<Mutex<OwnedSpine>>,
    /// path → file-cell id. The namespace layer (deos-zed keeps the identical
    /// map in `FirmamentFs.entries`, but as a single-threaded `RefCell`).
    entries: Mutex<BTreeMap<PathBuf, CellId>>,
}

impl SyncCellFs {
    /// A fresh cell-fs over a new `OwnedSpine` (its own ledger + executor, seeded
    /// with the editor author cell). Seed files with [`SyncCellFs::seed_file`].
    pub fn new() -> Self {
        SyncCellFs {
            spine: Arc::new(Mutex::new(OwnedSpine::new())),
            entries: Mutex::new(BTreeMap::new()),
        }
    }

    /// Seed a file into the namespace with initial `content`, as GENESIS — the
    /// spine installs a file cell holding the content projection + grants the
    /// editor its edit cap (deos-zed's `OwnedSpine::install_file`), and we
    /// register the path. Not a turn (no receipt).
    pub fn seed_file(&self, path: impl Into<PathBuf>, content: &str) -> Result<CellId> {
        let path = path.into();
        let file = self.spine.lock().unwrap().install_file(content)?;
        self.entries.lock().unwrap().insert(path, file);
        Ok(file)
    }

    /// How many save-turn receipts the spine has recorded — each a genuine
    /// finalized [`TurnReceipt`](deos_zed::fs::firmament_types::TurnReceipt).
    pub fn receipt_count(&self) -> usize {
        self.spine.lock().unwrap().receipt_count()
    }

    /// The Σ balance across the spine's ledger — the conservation observable. A
    /// content save leaves it INVARIANT (Σδ=0).
    pub fn total_balance(&self) -> i128 {
        self.spine.lock().unwrap().total_balance()
    }

    /// The file cell backing `path`, if mounted.
    pub fn cell_for(&self, path: &Path) -> Option<CellId> {
        self.entries.lock().unwrap().get(path).copied()
    }

    /// Read the committed content of the file-cell at `path` from the ledger
    /// (no turn). `Err` if no cell is mounted there.
    pub fn load(&self, path: &Path) -> Result<String> {
        let cell_id = self
            .entries
            .lock()
            .unwrap()
            .get(path)
            .copied()
            .ok_or_else(|| anyhow!("no cell mounted at {}", path.display()))?;
        let cell = self
            .spine
            .lock()
            .unwrap()
            .cell(&cell_id)
            .ok_or_else(|| anyhow!("file cell missing from ledger"))?;
        host_decode_content(&cell)
    }

    /// Save `content` to the file-cell at `path` — **a verified cap-gated turn**
    /// through the spine's executor, leaving a real receipt. If the path is new,
    /// a file cell is installed for it first (a "save as" into the namespace).
    pub fn save(&self, path: &Path, content: &str) -> Result<()> {
        // NB: bind the lookup to a local so the `entries` MutexGuard is dropped
        // BEFORE the `None` arm re-locks `entries` (a held-scrutinee-guard would
        // self-deadlock).
        let existing = self.entries.lock().unwrap().get(path).copied();
        let file = match existing {
            Some(c) => c,
            None => {
                let file = self.spine.lock().unwrap().install_file("")?;
                self.entries
                    .lock()
                    .unwrap()
                    .insert(path.to_path_buf(), file);
                file
            }
        };
        // THE SAVE IS A TURN — deos-zed's verified `commit_save`.
        self.spine.lock().unwrap().commit_save(file, content)?;
        Ok(())
    }

    /// List the immediate children of `path` in the namespace (files + implicit
    /// directories), exactly as deos-zed's `FirmamentFs::read_dir`.
    pub fn read_dir(&self, path: &Path) -> Vec<(PathBuf, bool)> {
        let entries = self.entries.lock().unwrap();
        let mut out = Vec::new();
        let mut seen_dirs = std::collections::BTreeSet::new();
        for p in entries.keys() {
            let Ok(rest) = p.strip_prefix(path) else {
                continue;
            };
            let mut comps = rest.components();
            let Some(first) = comps.next() else { continue };
            let child = path.join(first.as_os_str());
            if comps.next().is_some() {
                if seen_dirs.insert(child.clone()) {
                    out.push((child, true));
                }
            } else {
                out.push((child, false));
            }
        }
        out
    }

    /// Resolve `path` → metadata (file or implicit directory). `None` if nothing
    /// is mounted at or under it.
    pub fn metadata(&self, path: &Path) -> Option<CellMetadata> {
        let cell_id = self.entries.lock().unwrap().get(path).copied();
        if let Some(cell_id) = cell_id {
            let cell = self.spine.lock().unwrap().cell(&cell_id)?;
            let len = host_decode_content(&cell).map(|s| s.len()).unwrap_or(0) as u64;
            return Some(CellMetadata {
                is_dir: false,
                is_symlink: false,
                len,
            });
        }
        let is_dir = self
            .entries
            .lock()
            .unwrap()
            .keys()
            .any(|p| p.starts_with(path) && p != path);
        if is_dir {
            Some(CellMetadata {
                is_dir: true,
                is_symlink: false,
                len: 0,
            })
        } else {
            None
        }
    }
}

impl Default for SyncCellFs {
    fn default() -> Self {
        Self::new()
    }
}
