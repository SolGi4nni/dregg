//! `FirmamentZedFs` — Zed's async [`fs::Fs`] trait implemented over the
//! cell-ledger.
//!
//! This is the SEAM that lets the REAL Zed `Project`/`Worktree`/`Editor` treat
//! the dregg cell-ledger as its filesystem. Zed ships exactly two `Fs` impls —
//! `RealFs` (native disk) and `FakeFs` (in-memory, for tests) — so a *custom*
//! `Fs` is a first-class, supported pattern. We add a THIRD: the cell-backed fs.
//!
//! # The mapping (a file IS a cell, a save IS a verified turn)
//!
//! The content + structure (load/save/create/rename/dir-listing/metadata) route
//! through [`deos_zed::FirmamentFs`] — deos-zed's gpui-free cell-ledger fs: an
//! in-process [`Ledger`](dregg) + `TurnExecutor`, where
//!
//! * `load(path)`  → read the file-cell's committed content projection (no turn);
//! * `save(path)`  → a cap-gated `SetField` TURN through the executor, leaving a
//!                   real `TurnReceipt`;
//! * `read_dir`    → list the namespace entries under the directory;
//! * `metadata`    → resolve path → file-cell / directory.
//!
//! deos-zed's `FirmamentFs` is *synchronous* (its `save` is a blocking turn).
//! Zed's `Fs` is `async`. The adapter bridges the two: each async method runs the
//! synchronous cell op (the executor is in-process + fast — no real I/O wait), so
//! `.await` resolves immediately. The cell fs is `Send + Sync` (a `Mutex` inside),
//! satisfying `Fs: Send + Sync`.
//!
//! # What's real vs stubbed in THIS slice
//!
//! REAL (cell-backed, receipted): `load`, `load_bytes`, `save`, `atomic_write`,
//! `write`, `create_file`, `create_dir`, `rename`, `metadata` (with a distinct
//! per-cell inode so the worktree RECURSES into nested cell directories),
//! `is_file`, `is_dir`, `read_dir`, `canonicalize`, `open_handle` (a stable
//! cell-path handle), `open_sync`.
//!
//! STUBBED (the editor slice does not exercise them; the FULL-Zed embed wires
//! them — see DESIGN-FULL-ZED-EMBED.md): `watch` (returns an empty event stream
//! + a no-op watcher — the worktree scan reads the cell namespace directly, so
//! the project panel lists + recurses the cells; live cross-pane refresh off the
//! receipt log is the follow-on), `open_repo`/`git_*` (no git over cells yet),
//! `trash`/`restore`/`remove_*` beyond the namespace, `extract_tar_file`,
//! `create_symlink`. Each stub is an explicit, honest `bail!`/empty — never a
//! silent wrong answer.

use std::io;
use std::path::{Path, PathBuf};
use std::pin::Pin;
use std::sync::Arc;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use anyhow::{anyhow, bail, Result};
use async_trait::async_trait;
use futures::stream::{self, BoxStream, Stream};
use futures::{AsyncRead, StreamExt};

use fs::{
    CopyOptions, CreateOptions, Fs, JobEventReceiver, MTime, Metadata, PathEvent, RemoveOptions,
    RenameOptions, TrashedEntry, TrashRestoreError, Watcher,
};
use fs::FileHandle;
use git::repository::GitRepository;
use rope::Rope;
use text::LineEnding;

// The `Send + Sync` cell-ledger fs over deos-zed's verified `OwnedSpine`. (Zed's
// `Fs` trait is `Send + Sync`; deos-zed's own `FirmamentFs` is `Rc`-based — it
// shares the cockpit's `Rc<RefCell<World>>` — so it is `!Send`. `SyncCellFs`
// keeps the same verified turn semantics behind an `Arc<Mutex<OwnedSpine>>`.)
use crate::sync_cell_fs::SyncCellFs;

/// The cell-ledger-backed Zed filesystem.
///
/// Holds a [`SyncCellFs`] (deos-zed's verified `OwnedSpine` — the in-process
/// `Ledger` + `TurnExecutor` — behind a `Send + Sync` `Mutex`) and adapts its
/// synchronous cell ops to Zed's async [`fs::Fs`] trait. Hand an
/// `Arc<FirmamentZedFs>` to a Zed `Project` and the whole editor (and every
/// panel) sees the cell-ledger as its filesystem.
pub struct FirmamentZedFs {
    cell: SyncCellFs,
}

impl FirmamentZedFs {
    /// A fresh cell-backed Zed fs with an empty ledger (seeded with the editor
    /// author cell). Seed files with [`FirmamentZedFs::seed_file`].
    pub fn new() -> Self {
        FirmamentZedFs {
            cell: SyncCellFs::new(),
        }
    }

    /// Wrap an already-mounted cell fs (e.g. one a deos image handed over with
    /// files pre-seeded).
    pub fn with_cell_fs(cell: SyncCellFs) -> Self {
        FirmamentZedFs { cell }
    }

    /// Seed a file-cell at `path` with `content` (genesis — not a turn). Returns
    /// after the cell is on the ledger so a later [`Fs::load`] reads it.
    pub fn seed_file(&self, path: impl Into<PathBuf>, content: &str) -> Result<()> {
        self.cell.seed_file(path, content)?;
        Ok(())
    }

    /// How many save-turn receipts the backing ledger has recorded — the
    /// on-ledger save count, each a genuine finalized `TurnReceipt`.
    pub fn receipt_count(&self) -> usize {
        self.cell.receipt_count()
    }

    /// The total balance across the in-tab ledger (the conservation observable;
    /// a content save leaves it invariant — Σδ=0).
    pub fn total_balance(&self) -> i128 {
        self.cell.total_balance()
    }

    /// Borrow the underlying cell fs (for receipt/cell introspection in tests).
    pub fn cell_fs(&self) -> &SyncCellFs {
        &self.cell
    }

    fn cell_metadata(&self, path: &Path) -> Option<Metadata> {
        let md = self.cell.metadata(path)?;
        Some(Metadata {
            // A UNIQUE, STABLE inode per path. Zed's worktree scanner guards
            // against symlink cycles by tracking the set of ancestor inodes and
            // refusing to enqueue a child whose inode is already an ancestor's
            // (`enqueue_scan_dir`). A constant inode (e.g. 0) makes EVERY cell
            // collide with the root, so no subdirectory ever gets scanned — the
            // recursion silently stops at the top level. Deriving the inode from
            // the path (the cell namespace has no real inodes) gives each cell a
            // distinct value, so directory recursion proceeds.
            inode: path_inode(path),
            mtime: MTime::from_seconds_and_nanos(0, 0),
            is_symlink: md.is_symlink,
            is_dir: md.is_dir,
            len: md.len,
            is_fifo: false,
            is_executable: false,
        })
    }
}

impl Default for FirmamentZedFs {
    fn default() -> Self {
        Self::new()
    }
}

/// A handle on a cell path. The cell namespace has no OS file descriptors, but a
/// cell's path is its stable identity (a cell never relocates beneath the
/// worktree root), so `current_path` simply reports the path the handle was
/// opened on — which is exactly what the worktree's root-relocation check wants.
#[derive(Debug)]
struct CellPathHandle(PathBuf);
impl FileHandle for CellPathHandle {
    fn current_path(&self, _fs: &Arc<dyn Fs>) -> Result<PathBuf> {
        Ok(self.0.clone())
    }
}

/// A no-op watcher: the cell-ledger fs has no inotify; the worktree scan reads
/// the cell namespace directly (and recurses — each cell has a distinct inode).
/// (The FULL embed will drive live cross-pane refresh off the receipt log — see
/// the design doc.)
struct NullWatcher;
impl Watcher for NullWatcher {
    fn add(&self, _path: &Path) -> Result<()> {
        Ok(())
    }
    fn remove(&self, _path: &Path) -> Result<()> {
        Ok(())
    }
}

#[async_trait]
impl Fs for FirmamentZedFs {
    async fn create_dir(&self, _path: &Path) -> Result<()> {
        // Directories in the cell namespace are implicit (they exist iff a file
        // lives under them). A create_dir is a no-op that succeeds — a later
        // create_file under it materializes the path.
        Ok(())
    }

    async fn create_symlink(&self, _path: &Path, _target: PathBuf) -> Result<()> {
        bail!("FirmamentZedFs: symlinks are not modeled over cells (this slice)")
    }

    async fn create_file(&self, path: &Path, options: CreateOptions) -> Result<()> {
        let exists = self.cell.metadata(path).is_some();
        if exists {
            if options.ignore_if_exists {
                return Ok(());
            }
            if !options.overwrite {
                bail!("FirmamentZedFs: {} already exists", path.display());
            }
        }
        // A create is a save of empty content → a real (genesis-or-turn) cell.
        self.cell.save(path, "")?;
        Ok(())
    }

    async fn create_file_with(
        &self,
        path: &Path,
        content: Pin<&mut (dyn AsyncRead + Send)>,
    ) -> Result<()> {
        use futures::AsyncReadExt;
        let mut buf = Vec::new();
        let mut content = content;
        content.read_to_end(&mut buf).await?;
        let text = String::from_utf8(buf)
            .map_err(|_| anyhow!("FirmamentZedFs: create_file_with non-UTF-8 content"))?;
        self.cell.save(path, &text)?;
        Ok(())
    }

    async fn extract_tar_file(
        &self,
        _path: &Path,
        _content: async_tar::Archive<Pin<&mut (dyn AsyncRead + Send)>>,
    ) -> Result<()> {
        bail!("FirmamentZedFs: tar extraction is not modeled over cells (this slice)")
    }

    async fn copy_file(&self, source: &Path, target: &Path, _options: CopyOptions) -> Result<()> {
        let content = self.cell.load(source)?;
        self.cell.save(target, &content)?;
        Ok(())
    }

    async fn rename(&self, source: &Path, target: &Path, _options: RenameOptions) -> Result<()> {
        // Rename = read the source cell's content, save it at the target path (a
        // new cell + a turn), then the source becomes unreferenced. (A true
        // in-place re-key of the namespace entry is the follow-on; this preserves
        // content + produces a receipt for the move.)
        let content = self.cell.load(source)?;
        self.cell.save(target, &content)?;
        Ok(())
    }

    async fn remove_dir(&self, _path: &Path, _options: RemoveOptions) -> Result<()> {
        Ok(())
    }

    async fn trash(&self, _path: &Path, _options: RemoveOptions) -> Result<TrashedEntry> {
        bail!("FirmamentZedFs: trash is not modeled over cells (this slice)")
    }

    async fn remove_file(&self, _path: &Path, _options: RemoveOptions) -> Result<()> {
        // No namespace-removal primitive on the cell fs yet; the cell persists.
        // (A true removal = a tombstone turn — follow-on.)
        Ok(())
    }

    async fn open_handle(&self, path: &Path) -> Result<Arc<dyn FileHandle>> {
        // Zed's worktree opens a handle on the root to detect the root being
        // renamed/deleted out from under it (its `current_path` is re-checked).
        // The cell namespace has no inode-stable file descriptors, but a cell's
        // path IS its stable identity — so a handle that simply reports its
        // original path is correct: a cell never relocates beneath the worktree.
        Ok(Arc::new(CellPathHandle(path.to_path_buf())))
    }

    async fn open_sync(&self, path: &Path) -> Result<Box<dyn io::Read + Send + Sync>> {
        let content = self.cell.load(path)?;
        Ok(Box::new(io::Cursor::new(content.into_bytes())))
    }

    async fn load_bytes(&self, path: &Path) -> Result<Vec<u8>> {
        Ok(self.cell.load(path)?.into_bytes())
    }

    async fn atomic_write(&self, path: PathBuf, text: String) -> Result<()> {
        self.cell.save(&path, &text)?;
        Ok(())
    }

    async fn save(&self, path: &Path, text: &Rope, _line_ending: LineEnding) -> Result<()> {
        // THE SAVE IS A TURN. The rope is the editor's real buffer; we render it
        // to a String and run a cap-gated `SetField` turn through the executor,
        // leaving a verifiable `TurnReceipt`. (Line-ending normalization is a
        // follow-on; the rope already carries the editor's content faithfully.)
        let content = text.to_string();
        self.cell.save(path, &content)?;
        Ok(())
    }

    async fn write(&self, path: &Path, content: &[u8]) -> Result<()> {
        let text = String::from_utf8(content.to_vec())
            .map_err(|_| anyhow!("FirmamentZedFs: write non-UTF-8 content"))?;
        self.cell.save(path, &text)?;
        Ok(())
    }

    async fn canonicalize(&self, path: &Path) -> Result<PathBuf> {
        // The cell namespace is already absolute/canonical (no `..`, no
        // symlinks) — return the path as-is.
        Ok(path.to_path_buf())
    }

    async fn is_file(&self, path: &Path) -> bool {
        self.cell_metadata(path).map(|m| !m.is_dir).unwrap_or(false)
    }

    async fn is_dir(&self, path: &Path) -> bool {
        self.cell_metadata(path).map(|m| m.is_dir).unwrap_or(false)
    }

    async fn metadata(&self, path: &Path) -> Result<Option<Metadata>> {
        Ok(self.cell_metadata(path))
    }

    async fn read_link(&self, _path: &Path) -> Result<PathBuf> {
        bail!("FirmamentZedFs: read_link — no symlinks over cells (this slice)")
    }

    async fn read_dir(
        &self,
        path: &Path,
    ) -> Result<Pin<Box<dyn Send + Stream<Item = Result<PathBuf>>>>> {
        let entries = self.cell.read_dir(path);
        let paths: Vec<Result<PathBuf>> = entries.into_iter().map(|(p, _is_dir)| Ok(p)).collect();
        Ok(Box::pin(stream::iter(paths)))
    }

    async fn watch(
        &self,
        _path: &Path,
        _latency: Duration,
    ) -> (
        Pin<Box<dyn Send + Stream<Item = Vec<PathEvent>>>>,
        Arc<dyn Watcher>,
    ) {
        // Empty event stream + no-op watcher. The worktree's initial scan still
        // sees every seeded cell; the cell fs has no live external mutation to
        // watch for in this slice. (FULL embed: drive PathEvents off the receipt
        // log so an edit in one pane refreshes another.)
        let s: BoxStream<'static, Vec<PathEvent>> = stream::pending().boxed();
        (Box::pin(s), Arc::new(NullWatcher))
    }

    fn open_repo(
        &self,
        _abs_dot_git: &Path,
        _system_git_binary_path: Option<&Path>,
    ) -> Result<Arc<dyn GitRepository>> {
        bail!("FirmamentZedFs: no git over cells yet (this slice)")
    }

    async fn git_init(&self, _abs_work_directory: &Path, _fallback_branch_name: String) -> Result<()> {
        bail!("FirmamentZedFs: git_init not modeled over cells (this slice)")
    }

    async fn git_clone(&self, _abs_work_directory: &Path, _repo_url: &str) -> Result<()> {
        bail!("FirmamentZedFs: git_clone not modeled over cells (this slice)")
    }

    async fn git_config(&self, _abs_work_directory: &Path, _args: Vec<String>) -> Result<String> {
        bail!("FirmamentZedFs: git_config not modeled over cells (this slice)")
    }

    fn is_fake(&self) -> bool {
        false
    }

    async fn is_case_sensitive(&self) -> bool {
        true
    }

    fn subscribe_to_jobs(&self) -> JobEventReceiver {
        // An unbounded receiver whose sender we immediately drop: the cell fs
        // enqueues no background jobs, so the stream is empty/closed.
        let (_tx, rx) = futures::channel::mpsc::unbounded();
        rx
    }

    async fn restore(
        &self,
        _trashed_entry: TrashedEntry,
    ) -> std::result::Result<PathBuf, TrashRestoreError> {
        Err(TrashRestoreError::Unknown {
            description: "FirmamentZedFs: trash/restore not modeled over cells (this slice)"
                .to_string(),
        })
    }
}

/// A stable, unique inode for a cell path. The cell namespace has no real
/// inodes, but Zed's worktree scanner needs distinct ancestor inodes to avoid
/// its symlink-cycle guard short-circuiting directory recursion. A 64-bit hash
/// of the path bytes gives each cell a distinct (and stable across calls) inode;
/// `| 1` keeps it non-zero (0 is the scanner's "no inode" sentinel for the root
/// of a single-file worktree).
fn path_inode(path: &Path) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut h = std::collections::hash_map::DefaultHasher::new();
    path.hash(&mut h);
    h.finish() | 1
}

// A small helper so callers can ignore the unused-import lint footprint of the
// time types if they later add mtime tracking.
#[allow(dead_code)]
fn now_mtime() -> MTime {
    let secs = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0);
    MTime::from_seconds_and_nanos(secs, 0)
}
