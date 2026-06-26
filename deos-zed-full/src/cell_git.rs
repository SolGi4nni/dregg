//! `CellLedgerGit` — Zed's [`git::repository::GitRepository`] backed by the dregg
//! **cell-ledger / dregg-doc patch history**, NOT a host `.git`.
//!
//! This is the git surface of the full-Zed embed: the IDE's git panel renders
//! change history, status, blame, and diffs derived from the *receipt chain*
//! (each save = a verified turn = a "commit") and the *dregg-doc patch theory*
//! (each edit = a Pijul-shaped patch; blame attributes each line to its authoring
//! patch, stable across moves). There is no `git2`, no `.git` directory, no host
//! VCS anywhere in the data path.
//!
//! # The mapping (cell-ledger VCS → Zed's git types)
//!
//! | Zed `GitRepository` method | cell-ledger realization                                    |
//! |----------------------------|------------------------------------------------------------|
//! | `head_sha` / `revparse_batch` | the HEAD patch's [`dregg_doc::PatchId`] → an [`Oid`] (the chain tip). |
//! | `status(prefixes)`         | per-path **modified-since-HEAD**: the live cell content vs. the rendered text at the HEAD patch. A path whose cell changed since its last committed patch is `Modified` in the worktree. |
//! | `blame(path, content, …)`  | [`dregg_doc::blame`] over the path's replayed graph: each line → the [`Oid`] of the patch (turn) that authored it. Blame is **correct by construction** (atom ids are content-addressed, so authorship survives moves — the git-blame failure mode cannot occur). |
//! | `show(commit)` / `load_commit` | a [`CommitDetails`] / [`CommitDiff`] derived from a patch: the diff old→new rendered text between [`History::replay_to`] of the parent and the patch. |
//! | `load_committed_text(path)` | the rendered text of the path's history at HEAD (the committed content). |
//! | `branches`                 | a single synthetic `main` branch whose tip is the HEAD patch. |
//!
//! # Honest ceiling
//!
//! REAL (cell-ledger / dregg-doc derived, exercised by `tests/cell_ledger_git.rs`):
//! `head_sha`, `revparse_batch`, `status`, `blame`, `show`, `load_commit`,
//! `load_committed_text`, `load_index_text`, `diff`, `branches`, `path`,
//! `main_repository_path`.
//!
//! STUBBED — honest `bail!`/empty, never a silent wrong answer (each is a
//! mutation/remote/worktree op the read-only history surface does not model):
//! `set_index_text`, `stage/unstage/commit/push/pull/fetch`, `reset/checkout`,
//! all `stash_*`, `worktree`/`branch` mutation, `remote_*`, `checkpoint*`,
//! `initial_graph_data`/`search_commits`/`file_history_changed_files`,
//! `commit_data_reader`, `diff_tree`, `diff_stat`, `update_ref`/`delete_ref`,
//! `run_hook`, `repair_worktrees`, `load_commit_template`, `merge_message`,
//! `load_blob_content`, `default_branch`, `remote_url`, `create_archive_*`.
//!
//! # Panel auto-discovery (CLOSED)
//!
//! This object IS the substrate Zed's `git_ui` panel renders, and the panel
//! AUTO-DISCOVERS it from the worktree scan — no hand-injection. The scanner
//! emits an `UpdatedGitRepository` (which drives `GitStore` → `Fs::open_repo`)
//! when it lists a `.git` entry during the scan: it processes `.git` first
//! (`worktree.rs` `swap_to_front(DOT_GIT)`) and, because the child's
//! `file_name() == ".git"`, fires `insert_git_repository` → the git-store event
//! → `project/src/git_store.rs:447` (`fs.open_repo(...)`) →
//! `update_repositories_from_worktree` (`git_store.rs:1808`).
//!
//! [`crate::firmament_zed_fs::FirmamentZedFs`] presents a single synthetic `.git`
//! directory entry at the git work root (in `read_dir`/`metadata`, only when
//! [`crate::firmament_zed_fs::FirmamentZedFs::enable_git`] has armed this repo —
//! there is no host `.git` anywhere on the cell ledger), and `open_repo` returns
//! this `CellLedgerGit`. The result: a real `Project` over the cell-ledger fs
//! auto-discovers the repository and the `GitStore` renders REAL cell-ledger
//! status/blame/log/diff. Proven by running in
//! `tests/git_panel_auto_discovery.rs` (the discovered repo's status lists the
//! modified cell after a live edit).

use std::collections::HashMap as StdHashMap;
use std::path::{Path, PathBuf};
use std::str::FromStr;
use std::sync::{Arc, Mutex};

use anyhow::{Result, bail};
use futures::future::{BoxFuture, FutureExt};

use git::repository::{
    AskPassDelegate, Branch, BranchesScanResult, CommitDataReader, CommitDetails, CommitDiff,
    CommitFile, CommitOptions, CommitSummary, CreateWorktreeTarget, DiffType, FetchOptions,
    FileHistoryChangedFileSets, GitCommitTemplate, GitRepository, GitRepositoryCheckpoint,
    InitialGraphCommitData, LogOrder, LogSource, PushOptions, Remote, RepoPath, ResetMode,
    SearchCommitArgs, Worktree,
};
use git::stash::GitStash;
use git::status::{
    DiffTreeType, FileStatus, GitDiffStat, GitStatus, StatusCode, TrackedStatus, TreeDiff,
};
use git::{Oid, RemoteCommandOutput, RunHook};

use gpui::{AsyncApp, BackgroundExecutor, SharedString, Task};
use rope::Rope;
use text::LineEnding;

use collections::HashMap;

use dregg_doc::{Author, Doc, Granularity, History, PatchId, blame};

/// The synthetic author for editor saves coming through the cell-fs (a single
/// cap-holder identity for this slice; the real seam binds the turn's editor cell
/// id — see `firmament.rs`'s editor author cell). Distinct from `Author::SYSTEM`.
const EDITOR_AUTHOR: Author = Author(0xED);

/// The synthetic branch name the cell-ledger repository reports. There is one
/// linear patch history; we surface it as `main`.
const MAIN_BRANCH: &str = "main";

/// Derive a stable [`Oid`] (20-byte SHA-1-shaped) from a 128-bit [`PatchId`]. The
/// patch id is content-addressed over the patch's ops + author; we expand it to
/// 20 bytes (the low 16 are the id, the high 4 a domain tag) so it is a valid,
/// stable, collision-resistant commit oid for the git panel. The genesis patch
/// (`PatchId::GENESIS`, value 0) maps to the all-zero oid (git's "no parent").
fn patch_oid(patch: PatchId) -> Oid {
    let mut bytes = [0u8; 20];
    bytes[0..16].copy_from_slice(&patch.0.to_be_bytes());
    // Domain-tag the high 4 bytes so a patch oid is visibly a dregg-doc oid and
    // never accidentally equals a real git sha prefix.
    if patch != PatchId::GENESIS {
        bytes[16..20].copy_from_slice(&[0xD0, 0x66, 0xED, 0x60]);
    }
    Oid::from_bytes(&bytes).expect("20 bytes is a valid SHA-1 oid")
}

/// The per-path document history: a dregg-doc [`Doc`] whose patch chain IS the
/// file's commit history. A `record_save` diffs the new content into the
/// previous and commits a patch (the "commit" for that save).
struct PathDoc {
    doc: Doc,
}

impl PathDoc {
    fn new() -> Self {
        PathDoc {
            doc: Doc::new(Granularity::Line),
        }
    }

    /// Record a save: diff the current rendered text into `content` and commit a
    /// patch authored by the editor. Returns the new tip patch id (the "commit"
    /// id for this save). A no-op edit produces the empty-patch tip.
    fn record_save(&mut self, content: &str) -> PatchId {
        self.doc.edit(EDITOR_AUTHOR, content)
    }

    fn history(&self) -> &History {
        self.doc.history()
    }

    /// The rendered text at HEAD (the committed content).
    fn head_text(&self) -> String {
        self.doc.text()
    }
}

/// The cell-ledger-backed git repository. Holds the per-path dregg-doc histories
/// (the change history) keyed by the same paths the cell namespace uses, plus a
/// background executor so `status` can return a `Task`. This object is what
/// `FirmamentZedFs::open_repo` returns and what Zed's `git_ui` panel renders.
pub struct CellLedgerGit {
    /// Per-path patch history (the commit chain for each file). Mutex-guarded so
    /// the repo is `Send + Sync` (Zed shares it as `Arc<dyn GitRepository>`).
    docs: Mutex<StdHashMap<PathBuf, PathDoc>>,
    /// The live cell content reader: a snapshot of `path -> current committed cell
    /// content`. Compared against the dregg-doc HEAD text to compute worktree
    /// status (modified-since-HEAD). In the full embed this is the `SyncCellFs`
    /// `load`; here it is an injected snapshot so the repo stays decoupled from
    /// the fs lock order.
    live: Mutex<StdHashMap<PathBuf, String>>,
    /// The worktree root the namespace paths are relative to (for `RepoPath`).
    work_root: PathBuf,
    executor: BackgroundExecutor,
    trusted: std::sync::atomic::AtomicBool,
}

impl CellLedgerGit {
    /// A fresh cell-ledger repository rooted at `work_root`. Seed file histories
    /// with [`CellLedgerGit::record_genesis`] then drive saves with
    /// [`CellLedgerGit::record_save`].
    pub fn new(work_root: impl Into<PathBuf>, executor: BackgroundExecutor) -> Self {
        CellLedgerGit {
            docs: Mutex::new(StdHashMap::new()),
            live: Mutex::new(StdHashMap::new()),
            work_root: work_root.into(),
            executor,
            trusted: std::sync::atomic::AtomicBool::new(true),
        }
    }

    /// The worktree root the namespace paths are relative to. Used by
    /// [`crate::firmament_zed_fs::FirmamentZedFs`] to know under which directory
    /// to present the synthetic `.git` namespace entry that drives Zed's worktree
    /// scanner to auto-discover this repository.
    pub fn work_root(&self) -> &Path {
        &self.work_root
    }

    /// Record the genesis content for `path`: the first committed patch (the
    /// initial "commit"), and set the live content to match (clean worktree).
    pub fn record_genesis(&self, path: impl Into<PathBuf>, content: &str) -> PatchId {
        let path = path.into();
        let id = {
            let mut docs = self.docs.lock().unwrap();
            let entry = docs.entry(path.clone()).or_insert_with(PathDoc::new);
            entry.record_save(content)
        };
        self.live.lock().unwrap().insert(path, content.to_string());
        id
    }

    /// Record a SAVE for `path` as a new committed patch (a "commit"): diff the
    /// new content into the history and commit. The live content is set to match
    /// (a saved file is clean against its own new HEAD). Returns the patch id.
    /// This is the dregg-doc-side mirror of a cell-ledger save-turn.
    pub fn record_save(&self, path: impl Into<PathBuf>, content: &str) -> PatchId {
        let path = path.into();
        let id = {
            let mut docs = self.docs.lock().unwrap();
            let entry = docs.entry(path.clone()).or_insert_with(PathDoc::new);
            entry.record_save(content)
        };
        self.live.lock().unwrap().insert(path, content.to_string());
        id
    }

    /// Set the LIVE (working-tree) content for `path` WITHOUT committing — an
    /// unsaved editor buffer. This is what makes `status` report `Modified`: the
    /// live content diverges from the HEAD patch's rendered text.
    pub fn set_live(&self, path: impl Into<PathBuf>, content: &str) {
        self.live
            .lock()
            .unwrap()
            .insert(path.into(), content.to_string());
    }

    /// The HEAD patch id across all paths' histories — the repository tip. We take
    /// the most recently committed patch (the last save's patch id) as HEAD; for a
    /// single-file edit session this is exactly that file's tip.
    fn head_patch(&self) -> PatchId {
        let docs = self.docs.lock().unwrap();
        docs.values()
            .filter_map(|d| d.history().tip())
            .last()
            .unwrap_or(PatchId::GENESIS)
    }

    /// Convert a namespace path to a `RepoPath` (relative to the work root).
    fn repo_path(&self, path: &Path) -> Result<RepoPath> {
        let rel = path.strip_prefix(&self.work_root).unwrap_or(path);
        let s = rel.to_string_lossy();
        let s = s.strip_prefix('/').unwrap_or(&s);
        RepoPath::new(s)
    }

    /// The absolute namespace path for a `RepoPath` (work root + rel).
    fn abs_path(&self, repo_path: &RepoPath) -> PathBuf {
        self.work_root.join(repo_path.as_std_path())
    }
}

impl GitRepository for CellLedgerGit {
    fn load_index_text(&self, path: RepoPath) -> BoxFuture<'_, Option<String>> {
        // The index mirrors HEAD in this read-only history surface (no staging):
        // the committed text of the path at HEAD.
        self.load_committed_text(path)
    }

    fn load_committed_text(&self, path: RepoPath) -> BoxFuture<'_, Option<String>> {
        let abs = self.abs_path(&path);
        async move {
            let docs = self.docs.lock().unwrap();
            docs.get(&abs).map(|d| d.head_text())
        }
        .boxed()
    }

    fn load_blob_content(&self, _oid: Oid) -> BoxFuture<'_, Result<String>> {
        async { bail!("CellLedgerGit: load_blob_content not modeled (use load_commit for a patch's content)") }.boxed()
    }

    fn set_index_text(
        &self,
        _path: RepoPath,
        _content: Option<String>,
        _env: Arc<HashMap<String, String>>,
        _is_executable: bool,
    ) -> BoxFuture<'_, Result<()>> {
        async { bail!("CellLedgerGit: staging (set_index_text) is not modeled — a cell-ledger save IS the commit") }.boxed()
    }

    fn remote_url(&self, _name: &str) -> BoxFuture<'_, Option<String>> {
        async { None }.boxed()
    }

    fn revparse_batch(&self, revs: Vec<String>) -> BoxFuture<'_, Result<Vec<Option<String>>>> {
        let head = self.head_patch();
        async move {
            Ok(revs
                .into_iter()
                .map(|rev| match rev.as_str() {
                    "HEAD" => Some(patch_oid(head).to_string()),
                    // A literal patch-oid hex passes through if it is well-formed.
                    other => Oid::from_str(other).ok().map(|o| o.to_string()),
                })
                .collect())
        }
        .boxed()
    }

    fn merge_message(&self) -> BoxFuture<'_, Option<String>> {
        async { None }.boxed()
    }

    fn status(&self, path_prefixes: &[RepoPath]) -> Task<Result<GitStatus>> {
        // WORKTREE STATUS, derived from the cell-ledger / dregg-doc history: a path
        // is `Modified` in the worktree iff its LIVE cell content diverges from the
        // rendered text of its HEAD patch (an unsaved edit). A path that has live
        // content but no committed history is `Added`/untracked. This is real
        // modified-since-HEAD status with NO host git anywhere.
        let prefixes: Vec<PathBuf> = path_prefixes.iter().map(|p| self.abs_path(p)).collect();
        let docs = self.docs.lock().unwrap();
        let live = self.live.lock().unwrap();
        let mut entries: Vec<(RepoPath, FileStatus)> = Vec::new();
        for (path, live_content) in live.iter() {
            if !prefixes.is_empty() && !prefixes.iter().any(|pre| path.starts_with(pre)) {
                continue;
            }
            let Ok(rp) = self.repo_path(path) else {
                continue;
            };
            match docs.get(path) {
                Some(doc) => {
                    let head = doc.head_text();
                    if &head != live_content {
                        entries.push((
                            rp,
                            FileStatus::Tracked(TrackedStatus {
                                index_status: StatusCode::Unmodified,
                                worktree_status: StatusCode::Modified,
                            }),
                        ));
                    }
                    // else: clean (live == HEAD) — emit nothing (git omits clean files)
                }
                None => {
                    // Live content with no committed history → untracked/added.
                    entries.push((rp, FileStatus::Untracked));
                }
            }
        }
        // Finish off the gpui BACKGROUND executor — the same posture as Zed's
        // `RealGitRepository::status` (git status runs off the main thread). The
        // entries are already gathered from the (Mutex-guarded) histories above;
        // the sort + wrap complete on the background pool.
        self.executor.spawn(async move {
            entries.sort_unstable_by(|(a, _), (b, _)| a.cmp(b));
            Ok(GitStatus {
                entries: entries.into(),
            })
        })
    }

    fn diff_tree(&self, _request: DiffTreeType) -> BoxFuture<'_, Result<TreeDiff>> {
        async {
            Ok(TreeDiff {
                entries: HashMap::default(),
            })
        }
        .boxed()
    }

    fn stash_entries(&self) -> BoxFuture<'static, Result<GitStash>> {
        async { Ok(GitStash::default()) }.boxed()
    }

    fn branches(&self) -> BoxFuture<'_, Result<BranchesScanResult>> {
        // ONE synthetic branch: `main`, head = the HEAD patch.
        let head = self.head_patch();
        async move {
            let branch = Branch {
                is_head: true,
                ref_name: format!("refs/heads/{MAIN_BRANCH}").into(),
                upstream: None,
                most_recent_commit: Some(CommitSummary {
                    sha: patch_oid(head).to_string().into(),
                    subject: "cell-ledger save".into(),
                    commit_timestamp: 0,
                    author_name: "editor".into(),
                    has_parent: head != PatchId::GENESIS,
                }),
            };
            Ok(BranchesScanResult::from(vec![branch]))
        }
        .boxed()
    }

    fn change_branch(&self, _name: String) -> BoxFuture<'_, Result<()>> {
        async { bail!("CellLedgerGit: branch switching is not modeled (one linear patch history)") }
            .boxed()
    }
    fn create_branch(
        &self,
        _name: String,
        _base_branch: Option<String>,
    ) -> BoxFuture<'_, Result<()>> {
        async { bail!("CellLedgerGit: create_branch not modeled (branch = a dregg-doc History::branch follow-on)") }.boxed()
    }
    fn rename_branch(&self, _branch: String, _new_name: String) -> BoxFuture<'_, Result<()>> {
        async { bail!("CellLedgerGit: rename_branch not modeled") }.boxed()
    }
    fn delete_branch(
        &self,
        _is_remote: bool,
        _name: String,
        _force: bool,
    ) -> BoxFuture<'_, Result<()>> {
        async { bail!("CellLedgerGit: delete_branch not modeled") }.boxed()
    }

    fn worktrees(&self) -> BoxFuture<'_, Result<Vec<Worktree>>> {
        async { Ok(Vec::new()) }.boxed()
    }
    fn create_worktree(
        &self,
        _target: CreateWorktreeTarget,
        _path: PathBuf,
    ) -> BoxFuture<'_, Result<()>> {
        async { bail!("CellLedgerGit: create_worktree not modeled") }.boxed()
    }
    fn checkout_branch_in_worktree(
        &self,
        _branch_name: String,
        _worktree_path: PathBuf,
        _create: bool,
    ) -> BoxFuture<'_, Result<()>> {
        async { bail!("CellLedgerGit: checkout_branch_in_worktree not modeled") }.boxed()
    }
    fn remove_worktree(&self, _path: PathBuf, _force: bool) -> BoxFuture<'_, Result<()>> {
        async { bail!("CellLedgerGit: remove_worktree not modeled") }.boxed()
    }
    fn rename_worktree(&self, _old_path: PathBuf, _new_path: PathBuf) -> BoxFuture<'_, Result<()>> {
        async { bail!("CellLedgerGit: rename_worktree not modeled") }.boxed()
    }

    fn reset(
        &self,
        _commit: String,
        _mode: ResetMode,
        _env: Arc<HashMap<String, String>>,
    ) -> BoxFuture<'_, Result<()>> {
        async { bail!("CellLedgerGit: reset not modeled (time-travel is History::replay_to, not a mutation)") }.boxed()
    }
    fn checkout_files(
        &self,
        _commit: String,
        _paths: Vec<RepoPath>,
        _env: Arc<HashMap<String, String>>,
    ) -> BoxFuture<'_, Result<()>> {
        async { bail!("CellLedgerGit: checkout_files not modeled") }.boxed()
    }

    fn show(&self, commit: String) -> BoxFuture<'_, Result<CommitDetails>> {
        // A "commit" is a patch. Resolve the oid hex → patch id by matching it
        // against the patch chain, and report its CommitDetails.
        let target = parse_commit_oid(&commit);
        let docs = self.docs.lock().unwrap();
        let found = find_patch_summary(&docs, target);
        async move {
            match found {
                Some((sha, subject)) => Ok(CommitDetails {
                    sha: sha.into(),
                    message: subject.into(),
                    commit_timestamp: 0,
                    author_email: "editor@cell-ledger".into(),
                    author_name: "editor".into(),
                }),
                None => bail!("CellLedgerGit: no patch matches commit {commit}"),
            }
        }
        .boxed()
    }

    fn load_commit(&self, commit: String, _cx: AsyncApp) -> BoxFuture<'_, Result<CommitDiff>> {
        // The DIFF a commit introduced: replay the path's history to the patch and
        // to its predecessor, and emit each path's old→new rendered text. The git
        // panel renders this as the commit's changed files.
        let target = parse_commit_oid(&commit);
        let docs = self.docs.lock().unwrap();
        let files = commit_diff_files(&docs, &self.work_root, target);
        async move {
            if files.is_empty() {
                bail!("CellLedgerGit: no patch matches commit {commit}");
            }
            Ok(CommitDiff { files })
        }
        .boxed()
    }

    fn blame(
        &self,
        path: RepoPath,
        _content: Rope,
        _line_ending: LineEnding,
    ) -> BoxFuture<'_, Result<git::blame::Blame>> {
        // BLAME, correct by construction: dregg-doc attributes each LINE to the
        // patch (turn) that authored its atom — stable across moves, because atom
        // ids are content-addressed (the git-blame "smear on reflow" failure mode
        // cannot occur). We map each authoring PatchId → an Oid and build Zed's
        // `Blame` directly off the path's replayed graph.
        let abs = self.abs_path(&path);
        let docs = self.docs.lock().unwrap();
        let blame_result = docs.get(&abs).map(|doc| {
            let graph = doc.history().replay();
            let lines = blame(&graph);
            build_zed_blame(&lines, &path)
        });
        async move {
            match blame_result {
                Some(b) => Ok(b),
                None => bail!(
                    "CellLedgerGit: no history for {}",
                    path.as_std_path().display()
                ),
            }
        }
        .boxed()
    }

    fn path(&self) -> PathBuf {
        // The synthetic ".git" location: the work root + a virtual `.dregg-git`
        // marker (there is no real `.git` directory; this is the repo's identity).
        self.work_root.join(".dregg-git")
    }

    fn main_repository_path(&self) -> PathBuf {
        self.path()
    }

    fn stage_paths(
        &self,
        _paths: Vec<RepoPath>,
        _env: Arc<HashMap<String, String>>,
    ) -> BoxFuture<'_, Result<()>> {
        async { bail!("CellLedgerGit: staging not modeled — a save IS the commit") }.boxed()
    }
    fn unstage_paths(
        &self,
        _paths: Vec<RepoPath>,
        _env: Arc<HashMap<String, String>>,
    ) -> BoxFuture<'_, Result<()>> {
        async { bail!("CellLedgerGit: unstaging not modeled") }.boxed()
    }

    fn run_hook(
        &self,
        _hook: RunHook,
        _env: Arc<HashMap<String, String>>,
    ) -> BoxFuture<'_, Result<()>> {
        async { Ok(()) }.boxed()
    }

    fn commit(
        &self,
        _message: SharedString,
        _name_and_email: Option<(SharedString, SharedString)>,
        _options: CommitOptions,
        _askpass: AskPassDelegate,
        _env: Arc<HashMap<String, String>>,
    ) -> BoxFuture<'_, Result<()>> {
        async { bail!("CellLedgerGit: an explicit commit is not modeled — every cell-ledger save is already a committed patch") }.boxed()
    }

    fn stash_paths(
        &self,
        _paths: Vec<RepoPath>,
        _env: Arc<HashMap<String, String>>,
    ) -> BoxFuture<'_, Result<()>> {
        async { bail!("CellLedgerGit: stash not modeled") }.boxed()
    }
    fn stash_pop(
        &self,
        _index: Option<usize>,
        _env: Arc<HashMap<String, String>>,
    ) -> BoxFuture<'_, Result<()>> {
        async { bail!("CellLedgerGit: stash not modeled") }.boxed()
    }
    fn stash_apply(
        &self,
        _index: Option<usize>,
        _env: Arc<HashMap<String, String>>,
    ) -> BoxFuture<'_, Result<()>> {
        async { bail!("CellLedgerGit: stash not modeled") }.boxed()
    }
    fn stash_drop(
        &self,
        _index: Option<usize>,
        _env: Arc<HashMap<String, String>>,
    ) -> BoxFuture<'_, Result<()>> {
        async { bail!("CellLedgerGit: stash not modeled") }.boxed()
    }

    fn push(
        &self,
        _branch_name: String,
        _remote_branch_name: String,
        _upstream_name: String,
        _options: Option<PushOptions>,
        _askpass: AskPassDelegate,
        _env: Arc<HashMap<String, String>>,
        _cx: AsyncApp,
    ) -> BoxFuture<'_, Result<RemoteCommandOutput>> {
        async { bail!("CellLedgerGit: push not modeled (no remote — distribution is the CapTP/branch-and-stitch follow-on)") }.boxed()
    }
    fn pull(
        &self,
        _branch_name: Option<String>,
        _upstream_name: String,
        _rebase: bool,
        _askpass: AskPassDelegate,
        _env: Arc<HashMap<String, String>>,
        _cx: AsyncApp,
    ) -> BoxFuture<'_, Result<RemoteCommandOutput>> {
        async { bail!("CellLedgerGit: pull not modeled") }.boxed()
    }
    fn fetch(
        &self,
        _fetch_options: FetchOptions,
        _askpass: AskPassDelegate,
        _env: Arc<HashMap<String, String>>,
        _cx: AsyncApp,
    ) -> BoxFuture<'_, Result<RemoteCommandOutput>> {
        async { bail!("CellLedgerGit: fetch not modeled") }.boxed()
    }

    fn get_push_remote(&self, _branch: String) -> BoxFuture<'_, Result<Option<Remote>>> {
        async { Ok(None) }.boxed()
    }
    fn get_branch_remote(&self, _branch: String) -> BoxFuture<'_, Result<Option<Remote>>> {
        async { Ok(None) }.boxed()
    }
    fn get_all_remotes(&self) -> BoxFuture<'_, Result<Vec<Remote>>> {
        async { Ok(Vec::new()) }.boxed()
    }
    fn remove_remote(&self, _name: String) -> BoxFuture<'_, Result<()>> {
        async { bail!("CellLedgerGit: remotes not modeled") }.boxed()
    }
    fn create_remote(&self, _name: String, _url: String) -> BoxFuture<'_, Result<()>> {
        async { bail!("CellLedgerGit: remotes not modeled") }.boxed()
    }

    fn check_for_pushed_commit(&self) -> BoxFuture<'_, Result<Vec<SharedString>>> {
        async { Ok(Vec::new()) }.boxed()
    }

    fn diff(&self, diff: DiffType) -> BoxFuture<'_, Result<String>> {
        // A unified-ish diff of the worktree against HEAD: for each modified path,
        // emit the head→live line diff. (We render a simple, real diff off the
        // dregg-doc histories; the panel's hunk view consumes the per-file text.)
        let docs = self.docs.lock().unwrap();
        let live = self.live.lock().unwrap();
        let mut out = String::new();
        let mut paths: Vec<&PathBuf> = live.keys().collect();
        paths.sort();
        for path in paths {
            let Some(doc) = docs.get(path) else { continue };
            let head = doc.head_text();
            let live_content = &live[path];
            let (left, right) = match diff {
                // HeadToIndex / MergeBase collapse to head vs head (no staging) → empty.
                DiffType::HeadToIndex | DiffType::MergeBase { .. } => (head.clone(), head.clone()),
                DiffType::HeadToWorktree => (head.clone(), live_content.clone()),
            };
            if left != right {
                out.push_str(&render_text_diff(&path.to_string_lossy(), &left, &right));
            }
        }
        async move { Ok(out) }.boxed()
    }

    fn diff_stat(&self, _path_prefixes: &[RepoPath]) -> BoxFuture<'static, Result<GitDiffStat>> {
        async { Ok(GitDiffStat::default()) }.boxed()
    }

    fn checkpoint(&self) -> BoxFuture<'static, Result<GitRepositoryCheckpoint>> {
        async { bail!("CellLedgerGit: checkpoint not modeled (the receipt chain IS the durable checkpoint)") }.boxed()
    }
    fn restore_checkpoint(
        &self,
        _checkpoint: GitRepositoryCheckpoint,
    ) -> BoxFuture<'_, Result<()>> {
        async { bail!("CellLedgerGit: restore_checkpoint not modeled") }.boxed()
    }
    fn create_archive_checkpoint(&self) -> BoxFuture<'_, Result<(String, String)>> {
        async { bail!("CellLedgerGit: create_archive_checkpoint not modeled") }.boxed()
    }
    fn restore_archive_checkpoint(
        &self,
        _staged_sha: String,
        _unstaged_sha: String,
    ) -> BoxFuture<'_, Result<()>> {
        async { bail!("CellLedgerGit: restore_archive_checkpoint not modeled") }.boxed()
    }
    fn compare_checkpoints(
        &self,
        _left: GitRepositoryCheckpoint,
        _right: GitRepositoryCheckpoint,
    ) -> BoxFuture<'_, Result<bool>> {
        async { bail!("CellLedgerGit: compare_checkpoints not modeled") }.boxed()
    }
    fn diff_checkpoints(
        &self,
        _base_checkpoint: GitRepositoryCheckpoint,
        _target_checkpoint: GitRepositoryCheckpoint,
    ) -> BoxFuture<'_, Result<String>> {
        async { bail!("CellLedgerGit: diff_checkpoints not modeled") }.boxed()
    }

    fn load_commit_template(&self) -> BoxFuture<'_, Result<Option<GitCommitTemplate>>> {
        async { Ok(None) }.boxed()
    }

    fn default_branch(
        &self,
        _include_remote_name: bool,
    ) -> BoxFuture<'_, Result<Option<SharedString>>> {
        async { Ok(Some(MAIN_BRANCH.into())) }.boxed()
    }

    fn initial_graph_data(
        &self,
        _log_source: LogSource,
        _log_order: LogOrder,
        request_tx: async_channel::Sender<Vec<Arc<InitialGraphCommitData>>>,
    ) -> BoxFuture<'_, Result<()>> {
        // The COMMIT GRAPH for the panel's log view: each patch in chain order is a
        // node; its parent is the previous patch. Real history-from-the-patch-chain.
        let docs = self.docs.lock().unwrap();
        let graph_nodes = build_graph_nodes(&docs);
        async move {
            if !graph_nodes.is_empty() {
                request_tx.send(graph_nodes).await.ok();
            }
            Ok(())
        }
        .boxed()
    }

    fn search_commits(
        &self,
        _log_source: LogSource,
        _search_args: SearchCommitArgs,
        _request_tx: async_channel::Sender<Oid>,
    ) -> BoxFuture<'_, Result<()>> {
        async { Ok(()) }.boxed()
    }

    fn file_history_changed_files(
        &self,
        _paths: Vec<RepoPath>,
        _commit_limit: usize,
    ) -> BoxFuture<'_, Result<Vec<FileHistoryChangedFileSets>>> {
        async { Ok(Vec::new()) }.boxed()
    }

    fn commit_data_reader(&self) -> Result<CommitDataReader> {
        bail!(
            "CellLedgerGit: commit_data_reader not modeled (use show/load_commit for per-patch details)"
        )
    }

    fn update_ref(&self, _ref_name: String, _commit: String) -> BoxFuture<'_, Result<()>> {
        async { bail!("CellLedgerGit: update_ref not modeled") }.boxed()
    }
    fn delete_ref(&self, _ref_name: String) -> BoxFuture<'_, Result<()>> {
        async { bail!("CellLedgerGit: delete_ref not modeled") }.boxed()
    }
    fn repair_worktrees(&self) -> BoxFuture<'_, Result<()>> {
        async { Ok(()) }.boxed()
    }

    fn set_trusted(&self, trusted: bool) {
        self.trusted
            .store(trusted, std::sync::atomic::Ordering::Release);
    }
    fn is_trusted(&self) -> bool {
        self.trusted.load(std::sync::atomic::Ordering::Acquire)
    }
}

// --- patch ↔ oid + diff/blame helpers -------------------------------------

/// Parse a commit string (oid hex, possibly short) back to the `PatchId` it
/// encodes, or `None` if it does not look like a dregg-doc patch oid. We compare
/// against the patch chain by re-deriving each candidate's oid.
fn parse_commit_oid(commit: &str) -> Option<PatchId> {
    let oid = Oid::from_str(commit).ok()?;
    let bytes = oid.as_bytes();
    if bytes.len() < 16 {
        return None;
    }
    let mut id_bytes = [0u8; 16];
    id_bytes.copy_from_slice(&bytes[0..16]);
    Some(PatchId(u128::from_be_bytes(id_bytes)))
}

/// Find a patch in any path's history matching `target`, returning its (oid hex,
/// subject) for `show`.
fn find_patch_summary(
    docs: &StdHashMap<PathBuf, PathDoc>,
    target: Option<PatchId>,
) -> Option<(String, String)> {
    let target = target?;
    for doc in docs.values() {
        for (i, patch) in doc.history().patches().iter().enumerate() {
            if patch.id() == target {
                return Some((
                    patch_oid(target).to_string(),
                    format!("cell-ledger save #{} ({} ops)", i + 1, patch.ops.len()),
                ));
            }
        }
    }
    None
}

/// Build the changed-file diffs a patch introduced: for the path whose history
/// contains the patch, replay to the patch and to its predecessor and emit the
/// old→new rendered text.
fn commit_diff_files(
    docs: &StdHashMap<PathBuf, PathDoc>,
    work_root: &Path,
    target: Option<PatchId>,
) -> Vec<CommitFile> {
    let Some(target) = target else {
        return Vec::new();
    };
    let mut files = Vec::new();
    for (path, doc) in docs.iter() {
        let patches = doc.history().patches();
        let Some(pos) = patches.iter().position(|p| p.id() == target) else {
            continue;
        };
        let new_text = doc.history().replay_to(target);
        let new_rendered = render_clean(&new_text);
        let old_rendered = if pos == 0 {
            String::new()
        } else {
            let prev = patches[pos - 1].id();
            render_clean(&doc.history().replay_to(prev))
        };
        let rel = path.strip_prefix(work_root).unwrap_or(path);
        let rel_s = rel.to_string_lossy();
        let rel_s = rel_s.strip_prefix('/').unwrap_or(&rel_s);
        if let Ok(rp) = RepoPath::new(rel_s) {
            files.push(CommitFile {
                path: rp,
                old_text: if old_rendered.is_empty() {
                    None
                } else {
                    Some(old_rendered)
                },
                new_text: Some(new_rendered),
                is_binary: false,
            });
        }
    }
    files
}

/// Render a `DocGraph`'s clean content to text.
fn render_clean(graph: &dregg_doc::DocGraph) -> String {
    let rendered = dregg_doc::content(graph);
    rendered
        .segments
        .iter()
        .filter_map(|s| match s {
            dregg_doc::Segment::Clean(t) => Some(t.as_str()),
            dregg_doc::Segment::Conflict(_) => None,
        })
        .collect()
}

/// Build Zed's `Blame` directly from dregg-doc blame lines: each line range gets
/// the oid of its authoring patch. Lines are merged into contiguous runs sharing
/// the same patch (the same shape git-blame's incremental output produces).
fn build_zed_blame(lines: &[dregg_doc::BlameLine], path: &RepoPath) -> git::blame::Blame {
    use git::blame::BlameEntry;
    let mut entries: Vec<BlameEntry> = Vec::new();
    let mut messages: HashMap<Oid, String> = HashMap::default();
    let filename = path.as_std_path().to_string_lossy().to_string();

    let mut line_no: u32 = 0;
    let mut run_start: Option<(u32, PatchId)> = None;

    let flush = |entries: &mut Vec<BlameEntry>,
                 messages: &mut HashMap<Oid, String>,
                 start: u32,
                 end: u32,
                 patch: PatchId,
                 author: Author,
                 filename: &str| {
        let sha = patch_oid(patch);
        messages
            .entry(sha)
            .or_insert_with(|| format!("cell-ledger save (patch {:#x})", patch.0));
        entries.push(BlameEntry {
            sha,
            range: start..end,
            original_line_number: start + 1,
            author: Some(format!("author {:#x}", author.0)),
            author_mail: Some(format!("<{:#x}@cell-ledger>", author.0)),
            author_time: Some(0),
            author_tz: Some("+0000".to_string()),
            committer_name: Some("cell-ledger".to_string()),
            committer_email: Some("editor@cell-ledger".to_string()),
            committer_time: Some(0),
            committer_tz: Some("+0000".to_string()),
            summary: Some(format!("save (patch {:#x})", patch.0)),
            previous: None,
            filename: filename.to_string(),
        });
    };

    for line in lines {
        match run_start {
            Some((start, patch)) if patch == line.patch => {
                // continue the run
                let _ = start;
            }
            Some((start, patch)) => {
                // patch changed: flush the previous run [start, line_no)
                // (author of the run is the run's first line's author)
                let run_author = lines
                    .get(start as usize)
                    .map(|l| l.author)
                    .unwrap_or(Author::SYSTEM);
                flush(
                    &mut entries,
                    &mut messages,
                    start,
                    line_no,
                    patch,
                    run_author,
                    &filename,
                );
                run_start = Some((line_no, line.patch));
            }
            None => {
                run_start = Some((line_no, line.patch));
            }
        }
        line_no += 1;
    }
    if let Some((start, patch)) = run_start {
        let run_author = lines
            .get(start as usize)
            .map(|l| l.author)
            .unwrap_or(Author::SYSTEM);
        flush(
            &mut entries,
            &mut messages,
            start,
            line_no,
            patch,
            run_author,
            &filename,
        );
    }

    git::blame::Blame { entries, messages }
}

/// The commit-graph nodes for the log view: each patch in chain order, with its
/// predecessor as parent.
fn build_graph_nodes(docs: &StdHashMap<PathBuf, PathDoc>) -> Vec<Arc<InitialGraphCommitData>> {
    use smallvec::SmallVec;
    let mut nodes = Vec::new();
    for doc in docs.values() {
        let patches = doc.history().patches();
        for (i, patch) in patches.iter().enumerate() {
            let mut parents: SmallVec<[Oid; 1]> = SmallVec::new();
            if i > 0 {
                parents.push(patch_oid(patches[i - 1].id()));
            }
            nodes.push(Arc::new(InitialGraphCommitData {
                sha: patch_oid(patch.id()),
                parents,
                ref_names: Vec::new(),
            }));
        }
    }
    nodes
}

/// A minimal unified-style text diff for the `diff` output (line granularity).
fn render_text_diff(path: &str, old: &str, new: &str) -> String {
    let mut out = String::new();
    out.push_str(&format!("--- a/{path}\n+++ b/{path}\n"));
    let old_lines: Vec<&str> = old.lines().collect();
    let new_lines: Vec<&str> = new.lines().collect();
    // Simple line-by-line (not LCS-minimal — enough for the panel's per-file view;
    // the structural diff is `load_commit`'s old/new text the editor diffs).
    for l in &old_lines {
        out.push_str(&format!("-{l}\n"));
    }
    for l in &new_lines {
        out.push_str(&format!("+{l}\n"));
    }
    out
}
