//! **The dregg-native forge's VISUAL surface** — a repo / diff / pull-request /
//! review-thread projected as a serializable [`ViewNode`] tree, so the forge paints in
//! EVERY glass (cockpit gpui, browser HTML, Discord embed, terminal) from ONE piece of
//! DATA (renderer-independence), exactly like the chat card ([`deos_matrix::chat_view`])
//! and the reflective cockpit cards.
//!
//! ## Why a SELF-CONTAINED data model (no `dregg-doc` dep)
//!
//! The forge CORE — `PullRequest` / the pushout `merge` / `ConflictRegion` / the
//! `ProofCondition` CI gate / the review stitcher — lives in the EXCLUDED `dregg-doc`
//! workspace (`docs/deos/DREGG-FORGE.md`). Depending on it here would drag that whole
//! graph into `deos-view`'s tiny renderer crate. So this module defines a PLAIN,
//! serializable snapshot of the forge core's real concepts ([`ForgeView`] / [`Repo`] /
//! [`PullRequest`] / [`DiffHunk`] / [`ConflictView`] / [`CheckView`] / [`ReviewEntry`])
//! and renders THAT. The data these types carry is already computed by
//! `deos-zed-full/src/cell_git.rs` (`status`/`blame`/`show`/`diff`/`branches`), whose
//! `CommitDiff`/`FileStatus`/`ConflictRegion` shapes this mirrors faithfully — the live
//! wiring (a `From<PullRequest>` in `dregg-doc` → [`ForgeView`]) is a thin follow-up.
//! This is the SAME opaque-data-at-the-boundary decoupling `card_carry` used.
//!
//! ## The tree it paints
//!
//! A `tabs` of two panels — **repo** (the tracked-file list, each with its
//! modified-since-HEAD status) and **pull request** (a `base → head` header, the
//! check statuses as pills, a MERGE-GATE line, the diff as add/del rows, conflicts as
//! first-class attributed regions, and the review thread as attributed comment/approval
//! rows). Every empty case renders an HONEST empty state (never fabricated content).
//!
//! It is PURE `serde_json` + [`crate::tree`] (no `dregg-doc`, no gpui, no mozjs), so it
//! rides BOTH renderers: the ViewNode is built by [`crate::parse_view_tree`]-ing the
//! canonical JSON, guaranteeing [`forge_view`] and [`forge_view_json`] are the SAME
//! tree, and the web renderer ([`crate::web::render_html`], under `feature = "web"`)
//! paints the identical card in a browser.

use serde::{Deserialize, Serialize};
use serde_json::{json, Value};

use crate::tree::{parse_view_tree, ViewNode};

// ─────────────────────────────────────────────────────────────────────────────
// THE DATA MODEL — a plain, serializable snapshot of the forge core's concepts.
// ─────────────────────────────────────────────────────────────────────────────

/// **The whole forge surface** — a repository plus (optionally) the pull-request under
/// review. The top-level object [`forge_view`] projects into a `tabs` tree. A `None`
/// [`ForgeView::pull_request`] renders the PR tab's honest "no open pull request" state.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct ForgeView {
    /// The repository being browsed (a cell / path-tree of cells, in the forge core).
    pub repo: Repo,
    /// The pull request under review, if one is open (a fork's divergence + its review).
    pub pull_request: Option<PullRequest>,
}

/// A **repository** — a name and its tracked files (each with a worktree status). In the
/// forge core a repo IS a cell (or a path-tree of cells); `files` mirrors `cell_git`'s
/// `status` output (modified-since-HEAD per path).
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct Repo {
    /// The repo's display name (the cell's handle).
    pub name: String,
    /// The tracked files, each with its worktree status (`cell_git::status`).
    pub files: Vec<FileEntry>,
}

/// One tracked file + its worktree status against HEAD (mirrors `cell_git`'s per-path
/// `FileStatus`: a path whose cell changed since its last committed patch is `Modified`).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FileEntry {
    /// The repo-relative path.
    pub path: String,
    /// Its status against the HEAD patch.
    pub status: FileStatus,
}

/// A file's worktree status against HEAD — the plain mirror of `cell_git`'s `StatusCode`
/// / `FileStatus` (the receipt-chain-derived modified-since-HEAD read).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum FileStatus {
    /// Committed and unchanged since its last patch.
    Unmodified,
    /// Changed in the worktree since HEAD (a save not yet a commit/patch).
    Modified,
    /// Newly created since the fork base.
    Added,
    /// Removed since the fork base.
    Deleted,
    /// Present but not yet tracked by any patch.
    Untracked,
}

impl FileStatus {
    /// A one-word label + the semantic palette tag the renderer tints the status pill.
    fn label_tag(self) -> (&'static str, &'static str) {
        match self {
            FileStatus::Unmodified => ("unmodified", "muted"),
            FileStatus::Modified => ("modified", "warn"),
            FileStatus::Added => ("added", "good"),
            FileStatus::Deleted => ("deleted", "bad"),
            FileStatus::Untracked => ("untracked", "accent"),
        }
    }
}

/// A **pull request** — a fork's divergence under review. `base`/`head` name the two
/// forks (the pushout merge's inputs); `diff` is the divergence; `conflicts` are the
/// first-class `ConflictRegion`s a stitch surfaced; `checks` are the CI gates (verified
/// turns whose receipts gate the merge); `review` is the attributed review thread.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct PullRequest {
    /// The PR's title.
    pub title: String,
    /// The base branch/fork (the merge target).
    pub base: String,
    /// The head branch/fork (the proposed change).
    pub head: String,
    /// The diff of `base → head` (the two forks' divergence), grouped by file.
    pub diff: Vec<DiffHunk>,
    /// The first-class conflict regions a stitch surfaced (empty = a clean pushout).
    pub conflicts: Vec<ConflictView>,
    /// The CI checks (each a verified turn whose receipt gates the merge).
    pub checks: Vec<CheckView>,
    /// The attributed review thread (comments + approvals).
    pub review: Vec<ReviewEntry>,
}

/// A per-file diff hunk — the `base → head` divergence for one path (`cell_git`'s
/// `CommitDiff`/`CommitFile`: the old→new rendered text between two `History::replay_to`s).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DiffHunk {
    /// The file this hunk applies to.
    pub file: String,
    /// The changed lines (add / del / context).
    pub lines: Vec<DiffLine>,
}

/// One line of a diff hunk.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DiffLine {
    /// Whether the line was added, deleted, or is unchanged context.
    pub kind: DiffKind,
    /// The line text (without the +/-/space marker — the renderer supplies it).
    pub text: String,
}

/// A diff line's kind — added / deleted / unchanged context.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum DiffKind {
    /// A line present in `head` but not `base`.
    Add,
    /// A line present in `base` but not `head`.
    Del,
    /// A line present in both (shown for context).
    Context,
}

impl DiffKind {
    /// The gutter marker + the semantic palette tag.
    fn marker_tag(self) -> (&'static str, &'static str) {
        match self {
            DiffKind::Add => ("+", "good"),
            DiffKind::Del => ("−", "bad"),
            DiffKind::Context => (" ", "muted"),
        }
    }
}

/// A **first-class conflict region** — the two divergent alternatives, each ATTRIBUTED to
/// its author (a plain mirror of `dregg-doc`'s `ConflictRegion` / `resolution`). A stitch
/// that cannot pushout-merge surfaces this rather than silently overwriting; the review
/// resolves it by a verified patch.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConflictView {
    /// The file the conflict is in.
    pub file: String,
    /// The base side's author.
    pub ours_author: String,
    /// The base side's text.
    pub ours: String,
    /// The head side's author.
    pub theirs_author: String,
    /// The head side's text.
    pub theirs: String,
}

/// A **CI check** — a named verified turn whose receipt gates the merge (a `ProofCondition`
/// in the forge core). `name` + a pass/fail/pending status.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CheckView {
    /// The check's name (e.g. `build`, `test`, `proof`).
    pub name: String,
    /// Its status.
    pub status: CheckStatus,
}

/// A CI check's status.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum CheckStatus {
    /// The check's verified turn committed (its receipt is present).
    Passed,
    /// The check's turn was refused / the receipt records a failure.
    Failed,
    /// The check has not reported yet.
    Pending,
}

impl CheckStatus {
    /// A one-word label + the semantic palette tag for the check pill.
    fn label_tag(self) -> (&'static str, &'static str) {
        match self {
            CheckStatus::Passed => ("passed", "good"),
            CheckStatus::Failed => ("failed", "bad"),
            CheckStatus::Pending => ("pending", "warn"),
        }
    }
}

/// One **attributed review entry** — a comment or an approval, with its author + text
/// (the review stitcher's thread over the `ConflictRegion`s + resolutions).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReviewEntry {
    /// Who wrote it.
    pub author: String,
    /// Whether it is a comment or an approval.
    pub kind: ReviewKind,
    /// The entry's text.
    pub text: String,
}

/// A review entry's kind.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum ReviewKind {
    /// A review comment.
    Comment,
    /// An approval (a reviewer signing off).
    Approval,
}

impl ReviewKind {
    /// A short glyph-word label + the semantic palette tag for the review pill.
    fn label_tag(self) -> (&'static str, &'static str) {
        match self {
            ReviewKind::Comment => ("comment", "accent"),
            ReviewKind::Approval => ("approval", "good"),
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// THE MERGE GATE — the one derived verdict the PR header shows.
// ─────────────────────────────────────────────────────────────────────────────

/// **The merge-gate verdict** — the single derived answer the PR header renders: is this
/// PR mergeable? Conflicts block first (a first-class `ConflictRegion` must be resolved);
/// then any not-yet-passed check blocks (a CI gate's receipt is missing/failed); else the
/// pushout is clean and the PR is ready.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MergeGate {
    /// No conflicts, every check passed — the pushout is clean.
    Clean,
    /// `n` first-class conflict regions must be resolved before merge.
    Conflicts(usize),
    /// The pushout is clean but not every CI check has passed yet.
    AwaitingChecks,
}

impl MergeGate {
    /// Compute the gate for a pull request (conflicts dominate checks).
    pub fn of(pr: &PullRequest) -> MergeGate {
        if !pr.conflicts.is_empty() {
            MergeGate::Conflicts(pr.conflicts.len())
        } else if pr.checks.iter().any(|c| c.status != CheckStatus::Passed) {
            MergeGate::AwaitingChecks
        } else {
            MergeGate::Clean
        }
    }

    /// The gate line's text + the semantic palette tag.
    fn label_tag(self) -> (String, &'static str) {
        match self {
            MergeGate::Clean => ("✓ ready to merge — clean pushout".to_string(), "good"),
            MergeGate::Conflicts(n) => (
                format!(
                    "✗ {n} conflict{} — resolve to merge",
                    if n == 1 { "" } else { "s" }
                ),
                "bad",
            ),
            MergeGate::AwaitingChecks => (
                "◷ awaiting checks — a CI gate is not green".to_string(),
                "warn",
            ),
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// THE VIEW-TREE BUILDERS  (pure serde_json, mirroring deos_matrix::chat_view)
// ─────────────────────────────────────────────────────────────────────────────

/// A `deos.ui.text` node.
fn text(s: impl Into<String>) -> Value {
    json!({ "kind": "text", "props": { "text": s.into() } })
}

/// A `deos.ui.pill` node — a colored status badge (`tag` selects the semantic palette).
fn pill(s: impl Into<String>, tag: &str) -> Value {
    json!({ "kind": "pill", "props": { "text": s.into(), "tag": tag } })
}

/// A `deos.ui.row` node — a horizontal flex of children.
fn row(children: Vec<Value>) -> Value {
    json!({ "kind": "row", "props": {}, "children": children })
}

/// A `deos.ui.list` node — a vertical list of the child nodes.
fn list(children: Vec<Value>) -> Value {
    json!({ "kind": "list", "props": {}, "children": children })
}

/// A `deos.ui.vstack` node — a vertical column of the child nodes.
fn vstack(children: Vec<Value>) -> Value {
    json!({ "kind": "vstack", "props": {}, "children": children })
}

/// A `deos.ui.section` node — a titled, bordered container (`tag` = a styling accent).
fn section(title: &str, tag: &str, children: Vec<Value>) -> Value {
    json!({ "kind": "section", "props": { "title": title, "tag": tag }, "children": children })
}

/// A `deos.ui.divider` node — a thin horizontal rule.
fn divider() -> Value {
    json!({ "kind": "divider", "props": {} })
}

/// The repo panel: the repo name + the tracked-file list (each with its status pill), or
/// an honest empty state for a repo with no tracked files.
fn repo_panel(repo: &Repo) -> Value {
    let title = if repo.name.is_empty() {
        "repository".to_string()
    } else {
        format!("repository · {}", repo.name)
    };
    if repo.files.is_empty() {
        return section(
            &title,
            "",
            vec![text(
                "(no tracked files yet — this repo cell holds no committed patches)",
            )],
        );
    }
    let file_rows: Vec<Value> = repo
        .files
        .iter()
        .map(|f| {
            let (label, tag) = f.status.label_tag();
            row(vec![text(f.path.clone()), pill(label, tag)])
        })
        .collect();
    section(
        &title,
        "genuine",
        vec![
            pill(format!("{} file(s)", repo.files.len()), "accent"),
            list(file_rows),
        ],
    )
}

/// The diff section: one titled sub-section per file, each a list of add/del/context rows.
fn diff_section(diff: &[DiffHunk]) -> Value {
    if diff.is_empty() {
        return section(
            "diff",
            "",
            vec![text("(no changes — the forks are identical)")],
        );
    }
    let hunks: Vec<Value> = diff
        .iter()
        .map(|h| {
            let line_rows: Vec<Value> = h
                .lines
                .iter()
                .map(|l| {
                    let (marker, tag) = l.kind.marker_tag();
                    row(vec![pill(marker, tag), text(l.text.clone())])
                })
                .collect();
            section(&h.file, "", vec![list(line_rows)])
        })
        .collect();
    section("diff", "", hunks)
}

/// The conflicts section: each region as a titled sub-section with the two ATTRIBUTED
/// alternatives side by side. A clean pushout renders the honest "no conflicts" state.
fn conflicts_section(conflicts: &[ConflictView]) -> Value {
    if conflicts.is_empty() {
        return section(
            "conflicts",
            "",
            vec![text("(no conflicts — the pushout merged cleanly)")],
        );
    }
    let regions: Vec<Value> = conflicts
        .iter()
        .map(|c| {
            section(
                &c.file,
                "refusal",
                vec![
                    row(vec![
                        pill(format!("ours · {}", c.ours_author), "accent"),
                        text(c.ours.clone()),
                    ]),
                    row(vec![
                        pill(format!("theirs · {}", c.theirs_author), "warn"),
                        text(c.theirs.clone()),
                    ]),
                ],
            )
        })
        .collect();
    section(
        &format!("conflicts ({})", conflicts.len()),
        "refusal",
        regions,
    )
}

/// The checks row: one status pill per CI check, or an honest "no checks" state.
fn checks_section(checks: &[CheckView]) -> Value {
    if checks.is_empty() {
        return section("checks", "", vec![text("(no CI checks configured)")]);
    }
    let pills: Vec<Value> = checks
        .iter()
        .map(|c| {
            let (label, tag) = c.status.label_tag();
            pill(format!("{}: {}", c.name, label), tag)
        })
        .collect();
    section("checks", "", vec![row(pills)])
}

/// The review thread: one attributed row per entry (a `kind` pill + `author: text`), or an
/// honest "no reviews" state.
fn review_section(review: &[ReviewEntry]) -> Value {
    if review.is_empty() {
        return section(
            "review",
            "",
            vec![text("(no reviews yet — the thread is empty)")],
        );
    }
    let rows: Vec<Value> = review
        .iter()
        .map(|r| {
            let (label, tag) = r.kind.label_tag();
            row(vec![
                pill(label, tag),
                text(format!("{}: {}", r.author, r.text)),
            ])
        })
        .collect();
    section("review", "genuine", vec![list(rows)])
}

/// The pull-request panel: the `base → head` header + the merge-gate line, the checks, the
/// diff, the conflicts, and the review thread. A `None` PR renders the honest empty state.
fn pr_panel(pr: Option<&PullRequest>) -> Value {
    let Some(pr) = pr else {
        return section(
            "pull request",
            "",
            vec![text(
                "(no open pull request — fork the repo, diverge, and stitch to open one)",
            )],
        );
    };
    let gate = MergeGate::of(pr);
    let (gate_label, gate_tag) = gate.label_tag();

    let header = section(
        &format!("pull request · {}", pr.title),
        "",
        vec![
            row(vec![
                pill(pr.base.clone(), "muted"),
                text("→"),
                pill(pr.head.clone(), "accent"),
            ]),
            row(vec![pill(gate_label, gate_tag)]),
        ],
    );

    vstack(vec![
        header,
        checks_section(&pr.checks),
        divider(),
        diff_section(&pr.diff),
        conflicts_section(&pr.conflicts),
        review_section(&pr.review),
    ])
}

/// **The forge surface as a `deos.ui.*` view-tree** (a `serde_json::Value`) — a `tabs` of
/// the repo panel + the pull-request panel. The internal shape [`forge_view`] parses.
fn forge_value(fv: &ForgeView) -> Value {
    json!({
        "kind": "tabs",
        "props": {
            "tabs": ["repo", "pull request"],
            "selectedSlot": 0,
            "selectTurn": "",
        },
        "children": [
            repo_panel(&fv.repo),
            pr_panel(fv.pull_request.as_ref()),
        ],
    })
}

/// **The forge surface as a typed [`ViewNode`]** — the renderer-independent projection of
/// `fv`. Hand it to ANY [`crate`] renderer (native gpui / web HTML / discord embed / the
/// seL4 viewer) to paint the SAME card. Built by parsing the canonical JSON so this and
/// [`forge_view_json`] are guaranteed the identical tree.
pub fn forge_view(fv: &ForgeView) -> ViewNode {
    // The JSON is authored in-crate (the canonical `{kind, props, children}` shape), so
    // the parse cannot fail; a malformed builder would fail this in tests immediately.
    parse_view_tree(&forge_view_json(fv)).expect("the forge card JSON is well-formed")
}

/// **The forge surface as serialized `deos.ui.*` JSON** — byte-for-byte the shape a
/// [`crate`] renderer parses (via [`crate::parse_view_tree`]). This is the string the
/// cockpit mount bridges / a host serves.
pub fn forge_view_json(fv: &ForgeView) -> String {
    serde_json::to_string(&forge_value(fv)).expect("the forge card serializes")
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Recursively collect every `serde_json` node of `kind` in a value tree.
    fn collect<'a>(node: &'a Value, kind: &str, out: &mut Vec<&'a Value>) {
        if node["kind"] == kind {
            out.push(node);
        }
        if let Some(children) = node["children"].as_array() {
            for c in children {
                collect(c, kind, out);
            }
        }
    }

    fn of_kind<'a>(v: &'a Value, kind: &str) -> Vec<&'a Value> {
        let mut out = Vec::new();
        collect(v, kind, &mut out);
        out
    }

    /// Does the serialized JSON contain `needle` anywhere (a paint-content assertion).
    fn json_has(fv: &ForgeView, needle: &str) -> bool {
        forge_view_json(fv).contains(needle)
    }

    fn sample_repo() -> Repo {
        Repo {
            name: "cell-git".to_string(),
            files: vec![
                FileEntry {
                    path: "src/lib.rs".to_string(),
                    status: FileStatus::Modified,
                },
                FileEntry {
                    path: "src/new.rs".to_string(),
                    status: FileStatus::Added,
                },
                FileEntry {
                    path: "README.md".to_string(),
                    status: FileStatus::Unmodified,
                },
            ],
        }
    }

    fn sample_diff() -> Vec<DiffHunk> {
        vec![DiffHunk {
            file: "src/lib.rs".to_string(),
            lines: vec![
                DiffLine {
                    kind: DiffKind::Context,
                    text: "fn forge() {".to_string(),
                },
                DiffLine {
                    kind: DiffKind::Del,
                    text: "    old_body();".to_string(),
                },
                DiffLine {
                    kind: DiffKind::Add,
                    text: "    new_body();".to_string(),
                },
            ],
        }]
    }

    fn sample_review() -> Vec<ReviewEntry> {
        vec![
            ReviewEntry {
                author: "ada".to_string(),
                kind: ReviewKind::Comment,
                text: "please rename this".to_string(),
            },
            ReviewEntry {
                author: "grace".to_string(),
                kind: ReviewKind::Approval,
                text: "LGTM once green".to_string(),
            },
        ]
    }

    /// A CLEAN PR (no conflicts, all checks passed) shows the "ready to merge" gate.
    #[test]
    fn forge_clean_pr_shows_ready_to_merge_gate() {
        let fv = ForgeView {
            repo: sample_repo(),
            pull_request: Some(PullRequest {
                title: "add the forge card".to_string(),
                base: "main".to_string(),
                head: "forge-card".to_string(),
                diff: sample_diff(),
                conflicts: vec![],
                checks: vec![CheckView {
                    name: "build".to_string(),
                    status: CheckStatus::Passed,
                }],
                review: sample_review(),
            }),
        };
        assert_eq!(
            MergeGate::of(fv.pull_request.as_ref().unwrap()),
            MergeGate::Clean
        );
        assert!(json_has(&fv, "ready to merge"), "the clean gate renders");
        assert!(json_has(&fv, "add the forge card"), "the PR title renders");
        // The ViewNode parses (the whole tree is well-formed).
        let _ = forge_view(&fv);
    }

    /// A CONFLICTING PR shows the first-class conflict regions AND an "N conflicts" gate.
    #[test]
    fn forge_conflicting_pr_shows_conflict_regions_and_gate() {
        let fv = ForgeView {
            repo: sample_repo(),
            pull_request: Some(PullRequest {
                title: "diverging edit".to_string(),
                base: "main".to_string(),
                head: "feature".to_string(),
                diff: sample_diff(),
                conflicts: vec![
                    ConflictView {
                        file: "src/lib.rs".to_string(),
                        ours_author: "ada".to_string(),
                        ours: "let x = 1;".to_string(),
                        theirs_author: "grace".to_string(),
                        theirs: "let x = 2;".to_string(),
                    },
                    ConflictView {
                        file: "src/other.rs".to_string(),
                        ours_author: "ada".to_string(),
                        ours: "a".to_string(),
                        theirs_author: "grace".to_string(),
                        theirs: "b".to_string(),
                    },
                ],
                // Even with checks passing, conflicts dominate the gate.
                checks: vec![CheckView {
                    name: "build".to_string(),
                    status: CheckStatus::Passed,
                }],
                review: vec![],
            }),
        };
        assert_eq!(
            MergeGate::of(fv.pull_request.as_ref().unwrap()),
            MergeGate::Conflicts(2)
        );
        assert!(
            json_has(&fv, "2 conflicts"),
            "the conflict-count gate renders"
        );
        // Both attributed sides of a region are shown.
        assert!(json_has(&fv, "ours · ada"), "the base side is attributed");
        assert!(
            json_has(&fv, "theirs · grace"),
            "the head side is attributed"
        );
        assert!(
            json_has(&fv, "let x = 1;") && json_has(&fv, "let x = 2;"),
            "both divergent alternatives render"
        );
        let _ = forge_view(&fv);
    }

    /// A PR with an UNSATISFIED check shows the check pill AND an "awaiting checks" gate.
    #[test]
    fn forge_unsatisfied_check_shows_pill_and_awaiting_gate() {
        let fv = ForgeView {
            repo: sample_repo(),
            pull_request: Some(PullRequest {
                title: "needs CI".to_string(),
                base: "main".to_string(),
                head: "wip".to_string(),
                diff: sample_diff(),
                conflicts: vec![],
                checks: vec![
                    CheckView {
                        name: "build".to_string(),
                        status: CheckStatus::Passed,
                    },
                    CheckView {
                        name: "test".to_string(),
                        status: CheckStatus::Pending,
                    },
                ],
                review: vec![],
            }),
        };
        assert_eq!(
            MergeGate::of(fv.pull_request.as_ref().unwrap()),
            MergeGate::AwaitingChecks
        );
        assert!(
            json_has(&fv, "awaiting checks"),
            "the awaiting-checks gate renders"
        );
        assert!(
            json_has(&fv, "test: pending"),
            "the pending check pill renders"
        );
        let _ = forge_view(&fv);
    }

    /// The review thread renders attributed comment/approval rows.
    #[test]
    fn forge_review_thread_renders_attributed_rows() {
        let fv = ForgeView {
            repo: sample_repo(),
            pull_request: Some(PullRequest {
                title: "review me".to_string(),
                base: "main".to_string(),
                head: "topic".to_string(),
                diff: vec![],
                conflicts: vec![],
                checks: vec![],
                review: sample_review(),
            }),
        };
        let tree = forge_value(&fv);
        // The review section is a `list` of two attributed rows.
        let lists = of_kind(&tree, "list");
        assert!(!lists.is_empty(), "the review thread is a list");
        assert!(
            json_has(&fv, "ada: please rename this"),
            "the comment is attributed"
        );
        assert!(
            json_has(&fv, "grace: LGTM once green"),
            "the approval is attributed"
        );
        // Both review-kind pills present.
        assert!(
            json_has(&fv, "comment") && json_has(&fv, "approval"),
            "both review kinds render as pills"
        );
        let _ = forge_view(&fv);
    }

    /// An EMPTY repo with NO open PR renders honest empty states (no fabricated content).
    #[test]
    fn forge_empty_repo_and_no_pr_render_honest_empty_states() {
        let fv = ForgeView::default();
        assert!(
            json_has(&fv, "no tracked files yet"),
            "the empty repo says so"
        );
        assert!(
            json_has(&fv, "no open pull request"),
            "the absent PR says so"
        );
        // No file rows, no diff/conflict content are fabricated.
        let tree = forge_value(&fv);
        assert!(of_kind(&tree, "list").is_empty(), "nothing to list");
        let _ = forge_view(&fv);
    }

    /// The serialized card is well-formed JSON in the canonical `{kind, props, children}`
    /// shape, and its top node is the `tabs` (repo + pull-request panels).
    #[test]
    fn forge_serializes_to_the_canonical_tabs_shape() {
        let fv = ForgeView {
            repo: sample_repo(),
            pull_request: None,
        };
        let s = forge_view_json(&fv);
        let back: Value = serde_json::from_str(&s).expect("the forge card JSON parses");
        assert_eq!(back["kind"], "tabs");
        assert_eq!(back["props"]["tabs"][0], "repo");
        assert_eq!(back["props"]["tabs"][1], "pull request");
        assert_eq!(
            back["children"].as_array().unwrap().len(),
            2,
            "the repo panel + the PR panel"
        );
    }

    // ── THE SAME CARD PAINTS IN THE BROWSER GLASS (renderer-independence) ──
    //    Under `feature = "web"` the IDENTICAL ViewNode walks into HTML — proving the
    //    forge card is renderer-independent, not native-only.
    #[cfg(feature = "web")]
    #[test]
    fn forge_paints_in_the_browser_glass() {
        let fv = ForgeView {
            repo: sample_repo(),
            pull_request: Some(PullRequest {
                title: "browser-paint proof".to_string(),
                base: "main".to_string(),
                head: "web".to_string(),
                diff: sample_diff(),
                conflicts: vec![],
                checks: vec![CheckView {
                    name: "build".to_string(),
                    status: CheckStatus::Passed,
                }],
                review: sample_review(),
            }),
        };
        // `BindValues` is a `[u64]` slice (no `bind` nodes in the forge card → an empty
        // slice is the whole first-paint snapshot).
        let empty: &[u64] = &[];
        let html = crate::web::render_html(&forge_view(&fv), empty);
        assert!(!html.is_empty(), "the web renderer produced markup");
        // The SAME card content appears in the browser projection.
        assert!(
            html.contains("browser-paint proof"),
            "the PR title paints in HTML"
        );
        assert!(html.contains("passed"), "a check status paints in HTML");
        assert!(
            html.contains("ready to merge"),
            "the merge gate paints in HTML"
        );
    }
}
