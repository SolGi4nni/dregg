//! `clone` — fetch a repo at a pinned commit (the source commitment).
//!
//! Step ① of the deploy: `git clone` the repo (a remote URL, a `file://`, or a local path)
//! into a working directory and resolve the checked-out `HEAD` to its full commit hash. That
//! hash is the **source commitment** — it lands in the deploy receipt and is folded into the
//! published tree's `content_root`, so "this site was built from THAT commit" is provable.
//!
//! The clone source is tenant-controlled untrusted input, so before touching git the URL is
//! refused if it can turn a clone into command execution (the `ext::sh -c …` transport, a
//! leading-`-` URL becoming a git option, or a non-allowlisted transport scheme), and git is
//! pinned to the `file`/`https` transports via `GIT_ALLOW_PROTOCOL`.

use std::path::{Path, PathBuf};
use std::process::Command;

use serde::{Deserialize, Serialize};

/// The result of cloning: where the tree landed + the commit it is pinned at.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CloneResult {
    /// The working directory the repo was cloned into.
    pub workdir: PathBuf,
    /// The full 40-hex commit hash of the checked-out `HEAD`.
    pub commit: String,
}

/// Clone `repo_url` (optionally at `git_ref`) into `into`, returning the resolved commit.
///
/// `into` is created fresh: an existing clone is reused ONLY when its on-disk origin URL and
/// commit match THIS request (the idempotent resumed-activity case — a replayed Clone never
/// re-fetches). `git_ref` may be a branch, tag, or commit; `None` takes the remote's default
/// branch. A clone failure (bad URL/ref, no network, no git) fails closed — never publishing
/// an un-sourced site.
pub fn clone_repo(
    repo_url: &str,
    git_ref: Option<&str>,
    into: &Path,
) -> anyhow::Result<CloneResult> {
    // Refuse the transports that turn a clone into RCE before touching git.
    validate_repo_url(repo_url)?;

    // Idempotent reuse: a present clone is reused ONLY when its origin URL and (pinned)
    // commit match THIS request. A resume whose spec changed (a different repo, or a moved
    // ref) must NOT publish the stale tree under the new claimed commit — a mismatch falls
    // through to a fresh re-clone rather than returning the old head.
    if into.join(".git").is_dir() {
        if reuse_is_valid(into, repo_url, git_ref) {
            if let Ok(commit) = head_commit(into) {
                return Ok(CloneResult {
                    workdir: into.to_path_buf(),
                    commit,
                });
            }
        }
    }
    if into.exists() {
        std::fs::remove_dir_all(into)
            .map_err(|e| anyhow::anyhow!("clear workdir {}: {e}", into.display()))?;
    }
    if let Some(parent) = into.parent() {
        std::fs::create_dir_all(parent)
            .map_err(|e| anyhow::anyhow!("create workdir parent {}: {e}", parent.display()))?;
    }

    // A shallow clone of the requested ref keeps the fetch small. For a branch/tag we can
    // pass `--branch`; for a bare commit we clone then check it out.
    let mut cmd = git_command();
    cmd.arg("clone").arg("--depth").arg("1");
    let mut needs_checkout: Option<&str> = None;
    if let Some(r) = git_ref {
        if is_probably_ref_name(r) {
            cmd.arg("--branch").arg(r);
        } else {
            needs_checkout = Some(r);
        }
    }
    // `--` terminates options so a leading-`-` URL/ref can't become a git flag.
    cmd.arg("--").arg(repo_url).arg(into);
    run_git(&mut cmd, "clone")?;

    if let Some(commitish) = needs_checkout {
        // The shallow clone may not contain an arbitrary commit; deepen, then check it out.
        run_git(
            git_command()
                .arg("-C")
                .arg(into)
                .arg("fetch")
                .arg("--depth")
                .arg("1")
                .arg("origin")
                .arg("--")
                .arg(commitish),
            "fetch ref",
        )
        .ok();
        run_git(
            git_command()
                .arg("-C")
                .arg(into)
                .arg("checkout")
                .arg("--")
                .arg(commitish),
            "checkout",
        )?;
    }

    let commit = head_commit(into)?;
    Ok(CloneResult {
        workdir: into.to_path_buf(),
        commit,
    })
}

/// Resolve a working tree's `HEAD` to its full commit hash.
pub fn head_commit(workdir: &Path) -> anyhow::Result<String> {
    let out = Command::new("git")
        .arg("-C")
        .arg(workdir)
        .arg("rev-parse")
        .arg("HEAD")
        .output()
        .map_err(|e| anyhow::anyhow!("run `git rev-parse`: {e}"))?;
    if !out.status.success() {
        anyhow::bail!(
            "git rev-parse HEAD failed: {}",
            String::from_utf8_lossy(&out.stderr).trim()
        );
    }
    let commit = String::from_utf8_lossy(&out.stdout).trim().to_string();
    if commit.is_empty() {
        anyhow::bail!("git rev-parse HEAD returned empty");
    }
    Ok(commit)
}

/// A `git` invocation pinned to the safe transports. `GIT_ALLOW_PROTOCOL` whitelists
/// `file`/`https` and thereby *blocks* `ext::` (the `git clone "ext::sh -c <cmd>"` RCE) and
/// other smart-protocol transports.
fn git_command() -> Command {
    let mut cmd = Command::new("git");
    cmd.env("GIT_ALLOW_PROTOCOL", "file:https");
    cmd
}

/// Refuse a deploy source URL that turns a clone into command execution: a leading `-`
/// (becomes a git option), the `ext::` transport (runs an arbitrary command), and any
/// explicit scheme outside the `https`/`file` allowlist. A bare local path (a dev/file
/// fixture) carries no `://` and is allowed; `GIT_ALLOW_PROTOCOL` is the belt to this braces.
fn validate_repo_url(repo_url: &str) -> anyhow::Result<()> {
    let url = repo_url.trim();
    if url.is_empty() {
        anyhow::bail!("empty repo url");
    }
    if url.starts_with('-') {
        anyhow::bail!("repo url `{url}` may not start with `-` (would be parsed as a git option)");
    }
    let lower = url.to_ascii_lowercase();
    if lower.contains("ext::") {
        anyhow::bail!(
            "repo url `{url}` uses the `ext::` transport (arbitrary command execution) — refused"
        );
    }
    // If the URL names an explicit transport scheme, it must be in the allowlist. A path with
    // no `scheme://` (a local clone source) is permitted and gated by GIT_ALLOW_PROTOCOL.
    if let Some((scheme, _)) = lower.split_once("://") {
        let allowed = matches!(scheme, "https" | "http" | "file");
        if !allowed {
            anyhow::bail!(
                "repo url scheme `{scheme}://` is not allowed (only https/file); `{url}` refused"
            );
        }
    }
    Ok(())
}

/// Whether an on-disk clone at `into` may be reused for THIS request: its origin URL must
/// equal `repo_url`, and — when `git_ref` pins a specific commit — its `HEAD` must be that
/// commit. A moved branch/tag can't be cheaply re-verified offline, so the origin match is
/// the gate there; any mismatch returns `false` → the caller re-clones.
fn reuse_is_valid(into: &Path, repo_url: &str, git_ref: Option<&str>) -> bool {
    match origin_url(into) {
        Some(origin) if same_origin(&origin, repo_url) => {}
        _ => return false,
    }
    if let Some(r) = git_ref {
        // A raw commit hash request must match the checked-out HEAD (prefix-aware).
        if !is_probably_ref_name(r) {
            match head_commit(into) {
                Ok(head) if head.starts_with(r) || r.starts_with(&head) => {}
                _ => return false,
            }
        }
    }
    true
}

/// The configured `origin` remote URL of the clone at `into`, if any.
fn origin_url(into: &Path) -> Option<String> {
    let out = Command::new("git")
        .arg("-C")
        .arg(into)
        .arg("config")
        .arg("--get")
        .arg("remote.origin.url")
        .output()
        .ok()?;
    if !out.status.success() {
        return None;
    }
    let s = String::from_utf8_lossy(&out.stdout).trim().to_string();
    if s.is_empty() {
        None
    } else {
        Some(s)
    }
}

/// Compare a stored origin URL against a requested one, tolerant of the `.git` suffix and
/// (for local sources) path canonicalization, but treating different repos as different.
fn same_origin(stored: &str, requested: &str) -> bool {
    let norm = |s: &str| -> String {
        let s = s.trim().trim_end_matches('/');
        let s = s.strip_suffix(".git").unwrap_or(s);
        std::fs::canonicalize(s)
            .ok()
            .and_then(|p| p.to_str().map(str::to_string))
            .unwrap_or_else(|| s.to_string())
    };
    norm(stored) == norm(requested)
}

/// Whether `r` looks like a branch/tag name (safe for `git clone --branch`) rather than a
/// raw commit hash. A 7..=40-hex string is treated as a commit.
fn is_probably_ref_name(r: &str) -> bool {
    let looks_hex = r.len() >= 7 && r.len() <= 40 && r.bytes().all(|b| b.is_ascii_hexdigit());
    !looks_hex
}

fn run_git(cmd: &mut Command, what: &str) -> anyhow::Result<()> {
    let out = cmd
        .output()
        .map_err(|e| anyhow::anyhow!("run `git {what}`: {e}"))?;
    if !out.status.success() {
        anyhow::bail!(
            "git {what} failed: {}",
            String::from_utf8_lossy(&out.stderr).trim()
        );
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::process::Command;

    /// Build a tiny local git repo fixture with one commit, return (dir, commit).
    pub(crate) fn fixture_repo(files: &[(&str, &str)]) -> (tempfile::TempDir, String) {
        let dir = tempfile::tempdir().unwrap();
        let p = dir.path();
        let run = |args: &[&str]| {
            let ok = Command::new("git")
                .arg("-C")
                .arg(p)
                .args(args)
                .output()
                .unwrap()
                .status
                .success();
            assert!(ok, "git {args:?} failed");
        };
        run(&["init", "-q"]);
        run(&["config", "user.email", "t@example.test"]);
        run(&["config", "user.name", "deploy test"]);
        run(&["config", "commit.gpgsign", "false"]);
        for (path, body) in files {
            let fp = p.join(path);
            if let Some(parent) = fp.parent() {
                std::fs::create_dir_all(parent).unwrap();
            }
            std::fs::write(fp, body).unwrap();
        }
        run(&["add", "-A"]);
        run(&["commit", "-q", "-m", "fixture"]);
        let commit = head_commit(p).unwrap();
        (dir, commit)
    }

    #[test]
    fn clones_a_local_repo_at_its_head() {
        let (src, commit) = fixture_repo(&[("index.html", "<h1>fixture</h1>")]);
        let dst = tempfile::tempdir().unwrap();
        let into = dst.path().join("repo");
        let res = clone_repo(src.path().to_str().unwrap(), None, &into).unwrap();
        assert_eq!(res.commit, commit, "cloned commit matches the source HEAD");
        assert!(
            into.join("index.html").is_file(),
            "the tree is materialized"
        );
    }

    #[test]
    fn reclone_into_existing_clone_is_idempotent() {
        let (src, commit) = fixture_repo(&[("index.html", "<h1>x</h1>")]);
        let dst = tempfile::tempdir().unwrap();
        let into = dst.path().join("repo");
        let a = clone_repo(src.path().to_str().unwrap(), None, &into).unwrap();
        let b = clone_repo(src.path().to_str().unwrap(), None, &into).unwrap();
        assert_eq!(a.commit, commit);
        assert_eq!(b.commit, commit);
    }

    /// A resume whose spec changed to a DIFFERENT repo must NOT reuse the old tree (which
    /// would publish stale bytes under the new claimed source). The origin mismatch forces a
    /// fresh re-clone, so the returned commit is the NEW repo's HEAD.
    #[test]
    fn reuse_with_a_changed_repo_reclones_not_stale() {
        let (src_a, commit_a) = fixture_repo(&[("index.html", "<h1>A</h1>")]);
        let (src_b, commit_b) = fixture_repo(&[("index.html", "<h1>B</h1>")]);
        assert_ne!(commit_a, commit_b);
        let dst = tempfile::tempdir().unwrap();
        let into = dst.path().join("repo");

        let a = clone_repo(src_a.path().to_str().unwrap(), None, &into).unwrap();
        assert_eq!(a.commit, commit_a);

        let b = clone_repo(src_b.path().to_str().unwrap(), None, &into).unwrap();
        assert_eq!(
            b.commit, commit_b,
            "a changed repo spec must re-clone, not reuse the stale tree"
        );
        let body = std::fs::read_to_string(into.join("index.html")).unwrap();
        assert_eq!(
            body, "<h1>B</h1>",
            "the materialized tree is the new repo's"
        );
    }

    #[test]
    fn reuse_is_valid_gates_on_origin_and_commit() {
        let (src, commit) = fixture_repo(&[("index.html", "<h1>x</h1>")]);
        let dst = tempfile::tempdir().unwrap();
        let into = dst.path().join("repo");
        clone_repo(src.path().to_str().unwrap(), None, &into).unwrap();
        let url = src.path().to_str().unwrap();

        assert!(reuse_is_valid(&into, url, None));
        assert!(reuse_is_valid(&into, url, Some(&commit)));
        assert!(!reuse_is_valid(
            &into,
            url,
            Some("0000000000000000000000000000000000000000")
        ));
        let (other, _) = fixture_repo(&[("index.html", "<h1>y</h1>")]);
        assert!(!reuse_is_valid(&into, other.path().to_str().unwrap(), None));
    }

    /// An `ext::` transport repo URL (clone-time RCE) is refused before git runs.
    #[test]
    fn ext_transport_url_is_refused() {
        let into = tempfile::tempdir().unwrap().path().join("repo");
        let err = clone_repo("ext::sh -c 'touch /tmp/pwned'", None, &into).unwrap_err();
        assert!(err.to_string().contains("ext::"), "got {err}");
    }

    /// A leading-`-` repo URL (parsed as a git option) is refused.
    #[test]
    fn leading_dash_url_is_refused() {
        let into = tempfile::tempdir().unwrap().path().join("repo");
        let err = clone_repo("--upload-pack=touch /tmp/pwned", None, &into).unwrap_err();
        assert!(err.to_string().contains("may not start with"), "got {err}");
    }

    /// A non-allowlisted explicit scheme is refused; https/file are allowed.
    #[test]
    fn scheme_allowlist() {
        assert!(validate_repo_url("https://example.com/r.git").is_ok());
        assert!(validate_repo_url("file:///srv/r.git").is_ok());
        assert!(validate_repo_url("/local/abs/path").is_ok());
        assert!(validate_repo_url("git://example.com/r.git").is_err());
        assert!(validate_repo_url("ssh://git@h/r.git").is_err());
    }
}
