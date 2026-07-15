//! `build` — step ③: turn the cloned tree into a `dist/` of servable bytes, cap-bounded.
//!
//! The build is the one step that runs untrusted repo code, so it is **cap-bounded**:
//!
//! - [`BuildPlan::Command`] runs a build command (e.g. `npm run build`) as a wall-clock-bounded
//!   subprocess inside the deny-default [cage](crate::sandbox) (env-cleared, `HOME`/`TMPDIR`
//!   confined, rlimited, process-group reaped), at the declared tier. The hard-isolation
//!   boundary on a fleet node is the resident `grain-jail` confined-body cage; the same `tier`
//!   selects it there. The build is *metered* against the deploy budget by the durable workflow,
//!   so a build that overruns its lease is reaped.
//! - [`BuildPlan::Compute`] runs a wasm program through the injected [`ComputeRunner`] — the
//!   genuinely empty-`Linker` build (the resident `dregg-sandbox::run_workload` weld). The
//!   default [`FailClosedComputeRunner`] is an honest fail-closed seam.
//! - [`BuildPlan::Static`] has no build step — it stages the published directory directly.
//!
//! Every path materializes its result into one canonical `dist_dir`, so the Publish step (and a
//! post-crash resume) reads a single, on-disk location. Repo-controlled paths (`publish_dir`,
//! `output_dir`) and build-output symlinks are confined under the repo root / refused — a
//! `../..` traversal or a `dist/creds -> /etc` symlink never reads a host/other-tenant file into
//! the served site.

use std::path::{Path, PathBuf};
use std::time::Duration;

use serde::{Deserialize, Serialize};

use crate::plan::{BuildPlan, BuildTier};

/// The wall-clock bound on a build command, in seconds. Overridable via
/// `GIT_DEPLOY_BUILD_TIMEOUT_SECS`.
const DEFAULT_BUILD_TIMEOUT_SECS: u64 = 300;

fn build_timeout() -> Duration {
    let secs = std::env::var("GIT_DEPLOY_BUILD_TIMEOUT_SECS")
        .ok()
        .and_then(|s| s.parse::<u64>().ok())
        .filter(|s| *s > 0)
        .unwrap_or(DEFAULT_BUILD_TIMEOUT_SECS);
    Duration::from_secs(secs)
}

/// A wasm compute-build workload handed to the injected [`ComputeRunner`].
#[derive(Debug, Clone)]
pub struct ComputeWorkload {
    /// The source family (`wat`/`wasm`).
    pub lang: String,
    /// The program source (WAT text, or base64/bytes per the runner's contract).
    pub source: String,
    /// The sandbox grade the workload runs at.
    pub tier: BuildTier,
}

/// The compute tier a [`BuildPlan::Compute`] build runs through — an **injection seam**.
///
/// The canonical backing is the resident owned `dregg-sandbox::run_workload`: an
/// `#![forbid(unsafe_code)]` wasmi interpreter instantiated against an EMPTY `Linker` (the guest
/// is offered NO host imports, so it reaches nothing on the host and egress is denied by
/// construction). An integrator wires that engine in with a thin adapter that maps
/// [`BuildTier`] → `dregg_sandbox::CapTier`, compiles WAT→wasm when `lang == "wat"`, and returns
/// the run's output bytes. This crate stays light (no proof/agent tree) by taking the runner as
/// a parameter rather than depending on the engine.
pub trait ComputeRunner: Send + Sync {
    /// Run `workload` in the cap-bounded sandbox, returning the servable artifact bytes.
    fn run(&self, workload: &ComputeWorkload) -> anyhow::Result<Vec<u8>>;
}

/// The default compute runner: an honest fail-closed seam. A [`BuildPlan::Compute`] build with
/// no injected runner is refused with a pointer to the `dregg-sandbox` weld rather than silently
/// producing nothing (or, worse, running the workload unsandboxed).
pub struct FailClosedComputeRunner;

impl ComputeRunner for FailClosedComputeRunner {
    fn run(&self, workload: &ComputeWorkload) -> anyhow::Result<Vec<u8>> {
        anyhow::bail!(
            "no compute runner injected for a `compute` build (`{}` @ {:?}); wire the resident \
             dregg-sandbox::run_workload engine in as a ComputeRunner",
            workload.lang,
            workload.tier
        )
    }
}

/// The outcome of a build: which plan ran + how many files the `dist/` holds.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BuildOutcome {
    /// The build plan that ran (`static`/`command`/`compute`).
    pub plan_label: String,
    /// How many files landed in the published `dist/`.
    pub file_count: usize,
}

/// Run `plan` against the cloned `repo_dir`, materializing the servable output into `dist_dir`
/// (created fresh), routing a [`BuildPlan::Compute`] through `compute`. Returns the
/// [`BuildOutcome`].
///
/// A [`BuildPlan::Server`] is detected-but-not-handled here: a persistent server is not a
/// static-site publish, so this refuses it with a pointer rather than publishing a site.
pub fn run_build(
    plan: &BuildPlan,
    repo_dir: &Path,
    dist_dir: &Path,
    compute: &dyn ComputeRunner,
) -> anyhow::Result<BuildOutcome> {
    // Fresh dist each build (idempotent: a replayed Build overwrites cleanly).
    if dist_dir.exists() {
        std::fs::remove_dir_all(dist_dir)
            .map_err(|e| anyhow::anyhow!("clear dist {}: {e}", dist_dir.display()))?;
    }
    std::fs::create_dir_all(dist_dir)
        .map_err(|e| anyhow::anyhow!("create dist {}: {e}", dist_dir.display()))?;

    match plan {
        BuildPlan::Static { publish_dir } => {
            // `publish_dir` is repo-controlled: confine it under the repo root (a `../..`
            // traversal or a symlink escaping the repo is refused).
            let src = safe_subpath(repo_dir, publish_dir)?;
            if !src.is_dir() {
                anyhow::bail!("static publish dir `{}` is not a directory", src.display());
            }
            copy_tree(&src, dist_dir)?;
        }
        BuildPlan::Command {
            command,
            output_dir,
            tier,
        } => {
            run_command_bounded(command, repo_dir, *tier)?;
            // The build's servable output. Try the configured dir, then common fallbacks. Each
            // candidate is confined under the repo root.
            let out = resolve_output_dir(repo_dir, output_dir)?;
            copy_tree(&out, dist_dir)?;
        }
        BuildPlan::Compute {
            lang,
            source,
            tier,
            artifact,
        } => {
            // The genuinely cap-bounded build: run the program through the injected runner.
            let body = compute
                .run(&ComputeWorkload {
                    lang: lang.clone(),
                    source: source.clone(),
                    tier: *tier,
                })
                .map_err(|e| anyhow::anyhow!("compute build (`{lang}` @ {tier:?}): {e}"))?;
            // The artifact path is repo/manifest-controlled — confine it under the dist root.
            let dest = safe_join(dist_dir, artifact.trim_start_matches('/'))?;
            if let Some(parent) = dest.parent() {
                std::fs::create_dir_all(parent).ok();
            }
            std::fs::write(&dest, body)
                .map_err(|e| anyhow::anyhow!("write compute artifact {}: {e}", dest.display()))?;
        }
        BuildPlan::Server { .. } => {
            anyhow::bail!(
                "this repo detected as a SERVER target; a persistent server is not a static-site \
                 publish (run it in a server-launch lane, not the site-publish deploy)"
            );
        }
    }

    let file_count = count_files(dist_dir);
    if file_count == 0 {
        anyhow::bail!(
            "build produced no files in `{}` — nothing to publish",
            dist_dir.display()
        );
    }
    Ok(BuildOutcome {
        plan_label: plan.label().to_string(),
        file_count,
    })
}

/// Run a build command in the deny-default cage, bounded by the build timeout, at the resource
/// envelope `tier` selects.
fn run_command_bounded(command: &str, cwd: &Path, tier: BuildTier) -> anyhow::Result<()> {
    crate::sandbox::run_sandboxed_command(command, cwd, tier, build_timeout())
}

/// Resolve the build's output directory: the configured one, else a common fallback that exists
/// (`dist`/`build`/`out`/`public`). Every candidate is confined under the repo root — a
/// repo-controlled `output_dir = "../../etc"` (or a symlink escaping the repo) is refused.
fn resolve_output_dir(repo_dir: &Path, configured: &str) -> anyhow::Result<PathBuf> {
    if let Ok(primary) = safe_subpath(repo_dir, configured) {
        if primary.is_dir() {
            return Ok(primary);
        }
    }
    for cand in ["dist", "build", "out", "public"] {
        if let Ok(p) = safe_subpath(repo_dir, cand) {
            if p.is_dir() {
                return Ok(p);
            }
        }
    }
    anyhow::bail!(
        "build output dir `{}` not found under the repo root (and no dist/build/out/public \
         fallback); a `..`-traversal or repo-escaping output dir is refused",
        repo_dir.join(configured).display()
    )
}

/// Resolve `rel` against `base` and refuse anything that escapes the `base` root. The path must
/// exist. `canonicalize` resolves `..` AND follows symlinks, so a `rel` that is itself a symlink
/// to `/etc` lands outside the (canonicalized) root and is rejected.
fn safe_subpath(base: &Path, rel: &str) -> anyhow::Result<PathBuf> {
    let canon_root = base
        .canonicalize()
        .map_err(|e| anyhow::anyhow!("canonicalize root {}: {e}", base.display()))?;
    let canon = base
        .join(rel)
        .canonicalize()
        .map_err(|e| anyhow::anyhow!("resolve `{rel}` under the root: {e}"))?;
    if !canon.starts_with(&canon_root) {
        anyhow::bail!(
            "path `{rel}` escapes the root ({} is not under {})",
            canon.display(),
            canon_root.display()
        );
    }
    Ok(canon)
}

/// Join a not-yet-existing `rel` under `base`, refusing a `..`-traversal escape (a lexical check,
/// since the target does not exist yet so `canonicalize` cannot be used).
fn safe_join(base: &Path, rel: &str) -> anyhow::Result<PathBuf> {
    if rel.split(['/', '\\']).any(|c| c == "..") {
        anyhow::bail!("artifact path `{rel}` may not contain a `..` traversal component");
    }
    Ok(base.join(rel))
}

/// Recursively copy `src` into `dst`, skipping `.git`. Both must exist (`dst` is the dist root).
/// **Refuses symlinks**: each entry is `symlink_metadata`'d, and a symlink is an error rather
/// than followed/copied — a repo symlink `dist/creds -> /etc` (or to another tenant's tree)
/// never has its target bytes copied into the servable site.
fn copy_tree(src: &Path, dst: &Path) -> anyhow::Result<()> {
    for entry in
        std::fs::read_dir(src).map_err(|e| anyhow::anyhow!("read {}: {e}", src.display()))?
    {
        let entry = entry?;
        let name = entry.file_name();
        if name == ".git" {
            continue;
        }
        let from = entry.path();
        let to = dst.join(&name);
        let md = std::fs::symlink_metadata(&from)
            .map_err(|e| anyhow::anyhow!("stat {}: {e}", from.display()))?;
        if md.file_type().is_symlink() {
            anyhow::bail!(
                "refusing to publish symlink `{}` — a build output symlink is not followed (it \
                 could read host/other-tenant files into the served site)",
                from.display()
            );
        }
        if md.is_dir() {
            std::fs::create_dir_all(&to)?;
            copy_tree(&from, &to)?;
        } else {
            if let Some(parent) = to.parent() {
                std::fs::create_dir_all(parent).ok();
            }
            std::fs::copy(&from, &to)
                .map_err(|e| anyhow::anyhow!("copy {} -> {}: {e}", from.display(), to.display()))?;
        }
    }
    Ok(())
}

/// Count the regular files under `root` (recursively).
fn count_files(root: &Path) -> usize {
    let mut n = 0;
    let Ok(rd) = std::fs::read_dir(root) else {
        return 0;
    };
    for entry in rd.flatten() {
        let p = entry.path();
        if p.is_dir() {
            n += count_files(&p);
        } else {
            n += 1;
        }
    }
    n
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::plan::{BuildPlan, BuildTier};

    /// A test-double compute runner that emits fixed bytes — stands in for the injected
    /// dregg-sandbox weld so the Compute build path is exercised without the engine.
    struct FixedComputeRunner(&'static str);
    impl ComputeRunner for FixedComputeRunner {
        fn run(&self, _w: &ComputeWorkload) -> anyhow::Result<Vec<u8>> {
            Ok(self.0.as_bytes().to_vec())
        }
    }

    fn no_compute() -> FailClosedComputeRunner {
        FailClosedComputeRunner
    }

    #[test]
    fn static_build_stages_the_tree() {
        let repo = tempfile::tempdir().unwrap();
        std::fs::write(repo.path().join("index.html"), "<h1>hi</h1>").unwrap();
        std::fs::create_dir_all(repo.path().join(".git")).unwrap();
        std::fs::write(repo.path().join(".git/HEAD"), "ref: x").unwrap();
        let dist = tempfile::tempdir().unwrap();
        let out = run_build(
            &BuildPlan::Static {
                publish_dir: ".".into(),
            },
            repo.path(),
            &dist.path().join("dist"),
            &no_compute(),
        )
        .unwrap();
        assert_eq!(out.plan_label, "static");
        assert!(dist.path().join("dist/index.html").is_file());
        assert!(!dist.path().join("dist/.git").exists());
    }

    #[test]
    fn compute_build_runs_through_the_injected_runner() {
        let repo = tempfile::tempdir().unwrap();
        let plan = BuildPlan::Compute {
            lang: "wat".into(),
            source: "(module)".into(),
            tier: BuildTier::Sandboxed,
            artifact: "index.html".into(),
        };
        let dist = tempfile::tempdir().unwrap();
        let out = run_build(
            &plan,
            repo.path(),
            &dist.path().join("dist"),
            &FixedComputeRunner("42"),
        )
        .unwrap();
        assert_eq!(out.plan_label, "compute");
        let body = std::fs::read_to_string(dist.path().join("dist/index.html")).unwrap();
        assert_eq!(body, "42", "the injected runner's output is the artifact");
    }

    #[test]
    fn compute_build_without_a_runner_fails_closed() {
        let repo = tempfile::tempdir().unwrap();
        let plan = BuildPlan::Compute {
            lang: "wat".into(),
            source: "(module)".into(),
            tier: BuildTier::Sandboxed,
            artifact: "index.html".into(),
        };
        let dist = tempfile::tempdir().unwrap();
        let err =
            run_build(&plan, repo.path(), &dist.path().join("dist"), &no_compute()).unwrap_err();
        assert!(
            err.to_string().contains("no compute runner injected"),
            "got {err}"
        );
    }

    #[test]
    fn command_build_runs_a_subprocess_and_publishes_output() {
        let repo = tempfile::tempdir().unwrap();
        let plan = BuildPlan::Command {
            command: "mkdir -p dist && printf '<h1>built</h1>' > dist/index.html".into(),
            output_dir: "dist".into(),
            tier: BuildTier::Caged,
        };
        let dist = tempfile::tempdir().unwrap();
        let out = run_build(&plan, repo.path(), &dist.path().join("dist"), &no_compute()).unwrap();
        assert_eq!(out.plan_label, "command");
        let body = std::fs::read_to_string(dist.path().join("dist/index.html")).unwrap();
        assert_eq!(body, "<h1>built</h1>");
    }

    /// A repo-controlled `publish_dir` that escapes the repo root (`../../..`) is refused —
    /// nothing outside the repo is staged.
    #[test]
    fn static_publish_dir_traversal_is_refused() {
        let repo = tempfile::tempdir().unwrap();
        std::fs::write(repo.path().join("index.html"), "<h1>hi</h1>").unwrap();
        let dist = tempfile::tempdir().unwrap();
        let err = run_build(
            &BuildPlan::Static {
                publish_dir: "../../../../../../etc".into(),
            },
            repo.path(),
            &dist.path().join("dist"),
            &no_compute(),
        )
        .unwrap_err();
        assert!(
            err.to_string().contains("escapes the root"),
            "traversal must be refused, got {err}"
        );
    }

    /// A build output containing a symlink to a host path is refused — its target bytes are
    /// never copied into the published site.
    #[cfg(unix)]
    #[test]
    fn symlink_in_build_output_is_refused() {
        let repo = tempfile::tempdir().unwrap();
        std::fs::write(repo.path().join("index.html"), "<h1>hi</h1>").unwrap();
        std::os::unix::fs::symlink("/etc", repo.path().join("creds")).unwrap();
        let dist = tempfile::tempdir().unwrap();
        let err = run_build(
            &BuildPlan::Static {
                publish_dir: ".".into(),
            },
            repo.path(),
            &dist.path().join("dist"),
            &no_compute(),
        )
        .unwrap_err();
        assert!(
            err.to_string().contains("refusing to publish symlink"),
            "got {err}"
        );
        assert!(!dist.path().join("dist/creds/passwd").exists());
    }

    /// A `publish_dir` that is itself a symlink pointing outside the repo is refused
    /// (canonicalize lands outside the repo root).
    #[cfg(unix)]
    #[test]
    fn symlinked_publish_dir_escaping_repo_is_refused() {
        let repo = tempfile::tempdir().unwrap();
        std::fs::write(repo.path().join("index.html"), "<h1>hi</h1>").unwrap();
        let outside = tempfile::tempdir().unwrap();
        std::fs::write(outside.path().join("secret.txt"), "secret").unwrap();
        std::os::unix::fs::symlink(outside.path(), repo.path().join("out")).unwrap();
        let dist = tempfile::tempdir().unwrap();
        let err = run_build(
            &BuildPlan::Static {
                publish_dir: "out".into(),
            },
            repo.path(),
            &dist.path().join("dist"),
            &no_compute(),
        )
        .unwrap_err();
        assert!(err.to_string().contains("escapes the root"), "got {err}");
    }

    #[test]
    fn server_target_is_refused_with_the_pointer() {
        let repo = tempfile::tempdir().unwrap();
        let err = run_build(
            &BuildPlan::Server {
                entry: "Dockerfile".into(),
                port: 8080,
            },
            repo.path(),
            &tempfile::tempdir().unwrap().path().join("dist"),
            &no_compute(),
        )
        .unwrap_err();
        assert!(
            err.to_string().contains("server-launch lane"),
            "points at the server lane"
        );
    }
}
