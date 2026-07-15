//! `workflow` — the deploy as a crash-resumable, budget-metered durable workflow.
//!
//! A deploy is a three-step workflow — **Clone → Build → Publish** — driven over a
//! [`DurableJournal`]: each completed step is checkpointed (its output + the running meter
//! total recorded), so a deploy that crashes mid-build **resumes from its last checkpoint** — a
//! completed Clone/Build is replayed from the journal, never re-run (no re-clone, no re-build),
//! and the meter is never double-charged. Each step is budget-gated: a charge that would exceed
//! the deploy's prepaid ceiling fails the step before it runs (the lease lapse → the build is
//! reaped, never run-and-not-paid).
//!
//! The default [`FileJournal`] is an on-disk JSON-lines checkpoint log under the engine's
//! workroot — single-host, append-only, crash-durable. A **general durable-workflow engine**
//! (a durable-orchestration runtime over a Postgres/SQLite store) implements the SAME
//! [`DurableJournal`] trait to take over crash-resume + exactly-once at scale; this crate is the
//! deploy pipeline, driveable by either.
//!
//! The metering here is an owned prepaid-ceiling gate ([`prepaid_ceiling_admits`]); binding it
//! to a conserving settlement ledger (the resident `hosted-durable` rail) so a metered build
//! settles as an exactly-once transfer is the settlement weld.

use std::path::{Path, PathBuf};
use std::sync::Arc;

use serde::{Deserialize, Serialize};

use crate::build::{ComputeRunner, FailClosedComputeRunner};
use crate::plan::BuildPlan;
use crate::publish::{DeployManifestAsset, PublishTarget};
use crate::DeployConfig;

/// The three durable steps of a deploy (their journal keys).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum DeployStage {
    Clone,
    Build,
    Publish,
}

impl DeployStage {
    fn key(self) -> &'static str {
        match self {
            DeployStage::Clone => "clone",
            DeployStage::Build => "build",
            DeployStage::Publish => "publish",
        }
    }
}

/// The input to a deploy: a repo, a site name, an owner, and a prepaid budget.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeploySpec {
    /// The repo to deploy (a remote URL, a `file://`, or a local path).
    pub repo_url: String,
    /// The ref to pin (branch/tag/commit); `None` = the remote default branch.
    #[serde(default)]
    pub git_ref: Option<String>,
    /// The subdomain label to publish under.
    pub site_name: String,
    /// The publishing owner/agent (the cap holder).
    pub owner: String,
    /// The deploy-lease budget, in meter units. The three steps each charge `cost_per_step`; a
    /// step whose charge would exceed this fails the deploy (lease lapse → reap).
    pub budget_units: i64,
    /// Meter cost charged per step.
    pub cost_per_step: i64,
    /// An explicit build plan that overrides detection (and the in-repo manifest).
    #[serde(default)]
    pub build_override: Option<BuildPlan>,
}

impl DeploySpec {
    /// A straight deploy of `repo_url` as the site `site_name` for `owner`, with a default
    /// 1000-unit budget at 1 unit/step.
    pub fn new(
        repo_url: impl Into<String>,
        site_name: impl Into<String>,
        owner: impl Into<String>,
    ) -> DeploySpec {
        DeploySpec {
            repo_url: repo_url.into(),
            git_ref: None,
            site_name: site_name.into(),
            owner: owner.into(),
            budget_units: 1000,
            cost_per_step: 1,
            build_override: None,
        }
    }

    /// Set the prepaid budget + per-step cost.
    pub fn with_budget(mut self, budget_units: i64, cost_per_step: i64) -> DeploySpec {
        self.budget_units = budget_units;
        self.cost_per_step = cost_per_step;
        self
    }
}

/// The verifiable record a deploy leaves: which site, from which commit, at what content
/// commitment, for how much.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct DeployReceipt {
    pub site_name: String,
    pub owner: String,
    /// The live URL.
    pub url: String,
    /// The source commitment — the commit the site was built from.
    pub commit: String,
    /// The published site's content commitment (folds in the commit via the deploy manifest).
    pub content_root: String,
    /// The publish sequence assigned by the publish target.
    pub publish_seq: u64,
    /// How many assets the published site holds (including the injected deploy manifest).
    pub asset_count: usize,
    /// The build plan that ran (`static`/`command`/`compute`).
    pub build_plan: String,
    /// Total meter units charged against the deploy budget.
    pub meter_units: i64,
}

// ---------------------------------------------------------------------------
// Budget gate (owned prepaid-ceiling core; the settlement weld replaces the ledger).
// ---------------------------------------------------------------------------

/// Whether a prepaid budget of `budget` admits a charge of `cost` on top of `drawn`. A pure
/// ceiling: `drawn + cost <= budget`, saturating (never a wraparound admit). This is the one
/// headroom decision every step routes through — the same shape a conserving settlement meter
/// (`hosted-durable`) enforces when the deploy is bound to a real ledger.
pub fn prepaid_ceiling_admits(budget: i64, drawn: i64, cost: i64) -> bool {
    drawn.saturating_add(cost) <= budget
}

// ---------------------------------------------------------------------------
// The durable journal seam.
// ---------------------------------------------------------------------------

/// One durably-recorded step completion: the step's output JSON + the running meter total after
/// the step's charge.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StepCheckpoint {
    pub stage: DeployStage,
    /// The step's output payload (a `CloneOut`/`BuildOut`/`PublishOut` JSON).
    pub output: String,
    /// The deploy's running meter total after this step was metered.
    pub meter_total: i64,
}

/// The durable checkpoint log a deploy is driven over — an **injection seam**. The default
/// [`FileJournal`] is an on-disk JSON-lines log; a general durable-workflow engine implements
/// the same trait so crash-resume + exactly-once are the engine's, not this crate's.
pub trait DurableJournal {
    /// The checkpoint recorded for `stage`, if the step has completed (replayed, never re-run).
    fn completed(&self, stage: DeployStage) -> anyhow::Result<Option<StepCheckpoint>>;
    /// Durably record `checkpoint` as `stage`'s completion.
    fn checkpoint(&self, checkpoint: &StepCheckpoint) -> anyhow::Result<()>;
}

/// The default on-disk journal: an append-only JSON-lines file. Each line is a [`StepCheckpoint`];
/// the last line for a stage wins (a re-checkpoint is idempotent).
pub struct FileJournal {
    path: PathBuf,
}

impl FileJournal {
    /// A journal at `path` (created lazily on the first checkpoint).
    pub fn new(path: impl Into<PathBuf>) -> FileJournal {
        FileJournal { path: path.into() }
    }

    fn read_all(&self) -> anyhow::Result<Vec<StepCheckpoint>> {
        if !self.path.is_file() {
            return Ok(Vec::new());
        }
        let text = std::fs::read_to_string(&self.path)
            .map_err(|e| anyhow::anyhow!("read journal {}: {e}", self.path.display()))?;
        let mut out = Vec::new();
        for line in text.lines() {
            let line = line.trim();
            if line.is_empty() {
                continue;
            }
            let cp: StepCheckpoint = serde_json::from_str(line)
                .map_err(|e| anyhow::anyhow!("parse journal line: {e}"))?;
            out.push(cp);
        }
        Ok(out)
    }
}

impl DurableJournal for FileJournal {
    fn completed(&self, stage: DeployStage) -> anyhow::Result<Option<StepCheckpoint>> {
        // Last checkpoint for the stage wins.
        Ok(self
            .read_all()?
            .into_iter()
            .rev()
            .find(|c| c.stage == stage))
    }

    fn checkpoint(&self, checkpoint: &StepCheckpoint) -> anyhow::Result<()> {
        use std::io::Write;
        if let Some(parent) = self.path.parent() {
            std::fs::create_dir_all(parent)
                .map_err(|e| anyhow::anyhow!("create journal dir {}: {e}", parent.display()))?;
        }
        let mut f = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(&self.path)
            .map_err(|e| anyhow::anyhow!("open journal {}: {e}", self.path.display()))?;
        let line = serde_json::to_string(checkpoint)?;
        writeln!(f, "{line}").map_err(|e| anyhow::anyhow!("append journal: {e}"))?;
        f.flush().ok();
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Step output payloads.
// ---------------------------------------------------------------------------

#[derive(Serialize, Deserialize)]
struct CloneOut {
    commit: String,
}
#[derive(Serialize, Deserialize)]
struct BuildOut {
    plan_label: String,
}
#[derive(Serialize, Deserialize)]
struct PublishOut {
    content_root: String,
    publish_seq: u64,
    asset_count: usize,
    url: String,
}

// ---------------------------------------------------------------------------
// The engine.
// ---------------------------------------------------------------------------

/// What the deploy steps operate on: a working-directory root (per-instance clone/build dirs
/// live under it, so they survive a crash), the [`PublishTarget`] the Publish writes into, the
/// injected [`ComputeRunner`] a compute build routes through, and the [`DeployConfig`].
pub struct DeployEngine {
    workroot: PathBuf,
    target: Arc<dyn PublishTarget>,
    compute: Arc<dyn ComputeRunner>,
    config: DeployConfig,
}

impl DeployEngine {
    /// A deploy engine over `workroot`, publishing into `target`, with the fail-closed compute
    /// runner + default config. Wire a real compute runner with [`with_compute_runner`], and the
    /// apex/manifest with [`with_config`].
    pub fn new(workroot: impl Into<PathBuf>, target: Arc<dyn PublishTarget>) -> DeployEngine {
        DeployEngine {
            workroot: workroot.into(),
            target,
            compute: Arc::new(FailClosedComputeRunner),
            config: DeployConfig::default(),
        }
    }

    /// Inject the compute runner a `compute` build routes through (the resident
    /// `dregg-sandbox::run_workload` weld).
    pub fn with_compute_runner(mut self, compute: Arc<dyn ComputeRunner>) -> DeployEngine {
        self.compute = compute;
        self
    }

    /// Set the deploy config (apex, manifest filename, well-known manifest path).
    pub fn with_config(mut self, config: DeployConfig) -> DeployEngine {
        self.config = config;
        self
    }

    fn instance_root(&self, instance: &str) -> PathBuf {
        self.workroot.join(sanitize(instance))
    }
    fn repo_dir(&self, instance: &str) -> PathBuf {
        self.instance_root(instance).join("repo")
    }
    fn dist_dir(&self, instance: &str) -> PathBuf {
        self.instance_root(instance).join("dist")
    }
    fn journal_path(&self, instance: &str) -> PathBuf {
        self.instance_root(instance).join("journal.jsonl")
    }
    fn counts_path(&self, instance: &str) -> PathBuf {
        self.instance_root(instance).join("run-counts.json")
    }

    /// How many times a step (`clone`/`build`/`publish`) actually executed for this deploy.
    /// Exactly-once means this stays `1` across a crash + resume (a replayed step does not
    /// re-execute, so it does not re-increment).
    pub fn run_calls(&self, instance: &str, stage: DeployStage) -> i64 {
        read_counts(&self.counts_path(instance))
            .get(stage.key())
            .copied()
            .unwrap_or(0)
    }

    /// Run `spec` to completion over the default on-disk [`FileJournal`], returning the
    /// [`DeployReceipt`]. Start-or-resume: an instance whose journal already has completed steps
    /// resumes from the last checkpoint.
    pub fn deploy(&self, spec: &DeploySpec, instance: &str) -> anyhow::Result<DeployReceipt> {
        let journal = FileJournal::new(self.journal_path(instance));
        match self.deploy_until(spec, instance, &journal, None)? {
            Some(receipt) => Ok(receipt),
            None => anyhow::bail!("deploy did not complete (unexpected early stop)"),
        }
    }

    /// Run `spec` over an explicit `journal` (the durable-workflow-engine seam), optionally
    /// stopping after `stop_after` (the crash-injection point the resume test drives). Returns
    /// `Some(receipt)` on completion, `None` when stopped early.
    pub fn deploy_until(
        &self,
        spec: &DeploySpec,
        instance: &str,
        journal: &dyn DurableJournal,
        stop_after: Option<DeployStage>,
    ) -> anyhow::Result<Option<DeployReceipt>> {
        let budget = spec.budget_units;
        let cost = spec.cost_per_step;

        // --- ① CLONE ---
        let (clone_out, mut total) =
            self.step(journal, DeployStage::Clone, budget, cost, || {
                let repo_dir = self.repo_dir(instance);
                let res =
                    crate::clone::clone_repo(&spec.repo_url, spec.git_ref.as_deref(), &repo_dir)?;
                self.incr(instance, DeployStage::Clone);
                serde_json::to_string(&CloneOut { commit: res.commit }).map_err(Into::into)
            })?;
        let clone: CloneOut = serde_json::from_str(&clone_out)?;
        if stop_after == Some(DeployStage::Clone) {
            return Ok(None);
        }

        // --- ② BUILD ---
        let (build_out, total2) = self.step(journal, DeployStage::Build, budget, cost, || {
            let repo_dir = self.repo_dir(instance);
            let dist_dir = self.dist_dir(instance);
            let plan = crate::plan::detect(
                &repo_dir,
                spec.build_override.as_ref(),
                &self.config.manifest_file,
            )?;
            let outcome =
                crate::build::run_build(&plan, &repo_dir, &dist_dir, self.compute.as_ref())?;
            self.incr(instance, DeployStage::Build);
            serde_json::to_string(&BuildOut {
                plan_label: outcome.plan_label,
            })
            .map_err(Into::into)
        })?;
        total = total2.max(total);
        let build: BuildOut = serde_json::from_str(&build_out)?;
        if stop_after == Some(DeployStage::Build) {
            return Ok(None);
        }

        // --- ③ PUBLISH ---
        let (publish_out, total3) =
            self.step(journal, DeployStage::Publish, budget, cost, || {
                let dist_dir = self.dist_dir(instance);
                let manifest = DeployManifestAsset {
                    repo: spec.repo_url.clone(),
                    commit: clone.commit.clone(),
                    build_plan: build.plan_label.clone(),
                    site: spec.site_name.clone(),
                };
                let site = crate::publish::publish_dist(
                    self.target.as_ref(),
                    &spec.owner,
                    &spec.site_name,
                    &dist_dir,
                    &manifest,
                    &self.config.well_known_manifest,
                )?;
                self.incr(instance, DeployStage::Publish);
                serde_json::to_string(&PublishOut {
                    content_root: site.content_root,
                    publish_seq: site.seq,
                    asset_count: site.asset_count,
                    url: site.url,
                })
                .map_err(Into::into)
            })?;
        total = total3.max(total);
        let published: PublishOut = serde_json::from_str(&publish_out)?;

        Ok(Some(DeployReceipt {
            site_name: spec.site_name.clone(),
            owner: spec.owner.clone(),
            url: published.url,
            commit: clone.commit,
            content_root: published.content_root,
            publish_seq: published.publish_seq,
            asset_count: published.asset_count,
            build_plan: build.plan_label,
            meter_units: total,
        }))
    }

    /// Run one durable step: replay from the journal if already completed (never re-run); else
    /// budget-gate, run `activity`, meter, and checkpoint. Returns `(output_json, meter_total)`.
    fn step(
        &self,
        journal: &dyn DurableJournal,
        stage: DeployStage,
        budget: i64,
        cost: i64,
        activity: impl FnOnce() -> anyhow::Result<String>,
    ) -> anyhow::Result<(String, i64)> {
        if let Some(cp) = journal.completed(stage)? {
            // Replayed from history: the recorded output + meter total, no re-execution and no
            // re-charge.
            return Ok((cp.output, cp.meter_total));
        }
        // The running total is the last checkpoint's meter total (or 0).
        let drawn = self.last_total(journal)?;
        if !prepaid_ceiling_admits(budget, drawn, cost) {
            let projected = drawn.saturating_add(cost);
            anyhow::bail!(
                "deploy-lease exhausted: {} charge would reach {projected} > budget {budget}",
                stage.key()
            );
        }
        let output = activity()?;
        let meter_total = drawn + cost;
        journal.checkpoint(&StepCheckpoint {
            stage,
            output: output.clone(),
            meter_total,
        })?;
        Ok((output, meter_total))
    }

    /// The running meter total = the max recorded across completed checkpoints (steps meter
    /// monotonically, so the max is the latest).
    fn last_total(&self, journal: &dyn DurableJournal) -> anyhow::Result<i64> {
        let mut total = 0;
        for stage in [DeployStage::Clone, DeployStage::Build, DeployStage::Publish] {
            if let Some(cp) = journal.completed(stage)? {
                total = total.max(cp.meter_total);
            }
        }
        Ok(total)
    }

    fn incr(&self, instance: &str, stage: DeployStage) {
        let path = self.counts_path(instance);
        let mut counts = read_counts(&path);
        *counts.entry(stage.key().to_string()).or_insert(0) += 1;
        if let Some(parent) = path.parent() {
            let _ = std::fs::create_dir_all(parent);
        }
        if let Ok(json) = serde_json::to_string(&counts) {
            let _ = std::fs::write(&path, json);
        }
    }
}

fn read_counts(path: &Path) -> std::collections::HashMap<String, i64> {
    std::fs::read_to_string(path)
        .ok()
        .and_then(|t| serde_json::from_str(&t).ok())
        .unwrap_or_default()
}

/// Make an instance id safe as a single path component.
fn sanitize(instance: &str) -> String {
    instance
        .chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || c == '-' || c == '_' {
                c
            } else {
                '_'
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::publish::DirPublishTarget;

    fn fixture_repo(files: &[(&str, &str)]) -> (tempfile::TempDir, String) {
        use std::process::Command;
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
            std::fs::write(p.join(path), body).unwrap();
        }
        run(&["add", "-A"]);
        run(&["commit", "-q", "-m", "fixture"]);
        let commit = crate::clone::head_commit(p).unwrap();
        (dir, commit)
    }

    fn engine(work: &Path, out: &Path) -> DeployEngine {
        let target = Arc::new(DirPublishTarget::new(out, "sites.local"));
        DeployEngine::new(work, target).with_config(DeployConfig::new("sites.local"))
    }

    #[test]
    fn end_to_end_static_deploy() {
        let (src, commit) = fixture_repo(&[("index.html", "<h1>fixture</h1>")]);
        let work = tempfile::tempdir().unwrap();
        let out = tempfile::tempdir().unwrap();
        let eng = engine(work.path(), out.path());
        let spec = DeploySpec::new(src.path().to_str().unwrap(), "blog", "agent:ember");
        let receipt = eng.deploy(&spec, "d1").unwrap();
        assert_eq!(receipt.commit, commit);
        assert_eq!(receipt.build_plan, "static");
        assert_eq!(receipt.url, "https://blog.sites.local/");
        // 3 steps × 1 unit.
        assert_eq!(receipt.meter_units, 3);
        // index.html + the injected manifest.
        assert_eq!(receipt.asset_count, 2);
        // The site is materialized.
        assert!(out.path().join("blog/index.html").is_file());
    }

    /// Crash-resume + exactly-once: a deploy that "crashes" after Build (the journal + workdir
    /// survive) resumes and completes — and Clone/Build ran EXACTLY ONCE across the two runs
    /// (replayed from the journal, never re-executed).
    #[test]
    fn crash_after_build_resumes_and_is_exactly_once() {
        let (src, commit) = fixture_repo(&[("index.html", "<h1>x</h1>")]);
        let work = tempfile::tempdir().unwrap();
        let out = tempfile::tempdir().unwrap();
        let eng = engine(work.path(), out.path());
        let spec = DeploySpec::new(src.path().to_str().unwrap(), "blog", "agent:ember");

        // First run: crash after Build (Publish never happens).
        let journal = FileJournal::new(eng.journal_path("d2"));
        let stopped = eng
            .deploy_until(&spec, "d2", &journal, Some(DeployStage::Build))
            .unwrap();
        assert!(stopped.is_none(), "the run stopped before Publish");
        assert_eq!(eng.run_calls("d2", DeployStage::Clone), 1);
        assert_eq!(eng.run_calls("d2", DeployStage::Build), 1);
        assert_eq!(eng.run_calls("d2", DeployStage::Publish), 0);
        assert!(
            !out.path().join("blog/index.html").exists(),
            "not published yet"
        );

        // Resume (fresh journal handle over the same on-disk log): completes.
        let receipt = eng.deploy(&spec, "d2").unwrap();
        assert_eq!(receipt.commit, commit);
        assert!(
            out.path().join("blog/index.html").is_file(),
            "published on resume"
        );

        // Exactly-once: Clone/Build did NOT re-run on resume; only Publish executed.
        assert_eq!(
            eng.run_calls("d2", DeployStage::Clone),
            1,
            "clone replayed, not re-run"
        );
        assert_eq!(
            eng.run_calls("d2", DeployStage::Build),
            1,
            "build replayed, not re-run"
        );
        assert_eq!(eng.run_calls("d2", DeployStage::Publish), 1);
        assert_eq!(
            receipt.meter_units, 3,
            "meter not double-charged across the crash"
        );
    }

    #[test]
    fn over_budget_deploy_is_reaped_before_publish() {
        let (src, _) = fixture_repo(&[("index.html", "<h1>x</h1>")]);
        let work = tempfile::tempdir().unwrap();
        let out = tempfile::tempdir().unwrap();
        let eng = engine(work.path(), out.path());
        // Budget admits 2 steps at cost 1; the 3rd (publish) charge would reach 3 > 2.
        let spec =
            DeploySpec::new(src.path().to_str().unwrap(), "blog", "agent:ember").with_budget(2, 1);
        let err = eng.deploy(&spec, "d3").unwrap_err();
        assert!(
            err.to_string().contains("deploy-lease exhausted"),
            "got {err}"
        );
        assert!(
            !out.path().join("blog/index.html").exists(),
            "over-budget deploy did not publish"
        );
    }

    #[test]
    fn prepaid_ceiling_gate() {
        assert!(prepaid_ceiling_admits(10, 0, 5));
        assert!(prepaid_ceiling_admits(10, 5, 5));
        assert!(!prepaid_ceiling_admits(10, 6, 5));
        // Saturating: no wraparound admit.
        assert!(!prepaid_ceiling_admits(10, i64::MAX, 5));
    }
}
