//! `git-deploy` — auto-deploy-from-git: fetch a repo at a pinned commit, detect how
//! it becomes servable bytes, build it inside a deny-default OS cage, and publish a
//! content-addressed site tree carrying the source commitment.
//!
//! ```text
//!   deploy <git-url|.>
//!     │
//!     ▼ ① CLONE   — fetch the repo at a pinned commit          (the source commitment)
//!     ▼ ② DETECT  — heuristic / manifest → a BuildPlan         (static | command | compute)
//!     ▼ ③ BUILD   — run the build in a deny-default cage,      (env-cleared, rlimited,
//!     │              metered against the deploy budget          process-group reaped)
//!     ▼ ④ PUBLISH — dist/ → a content-addressed site + receipt (commit folded into the root)
//!     ▼ ⑤ LIVE    — served at <name>.<apex> by the publish target
//! ```
//!
//! The deploy is a **crash-resumable, exactly-once, budget-metered durable workflow**
//! ([`workflow`]): a deploy that crashes mid-build resumes from its last checkpoint (a
//! completed Clone/Build is replayed from the journal, never re-run), and each step is
//! metered against the deploy budget, fail-closed over the ceiling. The **source
//! commitment** — the cloned commit hash — lands in the [`DeployReceipt`] and is folded
//! into the published tree's `content_root` (a `/.well-known/deploy.json` manifest asset),
//! so *which commit a site was built from* is re-witnessable.
//!
//! # Weld seams (this crate is the pipeline, never the engine)
//!
//! - **Compute tier** — [`build::ComputeRunner`], injected. The resident owned
//!   `dregg-sandbox::run_workload` (an empty-`Linker` wasmi interpreter that reaches
//!   nothing on the host) is the canonical backing; the default runner is an honest
//!   fail-closed seam that names the weld.
//! - **Publish target** — [`publish::PublishTarget`], injected. The default
//!   [`publish::DirPublishTarget`] content-addresses each asset; a hosting registry or a
//!   launchpad landing-page target is the integrator's weld (so a launch gets a landing
//!   page shipped straight from its repo).
//! - **Durable workflow** — [`workflow::DurableJournal`], injected. The default
//!   [`workflow::FileJournal`] is an on-disk checkpoint log; a general durable-workflow
//!   engine implements the same trait to take over crash-resume + exactly-once.
//!
//! What is **reviewed-go** (a library seam, not a running server): the push-triggered
//! [`webhook`] receiver — it parses + signature-verifies a push event into a
//! [`DeploySpec`], but standing up a public listener is an operator action.
//!
//! # The round-trip, in one call
//!
//! ```no_run
//! use std::sync::Arc;
//! use git_deploy::{DeployConfig, DeployEngine, DeploySpec, publish::DirPublishTarget};
//!
//! let target = Arc::new(DirPublishTarget::new("/var/lib/deploy/sites", "sites.local"));
//! let engine = Arc::new(DeployEngine::new("/var/lib/deploy/work", target)
//!     .with_config(DeployConfig::new("sites.local")));
//! let spec = DeploySpec::new("https://example.com/repo.git", "blog", "agent:ember");
//! let receipt = engine.deploy(&spec, "deploy-1").expect("deploy");
//! println!("live at {} (commit {})", receipt.url, receipt.commit);
//! ```

pub mod build;
pub mod clone;
pub mod plan;
pub mod publish;
pub mod sandbox;
pub mod webhook;
pub mod workflow;

pub use build::{run_build, BuildOutcome, ComputeRunner, ComputeWorkload, FailClosedComputeRunner};
pub use clone::{clone_repo, head_commit, CloneResult};
pub use plan::{detect, manifest_site_name, BuildPlan, BuildTier, DeployManifest};
pub use publish::{
    publish_dist, DeployManifestAsset, DirPublishTarget, PublishTarget, PublishedSite, SiteContent,
    DEFAULT_WELL_KNOWN_MANIFEST,
};
pub use webhook::{deploy_spec_from_push, parse_push_event, verify_signature, PushEvent};
pub use workflow::{
    DeployEngine, DeployReceipt, DeploySpec, DeployStage, DurableJournal, FileJournal,
};

/// Deploy-wide configuration — the values that were product-specific in the original and
/// are now parameters. An apex domain, the in-repo manifest filename, and the well-known
/// path the source-commitment manifest is injected at.
#[derive(Debug, Clone)]
pub struct DeployConfig {
    /// The apex a published site is served under: `https://<name>.<apex>/`. No default
    /// is baked in beyond the neutral placeholder [`DeployConfig::DEFAULT_APEX`].
    pub apex: String,
    /// The in-repo manifest filename that overrides detection (default
    /// [`DeployConfig::DEFAULT_MANIFEST_FILE`]).
    pub manifest_file: String,
    /// Where the source-commitment manifest is injected within the published site
    /// (default [`DEFAULT_WELL_KNOWN_MANIFEST`](publish::DEFAULT_WELL_KNOWN_MANIFEST)).
    pub well_known_manifest: String,
}

impl DeployConfig {
    /// A neutral placeholder apex. Deployers set their own; nothing product-specific is
    /// hardcoded.
    pub const DEFAULT_APEX: &'static str = "sites.local";
    /// The in-repo deploy-manifest filename.
    pub const DEFAULT_MANIFEST_FILE: &'static str = "deploy.toml";

    /// A config serving sites under `apex`, with the default manifest filename + well-known
    /// path.
    pub fn new(apex: impl Into<String>) -> DeployConfig {
        DeployConfig {
            apex: apex.into(),
            manifest_file: Self::DEFAULT_MANIFEST_FILE.to_string(),
            well_known_manifest: publish::DEFAULT_WELL_KNOWN_MANIFEST.to_string(),
        }
    }

    /// Override the in-repo manifest filename.
    pub fn with_manifest_file(mut self, name: impl Into<String>) -> DeployConfig {
        self.manifest_file = name.into();
        self
    }

    /// The public URL a site named `name` is served at under this config's apex.
    pub fn site_url(&self, name: &str) -> String {
        format!("https://{name}.{}/", self.apex)
    }
}

impl Default for DeployConfig {
    fn default() -> Self {
        DeployConfig::new(DeployConfig::DEFAULT_APEX)
    }
}
