//! `publish` — step ④: a built `dist/` tree → a published, content-addressed site.
//!
//! Walks the `dist/` tree into a [`SiteContent`] (content-types inferred per file), **injects
//! the source commitment** as a `/.well-known/deploy.json` manifest asset, and publishes through
//! an injected [`PublishTarget`]. Because the manifest asset is part of the content, the commit
//! hash is folded into the site's `content_root` — so the published site itself carries,
//! re-witnessably, *which commit it was built from*.
//!
//! # Content addressing (the IPFS-backing seam)
//!
//! Each asset is keyed by `sha256(body)`; the site's `content_root` is `sha256` over the sorted
//! `(path, asset-hash)` pairs. This is a deterministic content address: the same bytes always
//! hash the same, and any change to any asset (including the injected commit) moves the root.
//! The default [`DirPublishTarget`] materializes the tree on disk; a content-addressed store
//! target (the resident `dregg-ipfs`) composes onto the SAME [`PublishTarget`] seam so token
//! metadata/images and launch landing pages are served content-addressed.
//!
//! # Composing with a launchpad
//!
//! A [`PublishTarget`] is the one seam a hosting registry or a launchpad landing-page host
//! implements. Handing a launch's repo through this pipeline into a launchpad-backed target is
//! how "a launch gets a landing page shipped straight from its repo" is realized.

use std::collections::BTreeMap;
use std::path::Path;
use std::sync::atomic::{AtomicU64, Ordering};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

/// Where the injected source-commitment manifest lands within the published site.
pub const DEFAULT_WELL_KNOWN_MANIFEST: &str = "/.well-known/deploy.json";

/// A single servable asset: its inferred content-type + its bytes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Asset {
    /// The MIME content-type served for this asset.
    pub content_type: String,
    /// The asset bytes.
    pub body: Vec<u8>,
}

impl Asset {
    /// An asset whose content-type is inferred from `key`'s extension.
    pub fn at(key: &str, body: Vec<u8>) -> Asset {
        Asset {
            content_type: content_type_for(key).to_string(),
            body,
        }
    }

    /// The asset's content address (`sha256(body)`, hex).
    pub fn content_hash(&self) -> String {
        hex(&Sha256::digest(&self.body))
    }
}

/// A site's servable content: request-path → [`Asset`], key-ordered so the content_root is
/// deterministic.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SiteContent {
    /// Request path (`/index.html`, `/css/app.css`) → asset.
    pub assets: BTreeMap<String, Asset>,
}

impl SiteContent {
    pub fn new() -> SiteContent {
        SiteContent::default()
    }

    pub fn is_empty(&self) -> bool {
        self.assets.is_empty()
    }

    /// Insert an asset at `key` with an explicit content-type + body.
    pub fn with_typed(mut self, key: &str, content_type: &str, body: Vec<u8>) -> SiteContent {
        self.assets.insert(
            normalize_key(key),
            Asset {
                content_type: content_type.to_string(),
                body,
            },
        );
        self
    }

    /// Resolve a request path to its asset (applying the same normalization as publish).
    pub fn resolve(&self, path: &str) -> Option<&Asset> {
        self.assets.get(&normalize_key(path))
    }

    /// The site's `content_root`: `sha256` over the sorted `(normalized-path, asset-hash)` pairs.
    /// A change to any asset — including the injected commit manifest — moves the root.
    pub fn content_root(&self) -> String {
        let mut hasher = Sha256::new();
        for (key, asset) in &self.assets {
            hasher.update((key.len() as u64).to_le_bytes());
            hasher.update(key.as_bytes());
            let h = asset.content_hash();
            hasher.update(h.as_bytes());
        }
        hex(&hasher.finalize())
    }
}

/// The verifiable record of a publish: which site, at what content commitment, for whom.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PublishedSite {
    /// The published subdomain label.
    pub name: String,
    /// The publishing owner.
    pub owner: String,
    /// The live URL.
    pub url: String,
    /// The content commitment (folds in the commit via the deploy manifest).
    pub content_root: String,
    /// How many assets the published site holds (including the injected deploy manifest).
    pub asset_count: usize,
    /// The publish sequence assigned by the target.
    pub seq: u64,
}

/// The target a built site is published into — an **injection seam**. The default
/// [`DirPublishTarget`] writes a content-addressed tree on disk; a hosting registry, a launchpad
/// landing-page host, or a content-addressed store (`dregg-ipfs`) implements the same trait.
pub trait PublishTarget: Send + Sync {
    /// Publish `content` as the site `name` for `owner`, returning the [`PublishedSite`] record.
    fn publish(
        &self,
        owner: &str,
        name: &str,
        content: &SiteContent,
    ) -> anyhow::Result<PublishedSite>;
}

/// The default publish target: materialize the content-addressed tree under `root/<name>/` and
/// serve it at `https://<name>.<apex>/`. Each asset is written at its request path; a sidecar
/// `.content-root` records the site's content commitment.
pub struct DirPublishTarget {
    root: std::path::PathBuf,
    apex: String,
    seq: AtomicU64,
}

impl DirPublishTarget {
    pub fn new(root: impl Into<std::path::PathBuf>, apex: impl Into<String>) -> DirPublishTarget {
        DirPublishTarget {
            root: root.into(),
            apex: apex.into(),
            seq: AtomicU64::new(0),
        }
    }
}

impl PublishTarget for DirPublishTarget {
    fn publish(
        &self,
        owner: &str,
        name: &str,
        content: &SiteContent,
    ) -> anyhow::Result<PublishedSite> {
        if content.is_empty() {
            anyhow::bail!("nothing to publish for site `{name}`");
        }
        let site_dir = self.root.join(sanitize_label(name));
        // Fresh publish: replace any prior tree so a redeploy is not a merge.
        if site_dir.exists() {
            std::fs::remove_dir_all(&site_dir)
                .map_err(|e| anyhow::anyhow!("clear site dir {}: {e}", site_dir.display()))?;
        }
        for (key, asset) in &content.assets {
            let rel = key.trim_start_matches('/');
            let dest = site_dir.join(rel);
            if let Some(parent) = dest.parent() {
                std::fs::create_dir_all(parent)
                    .map_err(|e| anyhow::anyhow!("create {}: {e}", parent.display()))?;
            }
            std::fs::write(&dest, &asset.body)
                .map_err(|e| anyhow::anyhow!("write {}: {e}", dest.display()))?;
        }
        let content_root = content.content_root();
        std::fs::write(site_dir.join(".content-root"), &content_root).ok();
        let seq = self.seq.fetch_add(1, Ordering::SeqCst) + 1;
        Ok(PublishedSite {
            name: name.to_string(),
            owner: owner.to_string(),
            url: format!("https://{name}.{}/", self.apex),
            content_root,
            asset_count: content.assets.len(),
            seq,
        })
    }
}

/// The source-commitment manifest committed into the published site.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct DeployManifestAsset {
    /// The repo the site was built from.
    pub repo: String,
    /// The full commit hash the build was pinned at (the source commitment).
    pub commit: String,
    /// The build plan that produced the published tree (`static`/`command`/`compute`).
    pub build_plan: String,
    /// The published subdomain label.
    pub site: String,
}

/// Walk `dist_dir` into a [`SiteContent`], inferring each file's content-type from its path.
/// Keys are absolute request paths rooted at the dist root (e.g. `dist/css/x.css` → `/css/x.css`).
/// **Refuses symlinks** (defense-in-depth over the build's own refusal): a symlink is never
/// followed to read a host/other-tenant file's bytes into the published content.
pub fn dist_to_content(dist_dir: &Path) -> anyhow::Result<SiteContent> {
    let mut content = SiteContent::new();
    walk(dist_dir, dist_dir, &mut content)?;
    if content.is_empty() {
        anyhow::bail!("dist `{}` has no files to publish", dist_dir.display());
    }
    Ok(content)
}

fn walk(root: &Path, dir: &Path, content: &mut SiteContent) -> anyhow::Result<()> {
    for entry in
        std::fs::read_dir(dir).map_err(|e| anyhow::anyhow!("read {}: {e}", dir.display()))?
    {
        let entry = entry?;
        let path = entry.path();
        let md = std::fs::symlink_metadata(&path)
            .map_err(|e| anyhow::anyhow!("stat {}: {e}", path.display()))?;
        if md.file_type().is_symlink() {
            anyhow::bail!(
                "refusing to publish symlink `{}` — symlinks are not followed into served content",
                path.display()
            );
        }
        if md.is_dir() {
            walk(root, &path, content)?;
        } else {
            let rel = path
                .strip_prefix(root)
                .map_err(|e| anyhow::anyhow!("strip prefix: {e}"))?;
            let key = format!("/{}", rel.to_string_lossy().replace('\\', "/"));
            let body = std::fs::read(&path)
                .map_err(|e| anyhow::anyhow!("read {}: {e}", path.display()))?;
            content
                .assets
                .insert(normalize_key(&key), Asset::at(&key, body));
        }
    }
    Ok(())
}

/// Publish a built `dist_dir` as the site `name` for `owner` through `target`, injecting the
/// source-commitment manifest at `well_known_path`. Returns the [`PublishedSite`] — whose
/// `content_root` now commits to the manifest (and thus the commit hash) too.
pub fn publish_dist(
    target: &dyn PublishTarget,
    owner: &str,
    name: &str,
    dist_dir: &Path,
    manifest: &DeployManifestAsset,
    well_known_path: &str,
) -> anyhow::Result<PublishedSite> {
    let mut content = dist_to_content(dist_dir)?;
    let manifest_json = serde_json::to_vec_pretty(manifest)?;
    content = content.with_typed(well_known_path, "application/json", manifest_json);
    target.publish(owner, name, &content)
}

/// Infer a MIME content-type from a request/file path extension.
fn content_type_for(key: &str) -> &'static str {
    let ext = key.rsplit('.').next().unwrap_or("").to_ascii_lowercase();
    match ext.as_str() {
        "html" | "htm" => "text/html; charset=utf-8",
        "css" => "text/css; charset=utf-8",
        "js" | "mjs" => "text/javascript; charset=utf-8",
        "json" => "application/json",
        "svg" => "image/svg+xml",
        "png" => "image/png",
        "jpg" | "jpeg" => "image/jpeg",
        "gif" => "image/gif",
        "webp" => "image/webp",
        "ico" => "image/x-icon",
        "wasm" => "application/wasm",
        "txt" | "md" => "text/plain; charset=utf-8",
        "woff2" => "font/woff2",
        "woff" => "font/woff",
        _ => "application/octet-stream",
    }
}

/// Normalize a request/content path: `/` → `/index.html`; a trailing slash → `…/index.html`;
/// ensure a leading `/`.
fn normalize_key(path: &str) -> String {
    let path = path.trim();
    if path.is_empty() || path == "/" {
        return "/index.html".to_string();
    }
    let with_slash = if path.starts_with('/') {
        path.to_string()
    } else {
        format!("/{path}")
    };
    if with_slash.ends_with('/') {
        format!("{with_slash}index.html")
    } else {
        with_slash
    }
}

/// Make a site label safe as a single path component.
fn sanitize_label(label: &str) -> String {
    label
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

fn hex(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;

    fn write(dir: &Path, rel: &str, body: &str) {
        let p = dir.join(rel);
        if let Some(parent) = p.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
        std::fs::write(p, body).unwrap();
    }

    #[test]
    fn dist_tree_becomes_content_with_types() {
        let dist = tempfile::tempdir().unwrap();
        write(dist.path(), "index.html", "<h1>hi</h1>");
        write(dist.path(), "css/app.css", "body{}");
        let content = dist_to_content(dist.path()).unwrap();
        assert_eq!(
            content.resolve("/").map(|a| a.content_type.as_str()),
            Some("text/html; charset=utf-8")
        );
        assert_eq!(
            content
                .resolve("/css/app.css")
                .map(|a| a.content_type.as_str()),
            Some("text/css; charset=utf-8")
        );
    }

    /// A symlink in the dist tree is refused at the publish walk (defense-in-depth), so a
    /// host/other-tenant file's bytes are never served.
    #[cfg(unix)]
    #[test]
    fn dist_symlink_is_refused_by_the_walk() {
        let dist = tempfile::tempdir().unwrap();
        write(dist.path(), "index.html", "<h1>hi</h1>");
        std::os::unix::fs::symlink("/etc/passwd", dist.path().join("creds")).unwrap();
        let err = dist_to_content(dist.path()).unwrap_err();
        assert!(
            err.to_string().contains("refusing to publish symlink"),
            "got {err}"
        );
    }

    #[test]
    fn publish_injects_the_commit_into_content_root() {
        let dist = tempfile::tempdir().unwrap();
        write(dist.path(), "index.html", "<h1>hi</h1>");
        let out = tempfile::tempdir().unwrap();
        let target = DirPublishTarget::new(out.path(), "sites.local");
        let manifest = DeployManifestAsset {
            repo: "file:///fixture".into(),
            commit: "deadbeefdeadbeefdeadbeefdeadbeefdeadbeef".into(),
            build_plan: "static".into(),
            site: "blog".into(),
        };
        let site = publish_dist(
            &target,
            "agent:ember",
            "blog",
            dist.path(),
            &manifest,
            DEFAULT_WELL_KNOWN_MANIFEST,
        )
        .unwrap();
        assert_eq!(site.owner, "agent:ember");
        assert_eq!(site.name, "blog");
        // index.html + the injected manifest = 2 assets.
        assert_eq!(site.asset_count, 2);
        // The committed manifest is materialized and carries the commit.
        let served = std::fs::read(out.path().join("blog/.well-known/deploy.json")).unwrap();
        let served: DeployManifestAsset = serde_json::from_slice(&served).unwrap();
        assert_eq!(served.commit, manifest.commit);
        // url is under the configured apex, not any hardcoded product domain.
        assert_eq!(site.url, "https://blog.sites.local/");

        // A different commit moves the content_root (the commit is bound into the commitment).
        let out2 = tempfile::tempdir().unwrap();
        let target2 = DirPublishTarget::new(out2.path(), "sites.local");
        let mut m2 = manifest.clone();
        m2.commit = "0000000000000000000000000000000000000000".into();
        let s2 = publish_dist(
            &target2,
            "agent:ember",
            "blog",
            dist.path(),
            &m2,
            DEFAULT_WELL_KNOWN_MANIFEST,
        )
        .unwrap();
        assert_ne!(
            site.content_root, s2.content_root,
            "commit binds the content_root"
        );
    }

    #[test]
    fn content_root_is_deterministic_and_content_addressed() {
        let a = SiteContent::new().with_typed("/index.html", "text/html", b"<h1>x</h1>".to_vec());
        let b = SiteContent::new().with_typed("/index.html", "text/html", b"<h1>x</h1>".to_vec());
        assert_eq!(a.content_root(), b.content_root(), "same bytes → same root");
        let c = SiteContent::new().with_typed("/index.html", "text/html", b"<h1>y</h1>".to_vec());
        assert_ne!(
            a.content_root(),
            c.content_root(),
            "different bytes → different root"
        );
    }
}
