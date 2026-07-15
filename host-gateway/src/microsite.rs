//! The static microsite data plane — published sites served by `Host`.
//!
//! A **microsite** is a named bundle of content-addressed assets owned by a subject.
//! The [`SiteRegistry`] resolves an inbound `Host` — the wildcard `<name>.<apex>`
//! (the deployment's configured hosting apex) — to a published site and serves its
//! assets. Every asset is committed by its [`Cid`] (a whole-blob blake3 address), and
//! a site's [`Microsite::content_root`] is the CID over its canonical
//! `path -> asset-CID` manifest — so a site's content is a single content-addressed
//! commitment a light client can re-witness.
//!
//! This is both the static serving plane the assembled gateway routes wildcard hosts
//! (and verified custom domains) to, AND the live source the cap-scoped `/api/sites`
//! read aggregates (owner-scoped).
//!
//! Publishing is owner-scoped: a site records the publishing `owner`, and a republish
//! by a different subject is refused (no takeover) — the same shape the custom-domain
//! binding enforces on-cell.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::{Arc, Mutex};

use dregg_ipfs::Cid;
use http_serve::WebResponse;
use serde::{Deserialize, Serialize};

use crate::content::address;
use crate::persist::{NullSites, SitePersistence};
use crate::util::lock;

/// The largest number of assets a single site may publish (an abuse bound).
pub const MAX_ASSETS: usize = 4096;
/// The largest total asset bytes a single site may publish (64 MiB — an abuse bound).
pub const MAX_SITE_BYTES: u64 = 64 * 1024 * 1024;

/// One published asset: its declared content-type and its raw bytes. The asset's
/// content address is [`Asset::cid`] (a whole-blob blake3 CID).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Asset {
    /// The `Content-Type` served for this asset.
    pub content_type: String,
    /// The raw asset bytes.
    pub body: Vec<u8>,
}

impl Asset {
    /// A new asset with an explicit content-type.
    pub fn new(content_type: impl Into<String>, body: impl Into<Vec<u8>>) -> Asset {
        Asset {
            content_type: content_type.into(),
            body: body.into(),
        }
    }

    /// An asset whose content-type is inferred from `path`'s extension (the common
    /// static-file case).
    pub fn at(path: &str, body: impl Into<Vec<u8>>) -> Asset {
        Asset::new(content_type_for(path), body)
    }

    /// The content address of this asset's bytes (a CIDv1, blake3 multihash).
    pub fn cid(&self) -> Cid {
        address(&self.body)
    }
}

/// A published site: a named, owner-scoped bundle of content-addressed assets keyed by
/// request path (`/index.html`, `/style.css`, …).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Microsite {
    /// The site `<name>` (its `<name>.<apex>` host serves the bytes).
    pub name: String,
    /// The owner subject the `/api/sites` read scopes on (and the republish gate).
    pub owner: String,
    /// The site's assets keyed by request path.
    pub assets: BTreeMap<String, Asset>,
}

impl Microsite {
    /// A new, empty site owned by `owner`.
    pub fn new(name: impl Into<String>, owner: impl Into<String>) -> Microsite {
        Microsite {
            name: name.into(),
            owner: owner.into(),
            assets: BTreeMap::new(),
        }
    }

    /// Add an asset at `path` (content-type inferred from the extension). Builder form.
    pub fn with(mut self, path: impl Into<String>, body: impl Into<Vec<u8>>) -> Microsite {
        let path = path.into();
        let asset = Asset::at(&path, body);
        self.assets.insert(path, asset);
        self
    }

    /// Add an asset at `path` with an explicit content-type. Builder form.
    pub fn with_asset(mut self, path: impl Into<String>, asset: Asset) -> Microsite {
        self.assets.insert(path.into(), asset);
        self
    }

    /// Total served bytes across all assets.
    pub fn bytes(&self) -> u64 {
        self.assets.values().map(|a| a.body.len() as u64).sum()
    }

    /// The site's **content root** — the CID over its canonical `path\0cid\n` manifest.
    /// A single content-addressed commitment binding the whole site's content, so two
    /// sites with identical content share a root and any asset change moves the root.
    pub fn content_root(&self) -> Cid {
        let mut manifest = Vec::new();
        for (path, asset) in &self.assets {
            manifest.extend_from_slice(path.as_bytes());
            manifest.push(0);
            manifest.extend_from_slice(asset.cid().to_string_cid().as_bytes());
            manifest.push(b'\n');
        }
        address(&manifest)
    }

    /// Total asset count.
    pub fn asset_count(&self) -> usize {
        self.assets.len()
    }

    /// Serve `path` against this site's assets. Resolution, in order:
    ///
    /// 1. an exact asset at `path`;
    /// 2. a directory index: a `path` ending in `/` (or the empty / root path) serves
    ///    `<path>index.html` (so `/`, `/docs/` resolve to their index);
    /// 3. otherwise a `404`.
    ///
    /// A custom `/404.html` asset, if published, is served as the not-found body (with a
    /// `404` status) — so a tenant styles its own not-found page.
    pub fn serve(&self, path: &str) -> WebResponse {
        // Exact hit.
        if let Some(asset) = self.assets.get(path) {
            return asset_response(200, asset);
        }
        // Directory index: root, empty, or a trailing-slash path -> `<dir>index.html`.
        let index_key = if path.is_empty() || path == "/" {
            "/index.html".to_string()
        } else if path.ends_with('/') {
            format!("{path}index.html")
        } else {
            String::new()
        };
        if !index_key.is_empty() {
            if let Some(asset) = self.assets.get(&index_key) {
                return asset_response(200, asset);
            }
        }
        // A tenant-supplied custom 404 page, else the JSON error.
        match self.assets.get("/404.html") {
            Some(asset) => asset_response(404, asset),
            None => WebResponse::error(404, format!("no asset at `{path}`")),
        }
    }
}

fn asset_response(status: u16, asset: &Asset) -> WebResponse {
    WebResponse {
        status,
        content_type: asset.content_type.clone(),
        body: asset.body.clone(),
    }
}

/// Why a publish was refused.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SiteError {
    /// `name` is not a valid single-label site name (empty, has a dot, or a bad char).
    InvalidName(String),
    /// A republish of an existing site by a subject that is not its owner (no takeover).
    OwnerMismatch { name: String },
    /// The site exceeds a publish bound (`too many assets` or `too many bytes`).
    TooLarge { name: String, reason: String },
    /// A publish with no owner subject (the write path is cap-gated).
    NoOwner,
}

impl std::fmt::Display for SiteError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SiteError::InvalidName(n) => write!(f, "`{n}` is not a valid site name"),
            SiteError::OwnerMismatch { name } => {
                write!(f, "only the owner of site `{name}` may republish it")
            }
            SiteError::TooLarge { name, reason } => {
                write!(f, "site `{name}` exceeds a publish bound: {reason}")
            }
            SiteError::NoOwner => write!(f, "a publish must carry a verified owner subject"),
        }
    }
}

impl std::error::Error for SiteError {}

/// The registry of published microsites — the wildcard `<name>.<apex>` data plane and
/// the live source for the cap-scoped `/api/sites` read.
pub struct SiteRegistry {
    sites: Mutex<BTreeMap<String, Microsite>>,
    by_owner: Mutex<BTreeMap<String, BTreeSet<String>>>,
    persistence: Arc<dyn SitePersistence>,
    apex: String,
}

impl SiteRegistry {
    /// A fresh registry serving `<name>.<apex>` for the deployment's hosting `apex`
    /// (e.g. `dregg.net`, `dregg.fg-goose.online`), in-RAM only. The apex is normalized
    /// (leading dot / trailing dot stripped, lowercased).
    pub fn new(apex: impl AsRef<str>) -> SiteRegistry {
        SiteRegistry::with_persistence(apex, Arc::new(NullSites))
    }

    /// A registry seeded from — and writing through to — `persistence`, so published
    /// sites survive a restart. Prior sites are reloaded and indexed at construction.
    pub fn with_persistence(
        apex: impl AsRef<str>,
        persistence: Arc<dyn SitePersistence>,
    ) -> SiteRegistry {
        let reg = SiteRegistry {
            sites: Mutex::new(BTreeMap::new()),
            by_owner: Mutex::new(BTreeMap::new()),
            persistence,
            apex: normalize_apex(apex.as_ref()),
        };
        for site in reg.persistence.load() {
            reg.index_insert(&site.owner, &site.name);
            lock(&reg.sites).insert(site.name.clone(), site);
        }
        reg
    }

    fn index_insert(&self, owner: &str, name: &str) {
        lock(&self.by_owner)
            .entry(owner.to_string())
            .or_default()
            .insert(name.to_string());
    }

    fn index_remove(&self, owner: &str, name: &str) {
        let mut idx = lock(&self.by_owner);
        if let Some(names) = idx.get_mut(owner) {
            names.remove(name);
            if names.is_empty() {
                idx.remove(owner);
            }
        }
    }

    /// The deployment's configured hosting apex.
    pub fn apex(&self) -> &str {
        &self.apex
    }

    /// Publish (or owner-republish) `site` — returns its content root. A republish by a
    /// different subject is refused ([`SiteError::OwnerMismatch`]); an invalid site name
    /// is [`SiteError::InvalidName`]; a site over the asset-count / byte bounds is
    /// [`SiteError::TooLarge`]. The published site is indexed by owner and persisted.
    pub fn publish(&self, site: Microsite) -> Result<Cid, SiteError> {
        let name = site.name.trim().to_ascii_lowercase();
        if !is_valid_label(&name) {
            return Err(SiteError::InvalidName(name));
        }
        if site.owner.trim().is_empty() {
            return Err(SiteError::NoOwner);
        }
        if site.assets.len() > MAX_ASSETS {
            return Err(SiteError::TooLarge {
                name,
                reason: format!("{} assets exceeds the {MAX_ASSETS} cap", site.assets.len()),
            });
        }
        let bytes = site.bytes();
        if bytes > MAX_SITE_BYTES {
            return Err(SiteError::TooLarge {
                name,
                reason: format!("{bytes} bytes exceeds the {MAX_SITE_BYTES}-byte cap"),
            });
        }
        let mut site = site;
        site.name = name.clone();
        let owner = site.owner.clone();
        let root = site.content_root();
        // Hold ONLY the sites lock for the owner-check + insert, then release it before
        // touching the owner index or the durable log — so the sole two-lock path
        // (list_for_owner: by_owner→sites) never inverts against this one.
        {
            let mut guard = lock(&self.sites);
            if let Some(existing) = guard.get(&name) {
                if existing.owner != owner {
                    return Err(SiteError::OwnerMismatch { name });
                }
            }
            guard.insert(name.clone(), site.clone());
        }
        self.index_insert(&owner, &name);
        self.persistence.publish(&site);
        Ok(root)
    }

    /// Take a site down: removes it from the registry, the owner index, and the durable
    /// log — but only if `owner` owns it (no cross-tenant takedown). Returns whether a
    /// site was removed.
    pub fn take_down(&self, name: &str, owner: &str) -> bool {
        let name = name.trim().to_ascii_lowercase();
        let removed = {
            let mut guard = lock(&self.sites);
            if guard.get(&name).map(|s| s.owner == owner).unwrap_or(false) {
                guard.remove(&name)
            } else {
                None
            }
        };
        if removed.is_some() {
            self.index_remove(owner, &name);
            self.persistence.remove(&name);
            true
        } else {
            false
        }
    }

    /// A clone of the published site `<name>`, if any.
    pub fn get(&self, name: &str) -> Option<Microsite> {
        lock(&self.sites)
            .get(&name.trim().to_ascii_lowercase())
            .cloned()
    }

    /// All published site names, sorted.
    pub fn names(&self) -> Vec<String> {
        lock(&self.sites).keys().cloned().collect()
    }

    /// The sites owned by `owner`, ordered by name — O(owned) via the owner index.
    pub fn list_for_owner(&self, owner: &str) -> Vec<Microsite> {
        let names: Vec<String> = lock(&self.by_owner)
            .get(owner)
            .map(|s| s.iter().cloned().collect())
            .unwrap_or_default();
        let guard = lock(&self.sites);
        names
            .into_iter()
            .filter_map(|n| guard.get(&n).cloned())
            .collect()
    }

    /// All published sites, sorted by name (a snapshot).
    pub fn list(&self) -> Vec<Microsite> {
        lock(&self.sites).values().cloned().collect()
    }

    /// Resolve an inbound wildcard `Host` (`<name>.<apex>`) to a **published** site
    /// name. Strips a `:port`, lowercases, and requires the label before `.<apex>` to
    /// be a single published label. `None` for a non-apex host or an unpublished name.
    pub fn site_for_host(&self, host: &str) -> Option<String> {
        let name = self.name_from_host(host)?;
        self.get(&name).map(|s| s.name)
    }

    /// The candidate site `<name>` a wildcard `Host` addresses — the label before
    /// `.<apex>` when it is a single label — WITHOUT requiring the site to exist (the
    /// on-demand-TLS `ask` uses this to check existence separately).
    pub fn name_from_host(&self, host: &str) -> Option<String> {
        let bare = host
            .split(':')
            .next()
            .unwrap_or(host)
            .trim()
            .to_ascii_lowercase();
        let suffix = format!(".{}", self.apex);
        let name = bare.strip_suffix(&suffix)?;
        // Exactly one label under the apex (`blog.<apex>`, not `a.b.<apex>`).
        if name.is_empty() || name.contains('.') {
            return None;
        }
        Some(name.to_string())
    }

    /// Whether `host` is a served wildcard host (a published `<name>.<apex>`).
    pub fn serves_host(&self, host: &str) -> bool {
        self.site_for_host(host).is_some()
    }

    /// Serve `path` for the wildcard `Host`, or `404` if the host is not a published
    /// site.
    pub fn resolve(&self, host: &str, path: &str) -> WebResponse {
        match self.site_for_host(host) {
            Some(name) => match self.get(&name) {
                Some(site) => site.serve(path),
                None => WebResponse::error(404, "site vanished"),
            },
            None => WebResponse::error(404, format!("no site for host `{host}`")),
        }
    }
}

/// Normalize a hosting apex: trim, strip a leading/trailing dot, lowercase.
pub fn normalize_apex(apex: &str) -> String {
    apex.trim()
        .trim_start_matches('.')
        .trim_end_matches('.')
        .to_ascii_lowercase()
}

/// Whether `label` is a valid single DNS label (a site `<name>`): 1..=63 chars,
/// `[a-z0-9-]`, not starting/ending with `-`, no dots.
pub fn is_valid_label(label: &str) -> bool {
    let l = label.trim();
    if l.is_empty() || l.len() > 63 || l.contains('.') {
        return false;
    }
    if l.starts_with('-') || l.ends_with('-') {
        return false;
    }
    l.chars()
        .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '-')
}

/// Infer a `Content-Type` from a path's extension (the common static-file types).
pub fn content_type_for(path: &str) -> String {
    let ext = path.rsplit('.').next().unwrap_or("").to_ascii_lowercase();
    let ct = match ext.as_str() {
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
        "txt" | "md" => "text/plain; charset=utf-8",
        "wasm" => "application/wasm",
        _ => "application/octet-stream",
    };
    ct.to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    const ALICE: &str = "dregg:aaaa0000aaaa0000";
    const BOB: &str = "dregg:bbbb1111bbbb1111";

    fn registry() -> SiteRegistry {
        SiteRegistry::new("dregg.net")
    }

    #[test]
    fn publishes_and_serves_by_wildcard_host() {
        let reg = registry();
        let site = Microsite::new("blog", ALICE)
            .with("/index.html", "<h1>hello</h1>")
            .with("/style.css", "h1{color:teal}");
        let root = reg.publish(site).expect("publish");
        assert!(!root.digest.is_empty());

        // The wildcard host resolves and serves the index (empty path -> /index.html).
        let resp = reg.resolve("blog.dregg.net", "/");
        assert_eq!(resp.status, 200);
        assert!(resp.content_type.starts_with("text/html"));
        assert_eq!(resp.body, b"<h1>hello</h1>");

        // The css asset serves with the inferred content-type.
        let css = reg.resolve("blog.dregg.net:443", "/style.css");
        assert_eq!(css.status, 200);
        assert!(css.content_type.starts_with("text/css"));

        // An unknown path 404s; an unknown host 404s.
        assert_eq!(reg.resolve("blog.dregg.net", "/nope").status, 404);
        assert_eq!(reg.resolve("nope.dregg.net", "/").status, 404);
        // A two-label host under the apex is not a wildcard site.
        assert!(reg.name_from_host("a.b.dregg.net").is_none());
    }

    #[test]
    fn republish_by_a_stranger_is_refused() {
        let reg = registry();
        reg.publish(Microsite::new("shop", ALICE).with("/index.html", "alice"))
            .expect("alice publishes");
        // Bob cannot take over alice's site name.
        assert_eq!(
            reg.publish(Microsite::new("shop", BOB).with("/index.html", "bob")),
            Err(SiteError::OwnerMismatch {
                name: "shop".into()
            }),
        );
        // Alice can republish her own site (new content -> new root).
        let r1 = reg.get("shop").unwrap().content_root();
        let r2 = reg
            .publish(Microsite::new("shop", ALICE).with("/index.html", "alice v2"))
            .expect("alice republishes");
        assert_ne!(r1, r2, "changed content moves the content root");
    }

    #[test]
    fn invalid_names_are_refused() {
        let reg = registry();
        assert!(matches!(
            reg.publish(Microsite::new("bad.name", ALICE)),
            Err(SiteError::InvalidName(_))
        ));
        assert!(matches!(
            reg.publish(Microsite::new("-bad", ALICE)),
            Err(SiteError::InvalidName(_))
        ));
    }

    #[test]
    fn content_root_is_deterministic_and_content_addressed() {
        let a = Microsite::new("s", ALICE).with("/index.html", "same");
        let b = Microsite::new("s", BOB).with("/index.html", "same");
        // The content root binds CONTENT, not owner — identical assets share a root.
        assert_eq!(a.content_root(), b.content_root());
    }
}
