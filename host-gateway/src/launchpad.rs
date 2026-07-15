//! The launchpad composition — a launch **gets a landing page**, and its metadata +
//! image are **content-addressed**.
//!
//! This is where the host gateway stops being a bag of surfaces and becomes the
//! offering: a verified hosting edge for agents and their launches. A [`Launch`]
//! (a slug, a title/blurb, an optional image + token metadata) is turned into
//!
//! 1. a **content-addressed** image + metadata — each pinned through the injected
//!    [`ContentStore`] and committed by its [`Cid`] (a dregg content commitment IS an
//!    IPFS CID, so the bytes are servable + re-witnessable from any node); and
//! 2. a **landing microsite** — a generated `index.html` (+ a `metadata.json` and the
//!    image asset) published into the [`SiteRegistry`] under the launch slug, so the
//!    instant a launch lands it is live at `<slug>.<apex>` with no extra step.
//!
//! The landing template is substrate-general (no product branding) — a caller styles
//! it or supplies its own `index.html` via [`Launch::with_landing`].

use dregg_ipfs::{Cid, IpfsClient};
use serde::{Deserialize, Serialize};

use crate::content::{ContentStore, address};
use crate::microsite::{Asset, Microsite, SiteError, SiteRegistry};

/// A launch to compose: an owner, a slug (its `<slug>.<apex>` host + site name), a
/// human title + blurb, and optional content-addressed metadata + image.
#[derive(Debug, Clone, Default)]
pub struct Launch {
    /// The owner subject (the site's owner + the metadata's provenance).
    pub owner: String,
    /// The slug — the site `<name>` and the `<slug>.<apex>` host.
    pub slug: String,
    /// A human-readable title for the generated landing page.
    pub title: String,
    /// A short blurb for the generated landing page.
    pub blurb: String,
    /// Token / launch metadata — content-addressed and published as `metadata.json`.
    /// `None` = no metadata asset.
    pub metadata: Option<serde_json::Value>,
    /// An image (bytes + a filename to serve it under) — content-addressed and served
    /// from the landing page. `None` = no image.
    pub image: Option<(String, Vec<u8>)>,
    /// A caller-supplied landing `index.html`, overriding the generated template.
    pub landing_html: Option<String>,
}

impl Launch {
    /// A new launch under `owner` at `slug`.
    pub fn new(owner: impl Into<String>, slug: impl Into<String>) -> Launch {
        Launch {
            owner: owner.into(),
            slug: slug.into(),
            ..Launch::default()
        }
    }

    /// Set the title + blurb the generated landing page renders.
    pub fn titled(mut self, title: impl Into<String>, blurb: impl Into<String>) -> Launch {
        self.title = title.into();
        self.blurb = blurb.into();
        self
    }

    /// Attach content-addressed launch/token metadata (published as `metadata.json`).
    pub fn with_metadata(mut self, metadata: serde_json::Value) -> Launch {
        self.metadata = Some(metadata);
        self
    }

    /// Attach a content-addressed image, served at `/{filename}` on the landing site.
    pub fn with_image(mut self, filename: impl Into<String>, bytes: impl Into<Vec<u8>>) -> Launch {
        self.image = Some((filename.into(), bytes.into()));
        self
    }

    /// Supply a landing `index.html`, overriding the generated template.
    pub fn with_landing(mut self, html: impl Into<String>) -> Launch {
        self.landing_html = Some(html.into());
        self
    }
}

/// The content-addressed record of a completed launch — the CIDs and the live landing
/// site. Every hosted artifact is addressable + re-witnessable.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LaunchReceipt {
    /// The launch slug (the published site name).
    pub slug: String,
    /// The owner subject.
    pub owner: String,
    /// The landing host (`<slug>.<apex>`).
    pub landing_host: String,
    /// The published site's content root (the CID over its whole asset manifest).
    pub site_root: Cid,
    /// The content address of the published `metadata.json` (if any).
    pub metadata_cid: Option<Cid>,
    /// The content address of the published image (if any).
    pub image_cid: Option<Cid>,
}

/// Why a launch could not be composed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LaunchError {
    /// The generated site could not be published (bad slug, or the slug is owned by a
    /// different subject).
    Site(SiteError),
    /// Pinning content to the backing store failed (transport error string).
    Content(String),
}

impl std::fmt::Display for LaunchError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LaunchError::Site(e) => write!(f, "landing site: {e}"),
            LaunchError::Content(e) => write!(f, "content store: {e}"),
        }
    }
}

impl std::error::Error for LaunchError {}

impl From<SiteError> for LaunchError {
    fn from(e: SiteError) -> LaunchError {
        LaunchError::Site(e)
    }
}

/// The launchpad — composes a [`Launch`] into a live landing microsite over a
/// [`SiteRegistry`], content-addressing its metadata + image through a [`ContentStore`].
pub struct Launchpad<'a, C: IpfsClient> {
    sites: &'a SiteRegistry,
    content: &'a ContentStore<C>,
}

impl<'a, C: IpfsClient> Launchpad<'a, C> {
    /// A launchpad publishing into `sites` and content-addressing into `content`.
    pub fn new(sites: &'a SiteRegistry, content: &'a ContentStore<C>) -> Launchpad<'a, C> {
        Launchpad { sites, content }
    }

    /// Compose `launch`: pin its metadata + image (content-addressed), generate (or
    /// adopt) its landing page, publish the microsite under the slug, and return the
    /// content-addressed [`LaunchReceipt`]. The landing site is live at
    /// `<slug>.<apex>` on return.
    pub fn launch(&self, launch: &Launch) -> Result<LaunchReceipt, LaunchError> {
        let mut site = Microsite::new(&launch.slug, &launch.owner);

        // Content-address + attach the metadata as `metadata.json`.
        let metadata_cid = match &launch.metadata {
            Some(meta) => {
                let bytes = serde_json::to_vec_pretty(meta).unwrap_or_default();
                let cid = self.pin(&bytes)?;
                site = site.with_asset("/metadata.json", Asset::new("application/json", bytes));
                Some(cid)
            }
            None => None,
        };

        // Content-address + attach the image.
        let mut image_path = None;
        let image_cid = match &launch.image {
            Some((filename, bytes)) => {
                let cid = self.pin(bytes)?;
                let path = format!("/{}", filename.trim_start_matches('/'));
                site = site.with_asset(&path, Asset::at(&path, bytes.clone()));
                image_path = Some(path);
                Some(cid)
            }
            None => None,
        };

        // The landing page: a caller-supplied index, else the generated template.
        let html = match &launch.landing_html {
            Some(html) => html.clone(),
            None => render_landing(launch, image_path.as_deref(), metadata_cid.as_ref()),
        };
        site = site.with_asset(
            "/index.html",
            Asset::new("text/html; charset=utf-8", html.into_bytes()),
        );

        let site_root = self.sites.publish(site)?;
        Ok(LaunchReceipt {
            slug: launch.slug.trim().to_ascii_lowercase(),
            owner: launch.owner.clone(),
            landing_host: format!(
                "{}.{}",
                launch.slug.trim().to_ascii_lowercase(),
                self.sites.apex()
            ),
            site_root,
            metadata_cid,
            image_cid,
        })
    }

    fn pin(&self, bytes: &[u8]) -> Result<Cid, LaunchError> {
        self.content
            .put(bytes)
            .map_err(|e| LaunchError::Content(e.to_string()))
    }
}

/// Compose `launch` into its landing microsite + content-addressed [`LaunchReceipt`]
/// **without** pinning to an [`IpfsClient`] — the pure content addresses (blake3) are
/// computed with no I/O ([`crate::content::address`]). The returned site is NOT yet
/// published; the caller publishes it (so ownership + name validity are enforced
/// uniformly by [`SiteRegistry::publish`]) and the returned receipt's
/// [`LaunchReceipt::site_root`] equals the published site's content root.
///
/// The HTTP write path uses this: a console runs a launch over HTTP and its metadata +
/// image are content-addressed; pinning the bytes to a Kubo daemon is a separate,
/// optional durability step (the same CIDs).
pub fn compose_unpinned(launch: &Launch, apex: &str) -> (Microsite, LaunchReceipt) {
    let mut site = Microsite::new(&launch.slug, &launch.owner);

    let metadata_cid = launch.metadata.as_ref().map(|meta| {
        let bytes = serde_json::to_vec_pretty(meta).unwrap_or_default();
        let cid = address(&bytes);
        site = site
            .clone()
            .with_asset("/metadata.json", Asset::new("application/json", bytes));
        cid
    });

    let mut image_path = None;
    let image_cid = launch.image.as_ref().map(|(filename, bytes)| {
        let cid = address(bytes);
        let path = format!("/{}", filename.trim_start_matches('/'));
        site = site
            .clone()
            .with_asset(&path, Asset::at(&path, bytes.clone()));
        image_path = Some(path);
        cid
    });

    let html = match &launch.landing_html {
        Some(html) => html.clone(),
        None => render_landing(launch, image_path.as_deref(), metadata_cid.as_ref()),
    };
    site = site.clone().with_asset(
        "/index.html",
        Asset::new("text/html; charset=utf-8", html.into_bytes()),
    );

    let slug = launch.slug.trim().to_ascii_lowercase();
    let site_root = site.content_root();
    let receipt = LaunchReceipt {
        slug: slug.clone(),
        owner: launch.owner.clone(),
        landing_host: format!("{slug}.{}", crate::microsite::normalize_apex(apex)),
        site_root,
        metadata_cid,
        image_cid,
    };
    (site, receipt)
}

/// Render the generated, substrate-general landing page. `image_path` (if any) is the
/// served path of the launch image; `metadata_cid` (if any) is shown as the content
/// address of the metadata a visitor can re-witness.
fn render_landing(launch: &Launch, image_path: Option<&str>, metadata_cid: Option<&Cid>) -> String {
    let title = html_escape(if launch.title.is_empty() {
        &launch.slug
    } else {
        &launch.title
    });
    let blurb = html_escape(&launch.blurb);
    let image = image_path
        .map(|p| {
            format!(
                "<img src=\"{}\" alt=\"{}\" style=\"max-width:100%;border-radius:12px\">",
                html_escape(p),
                title
            )
        })
        .unwrap_or_default();
    let metadata = metadata_cid
        .map(|cid| {
            format!(
                "<p class=\"cid\">metadata: <a href=\"/metadata.json\"><code>{}</code></a></p>",
                html_escape(&cid.to_string_cid())
            )
        })
        .unwrap_or_default();
    format!(
        "<!doctype html>\n<html lang=\"en\">\n<head>\n<meta charset=\"utf-8\">\n<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n<title>{title}</title>\n<style>\nbody{{font-family:system-ui,sans-serif;max-width:42rem;margin:4rem auto;padding:0 1.25rem;line-height:1.55}}\nh1{{font-size:2rem;margin:0 0 .5rem}}\n.blurb{{color:#444;font-size:1.1rem}}\n.cid{{color:#666;font-size:.85rem;word-break:break-all}}\ncode{{background:#f2f2f2;padding:.1rem .35rem;border-radius:4px}}\n@media(prefers-color-scheme:dark){{body{{background:#111;color:#eee}}.blurb{{color:#bbb}}.cid{{color:#999}}code{{background:#222}}}}\n</style>\n</head>\n<body>\n<h1>{title}</h1>\n<p class=\"blurb\">{blurb}</p>\n{image}\n{metadata}\n</body>\n</html>\n"
    )
}

/// Minimal HTML-attribute/text escaping for the generated landing page.
fn html_escape(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_ipfs::MockIpfs;

    const ALICE: &str = "dregg:alice";

    fn setup() -> (SiteRegistry, ContentStore<MockIpfs>) {
        (
            SiteRegistry::new("dregg.net"),
            ContentStore::new(MockIpfs::new()),
        )
    }

    #[test]
    fn a_launch_gets_a_live_landing_page_with_content_addressed_assets() {
        let (sites, content) = setup();
        let pad = Launchpad::new(&sites, &content);
        let launch = Launch::new(ALICE, "moon")
            .titled("Moon", "to the moon")
            .with_metadata(serde_json::json!({ "symbol": "MOON", "supply": 1_000_000 }))
            .with_image("logo.png", b"\x89PNG\r\n\x1a\n fake png".to_vec());

        let receipt = pad.launch(&launch).expect("launch composes");
        assert_eq!(receipt.slug, "moon");
        assert_eq!(receipt.landing_host, "moon.dregg.net");
        assert!(
            receipt.metadata_cid.is_some(),
            "metadata is content-addressed"
        );
        assert!(receipt.image_cid.is_some(), "image is content-addressed");

        // The landing site is LIVE at <slug>.<apex> — a launch gets a landing page.
        let landing = sites.resolve("moon.dregg.net", "/");
        assert_eq!(landing.status, 200);
        assert!(landing.content_type.starts_with("text/html"));
        let html = String::from_utf8_lossy(&landing.body);
        assert!(html.contains("Moon"), "title rendered: {html}");
        assert!(html.contains("to the moon"), "blurb rendered");
        assert!(html.contains("/logo.png"), "image referenced");

        // The metadata + image assets serve, and their bytes re-witness against the CIDs.
        let meta = sites.resolve("moon.dregg.net", "/metadata.json");
        assert_eq!(meta.status, 200);
        let meta_cid = address(&meta.body);
        assert_eq!(Some(meta_cid), receipt.metadata_cid);

        let img = sites.resolve("moon.dregg.net", "/logo.png");
        assert_eq!(img.status, 200);
        assert!(img.content_type.starts_with("image/png"));
        assert_eq!(Some(address(&img.body)), receipt.image_cid);

        // The pinned bytes are fetchable from the content store by CID (decentralized).
        let fetched = content
            .get(receipt.metadata_cid.as_ref().unwrap())
            .expect("fetch");
        assert_eq!(fetched, meta.body);
    }

    #[test]
    fn a_bare_launch_still_gets_a_landing_page() {
        let (sites, content) = setup();
        let pad = Launchpad::new(&sites, &content);
        let receipt = pad.launch(&Launch::new(ALICE, "bare")).expect("launch");
        assert_eq!(receipt.metadata_cid, None);
        assert_eq!(receipt.image_cid, None);
        assert_eq!(sites.resolve("bare.dregg.net", "/").status, 200);
    }

    #[test]
    fn a_caller_supplied_landing_overrides_the_template() {
        let (sites, content) = setup();
        let pad = Launchpad::new(&sites, &content);
        let launch = Launch::new(ALICE, "custom").with_landing("<h1>my own page</h1>");
        pad.launch(&launch).expect("launch");
        let body = sites.resolve("custom.dregg.net", "/").body;
        assert_eq!(body, b"<h1>my own page</h1>");
    }

    #[test]
    fn a_launch_over_a_stranger_slug_is_refused() {
        let (sites, content) = setup();
        sites
            .publish(Microsite::new("taken", "dregg:someone-else").with("/index.html", "x"))
            .unwrap();
        let pad = Launchpad::new(&sites, &content);
        let err = pad.launch(&Launch::new(ALICE, "taken")).unwrap_err();
        assert!(matches!(
            err,
            LaunchError::Site(SiteError::OwnerMismatch { .. })
        ));
    }
}
