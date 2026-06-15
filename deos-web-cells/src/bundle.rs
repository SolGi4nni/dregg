//! The `WebBundle` — a content-addressed bundle of DOM/JS/CSS that a `dregg://`
//! cell CONTAINS, and its publish (→ a real surface cell) + cap-gated fetch.
//!
//! `docs/deos/WEB-CELLS.md`: a web-of-cells cell can contain web content — a
//! static JS/HTML/CSS bundle, or a snapshot of LIVE DOM / reactive-signal state.
//! This module ships the data model + the publish/fetch, **entirely over the
//! stable `starbridge_web_surface` API** — never a bespoke fetch, never a parallel
//! attestation:
//!
//! - [`WebBundle`] is a manifest ([`BundleManifest`]) + the bundle's named
//!   **assets** (the root document, scripts, stylesheets, and — for a LIVE-DOM
//!   snapshot — the serialized DOM/signal state). Its identity is the blake3 of a
//!   **canonical encoding** ([`WebBundle::content_hash`]): two bundles are the same
//!   cell iff they encode the same bytes. Content-addressed by construction.
//! - [`publish_bundle`] commits that canonical encoding into a real `dregg://`
//!   surface cell via [`WebOfCells::publish`] — the cell's committed content hash
//!   IS the bundle's content hash — and returns the [`DreggUri`] (the bearer cap)
//!   plus a [`Sturdyref`] (the cap-handle behind the membrane, for rehydration).
//! - [`fetch_bundle`] resolves a `dregg://` ref through [`WebOfCells::fetch`], runs
//!   the REAL client-side [`crate::AttestedResource::verify`] (the attestation chain
//!   — content-addressed, receipt-in-stream, quorum), and only then decodes the
//!   verified bytes back into a [`WebBundle`]. An unattested/tampered bundle yields
//!   a [`BundleError`], never bytes — confinement before content.
//!
//! The **liveness-typing** of a bundle (Live / ReplayedDeterministic /
//! ReconstructedApproximate) is the rehydration-stack's [`crate::Rehydration`],
//! carried by the [`Sturdyref`] and surfaced at rehydration ([`crate::rehydrate`]
//! module) — not a field a publisher hand-asserts.
//!
//! ## What is real vs. the seam
//!
//! - **Real (the addressing + the attestation):** the content hash is the genuine
//!   `blake3` the web-of-cells commits; the publish writes it into a REAL
//!   `dregg_cell::Cell`'s state through `WebOfCells::publish`; the fetch is the REAL
//!   attested cross-cell read + `verify()`. The bundle's identity = the cell's
//!   committed content hash, checkable by a third party.
//! - **The seam (named, not papered): the RENDER.** Turning the verified bundle
//!   bytes into pixels is the `servo-render` Stage-A cap-gated pipeline
//!   (`servo-render::fetch_render_present`) — the render path just landed. This
//!   crate produces the cap-confined, attested, per-viewer bundle the renderer
//!   consumes; it does not itself rasterize DOM (the `MockSurface`/libservo seam
//!   `starbridge_web_surface::delegate` already names). See [`crate::cascade`].

use blake3::Hasher;
use starbridge_web_surface::{
    AttestedResource, DreggUri, FetchError, OriginChrome, SurfaceCapability, Sturdyref, WebOfCells,
};
use starbridge_web_surface::rehydrate::InteractionLog;

/// What KIND of web content a [`WebBundle`] carries — a static bundle, or a
/// snapshot of LIVE DOM / reactive-signal state.
///
/// This is a structural tag on the bundle's *origin*, not its trust: the
/// trust/liveness readout is the rehydration-stack's [`crate::Rehydration`]
/// (derived from the source context's witness-log), surfaced when the bundle is
/// REHYDRATED. A `LiveDomSnapshot` bundle is exactly "the frustum-snapshot applied
/// to the DOM": a paused camera on a running surface that re-expands per-viewer.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BundleKind {
    /// A static publish: HTML/JS/CSS authored once, served as-is (the
    /// `dregg://`-hosted page). The web's "ship a bundle" — but content-addressed
    /// and cap-gated.
    StaticBundle,
    /// A snapshot of LIVE DOM state (a serialized DOM tree / reactive-signal graph
    /// captured from a running surface). The leptosic angle: a Leptos app's live
    /// signal-graph state IS a "live DOM bundle" — publishing it shares the app's
    /// live state as a transcludable, rehydratable, cap-confined artifact.
    LiveDomSnapshot,
}

impl BundleKind {
    /// The canonical one-byte tag (folded into the content-address so a static
    /// bundle and a live-DOM snapshot with identical assets are DISTINCT cells).
    fn tag(self) -> u8 {
        match self {
            BundleKind::StaticBundle => 0x01,
            BundleKind::LiveDomSnapshot => 0x02,
        }
    }

    /// A human label for the trusted-path chrome / diagnostics.
    pub fn label(self) -> &'static str {
        match self {
            BundleKind::StaticBundle => "static-bundle",
            BundleKind::LiveDomSnapshot => "live-dom-snapshot",
        }
    }
}

/// One named **asset** in a bundle — the root document, a script, a stylesheet, or
/// (for a live-DOM snapshot) a serialized DOM/signal-state blob.
///
/// The `name` is the asset's identity within the bundle AND the **origin key** the
/// per-viewer membrane gates on: a weaker viewer's rehydrated projection may carry
/// only the assets its attenuated fetch-allowlist permits (see
/// [`WebBundle::asset_origin`] + the `rehydrate` module). So which assets a viewer
/// SEES is the REAL cap meet, not a parallel filter.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BundleAsset {
    /// The asset's name within the bundle (e.g. `index.html`, `app.js`,
    /// `theme.css`, `dom-state.json`). Unique per bundle; the origin key for the
    /// membrane's per-asset gate.
    pub name: String,
    /// The MIME-ish content type (a label for the renderer; e.g. `text/html`,
    /// `application/javascript`, `text/css`, `application/dom-snapshot`).
    pub content_type: String,
    /// The asset bytes. For a `LiveDomSnapshot` bundle, the serialized DOM/signal
    /// state blob lives here as an asset like any other.
    pub bytes: Vec<u8>,
}

impl BundleAsset {
    /// A bundle asset named `name` of `content_type` carrying `bytes`.
    pub fn new(name: impl Into<String>, content_type: impl Into<String>, bytes: Vec<u8>) -> Self {
        BundleAsset {
            name: name.into(),
            content_type: content_type.into(),
            bytes,
        }
    }

    /// `blake3` of this asset's bytes — its own content-address (a leaf of the
    /// bundle manifest's digest).
    pub fn digest(&self) -> [u8; 32] {
        *blake3::hash(&self.bytes).as_bytes()
    }
}

/// The **manifest** of a bundle — its kind, its entrypoint (the root document
/// name), and the per-asset digests. The manifest is the SMALL, content-addressed
/// description a [`crate::DomSnapshot`] embeds (via its digest) without the asset
/// bytes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BundleManifest {
    /// Static bundle vs. live-DOM snapshot (folded into the content-address).
    pub kind: BundleKind,
    /// The root document asset name (the entrypoint the renderer loads first —
    /// e.g. `index.html`). MUST name one of the bundle's assets.
    pub entrypoint: String,
    /// The per-asset digest table: `(asset name, content type, blake3(bytes))` for
    /// every asset, in canonical (name-sorted) order. This is the manifest's
    /// substance — it pins the bundle's shape WITHOUT the bytes, so a snapshot can
    /// carry the manifest digest cheaply.
    pub asset_digests: Vec<(String, String, [u8; 32])>,
}

impl BundleManifest {
    /// `blake3` of a canonical encoding of the manifest — the **manifest digest**.
    /// A [`crate::DomSnapshot`]'s culling boundary embeds THIS (one 32-byte hash),
    /// not the asset bytes, so the snapshot stays tiny.
    pub fn digest(&self) -> [u8; 32] {
        let mut h = Hasher::new();
        h.update(b"deos-web-cells-manifest-v1");
        h.update(&[self.kind.tag()]);
        h.update(&(self.entrypoint.len() as u64).to_le_bytes());
        h.update(self.entrypoint.as_bytes());
        h.update(&(self.asset_digests.len() as u64).to_le_bytes());
        // asset_digests is kept name-sorted (canonical) by WebBundle::manifest.
        for (name, ct, dig) in &self.asset_digests {
            h.update(&(name.len() as u64).to_le_bytes());
            h.update(name.as_bytes());
            h.update(&(ct.len() as u64).to_le_bytes());
            h.update(ct.as_bytes());
            h.update(dig);
        }
        *h.finalize().as_bytes()
    }

    /// The asset names the manifest pins (sorted — canonical). The culling boundary
    /// a snapshot carries (it bounds WHAT could re-expand, without the bytes).
    pub fn asset_names(&self) -> Vec<String> {
        self.asset_digests.iter().map(|(n, _, _)| n.clone()).collect()
    }
}

/// A **web bundle** — the content a `dregg://` cell contains: a manifest + the
/// named assets. Content-addressed: its identity is [`WebBundle::content_hash`].
///
/// `docs/deos/WEB-CELLS.md`: this is the unit you "publish/commit … or even bundles
/// of LIVE DOM state, and share that as part of the web-of-cells." A static bundle
/// is HTML/JS/CSS; a live-DOM snapshot is the serialized signal-graph/DOM state of
/// a running surface — the frustum-snapshot applied to the DOM.
#[derive(Clone, Debug)]
pub struct WebBundle {
    /// Static bundle vs. live-DOM snapshot.
    pub kind: BundleKind,
    /// The root document asset name (the entrypoint).
    pub entrypoint: String,
    /// The named assets (DOM/HTML, scripts, stylesheets, the DOM-state blob).
    /// Order-insensitive for identity: [`WebBundle::content_hash`] canonicalizes by
    /// name.
    pub assets: Vec<BundleAsset>,
}

/// `WebBundle` equality is **canonical** (order-insensitive), matching its
/// content-addressed identity: two bundles are equal iff they have the same kind,
/// entrypoint, and the same assets *by name* (regardless of construction order). This
/// is exactly the relation [`WebBundle::content_hash`] induces (the encoding sorts by
/// name), so `a == b` ⟺ `a.content_hash() == b.content_hash()` — and in particular a
/// bundle round-trips through `encode`/`decode` to an equal value even though `decode`
/// returns the canonical (name-sorted) order. (A positional `Vec` `PartialEq` would
/// contradict the documented order-insensitivity; we compare canonically instead.)
impl PartialEq for WebBundle {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
            && self.entrypoint == other.entrypoint
            && self.canonical_assets() == other.canonical_assets()
    }
}
impl Eq for WebBundle {}

/// What can go wrong building / publishing / fetching a [`WebBundle`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BundleError {
    /// The bundle's `entrypoint` does not name any of its assets — a bundle with no
    /// root document to load is malformed.
    EntrypointNotAnAsset {
        /// The entrypoint that named no asset.
        entrypoint: String,
    },
    /// Two assets share a name — a bundle's asset names must be unique (the name is
    /// the origin key the membrane gates on; a duplicate would be ambiguous).
    DuplicateAssetName {
        /// The name that appeared more than once.
        name: String,
    },
    /// The bundle has no assets at all.
    Empty,
    /// The `dregg://` fetch / attestation rejected (dead ref, tampered bytes,
    /// forged attestation, no quorum) — the REAL [`FetchError`], carried through.
    /// The bytes never reached a decode.
    Fetch(FetchError),
    /// The fetched, ATTESTED bytes did not decode as a canonical bundle encoding —
    /// the cell committed something that is not a `deos-web-cells` bundle (a wrong
    /// magic / truncated frame). Distinct from [`BundleError::Fetch`]: the
    /// attestation held, but the content is not a bundle.
    MalformedEncoding,
}

impl From<FetchError> for BundleError {
    fn from(e: FetchError) -> Self {
        BundleError::Fetch(e)
    }
}

/// The canonical-encoding magic — the first bytes of every published bundle, so a
/// fetch can tell a bundle cell from any other `dregg://` content.
const BUNDLE_MAGIC: &[u8; 8] = b"DEOSWB01";

impl WebBundle {
    /// Assemble a bundle from its `kind`, `entrypoint`, and `assets` — validating
    /// the entrypoint names an asset and asset names are unique.
    pub fn new(
        kind: BundleKind,
        entrypoint: impl Into<String>,
        assets: Vec<BundleAsset>,
    ) -> Result<Self, BundleError> {
        let entrypoint = entrypoint.into();
        if assets.is_empty() {
            return Err(BundleError::Empty);
        }
        // Unique asset names.
        let mut seen = std::collections::BTreeSet::new();
        for a in &assets {
            if !seen.insert(a.name.clone()) {
                return Err(BundleError::DuplicateAssetName { name: a.name.clone() });
            }
        }
        // The entrypoint must name an asset.
        if !assets.iter().any(|a| a.name == entrypoint) {
            return Err(BundleError::EntrypointNotAnAsset { entrypoint });
        }
        Ok(WebBundle { kind, entrypoint, assets })
    }

    /// A convenience: a STATIC HTML bundle of a single `index.html` document.
    pub fn static_html(html: impl Into<Vec<u8>>) -> WebBundle {
        // Single-asset, entrypoint = the doc; cannot fail validation.
        WebBundle {
            kind: BundleKind::StaticBundle,
            entrypoint: "index.html".to_string(),
            assets: vec![BundleAsset::new("index.html", "text/html", html.into())],
        }
    }

    /// A convenience: a LIVE-DOM snapshot bundle carrying a serialized DOM/signal
    /// state blob as `dom-state` plus a rendered `index.html` view. The leptosic
    /// "publish my app's live state" shape.
    pub fn live_dom_snapshot(
        rendered_html: impl Into<Vec<u8>>,
        dom_state: impl Into<Vec<u8>>,
    ) -> WebBundle {
        WebBundle {
            kind: BundleKind::LiveDomSnapshot,
            entrypoint: "index.html".to_string(),
            assets: vec![
                BundleAsset::new("index.html", "text/html", rendered_html.into()),
                BundleAsset::new("dom-state", "application/dom-snapshot", dom_state.into()),
            ],
        }
    }

    /// The bundle's assets in canonical (name-sorted) order — the order the content
    /// hash + manifest use, so identity is independent of construction order.
    pub fn canonical_assets(&self) -> Vec<&BundleAsset> {
        let mut v: Vec<&BundleAsset> = self.assets.iter().collect();
        v.sort_by(|a, b| a.name.cmp(&b.name));
        v
    }

    /// The bundle's **manifest** — its kind, entrypoint, and canonical per-asset
    /// digest table. The small content-addressed description a snapshot embeds.
    pub fn manifest(&self) -> BundleManifest {
        let asset_digests = self
            .canonical_assets()
            .into_iter()
            .map(|a| (a.name.clone(), a.content_type.clone(), a.digest()))
            .collect();
        BundleManifest {
            kind: self.kind,
            entrypoint: self.entrypoint.clone(),
            asset_digests,
        }
    }

    /// Look up an asset by name.
    pub fn asset(&self, name: &str) -> Option<&BundleAsset> {
        self.assets.iter().find(|a| a.name == name)
    }

    /// The **origin key** for an asset — the string the per-viewer membrane gates
    /// on (an asset is visible to a viewer iff the viewer's projected
    /// fetch-allowlist permits this origin). A stable `dregg-asset://<cell>/<name>`
    /// shape so asset visibility composes with the REAL allowlist meet.
    ///
    /// (Used by the `rehydrate` module to attenuate a weaker viewer's bundle to the
    /// assets its caps reach — never a parallel filter, the genuine
    /// `SurfaceCapability::may_fetch`.)
    pub fn asset_origin(cell: dregg_types::CellId, asset_name: &str) -> String {
        let mut hex = String::new();
        for b in cell.0.iter().take(4) {
            hex.push_str(&format!("{b:02x}"));
        }
        format!("dregg-asset://{hex}/{asset_name}")
    }

    /// The **canonical encoding** of the bundle — the exact bytes committed into
    /// the `dregg://` cell (so the cell's committed content hash IS the bundle's
    /// content hash). A length-prefixed, name-sorted framing behind [`BUNDLE_MAGIC`].
    /// Deterministic: identical bundles encode identically.
    pub fn encode(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(BUNDLE_MAGIC);
        out.push(self.kind.tag());
        // entrypoint
        out.extend_from_slice(&(self.entrypoint.len() as u64).to_le_bytes());
        out.extend_from_slice(self.entrypoint.as_bytes());
        // assets, name-sorted (canonical)
        let assets = self.canonical_assets();
        out.extend_from_slice(&(assets.len() as u64).to_le_bytes());
        for a in assets {
            out.extend_from_slice(&(a.name.len() as u64).to_le_bytes());
            out.extend_from_slice(a.name.as_bytes());
            out.extend_from_slice(&(a.content_type.len() as u64).to_le_bytes());
            out.extend_from_slice(a.content_type.as_bytes());
            out.extend_from_slice(&(a.bytes.len() as u64).to_le_bytes());
            out.extend_from_slice(&a.bytes);
        }
        out
    }

    /// Decode a canonical bundle encoding (the inverse of [`WebBundle::encode`]).
    /// Returns [`BundleError::MalformedEncoding`] on a wrong magic / truncated
    /// frame. Used by [`fetch_bundle`] on the VERIFIED bytes.
    pub fn decode(bytes: &[u8]) -> Result<WebBundle, BundleError> {
        let mut c = Cursor { bytes, pos: 0 };
        let magic = c.take(BUNDLE_MAGIC.len())?;
        if magic != BUNDLE_MAGIC {
            return Err(BundleError::MalformedEncoding);
        }
        let kind = match c.u8()? {
            0x01 => BundleKind::StaticBundle,
            0x02 => BundleKind::LiveDomSnapshot,
            _ => return Err(BundleError::MalformedEncoding),
        };
        let entrypoint = c.string()?;
        let n = c.u64()? as usize;
        let mut assets = Vec::with_capacity(n);
        for _ in 0..n {
            let name = c.string()?;
            let content_type = c.string()?;
            let blen = c.u64()? as usize;
            let bytes = c.take(blen)?.to_vec();
            assets.push(BundleAsset { name, content_type, bytes });
        }
        // Reconstruct via the validating constructor (entrypoint + uniqueness).
        WebBundle::new(kind, entrypoint, assets)
    }

    /// The bundle's **content hash** — `blake3` of its canonical encoding. THE
    /// content-address: two bundles are the same `dregg://` cell iff this matches.
    /// Equal to the committed content hash the cell carries after [`publish_bundle`].
    pub fn content_hash(&self) -> [u8; 32] {
        *blake3::hash(&self.encode()).as_bytes()
    }

    /// A stable `dregg-bundle://<hex content-hash>` identity string — the bundle's
    /// content-address as it would appear in a link (distinct from the per-cell
    /// `dregg://<cell>` locator, which [`publish_bundle`] returns).
    pub fn content_uri(&self) -> String {
        let h = self.content_hash();
        let mut s = String::from("dregg-bundle://");
        for b in h.iter() {
            s.push_str(&format!("{b:02x}"));
        }
        s
    }
}

/// **Publish** a [`WebBundle`] as a content-addressed `dregg://` cell.
///
/// `docs/deos/WEB-CELLS.md`: "publish/commit JS bundles, or even bundles of LIVE
/// DOM state, and share that as part of the web-of-cells." This commits the
/// bundle's canonical encoding into a REAL surface cell through the stable
/// [`WebOfCells::publish`] — so the cell's committed content hash IS
/// [`WebBundle::content_hash`] — and returns:
///
/// - the [`DreggUri`] (the bearer cap into the cell — the locator others fetch);
/// - a [`Sturdyref`] over that ref carrying the publisher's `lineage` (the
///   authority the bundle is served under) + a witness-log (here empty — a static
///   publish made no external interaction; a live-DOM snapshot would carry the
///   source surface's log) + `sources_reachable` — the cap-handle behind the
///   membrane that [`crate::rehydrate`] re-expands PER-VIEWER.
///
/// We add NO bespoke publish path: the content commitment, the attested root, the
/// trusted chrome are all the genuine web-of-cells machinery.
pub fn publish_bundle(
    web: &mut WebOfCells,
    seed: u8,
    bundle: &WebBundle,
    lineage: SurfaceCapability,
    witness_log: InteractionLog,
    sources_reachable: bool,
) -> (DreggUri, Sturdyref) {
    let encoded = bundle.encode();
    // The committed URL is the bundle's content-address — the trusted chrome shows
    // the bundle identity, drawn from the ledger, never the page.
    let committed_url = bundle.content_uri();
    let uri = web.publish(seed, &encoded, &committed_url);
    let sturdyref = Sturdyref::new(uri.clone(), lineage, witness_log, sources_reachable);
    (uri, sturdyref)
}

/// **Fetch** a published bundle through the REAL attested `dregg://` resolve, VERIFY
/// the attestation chain, and decode the verified bytes back into a [`WebBundle`].
///
/// The fetch runs FIRST and is verified BEFORE any decode: an unattested / tampered
/// / dead bundle yields a [`BundleError`] and NO bundle (the bytes never decode) —
/// confinement before content, the same discipline `rehydrate` enforces. Returns
/// the bundle + the ledger-drawn [`OriginChrome`] (the trusted-path badge: the cell
/// id + the committed content-address + the rights lineage + finality).
pub fn fetch_bundle(
    web: &WebOfCells,
    uri: &DreggUri,
) -> Result<(WebBundle, OriginChrome), BundleError> {
    // The REAL attested cross-cell read (no bespoke fetch).
    let (resource, chrome): (AttestedResource, OriginChrome) = web.fetch(uri)?;
    // The REAL client-side verification — content-addressed, receipt-in-stream,
    // receipt-stream-root reconstruction, quorum. An unattested scene rejects here.
    resource.verify()?;
    // Only NOW decode the verified bytes. (The cell could commit non-bundle content;
    // that is MalformedEncoding, distinct from an attestation failure.)
    let bundle = WebBundle::decode(&resource.content_bytes)?;
    Ok((bundle, chrome))
}

/// A tiny length-prefixed decode cursor (the inverse framing of
/// [`WebBundle::encode`]). Every short read is a [`BundleError::MalformedEncoding`].
struct Cursor<'a> {
    bytes: &'a [u8],
    pos: usize,
}

impl<'a> Cursor<'a> {
    fn take(&mut self, n: usize) -> Result<&'a [u8], BundleError> {
        let end = self.pos.checked_add(n).ok_or(BundleError::MalformedEncoding)?;
        if end > self.bytes.len() {
            return Err(BundleError::MalformedEncoding);
        }
        let slice = &self.bytes[self.pos..end];
        self.pos = end;
        Ok(slice)
    }

    fn u8(&mut self) -> Result<u8, BundleError> {
        Ok(self.take(1)?[0])
    }

    fn u64(&mut self) -> Result<u64, BundleError> {
        let b = self.take(8)?;
        let mut arr = [0u8; 8];
        arr.copy_from_slice(b);
        Ok(u64::from_le_bytes(arr))
    }

    fn string(&mut self) -> Result<String, BundleError> {
        let len = self.u64()? as usize;
        let b = self.take(len)?;
        String::from_utf8(b.to_vec()).map_err(|_| BundleError::MalformedEncoding)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use starbridge_web_surface::AuthRequired;

    fn html_bundle() -> WebBundle {
        WebBundle::new(
            BundleKind::StaticBundle,
            "index.html",
            vec![
                BundleAsset::new("index.html", "text/html", b"<h1>hello dregg</h1>".to_vec()),
                BundleAsset::new("app.js", "application/javascript", b"console.log(1)".to_vec()),
                BundleAsset::new("theme.css", "text/css", b"h1{color:rebeccapurple}".to_vec()),
            ],
        )
        .expect("valid bundle")
    }

    #[test]
    fn a_bundle_is_content_addressed_independent_of_asset_order() {
        // Identity is the canonical (name-sorted) encoding: the SAME assets in a
        // DIFFERENT order are the SAME cell.
        let a = html_bundle();
        let b = WebBundle::new(
            BundleKind::StaticBundle,
            "index.html",
            vec![
                BundleAsset::new("theme.css", "text/css", b"h1{color:rebeccapurple}".to_vec()),
                BundleAsset::new("app.js", "application/javascript", b"console.log(1)".to_vec()),
                BundleAsset::new("index.html", "text/html", b"<h1>hello dregg</h1>".to_vec()),
            ],
        )
        .unwrap();
        assert_eq!(a.content_hash(), b.content_hash());
        assert_eq!(a.content_uri(), b.content_uri());
    }

    #[test]
    fn a_changed_asset_byte_changes_the_content_address() {
        let a = html_bundle();
        let mut b = html_bundle();
        b.assets[1].bytes = b"console.log(2)".to_vec(); // app.js changed
        assert_ne!(a.content_hash(), b.content_hash());
    }

    #[test]
    fn the_kind_is_folded_into_the_address() {
        // A static bundle and a live-DOM snapshot with the SAME single asset are
        // DISTINCT cells (the kind tag is in the encoding).
        let html = b"<h1>x</h1>".to_vec();
        let st = WebBundle::new(
            BundleKind::StaticBundle,
            "index.html",
            vec![BundleAsset::new("index.html", "text/html", html.clone())],
        )
        .unwrap();
        let live = WebBundle::new(
            BundleKind::LiveDomSnapshot,
            "index.html",
            vec![BundleAsset::new("index.html", "text/html", html)],
        )
        .unwrap();
        assert_ne!(st.content_hash(), live.content_hash());
    }

    #[test]
    fn encode_decode_round_trips() {
        let a = html_bundle();
        let bytes = a.encode();
        let b = WebBundle::decode(&bytes).expect("decodes");
        assert_eq!(a, b);
        assert_eq!(a.content_hash(), b.content_hash());
    }

    #[test]
    fn a_malformed_encoding_is_rejected() {
        assert_eq!(WebBundle::decode(b"not a bundle"), Err(BundleError::MalformedEncoding));
        // Right magic, truncated body.
        let mut bytes = html_bundle().encode();
        bytes.truncate(BUNDLE_MAGIC.len() + 3);
        assert_eq!(WebBundle::decode(&bytes), Err(BundleError::MalformedEncoding));
    }

    #[test]
    fn an_entrypoint_naming_no_asset_is_rejected() {
        let err = WebBundle::new(
            BundleKind::StaticBundle,
            "missing.html",
            vec![BundleAsset::new("index.html", "text/html", b"x".to_vec())],
        )
        .unwrap_err();
        assert_eq!(err, BundleError::EntrypointNotAnAsset { entrypoint: "missing.html".to_string() });
    }

    #[test]
    fn duplicate_asset_names_are_rejected() {
        let err = WebBundle::new(
            BundleKind::StaticBundle,
            "index.html",
            vec![
                BundleAsset::new("index.html", "text/html", b"a".to_vec()),
                BundleAsset::new("index.html", "text/html", b"b".to_vec()),
            ],
        )
        .unwrap_err();
        assert_eq!(err, BundleError::DuplicateAssetName { name: "index.html".to_string() });
    }

    // ── publish → fetch → verify: the bundle IS the committed content. ──

    #[test]
    fn publish_then_fetch_round_trips_through_the_real_attested_path() {
        let mut web = WebOfCells::new(3);
        let bundle = html_bundle();
        let lineage = SurfaceCapability::root(crate::tests_support::cid(1), AuthRequired::Either);
        let (uri, _sturdyref) = publish_bundle(
            &mut web,
            1,
            &bundle,
            lineage,
            InteractionLog::new(),
            false,
        );

        let (fetched, chrome) = fetch_bundle(&web, &uri).expect("fetch + verify + decode");
        // The fetched bundle IS the published one (content-addressed).
        assert_eq!(fetched, bundle);
        assert_eq!(fetched.content_hash(), bundle.content_hash());
        // The committed content hash on the cell == the bundle's content hash:
        // the cell's identity-of-content IS the bundle's content-address.
        // (fetch's verify() already checked content_bytes hashes to the commitment.)
        // The trusted chrome shows the bundle's content-address, drawn from the ledger.
        assert_eq!(chrome.committed_url.as_deref(), Some(bundle.content_uri().as_str()));
        assert!(chrome.finalized);
    }

    #[test]
    fn an_attested_non_bundle_cell_yields_no_bundle() {
        // The fetch verifies BEFORE decode: a cell that committed content which is
        // NOT a bundle (here, raw bytes published directly through the web-of-cells)
        // passes the attestation chain but FAILS the bundle decode — MalformedEncoding,
        // no bundle. (The lower-level "lying node serves uncommitted bytes" tooth —
        // ContentDoesNotMatchCommitment — is the web-of-cells' own internal property,
        // tested in starbridge-web-surface; from here we exercise the public path: an
        // attested cell whose content is not a bundle yields no bundle.)
        let mut web = WebOfCells::new(3);
        let uri = web.publish(2, b"just some html, not a bundle encoding", "dregg://raw");
        // The attestation HOLDS (it is a genuine finalized read)…
        let (resource, _chrome) = web.fetch(&uri).expect("the raw cell resolves + attests");
        assert!(resource.verify().is_ok(), "the attestation chain still verifies");
        // …but fetch_bundle's decode rejects: attested, but not a bundle.
        assert_eq!(fetch_bundle(&web, &uri), Err(BundleError::MalformedEncoding));
    }

    #[test]
    fn a_dead_ref_yields_no_bundle() {
        let web = WebOfCells::new(3);
        let dead = DreggUri::new(crate::tests_support::cid(99));
        assert_eq!(fetch_bundle(&web, &dead), Err(BundleError::Fetch(FetchError::OriginNotFound)));
    }

    #[test]
    fn the_manifest_digest_is_stable_and_small() {
        // The manifest digest pins the bundle shape (one 32-byte hash) without the
        // bytes — what a DomSnapshot embeds. Stable across canonical reordering.
        let a = html_bundle();
        let mut shuffled = a.clone();
        shuffled.assets.reverse();
        assert_eq!(a.manifest().digest(), shuffled.manifest().digest());
        // And it tracks the bytes: change one asset → the digest changes.
        let mut changed = a.clone();
        changed.assets[0].bytes = b"<h1>different</h1>".to_vec();
        assert_ne!(a.manifest().digest(), changed.manifest().digest());
    }
}
