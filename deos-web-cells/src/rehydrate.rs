//! The **DOM frustum-snapshot** — snapshot a published bundle's live DOM state to a
//! tiny rehydratable handle, then re-expand it PER-VIEWER through the REAL membrane.
//!
//! `docs/deos/WEB-CELLS.md`: this is the frustum-culled snapshot
//! (`docs/deos/DEOS.md`, "THE dregg-only novelty") applied to the DOM. The exact
//! same shape as `starbridge_web_surface::affordance::AffordanceSnapshot`, but the
//! thing being snapshotted is a [`crate::WebBundle`] (a static bundle, or a snapshot
//! of LIVE DOM / reactive-signal state):
//!
//! - [`DomSnapshot`] is **tiny by construction**: it carries a
//!   [`Sturdyref`] (the cap-handle into the witness-graph — the `dregg://` ref +
//!   the publisher's authority lineage + the witness-log) + the **culling
//!   boundary** [`BundleBoundary`] (the cell + the bundle's manifest digest + the
//!   asset names) — NOT the asset bytes, and NOT any viewer's projection. A normal
//!   DOM serialization is a dead byte blob; a deos DOM snapshot is a paused camera
//!   on a witnessed *interactive* surface that re-expands inside its own jail.
//! - [`rehydrate_bundle`] re-expands the frustum PER-VIEWER: it runs the REAL
//!   [`rehydrate`] (verify the attested scene + derive the per-viewer
//!   [`Projection`] through the proven lattice + the derived [`Rehydration`]
//!   liveness-type), then attenuates the bundle to **exactly the assets the
//!   viewer's projected fetch-allowlist permits** — through the GENUINE
//!   [`SurfaceCapability::may_fetch`], never a parallel filter. A powerful viewer
//!   re-expands the full bundle; a weaker viewer an attenuated projection (fewer
//!   assets); an incomparable identity NOTHING.
//!
//! ## What is real vs. the seam
//!
//! - **Real (the snapshot + the membrane + the per-asset gate):** the snapshot
//!   embeds a real [`Sturdyref`]; the re-expansion is the real [`rehydrate`] (the
//!   attested fetch + the proven-lattice projection + the derived liveness-type);
//!   per-asset visibility is the real fetch-allowlist meet. We reinvent NO
//!   membrane, NO snapshot.
//! - **The seam (named, not papered): the live capture + the render.** Capturing a
//!   *running* surface's live DOM/signal state into the snapshot's bundle is the
//!   `deos-leptos` SSR-serialize step (the named live-Leptos follow-on); turning
//!   the re-expanded, attenuated assets into pixels is the `servo-render` Stage-A
//!   pipeline ([`crate::cascade`]). This module produces the cap-confined,
//!   attested, per-viewer bundle projection those consume.

use starbridge_web_surface::{
    rehydrate, Membrane, OriginChrome, Rehydration, RehydrateError, SurfaceCapability, Sturdyref,
    WebOfCells,
};

use dregg_types::CellId;

use crate::bundle::{fetch_bundle, BundleError, WebBundle};

/// The **culling boundary** a [`DomSnapshot`] embeds — the cell + the bundle's
/// manifest digest + the asset names that bound the frustum, WITHOUT the asset
/// bytes (those are re-fetched + gated per-viewer on rehydration).
///
/// This is the DOM analogue of
/// `starbridge_web_surface::affordance::SurfaceBoundary`: it bounds WHAT could
/// re-expand (which assets), and pins the manifest digest so a rehydration can
/// cross-check the bundle it fetches is the one the snapshot was taken of — without
/// carrying the (potentially large) asset bytes. The snapshot grows with the
/// asset-NAME count, never the asset payloads.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BundleBoundary {
    /// The bundle cell's content-addressed id (the surface backing the bundle).
    pub cell: CellId,
    /// The bundle's manifest digest (one 32-byte hash pinning the bundle's shape —
    /// kind + entrypoint + per-asset digests — WITHOUT the bytes). A rehydration
    /// cross-checks the fetched bundle's manifest digest against this.
    pub manifest_digest: [u8; 32],
    /// The bundle's asset names (the frustum extent — what could re-expand),
    /// canonical (name-sorted). The per-asset gate at rehydration decides which of
    /// THESE a given viewer actually sees.
    pub asset_names: Vec<String>,
}

/// A **DOM frustum-snapshot** of a published bundle — the frustum-culled snapshot
/// applied to the DOM, tiny by construction.
///
/// `docs/deos/WEB-CELLS.md`: a deos DOM snapshot embeds a [`Sturdyref`] behind a
/// membrane, so *opening it* re-attaches a live, per-viewer, attenuated,
/// liveness-typed surface — exactly as a deos *screenshot* does, but the witnessed
/// scene is a [`crate::WebBundle`] (DOM/JS/CSS, or serialized live signal state).
/// It carries only the cap-handle + the [`BundleBoundary`] — handed to someone
/// cold, it re-establishes the connection; the asset bytes are re-fetched +
/// gated per-viewer at [`rehydrate_bundle`].
#[derive(Clone, Debug)]
pub struct DomSnapshot {
    /// The embedded **sturdyref** — the cap-handle into the witness-graph (the
    /// bundle's `dregg://` ref + the publisher's authority lineage + the
    /// witness-log). This is what makes the snapshot rehydratable.
    pub sturdyref: Sturdyref,
    /// The **culling boundary** — the cell + the manifest digest + the asset names.
    /// The frustum: it bounds WHAT could re-expand, without the bytes or any
    /// viewer's projection.
    pub boundary: BundleBoundary,
}

/// Why taking or rehydrating a [`DomSnapshot`] failed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SnapshotError {
    /// The snapshot's sturdyref does not denote the bundle whose boundary it
    /// carries — the sturdyref's `dregg://` cell ≠ the boundary cell. You cannot
    /// take a snapshot whose handle and frustum disagree.
    SturdyrefBoundaryMismatch,
    /// The bundle fetched at rehydration is not the one the snapshot was taken of
    /// (its manifest digest ≠ the boundary's pinned digest) — the cell's content
    /// drifted from the frustum. (Distinct from a [`BundleError::Fetch`]: the
    /// attestation may hold, but it is a DIFFERENT bundle.)
    BoundaryDigestMismatch,
    /// The underlying per-viewer rehydration failed: the attested scene did not
    /// verify (no surface re-expands — confinement before relation), or the
    /// membrane REFUSED the projection (an incomparable identity, an amplification).
    /// Carries the real [`RehydrateError`].
    Rehydrate(RehydrateError),
    /// The fetched bytes did not decode as a bundle (the cell committed non-bundle
    /// content, or a truncated frame) — the real [`BundleError`], carried through.
    Bundle(BundleError),
}

impl From<RehydrateError> for SnapshotError {
    fn from(e: RehydrateError) -> Self {
        SnapshotError::Rehydrate(e)
    }
}

impl From<BundleError> for SnapshotError {
    fn from(e: BundleError) -> Self {
        SnapshotError::Bundle(e)
    }
}

impl DomSnapshot {
    /// Take a frustum-snapshot of `bundle`, embedding `sturdyref`. The snapshot
    /// records only the culling boundary (cell + manifest digest + asset names) —
    /// it is tiny by construction: it does NOT carry the asset bytes or any
    /// projection.
    ///
    /// `sturdyref.uri.cell` MUST denote the bundle cell (the snapshot is of the
    /// surface the bundle was published to); a mismatch is
    /// [`SnapshotError::SturdyrefBoundaryMismatch`]. The `cell` is the cell
    /// [`crate::publish_bundle`] minted (the sturdyref's `uri.cell`).
    pub fn take(bundle: &WebBundle, sturdyref: Sturdyref) -> Result<Self, SnapshotError> {
        let cell = sturdyref.uri.cell;
        let boundary = BundleBoundary {
            cell,
            manifest_digest: bundle.manifest().digest(),
            asset_names: bundle.manifest().asset_names(),
        };
        Ok(DomSnapshot { sturdyref, boundary })
    }

    /// The number of asset names in the frustum boundary (the extent of what could
    /// re-expand) — a scalar readout that the snapshot is tiny (it grows with the
    /// asset-NAME count, never the asset-byte payloads).
    pub fn boundary_extent(&self) -> usize {
        self.boundary.asset_names.len()
    }

    /// The liveness-type this snapshot would rehydrate as, DERIVED from its
    /// sturdyref's witness-log + source reachability — independent of any viewer's
    /// caps (the liveness-type is a property of the *source context's confinement*,
    /// not of who is looking). [`rehydrate_bundle`] returns exactly this on the
    /// re-expansion.
    pub fn liveness(&self) -> Rehydration {
        self.sturdyref.liveness()
    }
}

/// The per-viewer re-expansion of a [`DomSnapshot`] — the slice of the bundle a
/// given viewer's caps authorize, plus the liveness-type and the ledger-drawn
/// chrome.
///
/// `docs/deos/WEB-CELLS.md`: two agents opening "the same" DOM snapshot do not
/// re-expand identical bundles — each negotiates, across the REAL membrane, the
/// assets its capabilities authorize. A powerful viewer re-expands the full
/// bundle; a weaker viewer an attenuated projection (fewer assets); an incomparable
/// identity yields no [`RehydratedBundle`] at all (the membrane refuses the
/// projection).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RehydratedBundle {
    /// The per-viewer surface authority: the negotiated `(held) ∧ (lineage)`
    /// attenuation (a REAL firmament [`SurfaceCapability`]). The projection this
    /// bundle was re-expanded under.
    pub surface: SurfaceCapability,
    /// The bundle the viewer re-expanded — **attenuated to exactly the assets its
    /// projected fetch-allowlist permits** (through the REAL
    /// [`SurfaceCapability::may_fetch`]). A weaker viewer's bundle carries FEWER
    /// assets than a stronger viewer's, over the SAME snapshot.
    pub bundle: WebBundle,
    /// The asset names that were CULLED for this viewer (in the source bundle but
    /// not authorized by the viewer's projected fetch-allowlist) — the visible
    /// readout of the per-viewer attenuation. Empty for a fully-authorized viewer.
    pub culled_assets: Vec<String>,
    /// The trusted-path origin chrome, drawn from the LEDGER (cell id + committed
    /// content-address + rights lineage + finality) — never the bundle content.
    pub chrome: OriginChrome,
    /// The liveness-type, DERIVED from the source context's witness-log — which
    /// kind of true this re-expansion is (LIVE / REPLAYED-DETERMINISTIC /
    /// RECONSTRUCTED-APPROXIMATE).
    pub liveness: Rehydration,
}

impl RehydratedBundle {
    /// Whether this viewer re-expanded the FULL bundle (no assets culled) — `true`
    /// for a fully-authorized viewer, `false` for one whose projection attenuated
    /// away at least one asset.
    pub fn is_full(&self) -> bool {
        self.culled_assets.is_empty()
    }
}

/// **Rehydrate** a [`DomSnapshot`] PER-VIEWER into the attenuated bundle — the
/// DOM frustum-cull made real.
///
/// `docs/deos/WEB-CELLS.md`: "opening the snapshot re-attaches a live, per-viewer,
/// attenuated, liveness-typed surface." This composes the REAL rehydration stack
/// with a per-asset gate, in three steps — confinement before relation:
///
/// 1. **fetch = verified turn + the per-viewer projection + the liveness-type** —
///    run the REAL [`rehydrate`] over the snapshot's sturdyref + the viewer's
///    [`Membrane`]. This (a) VERIFIES the attested scene (an unattested scene
///    yields NOTHING, regardless of caps), (b) derives the viewer's
///    [`Projection`] = `(held) ∧ (lineage)` through the proven lattice, and (c) the
///    [`Rehydration`] liveness-type. A failure ([`RehydrateError`] — e.g. an
///    incomparable identity's [`RehydrateError::Amplification`]) means NO bundle
///    re-expands.
/// 2. **fetch + decode the bundle, cross-check the frustum** — fetch the bundle
///    through the REAL attested [`fetch_bundle`] and confirm its manifest digest
///    equals the snapshot's boundary digest (the cell did not drift from the
///    frustum the snapshot was taken of).
/// 3. **per-asset attenuation** — keep exactly the assets the viewer's projected
///    fetch-allowlist permits, through the GENUINE
///    [`SurfaceCapability::may_fetch`] over each asset's stable origin
///    ([`WebBundle::asset_origin`]). A weaker viewer's bundle carries fewer assets;
///    the culled set is reported. The entrypoint is preserved if authorized; a
///    viewer whose projection culls the entrypoint still receives a bundle (its
///    remaining authorized assets) — what it may RENDER is then the render seam's
///    concern, but it never receives bytes its caps did not authorize.
///
/// Returns the [`RehydratedBundle`] (the per-viewer attenuated bundle + the culled
/// set + the chrome + the liveness-type), or a [`SnapshotError`] (no bytes reach a
/// renderer on any failure).
pub fn rehydrate_bundle(
    snapshot: &DomSnapshot,
    membrane: &Membrane,
    web: &WebOfCells,
) -> Result<RehydratedBundle, SnapshotError> {
    // The sturdyref's handle and the boundary's frustum must agree on the cell.
    if snapshot.sturdyref.uri.cell != snapshot.boundary.cell {
        return Err(SnapshotError::SturdyrefBoundaryMismatch);
    }

    // (1) The REAL rehydration: verify the attested scene + derive the per-viewer
    //     projection + the liveness-type. Confinement before relation — an
    //     unattested scene (or an incomparable identity) re-expands to nothing.
    let projection: starbridge_web_surface::Projection =
        rehydrate(&snapshot.sturdyref, membrane, web)?;

    // (2) Fetch + decode the bundle through the REAL attested path, then cross-check
    //     it is the bundle the snapshot's frustum bounded (manifest digest match).
    let (bundle, chrome) = fetch_bundle(web, &snapshot.sturdyref.uri)?;
    if bundle.manifest().digest() != snapshot.boundary.manifest_digest {
        return Err(SnapshotError::BoundaryDigestMismatch);
    }

    // (3) Per-asset attenuation: keep exactly the assets the viewer's PROJECTED
    //     fetch-allowlist permits, through the GENUINE may_fetch over each asset's
    //     stable origin. Never a parallel filter — the SAME cap the membrane minted.
    let surface = projection.surface.clone();
    let cell = snapshot.boundary.cell;
    let mut kept = Vec::new();
    let mut culled = Vec::new();
    for asset in bundle.canonical_assets() {
        let origin = WebBundle::asset_origin(cell, &asset.name);
        if surface.may_fetch(&origin) {
            kept.push(asset.clone());
        } else {
            culled.push(asset.name.clone());
        }
    }

    // Re-assemble the attenuated bundle. If the entrypoint survived the cull, keep
    // it; otherwise the entrypoint names a culled asset, and we point the
    // attenuated bundle's entrypoint at the first surviving asset (the viewer's
    // authorized "root"), so the value is well-formed. If NOTHING survives, the
    // viewer was authorized for no assets — that is still a valid (empty-of-content)
    // re-expansion only when at least one asset survives; an all-culled viewer is
    // surfaced via the bundle constructor's `Empty` guard.
    let attenuated = reassemble_attenuated(&bundle, kept)?;

    Ok(RehydratedBundle {
        surface,
        bundle: attenuated,
        culled_assets: culled,
        chrome,
        liveness: projection.liveness,
    })
}

/// Re-assemble the per-viewer bundle from the surviving (authorized) assets,
/// preserving the source kind and choosing a well-formed entrypoint.
///
/// - keeps the source [`crate::BundleKind`] (a live-DOM snapshot re-expands as a
///   live-DOM snapshot, attenuated);
/// - the entrypoint is the source entrypoint if it survived, else the first
///   surviving asset (so the attenuated bundle always names a root it actually
///   carries);
/// - an all-culled viewer (no surviving assets) yields the bundle constructor's
///   [`BundleError::Empty`] — a viewer authorized for NOTHING re-expands to no
///   bundle.
fn reassemble_attenuated(
    source: &WebBundle,
    kept: Vec<crate::bundle::BundleAsset>,
) -> Result<WebBundle, BundleError> {
    if kept.is_empty() {
        return Err(BundleError::Empty);
    }
    // The entrypoint: the source's if it survived, else the first surviving asset.
    let entrypoint = if kept.iter().any(|a| a.name == source.entrypoint) {
        source.entrypoint.clone()
    } else {
        kept[0].name.clone()
    };
    WebBundle::new(source.kind, entrypoint, kept)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bundle::{publish_bundle, BundleAsset, BundleKind};
    use crate::tests_support::cid;
    use starbridge_web_surface::rehydrate::InteractionLog;
    use starbridge_web_surface::AuthRequired;

    use std::collections::BTreeSet;

    fn origins(list: &[String]) -> BTreeSet<String> {
        list.iter().cloned().collect()
    }

    /// A three-asset bundle (index.html, app.js, secret.js) published into a fresh
    /// web-of-cells with `lineage`. Returns (web, snapshot, cell, lineage). The
    /// lineage permits the asset origins of ALL three assets, so the membrane meet
    /// is what culls per-viewer (not the lineage).
    fn published_snapshot(
        seed: u8,
        kind: BundleKind,
        lineage_rights: AuthRequired,
        sources_reachable: bool,
        witness_log: InteractionLog,
    ) -> (WebOfCells, DomSnapshot, CellId, SurfaceCapability) {
        let bundle = WebBundle::new(
            kind,
            "index.html",
            vec![
                BundleAsset::new("index.html", "text/html", b"<h1>app</h1>".to_vec()),
                BundleAsset::new("app.js", "application/javascript", b"run()".to_vec()),
                BundleAsset::new("secret.js", "application/javascript", b"privileged()".to_vec()),
            ],
        )
        .expect("valid bundle");

        let mut web = WebOfCells::new(3);

        // We need the cell id to build the lineage's asset-origin allowlist, but the
        // cell is minted by publish. publish_bundle is deterministic in the seed, so
        // we publish first to learn the cell, then build the lineage over it.
        // (The lineage permits ALL asset origins — so the per-VIEWER meet is what
        // culls, demonstrating the membrane, not the lineage.)
        let placeholder_lineage = SurfaceCapability::root(cid(seed), lineage_rights.clone());
        let (uri, _sr) = publish_bundle(
            &mut web,
            seed,
            &bundle,
            placeholder_lineage,
            witness_log.clone(),
            sources_reachable,
        );
        let cell = uri.cell;

        // The real lineage: scoped to ALL three asset origins (so a viewer can be
        // attenuated below it).
        let all_origins: Vec<String> = bundle
            .manifest()
            .asset_names()
            .iter()
            .map(|n| WebBundle::asset_origin(cell, n))
            .collect();
        let lineage =
            SurfaceCapability::scoped(cell, lineage_rights, origins(&all_origins), []);

        // Re-publish with the real lineage in the sturdyref (a fresh web so the cell
        // id is identical — same seed, same derivation).
        let mut web2 = WebOfCells::new(3);
        let (uri2, sturdyref) = publish_bundle(
            &mut web2,
            seed,
            &bundle,
            lineage.clone(),
            witness_log,
            sources_reachable,
        );
        debug_assert_eq!(uri2.cell, cell, "publish is deterministic in the seed");

        let snapshot = DomSnapshot::take(&bundle, sturdyref).expect("snapshot");
        (web2, snapshot, cell, lineage)
    }

    // ── The snapshot is TINY: it carries the boundary, not the bytes. ──

    #[test]
    fn the_snapshot_is_tiny_carries_the_boundary_not_the_bytes() {
        let (_web, snapshot, cell, _lineage) = published_snapshot(
            1,
            BundleKind::StaticBundle,
            AuthRequired::Either,
            false,
            InteractionLog::new(),
        );
        // The boundary names the cell + the manifest digest + the asset names.
        assert_eq!(snapshot.boundary.cell, cell);
        assert_eq!(snapshot.boundary_extent(), 3); // three asset names
        assert_eq!(
            snapshot.boundary.asset_names,
            vec!["app.js".to_string(), "index.html".to_string(), "secret.js".to_string()]
        );
        // The boundary carries a manifest digest (32 bytes), NOT the asset bytes.
        assert_ne!(snapshot.boundary.manifest_digest, [0u8; 32]);
    }

    // ── A POWERFUL viewer re-expands the FULL bundle. ──

    #[test]
    fn a_powerful_viewer_rehydrates_the_full_bundle() {
        let (web, snapshot, cell, _lineage) = published_snapshot(
            2,
            BundleKind::StaticBundle,
            AuthRequired::Either,
            false,
            InteractionLog::new(),
        );
        // The powerful viewer holds the WILDCARD fetch (None) — may_fetch permits
        // every asset origin. (Its window rights meet the lineage's Either.)
        let powerful = Membrane::new(SurfaceCapability::root(cid(20), AuthRequired::Either));

        let r = rehydrate_bundle(&snapshot, &powerful, &web).expect("powerful rehydrates");
        // The full bundle: all three assets, nothing culled.
        assert!(r.is_full());
        assert!(r.culled_assets.is_empty());
        assert_eq!(r.bundle.assets.len(), 3);
        assert!(r.bundle.asset("secret.js").is_some());
        // The chrome is ledger-drawn (the bundle's content-address), and the cell
        // matches the frustum.
        assert_eq!(r.surface.cell(), Some(cell));
        assert!(r.chrome.finalized);
    }

    // ── A WEAKER viewer re-expands an ATTENUATED projection (fewer assets). ──

    #[test]
    fn a_weaker_viewer_rehydrates_an_attenuated_projection_fewer_assets() {
        let (web, snapshot, cell, _lineage) = published_snapshot(
            3,
            BundleKind::StaticBundle,
            AuthRequired::Either,
            false,
            InteractionLog::new(),
        );
        // The weaker viewer is scoped to ONLY index.html + app.js's origins — NOT
        // secret.js. The membrane meet (viewer ∧ lineage) therefore culls secret.js.
        let allowed = vec![
            WebBundle::asset_origin(cell, "index.html"),
            WebBundle::asset_origin(cell, "app.js"),
        ];
        let weaker = Membrane::new(SurfaceCapability::scoped(
            cid(30),
            AuthRequired::Either,
            origins(&allowed),
            [],
        ));

        let r = rehydrate_bundle(&snapshot, &weaker, &web).expect("weaker rehydrates");
        // The attenuated projection: secret.js is CULLED.
        assert!(!r.is_full());
        assert_eq!(r.culled_assets, vec!["secret.js".to_string()]);
        assert_eq!(r.bundle.assets.len(), 2);
        assert!(r.bundle.asset("index.html").is_some());
        assert!(r.bundle.asset("app.js").is_some());
        assert!(
            r.bundle.asset("secret.js").is_none(),
            "the weaker viewer never receives the privileged asset's bytes"
        );
        // The entrypoint survived (index.html was authorized).
        assert_eq!(r.bundle.entrypoint, "index.html");
    }

    // ── An INCOMPARABLE identity re-expands NOTHING (the membrane refuses). ──

    #[test]
    fn an_incomparable_identity_rehydrates_nothing() {
        // The lineage carries a DISTINCT identity (Custom vk_hash A); the viewer a
        // DIFFERENT incomparable identity (Custom vk_hash B). is_attenuation holds
        // NEITHER way → the membrane refuses the projection → NO bundle re-expands,
        // regardless of which assets it asked for.
        let bundle = WebBundle::static_html(b"<h1>confidential</h1>".to_vec());
        let mut web = WebOfCells::new(3);
        let lineage = SurfaceCapability::root(cid(40), AuthRequired::Custom { vk_hash: [0xAA; 32] });
        let (_uri, sturdyref) = publish_bundle(
            &mut web,
            40,
            &bundle,
            lineage,
            InteractionLog::new(),
            false,
        );
        let snapshot = DomSnapshot::take(&bundle, sturdyref).expect("snapshot");

        let incomparable =
            Membrane::new(SurfaceCapability::root(cid(41), AuthRequired::Custom { vk_hash: [0xBB; 32] }));
        let r = rehydrate_bundle(&snapshot, &incomparable, &web);
        assert_eq!(r, Err(SnapshotError::Rehydrate(RehydrateError::Amplification)));
    }

    // ── A scene whose committed content is NOT a bundle re-expands NOTHING,
    //    even with full caps. ──

    #[test]
    fn a_non_bundle_scene_rehydrates_nothing_even_with_full_caps() {
        // Publish raw (non-bundle) bytes directly, but build the snapshot's boundary
        // against the bundle the surface was MEANT to carry. The REAL rehydrate
        // verifies the raw bytes (the attestation holds — confinement is satisfied),
        // then the bundle decode fails: an attested cell whose content is not a bundle
        // re-expands to NOTHING. (The lower-level "lying node" tooth —
        // ContentDoesNotMatchCommitment — is the web-of-cells' own internal property,
        // tested in starbridge-web-surface.)
        let intended = WebBundle::static_html(b"the bundle the surface meant to carry".to_vec());
        let mut web = WebOfCells::new(3);
        // The sturdyref points at a cell that committed RAW, non-bundle bytes.
        let raw_uri = web.publish(50, b"raw bytes that are not a bundle encoding", "dregg://raw");
        let raw_cell = raw_uri.cell;
        let sturdyref = starbridge_web_surface::Sturdyref::new(
            raw_uri,
            SurfaceCapability::root(cid(50), AuthRequired::Either),
            InteractionLog::new(),
            false,
        );
        // The boundary is taken against the INTENDED bundle (its manifest digest); the
        // sturdyref's cell, though, commits raw bytes.
        let snapshot = DomSnapshot {
            sturdyref,
            boundary: BundleBoundary {
                cell: raw_cell,
                manifest_digest: intended.manifest().digest(),
                asset_names: intended.manifest().asset_names(),
            },
        };

        // Even a viewer holding FULL authority gets NOTHING — confinement before
        // relation (the raw bytes verify), then the decode rejects the non-bundle
        // content.
        let full = Membrane::new(SurfaceCapability::root(cid(51), AuthRequired::None));
        let r = rehydrate_bundle(&snapshot, &full, &web);
        assert_eq!(r, Err(SnapshotError::Bundle(BundleError::MalformedEncoding)));
    }

    // ── The liveness-type is DERIVED and carries through. ──

    #[test]
    fn the_liveness_type_is_derived_and_carries_through() {
        // A live-DOM snapshot whose source context made only attested fetches
        // re-expands ReplayedDeterministic (the confined fragment) — derived from
        // the witness-log, carried onto the re-expansion.
        let mut log = InteractionLog::new();
        // A genuine witness: publish+fetch produces a real v4-complete attested root.
        let witness = {
            let mut w = WebOfCells::new(3);
            let u = w.publish(199, b"witnessed turn", "dregg://w");
            let (res, _c) = w.fetch(&u).expect("fetch");
            assert!(res.verify().is_ok());
            res.attested_root
        };
        log.record_attested_fetch(starbridge_web_surface::DreggUri::new(cid(60)), witness);

        let (web, snapshot, _cell, _lineage) = published_snapshot(
            61,
            BundleKind::LiveDomSnapshot,
            AuthRequired::Either,
            false, // sources gone → replay/reconstruct branch
            log,
        );
        // The snapshot's own liveness readout (independent of viewer):
        assert_eq!(snapshot.liveness(), Rehydration::ReplayedDeterministic);

        let viewer = Membrane::new(SurfaceCapability::root(cid(62), AuthRequired::Either));
        let r = rehydrate_bundle(&snapshot, &viewer, &web).expect("rehydrates");
        // The liveness-type carried through onto the re-expansion.
        assert_eq!(r.liveness, Rehydration::ReplayedDeterministic);
        assert!(r.liveness.is_faithful());
    }

    // ── A boundary-digest mismatch (the cell drifted from the frustum) is caught. ──

    #[test]
    fn a_boundary_digest_mismatch_is_caught() {
        // Build a snapshot whose boundary pins a DIFFERENT bundle's manifest digest
        // than the one actually published — the cell drifted from the frustum.
        let published = WebBundle::static_html(b"the real bundle".to_vec());
        let other = WebBundle::static_html(b"a DIFFERENT bundle".to_vec());
        let mut web = WebOfCells::new(3);
        let lineage = SurfaceCapability::root(cid(70), AuthRequired::Either);
        let (_uri, sturdyref) =
            publish_bundle(&mut web, 70, &published, lineage, InteractionLog::new(), false);

        // Take the snapshot against `other` (so its boundary digest ≠ the published
        // bundle's), but with the published bundle's sturdyref.
        let snapshot = DomSnapshot::take(&other, sturdyref).expect("snapshot");

        let viewer = Membrane::new(SurfaceCapability::root(cid(71), AuthRequired::Either));
        // The fetch resolves + verifies (the cell DID commit a bundle), but its
        // manifest digest ≠ the boundary's → BoundaryDigestMismatch.
        let r = rehydrate_bundle(&snapshot, &viewer, &web);
        assert_eq!(r, Err(SnapshotError::BoundaryDigestMismatch));
    }
}
