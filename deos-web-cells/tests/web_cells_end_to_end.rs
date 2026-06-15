//! End-to-end: a live-DOM / JS-bundle web-of-cells cell, the whole story.
//!
//! `docs/deos/WEB-CELLS.md`, demonstrated against the STABLE
//! `starbridge-web-surface` API — never a parallel model:
//!
//! 1. **publish → fetch** a `WebBundle` as a content-addressed `dregg://` cell
//!    (the cell's committed content hash IS the bundle's content hash; the fetch is
//!    the REAL attested cross-cell read + verify).
//! 2. **the cap tooth** — an unattested / tampered bundle yields no bytes (the
//!    `verify()` rejects before any decode).
//! 3. **the DOM frustum-snapshot → per-viewer rehydration** — a tiny `DomSnapshot`
//!    re-expands PER-VIEWER through the REAL `Membrane`: a powerful viewer gets the
//!    full bundle, a weaker viewer an attenuated projection (fewer assets), an
//!    incomparable identity nothing.
//! 4. **transclusion-with-provenance** — another surface includes a bundle fragment
//!    carrying the source's receipt-pinned provenance (the live quote), via the
//!    REAL `TranscludedField`.

use deos_web_cells::{
    fetch_bundle, publish_bundle, rehydrate_bundle, transclude_bundle_fragment, BundleAsset,
    BundleError, BundleKind, CascadeError, DomSnapshot, SnapshotError, WebBundle,
};
use deos_web_cells::tests_support::cid;

use starbridge_web_surface::rehydrate::InteractionLog;
use starbridge_web_surface::{
    AuthRequired, DreggUri, FetchError, Membrane, RehydrateError, SurfaceCapability,
    WebOfCells,
};

use std::collections::BTreeSet;

fn origins(list: &[String]) -> BTreeSet<String> {
    list.iter().cloned().collect()
}

/// A leptosic "publish my app's live state" bundle: a rendered view + a serialized
/// signal-state blob + a privileged admin script — the live-DOM snapshot shape.
fn live_app_bundle() -> WebBundle {
    WebBundle::new(
        BundleKind::LiveDomSnapshot,
        "index.html",
        vec![
            BundleAsset::new(
                "index.html",
                "text/html",
                b"<div id=app><h1>counter: 3</h1></div>".to_vec(),
            ),
            BundleAsset::new(
                "dom-state",
                "application/dom-snapshot",
                // the serialized live signal graph — a Leptos app's state.
                br#"{"signals":{"counter":3},"effects":["render"]}"#.to_vec(),
            ),
            BundleAsset::new(
                "admin.js",
                "application/javascript",
                b"resetAllUsers()".to_vec(),
            ),
        ],
    )
    .expect("a valid live-DOM snapshot bundle")
}

#[test]
fn the_whole_story_publish_fetch_snapshot_rehydrate_transclude() {
    // ── (1) PUBLISH a live-DOM snapshot bundle as a content-addressed dregg:// cell. ──
    let bundle = live_app_bundle();
    let mut web = WebOfCells::new(3);

    // Learn the cell (publish is deterministic in the seed) so the lineage can be
    // scoped to the asset origins.
    let seed = 7u8;
    let probe_lineage = SurfaceCapability::root(cid(seed), AuthRequired::Either);
    let (uri0, _sr0) = publish_bundle(
        &mut web,
        seed,
        &bundle,
        probe_lineage,
        InteractionLog::new(),
        false,
    );
    let cell = uri0.cell;

    // The real publish: the lineage permits ALL three asset origins, so the
    // per-VIEWER membrane meet (not the lineage) is what culls.
    let all_origins: Vec<String> = bundle
        .manifest()
        .asset_names()
        .iter()
        .map(|n| WebBundle::asset_origin(cell, n))
        .collect();
    let lineage = SurfaceCapability::scoped(cell, AuthRequired::Either, origins(&all_origins), []);

    let mut web = WebOfCells::new(3);
    let (uri, sturdyref) =
        publish_bundle(&mut web, seed, &bundle, lineage, InteractionLog::new(), false);
    assert_eq!(uri.cell, cell, "publish is deterministic in the seed");

    // ── FETCH through the REAL attested path: the fetched bundle IS the published. ──
    let (fetched, chrome) = fetch_bundle(&web, &uri).expect("publish → fetch round-trips");
    assert_eq!(fetched, bundle);
    assert_eq!(fetched.content_hash(), bundle.content_hash());
    // The trusted chrome shows the bundle's content-address, drawn from the ledger.
    assert_eq!(chrome.committed_url.as_deref(), Some(bundle.content_uri().as_str()));
    assert!(chrome.finalized);

    // ── (2) THE CAP TOOTH: nothing reaches a decode without a verified bundle. ──
    {
        // A dead `dregg://` ref yields no bundle (OriginNotFound).
        let dead = DreggUri::new(cid(250));
        assert_eq!(
            fetch_bundle(&web, &dead),
            Err(BundleError::Fetch(FetchError::OriginNotFound)),
            "a dead ref yields no bundle"
        );
        // An attested cell whose committed content is NOT a bundle passes the
        // attestation chain but fails the decode — no bundle. (The lower-level "lying
        // node serves uncommitted bytes" tooth — ContentDoesNotMatchCommitment — is
        // the web-of-cells' own internal property, tested in starbridge-web-surface;
        // here we exercise the public path.)
        let mut raw_web = WebOfCells::new(3);
        let raw_uri = raw_web.publish(8, b"raw bytes, not a bundle encoding", "dregg://raw");
        let (resource, _c) = raw_web.fetch(&raw_uri).expect("the raw cell resolves + attests");
        assert!(resource.verify().is_ok(), "the attestation still verifies");
        assert_eq!(
            fetch_bundle(&raw_web, &raw_uri),
            Err(BundleError::MalformedEncoding),
            "an attested non-bundle cell yields no bundle"
        );
    }

    // ── (3) THE DOM FRUSTUM-SNAPSHOT → PER-VIEWER REHYDRATION. ──
    let snapshot = DomSnapshot::take(&bundle, sturdyref).expect("snapshot the bundle");
    // The snapshot is TINY: it carries the boundary (cell + manifest digest + asset
    // names), not the bytes.
    assert_eq!(snapshot.boundary_extent(), 3);
    assert_eq!(snapshot.boundary.cell, cell);

    // (3a) A POWERFUL viewer (wildcard fetch) re-expands the FULL bundle.
    let powerful = Membrane::new(SurfaceCapability::root(cid(20), AuthRequired::Either));
    let full = rehydrate_bundle(&snapshot, &powerful, &web).expect("powerful rehydrates");
    assert!(full.is_full());
    assert_eq!(full.bundle.assets.len(), 3);
    assert!(full.bundle.asset("admin.js").is_some());
    assert_eq!(full.bundle.kind, BundleKind::LiveDomSnapshot); // re-expands as the same kind

    // (3b) A WEAKER viewer (scoped to index.html + dom-state, NOT admin.js) gets an
    //      ATTENUATED projection — the privileged admin.js is CULLED.
    let weaker_allowed = vec![
        WebBundle::asset_origin(cell, "index.html"),
        WebBundle::asset_origin(cell, "dom-state"),
    ];
    let weaker = Membrane::new(SurfaceCapability::scoped(
        cid(30),
        AuthRequired::Either,
        origins(&weaker_allowed),
        [],
    ));
    let attenuated = rehydrate_bundle(&snapshot, &weaker, &web).expect("weaker rehydrates");
    assert!(!attenuated.is_full());
    assert_eq!(attenuated.culled_assets, vec!["admin.js".to_string()]);
    assert!(attenuated.bundle.asset("index.html").is_some());
    assert!(attenuated.bundle.asset("dom-state").is_some());
    assert!(
        attenuated.bundle.asset("admin.js").is_none(),
        "the weaker viewer never receives the privileged asset's bytes"
    );
    // Two viewers re-expanded the SAME snapshot to DIFFERENT bundles.
    assert_ne!(full.bundle, attenuated.bundle);

    // (3c) An INCOMPARABLE identity re-expands NOTHING (the membrane refuses).
    //      (Re-publish under a Custom-identity lineage so the meet is incomparable.)
    let mut idweb = WebOfCells::new(3);
    let id_bundle = WebBundle::static_html(b"<h1>confidential</h1>".to_vec());
    let id_lineage = SurfaceCapability::root(cid(40), AuthRequired::Custom { vk_hash: [0xAA; 32] });
    let (_iduri, id_sr) = publish_bundle(
        &mut idweb,
        40,
        &id_bundle,
        id_lineage,
        InteractionLog::new(),
        false,
    );
    let id_snapshot = DomSnapshot::take(&id_bundle, id_sr).expect("snapshot");
    let incomparable =
        Membrane::new(SurfaceCapability::root(cid(41), AuthRequired::Custom { vk_hash: [0xBB; 32] }));
    assert_eq!(
        rehydrate_bundle(&id_snapshot, &incomparable, &idweb),
        Err(SnapshotError::Rehydrate(RehydrateError::Amplification)),
        "an incomparable identity gets no projection"
    );

    // ── (4) TRANSCLUSION-WITH-PROVENANCE: include a fragment into another surface. ──
    // Another surface transcludes the live app's `dom-state` fragment — the live
    // quote, carrying the source's receipt-pinned provenance.
    let quote = transclude_bundle_fragment(&web, &uri, "dom-state")
        .expect("the fragment transcludes");
    // The fragment bytes ARE the source asset's committed bytes (not a copy).
    assert_eq!(quote.fragment_bytes, br#"{"signals":{"counter":3},"effects":["render"]}"#);
    assert_eq!(quote.asset_name, "dom-state");
    // It carries the receipt-pinned provenance: the source bundle ref + finalized.
    assert_eq!(quote.cite().source, uri);
    assert!(quote.cite().finalized);
    // And it re-verifies (content→commitment→receipt→receipt-stream-root→quorum).
    assert!(quote.verify().is_ok(), "the transcluded fragment's provenance re-verifies");

    // A fragment NOT in the source bundle is refused. (BundleFragmentQuote carries a
    // TranscludedField, which is not Eq, so we match on the error variant.)
    let missing = transclude_bundle_fragment(&web, &uri, "not-an-asset.js");
    assert!(
        matches!(&missing, Err(CascadeError::NoSuchAsset { asset_name }) if asset_name == "not-an-asset.js"),
        "a fragment not in the source bundle is refused, got {missing:?}"
    );
}

#[test]
fn a_dead_ref_yields_nothing_everywhere() {
    // The same dead `dregg://` ref is refused identically by fetch, rehydrate, and
    // transclude — confinement before content, the one discipline everywhere.
    let web = WebOfCells::new(3);
    let dead = DreggUri::new(cid(99));

    assert_eq!(
        fetch_bundle(&web, &dead),
        Err(BundleError::Fetch(FetchError::OriginNotFound))
    );

    let dead_snapshot = DomSnapshot {
        sturdyref: starbridge_web_surface::Sturdyref::new(
            dead.clone(),
            SurfaceCapability::root(cid(99), AuthRequired::Either),
            InteractionLog::new(),
            false,
        ),
        boundary: deos_web_cells::BundleBoundary {
            cell: cid(99),
            manifest_digest: [0u8; 32],
            asset_names: vec![],
        },
    };
    let viewer = Membrane::new(SurfaceCapability::root(cid(98), AuthRequired::Either));
    assert_eq!(
        rehydrate_bundle(&dead_snapshot, &viewer, &web),
        Err(SnapshotError::Rehydrate(RehydrateError::Fetch(FetchError::OriginNotFound)))
    );

    assert!(matches!(
        transclude_bundle_fragment(&web, &dead, "x"),
        Err(CascadeError::Transclusion(_))
    ));
}

#[test]
fn a_static_bundle_and_a_live_snapshot_with_the_same_assets_are_distinct_cells() {
    // The BundleKind is folded into the content-address: a static bundle and a
    // live-DOM snapshot with identical bytes are DIFFERENT dregg:// cells — so you
    // cannot pass one off as the other.
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
    assert_ne!(st.content_uri(), live.content_uri());

    // Both publish + fetch + round-trip as themselves (content-addressed identity).
    let mut web = WebOfCells::new(3);
    let (su, _) = publish_bundle(
        &mut web,
        60,
        &st,
        SurfaceCapability::root(cid(60), AuthRequired::Either),
        InteractionLog::new(),
        false,
    );
    let (lu, _) = publish_bundle(
        &mut web,
        61,
        &live,
        SurfaceCapability::root(cid(61), AuthRequired::Either),
        InteractionLog::new(),
        false,
    );
    assert_ne!(su.cell, lu.cell);
    let (sf, _) = fetch_bundle(&web, &su).unwrap();
    let (lf, _) = fetch_bundle(&web, &lu).unwrap();
    assert_eq!(sf.kind, BundleKind::StaticBundle);
    assert_eq!(lf.kind, BundleKind::LiveDomSnapshot);
}
