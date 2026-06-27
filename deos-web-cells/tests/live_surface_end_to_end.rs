//! End-to-end: **publish a LIVE rendered surface's DOM state as a web-of-cells cell**,
//! the whole story, through the STABLE public `deos_web_cells` API — never a parallel
//! model.
//!
//! `docs/deos/WEB-CELLS.md`, the leptosic headline ("publish/commit … bundles of LIVE
//! DOM state, and share that as part of the web of cells"):
//!
//! 1. **capture → commit → publish** — a `RenderedSurface` (the rendered fragment tree
//!    + asset refs) is captured into a `LiveDomSnapshot` `WebBundle` and published
//!      through the REAL `publish_bundle` chain (content → commitment → receipt →
//!      stream-root → quorum). The published cell IS the DOM state at a committed height.
//! 2. **transclude a DOM fragment** — a span/region of the published surface's rendered
//!    DOM renders into a `DreggverseDocument` carrying the source's receipt-pinned
//!    provenance (the live quote at the DOM level).
//! 3. **the darkened viewer** — a viewer lacking authority sees the citation, not the
//!    DOM bytes (the REAL membrane projection, never a forgery).
//! 4. **re-publish on change tracks live** — amending the surface advances the committed
//!    DOM-state height; a snapshot pins the old, a live transclusion re-resolves to the
//!    new (the REAL versioned-transclusion snapshot/live dial).

use deos_web_cells::tests_support::cid;
use deos_web_cells::{
    fetch_bundle, publish_live_surface, AmendError, BundleAsset, BundleKind, DomNode,
    DreggverseDocument, FetchError, PublishedSurface, RenderedSpan, RenderedSurface, Span,
    SpanRange, SurfaceCapability, WebBundle, WebOfCells, DOM_STATE_ASSET, RENDERED_VIEW_ASSET,
};

use starbridge_web_surface::rehydrate::InteractionLog;
use starbridge_web_surface::{AuthRequired, DreggUri, Membrane};

use std::collections::BTreeSet;

fn origins(list: &[String]) -> BTreeSet<String> {
    list.iter().cloned().collect()
}

/// A leptosic "todo app" surface: a rendered `<main id=app>` tree (the count of open
/// items is embedded in the view) + a referenced `app.js`. Amending `open` re-captures
/// a different DOM state.
fn todo_surface(open: u32) -> RenderedSurface {
    let fragment = DomNode::element(
        "main",
        [("id".to_string(), "app".to_string())],
        [
            DomNode::labelled("h1", "todos"),
            DomNode::labelled("span", format!("open: {open}")),
        ],
    );
    RenderedSurface::new(
        fragment,
        [BundleAsset::new(
            "app.js",
            "application/javascript",
            b"hydrate(app)".to_vec(),
        )],
    )
}

#[test]
fn the_whole_live_surface_story_capture_publish_transclude_darken_amend() {
    // ── (1) CAPTURE → COMMIT → PUBLISH a live rendered surface's DOM state. ──
    let surface = todo_surface(3);
    let mut web = WebOfCells::new(3);

    // Learn the cell (publish is deterministic in the seed) so the lineage can scope to
    // the asset origins.
    let seed = 11u8;
    let probe = SurfaceCapability::root(cid(seed), AuthRequired::Either);
    let (probe_pub, _) = publish_live_surface(
        &mut web,
        seed,
        surface.clone(),
        probe,
        InteractionLog::new(),
        false,
    )
    .expect("captures + publishes");
    let cell = probe_pub.cell();

    // The lineage permits ALL asset origins (so the per-VIEWER membrane meet, not the
    // lineage, is what darkens / culls).
    let all_origins: Vec<String> = probe_pub
        .bundle()
        .manifest()
        .asset_names()
        .iter()
        .map(|n| WebBundle::asset_origin(cell, n))
        .collect();
    let lineage = SurfaceCapability::scoped(cell, AuthRequired::Either, origins(&all_origins), []);

    let mut web = WebOfCells::new(3);
    let (mut published, _sturdyref) = publish_live_surface(
        &mut web,
        seed,
        surface.clone(),
        lineage.clone(),
        InteractionLog::new(),
        false,
    )
    .expect("captures + publishes");
    assert_eq!(
        published.cell(),
        cell,
        "publish is deterministic in the seed"
    );

    // The published cell IS the DOM state at a committed height: a REAL attested fetch
    // round-trips to the captured bundle, and the trusted chrome shows its content
    // address (drawn from the ledger).
    let (fetched, chrome) = fetch_bundle(&web, &published.uri).expect("fetch + verify + decode");
    assert_eq!(fetched, published.bundle());
    assert_eq!(fetched.kind, BundleKind::LiveDomSnapshot);
    assert!(chrome.finalized);
    assert_eq!(
        chrome.committed_url.as_deref(),
        Some(published.bundle().content_uri().as_str())
    );
    // The captured DOM state has both the rendered view + the serialized dom-state.
    assert!(fetched.asset(RENDERED_VIEW_ASSET).is_some());
    assert_eq!(
        fetched.asset(DOM_STATE_ASSET).unwrap().bytes,
        surface.dom_state()
    );

    // ── (2) TRANSCLUDE A DOM FRAGMENT into a DreggverseDocument with provenance. ──
    // The rendered view contains `<span>open: 3</span>`; quote exactly that DOM fragment.
    let html = String::from_utf8(
        published
            .bundle()
            .asset(RENDERED_VIEW_ASSET)
            .unwrap()
            .bytes
            .clone(),
    )
    .unwrap();
    let frag = "<span>open: 3</span>";
    let at = html
        .find(frag)
        .expect("the span fragment is in the rendered view");
    let range = SpanRange::new(at, at + frag.len());

    let doc = DreggverseDocument::from_spans(vec![
        Span::own(b"status: ".to_vec()),
        published.quote_fragment(range),
    ]);
    let rendered = doc.resolve(&web).expect("the DOM-fragment span resolves");
    assert_eq!(
        rendered.composed_text().unwrap(),
        "status: <span>open: 3</span>"
    );
    // The span carries the surface's receipt-pinned provenance + the parallel-source link.
    let prov = rendered.spans()[1]
        .provenance()
        .expect("the DOM-fragment span is provenanced");
    assert_eq!(prov.source, published.uri);
    assert!(prov.finalized);
    assert_eq!(
        rendered.spans()[1].source_link(),
        Some((published.uri.clone(), range))
    );

    // ── (3) THE DARKENED VIEWER: a viewer lacking authority sees the citation, not the
    //        DOM bytes. ──
    let whole_doc = DreggverseDocument::from_spans(vec![
        Span::own(b"<".to_vec()),
        published.quote_rendered(),
        Span::own(b">".to_vec()),
    ]);
    // A full-authority viewer reads the DOM for real.
    let full_viewer = Membrane::new(SurfaceCapability::root(cid(20), AuthRequired::Either));
    let full = whole_doc
        .resolve_for(&web, &full_viewer, &lineage)
        .expect("full viewer resolves");
    assert!(full.is_full());
    assert!(full.composed_text().unwrap().contains("open: 3"));

    // A viewer scoped to a DIFFERENT origin (not the surface's rendered-view origin) is
    // darkened on that span — the citation survives, the DOM bytes are withheld.
    let elsewhere = WebBundle::asset_origin(cell, "unrelated-asset");
    let darkened_viewer = Membrane::new(SurfaceCapability::scoped(
        cid(30),
        AuthRequired::Either,
        origins(&[elsewhere]),
        [],
    ));
    let dark = whole_doc
        .resolve_for(&web, &darkened_viewer, &lineage)
        .expect("darkened viewer resolves");
    assert!(!dark.is_full());
    assert_eq!(dark.darkened_count(), 1);
    assert_eq!(
        dark.composed_text().unwrap(),
        "<>",
        "no DOM bytes for the darkened span"
    );
    assert!(
        !dark
            .composed_bytes()
            .windows(b"open:".len())
            .any(|w| w == b"open:"),
        "the darkened viewer never sees the surface's DOM bytes"
    );
    // …BUT the darkened span keeps its citation (the docuverse skeleton survives).
    assert!(matches!(&dark.spans()[1], RenderedSpan::Darkened { .. }));
    assert_eq!(dark.spans()[1].provenance().unwrap().source, published.uri);

    // ── (4) RE-PUBLISH ON CHANGE TRACKS LIVE: amend the surface; a snapshot pins the
    //        old DOM-state height, a live transclusion re-resolves to the new. ──
    let snap = published
        .dom_state_snapshot(&web)
        .expect("snapshot the current DOM state");
    let live = published.dom_state_live();
    let pinned_height = snap.pinning().pinned_height().expect("a pinned height");

    let new_height = published
        .amend(&mut web, todo_surface(5))
        .expect("amend advances the surface to a new DOM state");
    assert!(
        new_height > pinned_height,
        "the committed DOM-state height advanced"
    );

    // The SNAPSHOT is stable (still the open:3 DOM state); the LIVE quote re-resolves to
    // the open:5 DOM state.
    let snap_state = decode_dom_state(snap.read(&web).expect("snapshot reads").displayed_bytes());
    assert_eq!(
        snap_state,
        todo_surface(3).dom_state(),
        "snapshot pins the OLD DOM state"
    );
    let live_state = decode_dom_state(live.read(&web).expect("live reads").displayed_bytes());
    assert_eq!(
        live_state,
        todo_surface(5).dom_state(),
        "live re-resolves to the NEW DOM state"
    );

    // And a fresh document re-resolve of the whole rendered DOM now shows open:5 (the
    // unbreakable link at the DOM level — same EDL, advanced surface).
    let r_after = whole_doc.resolve(&web).expect("re-resolves post-amend");
    assert!(r_after.composed_text().unwrap().contains("open: 5"));
    assert!(!r_after.composed_text().unwrap().contains("open: 3"));
}

#[test]
fn a_captured_surface_is_a_faithful_deterministic_tree_not_a_blob() {
    // The capture is the real DOM tree (element/attrs/text/children), serialized
    // deterministically + content-addressed — identical DOM state addresses identically.
    let a = todo_surface(2).into_bundle().expect("captures");
    let b = todo_surface(2).into_bundle().expect("captures");
    assert_eq!(a.content_hash(), b.content_hash());
    assert_ne!(
        a.content_hash(),
        todo_surface(3).into_bundle().unwrap().content_hash()
    );

    // The node tree extent is the real count of element + text nodes.
    let surface = todo_surface(0);
    // main > (h1>text, span>text) = main, h1, "todos", span, "open: 0" = 5 nodes.
    assert_eq!(surface.fragment.node_count(), 5);
}

#[test]
fn amend_of_an_unpublished_surface_is_refused() {
    // A PublishedSurface handle whose ref was never committed cannot be amended.
    let mut web = WebOfCells::new(3);
    let mut handle = PublishedSurface {
        uri: DreggUri::new(cid(199)),
        seed: 199,
        lineage: SurfaceCapability::root(cid(199), AuthRequired::Either),
        surface: todo_surface(0),
    };
    assert_eq!(
        handle.amend(&mut web, todo_surface(1)),
        Err(AmendError::Fetch(FetchError::OriginNotFound))
    );
}

/// Pull the `dom-state` asset bytes out of a versioned read's displayed bundle bytes
/// (the read displays the surface cell's whole committed bundle).
fn decode_dom_state(bundle_bytes: &[u8]) -> Vec<u8> {
    WebBundle::decode(bundle_bytes)
        .expect("the displayed bytes decode as a bundle")
        .asset(DOM_STATE_ASSET)
        .expect("a dom-state asset")
        .bytes
        .clone()
}
