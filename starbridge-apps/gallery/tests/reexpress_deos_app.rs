//! RE-EXPRESSION proof: the `gallery` starbridge-app, on the composed deos framework
//! — **the same app, smaller + more capable, now SHIPPED from `src/`.**
//!
//! The sealed-submission art gallery, expressed as a composed [`DeosApp`] shipping
//! from `src/lib.rs`. This file drives the SHIPPED surface ([`gallery_app`] from
//! `src/`): per-viewer projection, the cap-gated fires through the mounted axum
//! surface, the `dregg://` web-of-cells publish, the rehydratable frustum-snapshot,
//! the generated `<dregg-affordance-surface>` component, and the manifest.
//!
//! The GALLERY's surface on the visitor ⊂ artist ⊂ curator rights ladder
//! (`Signature ⊂ Either ⊂ None`):
//!   - `view_gallery` — cap-only (a VISITOR browses);
//!   - `submit` / `close_submissions` / `reveal` / `curate` — GATED (cap∧state): the
//!     cap-gate AND a live-state PHASE precondition, with the FULL gallery program
//!     re-enforced by the executor on the fire (the seam — see `tests/deos_seam.rs`).
//!     The submission board lives ON-LEDGER: a submit writes a `WriteOnce` slot, so
//!     SWAPPING a committed submission is an executor refusal (anti-tamper).
//!
//! Every affordance carries a REAL [`Effect`]; every fire is a real verified turn
//! through the embedded executor; the gate is the genuine `is_attenuation` (+ the
//! genuine `CellProgram::evaluate` for the gated ones). No parallel model.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CapTpServer, DeosApp, EmbeddedExecutor,
    FederationId, Interaction, InteractionLog, RehydrateError, Rehydration,
};

use starbridge_gallery::{gallery_app, seed_gallery};

fn agent() -> (AppCipherclerk, EmbeddedExecutor) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x6a; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    (cclerk, executor)
}

// =============================================================================
// SMALLER: the whole surface is one builder (the SHIPPED `src::gallery_app`).
// =============================================================================

#[test]
fn the_whole_app_is_one_composed_registration() {
    let (cclerk, executor) = agent();
    let app = gallery_app(&cclerk, &executor);

    assert_eq!(app.name(), "gallery");
    assert_eq!(app.cells().len(), 1);
    let gallery = &app.cells()[0];
    assert_eq!(
        gallery.surface().all_names(),
        vec!["view_gallery".to_string()],
        "the cap-only surface: just the browse read (the lifecycle ops are gated)"
    );
    let mut gated: Vec<String> = gallery
        .gated_surface()
        .affordances
        .iter()
        .map(|g| g.name().to_string())
        .collect();
    gated.sort();
    assert_eq!(
        gated,
        vec![
            "close_submissions".to_string(),
            "curate".to_string(),
            "reveal".to_string(),
            "submit".to_string(),
        ]
    );

    assert_eq!(gallery.cell(), cclerk.cell_id());
    assert_eq!(
        gallery.published_authority(),
        Some(&AuthRequired::Signature)
    );

    let ctx = dregg_app_framework::StarbridgeAppContext::new(cclerk.clone(), executor.clone());
    let keys = app.register(&ctx);
    assert_eq!(keys.len(), 1);
    assert_eq!(ctx.affordance_registry().len(), 1);
}

// =============================================================================
// MORE CAPABLE (1): per-viewer projection of the cap-only surface (HTTP).
// =============================================================================

#[tokio::test]
async fn the_three_gallery_roles_see_different_cap_only_surfaces() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent();
    let app = gallery_app(&cclerk, &executor);
    let router = app.mount();

    async fn visible(router: &axum::Router, tier: &str) -> serde_json::Value {
        let resp = router
            .clone()
            .oneshot(
                Request::get("/gallery/projected")
                    .header(dregg_app_framework::HELD_RIGHTS_HEADER, tier)
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(resp.status(), StatusCode::OK);
        let bytes = axum::body::to_bytes(resp.into_body(), usize::MAX)
            .await
            .unwrap();
        serde_json::from_slice::<serde_json::Value>(&bytes).unwrap()["visible"].clone()
    }

    // Every tier sees only `view_gallery` on the cap-only projection — submit/reveal/curate are
    // GATED (they light on the gated surface against the live PHASE, the htmx tooth).
    assert_eq!(
        visible(&router, "signature").await,
        serde_json::json!(["view_gallery"])
    );
    assert_eq!(
        visible(&router, "either").await,
        serde_json::json!(["view_gallery"])
    );
    assert_eq!(
        visible(&router, "root").await,
        serde_json::json!(["view_gallery"])
    );
}

// =============================================================================
// MORE CAPABLE (2): a cap-only fire is a real verified turn; anti-ghost holds.
// =============================================================================

#[tokio::test]
async fn a_visitor_can_view_the_gallery_a_real_turn() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent();
    let app = gallery_app(&cclerk, &executor);
    let _ = seed_gallery(&executor, "curator");
    let router = app.mount();

    async fn fire(router: &axum::Router, name: &str, tier: &str) -> StatusCode {
        router
            .clone()
            .oneshot(
                Request::post(format!("/gallery/fire/{name}"))
                    .header(dregg_app_framework::HELD_RIGHTS_HEADER, tier)
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap()
            .status()
    }

    // The CAP tooth, in-band (anti-ghost): nobody is below the visitor tier (Signature is the
    // floor), so any held tier clears the `view_gallery` cap gate (not 403).
    assert_ne!(
        fire(&router, "view_gallery", "signature").await,
        StatusCode::FORBIDDEN,
        "a visitor is cap-authorized to browse (clears the cap gate)"
    );
}

// =============================================================================
// MORE CAPABLE (3): web-of-cells — the GALLERY cell is a distributed sturdyref.
// =============================================================================

#[tokio::test]
async fn the_gallery_is_published_into_the_web_of_cells() {
    let (cclerk, executor) = agent();
    let captp = CapTpServer::new(FederationId([0x6a; 32]));
    let base = gallery_app(&cclerk, &executor);
    let app = DeosApp::builder("gallery", cclerk.clone(), executor.clone())
        .web_of_cells(captp)
        .cell(base.cells()[0].clone())
        .build();

    // The GALLERY cell is exported as a real `dregg://` sturdyref — a visitor/auditor on another
    // federation reacquires the gallery across the membrane.
    let uris = app.publish_all(100).await;
    assert_eq!(uris.len(), 1);
    assert!(
        uris[0].starts_with("dregg://"),
        "a real sturdyref: {}",
        uris[0]
    );
}

// =============================================================================
// MORE CAPABLE (4): rehydratable frustum-snapshot of the gallery, per-viewer.
// =============================================================================

#[test]
fn a_gallery_snapshot_rehydrates_per_viewer_respecting_the_lattice() {
    let (cclerk, executor) = agent();
    let app = gallery_app(&cclerk, &executor);
    let gallery = &app.cells()[0];

    let log = InteractionLog::new().record(Interaction::witnessed_turn(gallery.cell(), [9u8; 32]));
    let snap = gallery.snapshot(log, false);
    assert_eq!(
        snap.lineage,
        AuthRequired::Signature,
        "snapshot at the published lineage"
    );
    assert_eq!(snap.liveness(), Rehydration::ReplayedDeterministic);
    assert!(snap.liveness().is_faithful());

    // A VISITOR (Signature) rehydrating reacquires only `view_gallery` — the snapshot respects
    // the lattice.
    let visitor = gallery.rehydrate(&snap, AuthRequired::Signature).unwrap();
    assert_eq!(visitor.visible_names(), vec!["view_gallery".to_string()]);

    // An INCOMPARABLE authority cannot rehydrate at all — the membrane mints NO projection.
    let blocked = gallery.rehydrate(&snap, AuthRequired::Custom { vk_hash: [7u8; 32] });
    assert!(matches!(blocked, Err(RehydrateError::Amplification { .. })));
}

// =============================================================================
// MORE CAPABLE (5): the generated web component + the manifest (with gated state-gates).
// =============================================================================

#[tokio::test]
async fn the_app_ships_a_web_component_surface_and_a_manifest() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent();
    let app = gallery_app(&cclerk, &executor);
    let router = app.mount();

    let surface = router
        .clone()
        .oneshot(Request::get("/surface.js").body(Body::empty()).unwrap())
        .await
        .unwrap();
    assert_eq!(surface.status(), StatusCode::OK);
    let ct = surface
        .headers()
        .get(axum::http::header::CONTENT_TYPE)
        .unwrap()
        .to_str()
        .unwrap()
        .to_string();
    assert!(ct.contains("javascript"), "served as a JS module: {ct}");
    let bytes = axum::body::to_bytes(surface.into_body(), usize::MAX)
        .await
        .unwrap();
    let js = String::from_utf8(bytes.to_vec()).unwrap();
    assert!(js.contains("customElements.define(\"dregg-affordance-surface\""));
    assert!(js.contains("fireEndpoint: \"/gallery/fire/view_gallery\","));

    let manifest = router
        .oneshot(Request::get("/manifest").body(Body::empty()).unwrap())
        .await
        .unwrap();
    assert_eq!(manifest.status(), StatusCode::OK);
    let bytes = axum::body::to_bytes(manifest.into_body(), usize::MAX)
        .await
        .unwrap();
    let m: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    assert_eq!(m["app"], "gallery");
    assert_eq!(m["discoverable"], serde_json::json!(["gallery", "art"]));
    assert!(
        m["persistence"]
            .as_str()
            .unwrap()
            .contains("embedded-ledger")
    );
    assert_eq!(m["cells"].as_array().unwrap().len(), 1);
    let gated = m["cells"][0]["gatedAffordances"]
        .as_array()
        .expect("gated affordances");
    let names: Vec<&str> = gated.iter().filter_map(|g| g["name"].as_str()).collect();
    assert!(names.contains(&"submit"), "submit is advertised as gated");
    assert!(
        names.contains(&"close_submissions"),
        "close_submissions is advertised as gated"
    );
    assert!(names.contains(&"reveal"), "reveal is advertised as gated");
    assert!(names.contains(&"curate"), "curate is advertised as gated");
}
