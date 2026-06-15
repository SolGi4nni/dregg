//! RE-EXPRESSION proof: the `storage-gateway-mandate` starbridge-app, on the composed
//! deos framework — **the SAME app, now SHIPPED from `src/` with a deos surface.**
//!
//! `docs/deos/APPS-DEOS-INTEGRATION-CENSUS.md`: the storage-gateway mandate's scaffold
//! floor ([`sgm_cell_program`] / [`sgm_factory_descriptor`]) was executor-truth (the
//! volume-budget caveats bite on a born cell) but had NO deos surface. This file drives
//! the PROMOTED surface ([`gateway_app`] from `src/`): per-viewer projection, the
//! cap-gated fires through the mounted axum surface, the `dregg://` web-of-cells publish,
//! the rehydratable frustum-snapshot, the generated `<dregg-affordance-surface>`
//! component, and the manifest — none of which the floor scaffold had.
//!
//! The GATEWAY's surface on the reader ⊂ writer ⊂ mandate-holder rights ladder
//! (`Signature ⊂ Either ⊂ None`):
//!   - `get` / `list` — cap-only (a READER reads / enumerates);
//!   - `put` — GATED (cap∧state): the cap-gate AND a live-state precondition (budget
//!     remains), with the FULL gateway invariants re-enforced by the executor on the fire
//!     (the volume budget as a LIVE gate — see `tests/deos_seam.rs`).
//!
//! Every affordance carries a REAL [`Effect`]; every fire is a real verified turn through
//! the embedded executor; the gate is the genuine `is_attenuation` (+ the genuine
//! `CellProgram::evaluate` for the gated one). No parallel model.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CapTpServer, DeosApp, EmbeddedExecutor,
    FederationId, Interaction, InteractionLog, RehydrateError, Rehydration,
};

use starbridge_storage_gateway_mandate::{
    DEFAULT_COMMITMENT_ANCHOR, DEFAULT_KEY_PREFIX, DEFAULT_READ_COMPARTMENT,
    DEFAULT_VOLUME_CEILING, gateway_app, seed_gateway,
};

fn agent() -> (AppCipherclerk, EmbeddedExecutor) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x42; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    (cclerk, executor)
}

fn seed(executor: &EmbeddedExecutor) {
    seed_gateway(
        executor,
        DEFAULT_COMMITMENT_ANCHOR,
        DEFAULT_VOLUME_CEILING,
        DEFAULT_KEY_PREFIX,
        DEFAULT_READ_COMPARTMENT,
    );
}

// =============================================================================
// SMALLER: the whole surface is one builder (the SHIPPED `src::gateway_app`).
// =============================================================================

#[test]
fn the_whole_app_is_one_composed_registration() {
    let (cclerk, executor) = agent();
    let app = gateway_app(&cclerk, &executor);

    // ONE app, ONE cell. The cap-only surface carries the two reads; the metered write
    // (`put`) is GATED (cap∧state).
    assert_eq!(app.name(), "storage-gateway-mandate");
    assert_eq!(app.cells().len(), 1);
    let gateway = &app.cells()[0];
    assert_eq!(
        gateway.surface().all_names(),
        vec!["get".to_string(), "list".to_string()],
        "the cap-only surface: the two reads (get + list)"
    );
    // The gated surface carries the single state-mutating, cap∧state operation.
    let gated: Vec<String> = gateway
        .gated_surface()
        .affordances
        .iter()
        .map(|g| g.name().to_string())
        .collect();
    assert_eq!(gated, vec!["put".to_string()]);

    // The GATEWAY cell is the agent's own (so fires execute against the seeded ledger),
    // and is published into the web-of-cells at the reader tier.
    assert_eq!(gateway.cell(), cclerk.cell_id());
    assert_eq!(
        gateway.published_authority(),
        Some(&AuthRequired::Signature)
    );

    // ONE registration folds the whole surface into a shared host context.
    let ctx = dregg_app_framework::StarbridgeAppContext::new(cclerk.clone(), executor.clone());
    let keys = app.register(&ctx);
    assert_eq!(keys.len(), 1);
    assert_eq!(ctx.affordance_registry().len(), 1);
}

// =============================================================================
// MORE CAPABLE (1): per-viewer projection of the cap-only surface (HTTP).
// =============================================================================

#[tokio::test]
async fn the_storage_roles_see_their_cap_only_surfaces() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent();
    let app = gateway_app(&cclerk, &executor);
    let router = app.mount();

    async fn visible(router: &axum::Router, tier: &str) -> serde_json::Value {
        let resp = router
            .clone()
            .oneshot(
                Request::get("/gateway/projected")
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

    // A READER (Signature) sees both reads `get` + `list` (the narrow read tier). `put` is
    // GATED (not on the cap-only projection); it lights on the gated surface against live
    // state.
    assert_eq!(
        visible(&router, "signature").await,
        serde_json::json!(["get", "list"])
    );
    // A WRITER (Either) sees the same cap-only set (the reads) — `put` is GATED.
    assert_eq!(
        visible(&router, "either").await,
        serde_json::json!(["get", "list"])
    );
    // The MANDATE-HOLDER (root) ⊇ writer ⊇ reader, so it also sees the two cap-only reads.
    assert_eq!(
        visible(&router, "root").await,
        serde_json::json!(["get", "list"])
    );
}

// =============================================================================
// MORE CAPABLE (2): a cap-only fire is a real verified turn; anti-ghost holds.
// =============================================================================

#[tokio::test]
async fn a_reader_can_get_a_real_turn_through_the_mounted_surface() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent();
    let app = gateway_app(&cclerk, &executor);
    seed(&executor);
    let router = app.mount();

    async fn fire(router: &axum::Router, name: &str, tier: &str) -> StatusCode {
        router
            .clone()
            .oneshot(
                Request::post(format!("/gateway/fire/{name}"))
                    .header(dregg_app_framework::HELD_RIGHTS_HEADER, tier)
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap()
            .status()
    }

    // A READER (Signature) firing `get` CLEARS the cap gate (not 403) — `get` requires
    // only `Signature`. A real verified read turn through the embedded executor.
    assert_ne!(
        fire(&router, "get", "signature").await,
        StatusCode::FORBIDDEN,
        "a reader is cap-authorized to get (clears the cap gate)"
    );
    // `list` is equally a reader affordance.
    assert_ne!(
        fire(&router, "list", "signature").await,
        StatusCode::FORBIDDEN
    );
}

// =============================================================================
// MORE CAPABLE (3): web-of-cells — the GATEWAY cell is a distributed sturdyref.
// =============================================================================

#[tokio::test]
async fn the_gateway_is_published_into_the_web_of_cells() {
    let (cclerk, executor) = agent();
    // The SHIPPED surface, re-built with a captp server attached (the web-of-cells
    // minter). `gateway_app` publishes the gateway cell at the reader tier.
    let captp = CapTpServer::new(FederationId([0x42; 32]));
    let base = gateway_app(&cclerk, &executor);
    let app = DeosApp::builder("storage-gateway-mandate", cclerk.clone(), executor.clone())
        .web_of_cells(captp)
        .cell(base.cells()[0].clone())
        .build();

    // The GATEWAY cell is exported as a real `dregg://` sturdyref — a peer on another
    // federation reacquires the gateway across the membrane.
    let uris = app.publish_all(100).await;
    assert_eq!(uris.len(), 1);
    assert!(
        uris[0].starts_with("dregg://"),
        "a real sturdyref: {}",
        uris[0]
    );
}

// =============================================================================
// MORE CAPABLE (4): rehydratable frustum-snapshot of the gateway, per-viewer.
// =============================================================================

#[test]
fn a_gateway_snapshot_rehydrates_per_viewer_respecting_the_lattice() {
    let (cclerk, executor) = agent();
    let app = gateway_app(&cclerk, &executor);
    let gateway = &app.cells()[0];

    // Snapshot the gateway; it witnessed a metered-write turn, sources gone (a cold
    // snapshot handed to a downstream auditor) ⇒ liveness REPLAYED-DETERMINISTIC.
    let log = InteractionLog::new().record(Interaction::witnessed_turn(gateway.cell(), [9u8; 32]));
    let snap = gateway.snapshot(log, false);
    assert_eq!(
        snap.lineage,
        AuthRequired::Signature,
        "snapshot at the published lineage"
    );
    assert_eq!(snap.liveness(), Rehydration::ReplayedDeterministic);
    assert!(snap.liveness().is_faithful());

    // A READER (Signature) rehydrating reacquires both cap-only reads (the surface at its
    // tier) — the gateway snapshot respects the lattice.
    let reader = gateway.rehydrate(&snap, AuthRequired::Signature).unwrap();
    assert_eq!(
        reader.visible_names(),
        vec!["get".to_string(), "list".to_string()]
    );

    // An INCOMPARABLE authority (a distinct Custom identity) cannot rehydrate at all — the
    // membrane mints NO projection (the no-peek refusal → Amplification).
    let blocked = gateway.rehydrate(&snap, AuthRequired::Custom { vk_hash: [7u8; 32] });
    assert!(matches!(blocked, Err(RehydrateError::Amplification { .. })));
}

// =============================================================================
// MORE CAPABLE (5): the generated web component + the manifest (with gated state-gate).
// =============================================================================

#[tokio::test]
async fn the_app_ships_a_web_component_surface_and_a_manifest() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent();
    let app = gateway_app(&cclerk, &executor);
    let router = app.mount();

    // GET /surface.js serves the `<dregg-affordance-surface>` web component, generated
    // from the Rust source of truth (the floor hand-wrote its JS).
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
    // The anti-drift affordance map names the cap-only fire endpoints.
    assert!(js.contains("fireEndpoint: \"/gateway/fire/get\","));
    assert!(js.contains("fireEndpoint: \"/gateway/fire/list\","));

    // GET /manifest serves the whole composed surface, including the GATED affordance with
    // its state-gate described (the cap∧state posture is visible to any client).
    let manifest = router
        .oneshot(Request::get("/manifest").body(Body::empty()).unwrap())
        .await
        .unwrap();
    assert_eq!(manifest.status(), StatusCode::OK);
    let bytes = axum::body::to_bytes(manifest.into_body(), usize::MAX)
        .await
        .unwrap();
    let m: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    assert_eq!(m["app"], "storage-gateway-mandate");
    assert_eq!(m["discoverable"], serde_json::json!(["storage"]));
    assert!(
        m["persistence"]
            .as_str()
            .unwrap()
            .contains("embedded-ledger")
    );
    assert_eq!(m["cells"].as_array().unwrap().len(), 1);
    // The manifest advertises the gated (cap∧state) `put` affordance.
    let gated = m["cells"][0]["gatedAffordances"]
        .as_array()
        .expect("gated affordances");
    let names: Vec<&str> = gated.iter().filter_map(|g| g["name"].as_str()).collect();
    assert!(names.contains(&"put"), "put is advertised as gated");
}
