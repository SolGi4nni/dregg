//! RE-EXPRESSION proof: the `compartment-workflow-mandate` starbridge-app, on the
//! composed deos framework — **the same app, smaller + more capable, now SHIPPED from
//! `src/`.**
//!
//! `docs/deos/APPS-DEOS-INTEGRATION-CENSUS.md` (the workflow port): the compartment
//! workflow MANDATE, re-expressed as a composed [`DeosApp`] and PROMOTED into
//! `src/lib.rs` (it lived in this test). This file drives the SHIPPED surface
//! ([`workflow_app`] from `src/`), proving the promotion: per-viewer projection, the
//! cap-gated fires through the mounted axum surface, the `dregg://` web-of-cells
//! publish, the rehydratable frustum-snapshot, the generated `<dregg-affordance-surface>`
//! component, and the manifest — none of which the floor's bones had.
//!
//! The MANDATE's surface on the observer ⊂ operator rights ladder (`Signature ⊂ None`):
//!   - `view_workflow` — cap-only (an OBSERVER reads the charter cursor);
//!   - `advance_step` — GATED (cap∧state): the cap-gate AND a live-state precondition
//!     (the cursor is not at the terminal), with the FULL workflow program re-enforced by
//!     the executor on the fire (the seam the census flagged, now CLOSED — see
//!     `tests/deos_seam.rs`).
//!
//! Every affordance carries a REAL [`Effect`]; every fire is a real verified turn through
//! the embedded executor; the gate is the genuine `is_attenuation` (+ the genuine
//! `CellProgram::evaluate` for the gated one). No parallel model.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CapTpServer, DeosApp, EmbeddedExecutor,
    FederationId, Interaction, InteractionLog, RehydrateError, Rehydration,
};

use starbridge_compartment_workflow_mandate::{seed_workflow, workflow_app};

fn agent() -> (AppCipherclerk, EmbeddedExecutor) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x3c; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    (cclerk, executor)
}

/// Seed a mandate with a small charter terminal (3 steps) and the genesis cursor 0.
fn seed(executor: &EmbeddedExecutor) -> u64 {
    seed_workflow(executor, 42, 3, [0x11; 32], 5)
}

// =============================================================================
// SMALLER: the whole surface is one builder (the SHIPPED `src::workflow_app`).
// =============================================================================

#[test]
fn the_whole_app_is_one_composed_registration() {
    let (cclerk, executor) = agent();
    let app = workflow_app(&cclerk, &executor);

    // ONE app, ONE cell. The cap-only surface carries the read; the state-mutating op
    // (advance_step) is GATED (cap∧state).
    assert_eq!(app.name(), "compartment-workflow-mandate");
    assert_eq!(app.cells().len(), 1);
    let mandate = &app.cells()[0];
    assert_eq!(
        mandate.surface().all_names(),
        vec!["view_workflow".to_string()],
        "the cap-only surface: the charter-cursor read"
    );
    // The gated surface carries the one state-mutating, cap∧state operation.
    let gated: Vec<String> = mandate
        .gated_surface()
        .affordances
        .iter()
        .map(|g| g.name().to_string())
        .collect();
    assert_eq!(gated, vec!["advance_step".to_string()]);

    // The MANDATE cell is the agent's own (so fires execute against the seeded ledger),
    // and is published into the web-of-cells at the observer tier.
    assert_eq!(mandate.cell(), cclerk.cell_id());
    assert_eq!(
        mandate.published_authority(),
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
async fn the_two_workflow_roles_see_different_cap_only_surfaces() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent();
    let app = workflow_app(&cclerk, &executor);
    let router = app.mount();

    async fn visible(router: &axum::Router, tier: &str) -> serde_json::Value {
        let resp = router
            .clone()
            .oneshot(
                Request::get("/workflow/projected")
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

    // An OBSERVER (Signature) sees only `view_workflow` (the narrow read tier). The
    // `advance_step` op is GATED (not on the cap-only projection); it lights on the gated
    // surface against live state.
    assert_eq!(
        visible(&router, "signature").await,
        serde_json::json!(["view_workflow"])
    );
    // The OPERATOR (root) sees the same cap-only set — there are no extra cap-only ops at
    // the operator tier here (advance_step is gated, not cap-only).
    assert_eq!(
        visible(&router, "root").await,
        serde_json::json!(["view_workflow"])
    );
}

// =============================================================================
// MORE CAPABLE (2): a cap-only fire is a real verified turn; anti-ghost holds.
// =============================================================================

#[tokio::test]
async fn an_observer_can_view_the_workflow_a_real_turn() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent();
    let app = workflow_app(&cclerk, &executor);
    let _ = seed(&executor);
    let router = app.mount();

    // Fire a CAP-ONLY affordance (the `/fire/{name}` route).
    async fn fire(router: &axum::Router, name: &str, tier: &str) -> StatusCode {
        router
            .clone()
            .oneshot(
                Request::post(format!("/workflow/fire/{name}"))
                    .header(dregg_app_framework::HELD_RIGHTS_HEADER, tier)
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap()
            .status()
    }
    // Fire a GATED affordance (the state-aware `/gated/fire/{name}` route).
    async fn fire_gated(router: &axum::Router, name: &str, tier: &str) -> StatusCode {
        router
            .clone()
            .oneshot(
                Request::post(format!("/workflow/gated/fire/{name}"))
                    .header(dregg_app_framework::HELD_RIGHTS_HEADER, tier)
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap()
            .status()
    }

    // The CAP tooth, in-band (anti-ghost): an OBSERVER (Signature) CLEARS the cap gate
    // for `view_workflow` (Signature ⊇ Signature) — not 403.
    assert_ne!(
        fire(&router, "view_workflow", "signature").await,
        StatusCode::FORBIDDEN,
        "an observer is cap-authorized to view the workflow (clears the cap gate)"
    );
    // The genuine cap refusal on the HTTP surface: an OBSERVER (Signature) firing the
    // OPERATOR-tier GATED `advance_step` (requires None/root) is REFUSED at the cap gate
    // (403) BEFORE anything reaches the executor — the genuine `is_attenuation`
    // (None ⊄ Signature). An auditor can read the cursor but cannot drive it.
    assert_eq!(
        fire_gated(&router, "advance_step", "signature").await,
        StatusCode::FORBIDDEN,
        "an observer firing the operator-tier advance_step is refused at the cap gate"
    );
    // The OPERATOR (root) CLEARS the cap gate for `advance_step` (not 403) — it is
    // cap-authorized to drive the charter cursor (the fire is a real verified turn).
    assert_ne!(
        fire_gated(&router, "advance_step", "root").await,
        StatusCode::FORBIDDEN,
        "the operator is cap-authorized to advance the workflow (clears the cap gate)"
    );
}

// =============================================================================
// MORE CAPABLE (3): web-of-cells — the MANDATE cell is a distributed sturdyref.
// =============================================================================

#[tokio::test]
async fn the_mandate_is_published_into_the_web_of_cells() {
    let (cclerk, executor) = agent();
    // The SHIPPED surface, re-built with a captp server attached (the web-of-cells
    // minter). `workflow_app` publishes the mandate cell at the observer tier.
    let captp = CapTpServer::new(FederationId([0x3c; 32]));
    let base = workflow_app(&cclerk, &executor);
    let app = DeosApp::builder(
        "compartment-workflow-mandate",
        cclerk.clone(),
        executor.clone(),
    )
    .web_of_cells(captp)
    .cell(base.cells()[0].clone())
    .build();

    // The MANDATE cell is exported as a real `dregg://` sturdyref — an auditor on another
    // federation reacquires the workflow's charter state across the membrane.
    let uris = app.publish_all(100).await;
    assert_eq!(uris.len(), 1);
    assert!(
        uris[0].starts_with("dregg://"),
        "a real sturdyref: {}",
        uris[0]
    );
}

// =============================================================================
// MORE CAPABLE (4): rehydratable frustum-snapshot of the mandate, per-viewer.
// =============================================================================

#[test]
fn a_mandate_snapshot_rehydrates_per_viewer_respecting_the_lattice() {
    let (cclerk, executor) = agent();
    let app = workflow_app(&cclerk, &executor);
    let mandate = &app.cells()[0];

    // Snapshot the mandate; it witnessed a step-advance turn, sources gone (a cold
    // snapshot handed to a downstream auditor) ⇒ liveness REPLAYED-DETERMINISTIC.
    let log = InteractionLog::new().record(Interaction::witnessed_turn(mandate.cell(), [9u8; 32]));
    let snap = mandate.snapshot(log, false);
    assert_eq!(
        snap.lineage,
        AuthRequired::Signature,
        "snapshot at the published lineage"
    );
    assert_eq!(snap.liveness(), Rehydration::ReplayedDeterministic);
    assert!(snap.liveness().is_faithful());

    // An OBSERVER (Signature) rehydrating reacquires only `view_workflow` (the cap-only
    // surface at its tier) — the mandate snapshot respects the lattice.
    let observer = mandate.rehydrate(&snap, AuthRequired::Signature).unwrap();
    assert_eq!(observer.visible_names(), vec!["view_workflow".to_string()]);

    // An INCOMPARABLE authority (a distinct Custom identity) cannot rehydrate at all —
    // the membrane mints NO projection (the no-peek refusal / Amplification).
    let blocked = mandate.rehydrate(&snap, AuthRequired::Custom { vk_hash: [7u8; 32] });
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
    let app = workflow_app(&cclerk, &executor);
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
    // The anti-drift affordance map names the cap-only fire endpoint.
    assert!(js.contains("fireEndpoint: \"/workflow/fire/view_workflow\","));

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
    assert_eq!(m["app"], "compartment-workflow-mandate");
    assert_eq!(
        m["discoverable"],
        serde_json::json!(["workflow", "compartment"])
    );
    assert!(
        m["persistence"]
            .as_str()
            .unwrap()
            .contains("embedded-ledger")
    );
    assert_eq!(m["cells"].as_array().unwrap().len(), 1);
    // The manifest advertises the gated (cap∧state) affordance.
    let gated = m["cells"][0]["gatedAffordances"]
        .as_array()
        .expect("gated affordances");
    let names: Vec<&str> = gated.iter().filter_map(|g| g["name"].as_str()).collect();
    assert!(
        names.contains(&"advance_step"),
        "advance_step is advertised as gated"
    );
}
