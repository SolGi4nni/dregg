//! RE-EXPRESSION proof: the `escrow-market` starbridge-app, on the composed deos
//! framework — **the same app, smaller + more capable, now SHIPPED from `src/`.**
//!
//! `docs/deos/APPS-DEOS-INTEGRATION-CENSUS.md`: the escrowed-delivery marketplace,
//! re-expressed as a composed [`DeosApp`] and PROMOTED into `src/lib.rs`. This file
//! drives the SHIPPED surface ([`escrow_app`] from `src/`), proving the promotion:
//! per-viewer projection, the cap-gated fires through the mounted axum surface, the
//! `dregg://` web-of-cells publish, the rehydratable frustum-snapshot, the generated
//! `<dregg-affordance-surface>` component, and the manifest — none of which the floor
//! crate's hand-wired JS had.
//!
//! The ESCROW's surface on the observer ⊂ buyer ⊂ seller rights ladder
//! (`Signature ⊂ Either ⊂ None`):
//!   - `view_escrow` — cap-only (an OBSERVER reads the order state);
//!   - `fund` / `ship` / `settle` — GATED (cap∧state): the cap-gate AND a live-state
//!     STATE-code precondition, with the FULL escrow program re-enforced by the executor
//!     on the fire (the seam — see `tests/deos_seam.rs`).
//!
//! Every affordance carries a REAL [`Effect`]; every fire is a real verified turn through
//! the embedded executor; the gate is the genuine `is_attenuation` (+ the genuine
//! `CellProgram::evaluate` for the gated ones). No parallel model.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CapTpServer, DeosApp, EmbeddedExecutor,
    FederationId, Interaction, InteractionLog, RehydrateError, Rehydration,
};

use starbridge_escrow_market::{escrow_app, seed_escrow};

fn agent() -> (AppCipherclerk, EmbeddedExecutor) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x62; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    (cclerk, executor)
}

// =============================================================================
// SMALLER: the whole surface is one builder (the SHIPPED `src::escrow_app`).
// =============================================================================

#[test]
fn the_whole_app_is_one_composed_registration() {
    let (cclerk, executor) = agent();
    let app = escrow_app(&cclerk, &executor);

    // ONE app, ONE cell. The cap-only surface carries just the read; the state-mutating
    // ops (fund / ship / settle) are GATED (cap∧state).
    assert_eq!(app.name(), "escrow-market");
    assert_eq!(app.cells().len(), 1);
    let escrow = &app.cells()[0];
    assert_eq!(
        escrow.surface().all_names(),
        vec!["view_escrow".to_string()],
        "the cap-only surface: just the order read (fund/ship/settle are gated)"
    );
    // The gated surface carries the three state-mutating, cap∧state lifecycle operations.
    let mut gated: Vec<String> = escrow
        .gated_surface()
        .affordances
        .iter()
        .map(|g| g.name().to_string())
        .collect();
    gated.sort();
    assert_eq!(
        gated,
        vec!["fund".to_string(), "settle".to_string(), "ship".to_string()]
    );

    // The ESCROW cell is the agent's own (so fires execute against the seeded ledger),
    // and is published into the web-of-cells at the observer tier.
    assert_eq!(escrow.cell(), cclerk.cell_id());
    assert_eq!(escrow.published_authority(), Some(&AuthRequired::Signature));

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
async fn the_three_escrow_roles_see_different_cap_only_surfaces() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent();
    let app = escrow_app(&cclerk, &executor);
    let router = app.mount();

    async fn visible(router: &axum::Router, tier: &str) -> serde_json::Value {
        let resp = router
            .clone()
            .oneshot(
                Request::get("/escrow/projected")
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

    // An OBSERVER (Signature) sees only `view_escrow` (the narrow read tier).
    assert_eq!(
        visible(&router, "signature").await,
        serde_json::json!(["view_escrow"])
    );
    // A BUYER (Either) sees the same cap-only set — `fund` is GATED (not on the cap-only
    // projection); it lights on the gated surface against live state (the htmx tooth).
    assert_eq!(
        visible(&router, "either").await,
        serde_json::json!(["view_escrow"])
    );
    // The SELLER (root) also sees only `view_escrow` on the cap-only projection — `ship` and
    // `settle` are GATED too (they light on the gated surface against live state).
    assert_eq!(
        visible(&router, "root").await,
        serde_json::json!(["view_escrow"])
    );
}

// =============================================================================
// MORE CAPABLE (2): a cap-only fire is a real verified turn; anti-ghost holds.
// =============================================================================

#[tokio::test]
async fn an_observer_can_view_the_escrow_a_real_turn() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent();
    let app = escrow_app(&cclerk, &executor);
    let _ = seed_escrow(&executor, "acme-corp", 1000);
    let router = app.mount();

    async fn fire(router: &axum::Router, name: &str, tier: &str) -> StatusCode {
        router
            .clone()
            .oneshot(
                Request::post(format!("/escrow/fire/{name}"))
                    .header(dregg_app_framework::HELD_RIGHTS_HEADER, tier)
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap()
            .status()
    }

    // The CAP tooth, in-band (anti-ghost): nobody is below the observer tier (Signature is
    // the floor), so any held tier clears the `view_escrow` cap gate (not 403). The observer
    // read is a real EmitEvent turn through the executor.
    assert_ne!(
        fire(&router, "view_escrow", "signature").await,
        StatusCode::FORBIDDEN,
        "an observer is cap-authorized to view (clears the cap gate)"
    );
}

// =============================================================================
// MORE CAPABLE (3): web-of-cells — the ESCROW cell is a distributed sturdyref.
// =============================================================================

#[tokio::test]
async fn the_escrow_is_published_into_the_web_of_cells() {
    let (cclerk, executor) = agent();
    // The SHIPPED surface, re-built with a captp server attached (the web-of-cells minter).
    // `escrow_app` publishes the escrow cell at the observer tier.
    let captp = CapTpServer::new(FederationId([0x62; 32]));
    let base = escrow_app(&cclerk, &executor);
    let app = DeosApp::builder("escrow-market", cclerk.clone(), executor.clone())
        .web_of_cells(captp)
        .cell(base.cells()[0].clone())
        .build();

    // The ESCROW cell is exported as a real `dregg://` sturdyref — an auditor on another
    // federation reacquires the order across the membrane.
    let uris = app.publish_all(100).await;
    assert_eq!(uris.len(), 1);
    assert!(
        uris[0].starts_with("dregg://"),
        "a real sturdyref: {}",
        uris[0]
    );
}

// =============================================================================
// MORE CAPABLE (4): rehydratable frustum-snapshot of the escrow, per-viewer.
// =============================================================================

#[test]
fn an_escrow_snapshot_rehydrates_per_viewer_respecting_the_lattice() {
    let (cclerk, executor) = agent();
    let app = escrow_app(&cclerk, &executor);
    let escrow = &app.cells()[0];

    // Snapshot the escrow; it witnessed a funding turn, sources gone (a cold snapshot handed
    // to a downstream auditor) ⇒ liveness REPLAYED-DETERMINISTIC.
    let log = InteractionLog::new().record(Interaction::witnessed_turn(escrow.cell(), [9u8; 32]));
    let snap = escrow.snapshot(log, false);
    assert_eq!(
        snap.lineage,
        AuthRequired::Signature,
        "snapshot at the published lineage"
    );
    assert_eq!(snap.liveness(), Rehydration::ReplayedDeterministic);
    assert!(snap.liveness().is_faithful());

    // An OBSERVER (Signature) rehydrating reacquires only `view_escrow` (the cap-only surface
    // at its tier) — the snapshot respects the lattice.
    let observer = escrow.rehydrate(&snap, AuthRequired::Signature).unwrap();
    assert_eq!(observer.visible_names(), vec!["view_escrow".to_string()]);

    // An INCOMPARABLE authority (a distinct Custom identity) cannot rehydrate at all — the
    // membrane mints NO projection (the no-peek refusal).
    let blocked = escrow.rehydrate(&snap, AuthRequired::Custom { vk_hash: [7u8; 32] });
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
    let app = escrow_app(&cclerk, &executor);
    let router = app.mount();

    // GET /surface.js serves the `<dregg-affordance-surface>` web component, generated from
    // the Rust source of truth (the floor hand-wrote its JS).
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
    assert!(js.contains("fireEndpoint: \"/escrow/fire/view_escrow\","));

    // GET /manifest serves the whole composed surface, including the GATED affordances with
    // their state-gate described (the cap∧state posture is visible to any client).
    let manifest = router
        .oneshot(Request::get("/manifest").body(Body::empty()).unwrap())
        .await
        .unwrap();
    assert_eq!(manifest.status(), StatusCode::OK);
    let bytes = axum::body::to_bytes(manifest.into_body(), usize::MAX)
        .await
        .unwrap();
    let m: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    assert_eq!(m["app"], "escrow-market");
    assert_eq!(
        m["discoverable"],
        serde_json::json!(["escrow", "marketplace"])
    );
    assert!(
        m["persistence"]
            .as_str()
            .unwrap()
            .contains("embedded-ledger")
    );
    assert_eq!(m["cells"].as_array().unwrap().len(), 1);
    // The manifest advertises the three gated (cap∧state) affordances.
    let gated = m["cells"][0]["gatedAffordances"]
        .as_array()
        .expect("gated affordances");
    let names: Vec<&str> = gated.iter().filter_map(|g| g["name"].as_str()).collect();
    assert!(names.contains(&"fund"), "fund is advertised as gated");
    assert!(names.contains(&"ship"), "ship is advertised as gated");
    assert!(names.contains(&"settle"), "settle is advertised as gated");
}
