//! RE-EXPRESSION proof: the `agent-provenance` starbridge-app, on the composed deos
//! framework — **the same app, smaller + more capable, SHIPPED from `src/`.**
//!
//! `docs/deos/APPS-DEOS-INTEGRATION-CENSUS.md`: the agent-provenance LOG, re-expressed as
//! a composed [`DeosApp`] and SHIPPED in `src/lib.rs`. This file drives the SHIPPED
//! surface ([`provenance_app`] from `src/`): per-viewer projection, the cap-gated fires
//! through the mounted axum surface, the `dregg://` web-of-cells publish, the
//! rehydratable frustum-snapshot, the generated `<dregg-affordance-surface>` component,
//! and the manifest — none of which the floor bones had.
//!
//! The LOG's surface on the verifier ⊂ recorder rights ladder (`Signature ⊂ Either ⊂
//! None`):
//!   - `view_provenance` — cap-only (a VERIFIER reads + re-derives the chain);
//!   - `append_entry` — GATED (cap∧state): the cap-gate AND a live-state precondition,
//!     with the FULL provenance program re-enforced by the executor on the fire (the seam
//!     the census flagged, now CLOSED — see `tests/deos_seam.rs`).
//!
//! Every affordance carries a REAL [`Effect`]; every fire is a real verified turn through
//! the embedded executor; the gate is the genuine `is_attenuation` (+ the genuine
//! `CellProgram::evaluate` for the gated one). No parallel model.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CapTpServer, DeosApp, EmbeddedExecutor,
    FederationId, Interaction, InteractionLog, RehydrateError, Rehydration,
};

use starbridge_agent_provenance::{provenance_app, seed_log};

fn agent() -> (AppCipherclerk, EmbeddedExecutor) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x9c; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    (cclerk, executor)
}

// =============================================================================
// SMALLER: the whole surface is one builder (the SHIPPED `src::provenance_app`).
// =============================================================================

#[test]
fn the_whole_app_is_one_composed_registration() {
    let (cclerk, executor) = agent();
    let app = provenance_app(&cclerk, &executor);

    // ONE app, ONE cell. The cap-only surface carries the read; the state-mutating op
    // (append_entry) is GATED (cap∧state).
    assert_eq!(app.name(), "agent-provenance");
    assert_eq!(app.cells().len(), 1);
    let log = &app.cells()[0];
    assert_eq!(
        log.surface().all_names(),
        vec!["view_provenance".to_string()],
        "the cap-only surface: the verifier read (verify_chain's deos home)"
    );
    // The gated surface carries the state-mutating, cap∧state operation.
    let gated: Vec<String> = log
        .gated_surface()
        .affordances
        .iter()
        .map(|g| g.name().to_string())
        .collect();
    assert_eq!(gated, vec!["append_entry".to_string()]);

    // The LOG cell is the agent's own (so fires execute against the seeded ledger), and is
    // published into the web-of-cells at the verifier tier.
    assert_eq!(log.cell(), cclerk.cell_id());
    assert_eq!(log.published_authority(), Some(&AuthRequired::Signature));

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
async fn the_three_provenance_roles_see_different_cap_only_surfaces() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent();
    let app = provenance_app(&cclerk, &executor);
    let router = app.mount();

    async fn visible(router: &axum::Router, tier: &str) -> serde_json::Value {
        let resp = router
            .clone()
            .oneshot(
                Request::get("/log/projected")
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

    // A VERIFIER (Signature) sees `view_provenance` (the narrow read tier).
    assert_eq!(
        visible(&router, "signature").await,
        serde_json::json!(["view_provenance"])
    );
    // A RECORDER (Either) sees the same cap-only set — `append_entry` is GATED (not on the
    // cap-only projection); it lights on the gated surface against live state.
    assert_eq!(
        visible(&router, "either").await,
        serde_json::json!(["view_provenance"])
    );
    // The OWNER (root) attenuates down to the same cap-only read (no grant affordance on
    // this app — append is the only mutation and it is gated).
    assert_eq!(
        visible(&router, "root").await,
        serde_json::json!(["view_provenance"])
    );
}

// =============================================================================
// MORE CAPABLE (2): the gated cap tooth bites over HTTP; anti-ghost holds.
// =============================================================================

#[tokio::test]
async fn the_recorder_cap_tooth_bites_over_http_anti_ghost() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent();
    let app = provenance_app(&cclerk, &executor);
    let _ = seed_log(&executor, b"genesis");
    let router = app.mount();

    async fn fire_gated(router: &axum::Router, name: &str, tier: &str) -> StatusCode {
        router
            .clone()
            .oneshot(
                Request::post(format!("/log/gated/fire/{name}"))
                    .header(dregg_app_framework::HELD_RIGHTS_HEADER, tier)
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap()
            .status()
    }

    // The CAP tooth, in-band (anti-ghost): a VERIFIER (Signature — a RECOGNIZED tier, but
    // NARROWER than the Either `append_entry` requires) firing the gated `append_entry` is
    // REFUSED at the cap gate (403 FORBIDDEN) BEFORE anything reaches the executor. The cap
    // gate is the genuine `is_attenuation` (`Either` ⊄ `Signature`).
    assert_eq!(
        fire_gated(&router, "append_entry", "signature").await,
        StatusCode::FORBIDDEN,
        "a verifier (Signature) is refused at the recorder cap gate (Either required)"
    );

    // A RECORDER (Either) CLEARS the cap gate (not 403) — it is cap-authorized to append.
    // (The seeded log satisfies the live-state precondition, so the gated fire proceeds to a
    // real verified turn rather than being held at either tooth.)
    assert_ne!(
        fire_gated(&router, "append_entry", "either").await,
        StatusCode::FORBIDDEN,
        "a recorder is cap-authorized to append (clears the cap gate)"
    );
}

// =============================================================================
// MORE CAPABLE (3): web-of-cells — the LOG cell is a distributed sturdyref.
// =============================================================================

#[tokio::test]
async fn the_log_is_published_into_the_web_of_cells() {
    let (cclerk, executor) = agent();
    // The SHIPPED surface, re-built with a captp server attached (the web-of-cells
    // minter). `provenance_app` publishes the log cell at the verifier tier.
    let captp = CapTpServer::new(FederationId([0x9c; 32]));
    let base = provenance_app(&cclerk, &executor);
    let app = DeosApp::builder("agent-provenance", cclerk.clone(), executor.clone())
        .web_of_cells(captp)
        .cell(base.cells()[0].clone())
        .build();

    // The LOG cell is exported as a real `dregg://` sturdyref — a third-party auditor on
    // another federation reacquires the log's provenance across the membrane.
    let uris = app.publish_all(100).await;
    assert_eq!(uris.len(), 1);
    assert!(
        uris[0].starts_with("dregg://"),
        "a real sturdyref: {}",
        uris[0]
    );
}

// =============================================================================
// MORE CAPABLE (4): rehydratable frustum-snapshot of the log, per-viewer.
// =============================================================================

#[test]
fn a_log_snapshot_rehydrates_per_viewer_respecting_the_lattice() {
    let (cclerk, executor) = agent();
    let app = provenance_app(&cclerk, &executor);
    let log = &app.cells()[0];

    // Snapshot the log; it witnessed an append turn, sources gone (a cold snapshot handed
    // to a downstream auditor) ⇒ liveness REPLAYED-DETERMINISTIC.
    let wlog = InteractionLog::new().record(Interaction::witnessed_turn(log.cell(), [9u8; 32]));
    let snap = log.snapshot(wlog, false);
    assert_eq!(
        snap.lineage,
        AuthRequired::Signature,
        "snapshot at the published lineage"
    );
    assert_eq!(snap.liveness(), Rehydration::ReplayedDeterministic);
    assert!(snap.liveness().is_faithful());

    // A VERIFIER (Signature) rehydrating reacquires `view_provenance` (the cap-only surface
    // at its tier) — the log snapshot respects the lattice.
    let verifier = log.rehydrate(&snap, AuthRequired::Signature).unwrap();
    assert_eq!(
        verifier.visible_names(),
        vec!["view_provenance".to_string()]
    );

    // An INCOMPARABLE authority (a distinct Custom identity) cannot rehydrate at all — the
    // membrane mints NO projection (the no-peek refusal).
    let blocked = log.rehydrate(&snap, AuthRequired::Custom { vk_hash: [7u8; 32] });
    assert!(matches!(blocked, Err(RehydrateError::Amplification { .. })));
}

// =============================================================================
// MORE CAPABLE (5): the generated web component + the manifest (with the gated state-gate).
// =============================================================================

#[tokio::test]
async fn the_app_ships_a_web_component_surface_and_a_manifest() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent();
    let app = provenance_app(&cclerk, &executor);
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
    assert!(js.contains("fireEndpoint: \"/log/fire/view_provenance\","));

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
    assert_eq!(m["app"], "agent-provenance");
    assert_eq!(
        m["discoverable"],
        serde_json::json!(["provenance", "audit"])
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
        names.contains(&"append_entry"),
        "append_entry is advertised as gated"
    );
}
