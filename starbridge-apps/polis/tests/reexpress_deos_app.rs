//! RE-EXPRESSION proof: the five `polis` governance families, on the composed deos
//! framework — **the same governance, now a LIVE per-viewer, cap-gated web surface.**
//!
//! `docs/deos/DEOS.md` + `Dregg2/Deos/{GatedAffordance,WorkflowBridge}.lean`: a deos app is
//! the six kernel layers wired into ONE shape. This file drives the deos skin
//! (`src/deos.rs`) over the pure polis library — proving, per family, the surface the bare
//! library never had: the cap-only + gated affordance split, per-viewer projection over
//! HTTP (mount + `/<cell>/projected` + `HELD_RIGHTS_HEADER`), the `dregg://` web-of-cells
//! publish, the generated `/surface.js` web component, and the `/manifest`.
//!
//! Coverage (per the task's representative split):
//!   * COUNCIL, MANDATE, IDENTITY — FULLY re-expressed: surface names (cap-only + gated),
//!     per-viewer HTTP projection, web-of-cells `dregg://` publish, `/surface.js` + `/manifest`;
//!   * AMENDMENT, CONSTITUTION — build + register + at least one gated affordance present.
//!
//! The deos surface is compiled INTO THIS TEST BINARY via `#[path]` (it is NOT a library
//! module — `dregg-sdk` depends on `starbridge-polis` and `dregg-app-framework` depends on
//! `dregg-sdk`, so a normal `polis -> app-framework` edge would close an illegal package
//! cycle; Cargo permits it only across this dev-dependency edge). See `Cargo.toml`.

#![cfg(feature = "deos")]
#![allow(dead_code)] // the included `src/deos.rs` has pub items each test binary uses a subset of

#[path = "../src/deos.rs"]
mod deos;

use deos::*;
use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CapTpServer, CellId, DeosApp, EmbeddedExecutor,
    FederationId, HELD_RIGHTS_HEADER, StarbridgeAppContext,
};
use starbridge_polis::{
    constitution::ConstitutionParams,
    council::{AmendmentTerms, CouncilCharter},
    identity::{IdentityCharter, key_set_commitment},
    mandate::{WorkerMandate, tool_scope_commitment},
};

fn agent(seed: u8) -> (AppCipherclerk, EmbeddedExecutor) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    (cclerk, executor)
}

fn council_2of3() -> CouncilCharter {
    CouncilCharter::new(
        vec![
            CellId::from_bytes([0x11; 32]),
            CellId::from_bytes([0x22; 32]),
            CellId::from_bytes([0x33; 32]),
        ],
        2,
    )
}

fn worker_mandate() -> WorkerMandate {
    WorkerMandate {
        orchestrator: CellId::from_bytes([0xAA; 32]),
        slice: 30,
        tool_scope: tool_scope_commitment(&["search", "fetch"]),
        worker_tag: dregg_app_framework::field_from_u64(1),
    }
}

fn identity_charter() -> IdentityCharter {
    IdentityCharter {
        council: CouncilCharter::new(
            vec![
                CellId::from_bytes([0xD1; 32]),
                CellId::from_bytes([0xD2; 32]),
            ],
            2,
        ),
        cooling_period: 50,
    }
}

// =============================================================================
// COUNCIL (full) — surface split, per-viewer HTTP projection, publish, surface.js + manifest.
// =============================================================================

#[test]
fn council_is_one_composed_app_with_the_cap_only_and_gated_split() {
    let (cclerk, executor) = agent(0xC0);
    let app = council_app(&cclerk, &executor);

    assert_eq!(app.name(), "polis-council");
    assert_eq!(app.cells().len(), 1);
    let cell = &app.cells()[0];
    // The cap-only surface carries the read; the state-mutating ops are GATED (cap∧state).
    assert_eq!(
        cell.surface().all_names(),
        vec!["view_council".to_string()],
        "the cap-only surface: the observer read",
    );
    let mut gated: Vec<String> = cell
        .gated_surface()
        .affordances
        .iter()
        .map(|g| g.name().to_string())
        .collect();
    gated.sort();
    assert_eq!(
        gated,
        vec!["approve".to_string(), "certify".to_string()],
        "the gated (cap∧state) surface: the participant + authority transitions",
    );
    // The proposal cell is the agent's own (so fires execute against the seeded ledger), and
    // is published into the web-of-cells at the observer tier.
    assert_eq!(cell.cell(), cclerk.cell_id());
    assert_eq!(cell.published_authority(), Some(&AuthRequired::Signature));
}

#[tokio::test]
async fn council_projects_per_viewer_over_http() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent(0xC1);
    let app = council_app(&cclerk, &executor);
    let router = app.mount();

    async fn visible(router: &axum::Router, tier: &str) -> serde_json::Value {
        let resp = router
            .clone()
            .oneshot(
                Request::get("/council-proposal/projected")
                    .header(HELD_RIGHTS_HEADER, tier)
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(resp.status(), StatusCode::OK, "projection over HTTP is OK");
        let bytes = axum::body::to_bytes(resp.into_body(), usize::MAX)
            .await
            .unwrap();
        serde_json::from_slice::<serde_json::Value>(&bytes).unwrap()["visible"].clone()
    }

    // The cap-only surface holds only the read; every tier at/above `Signature` sees it.
    assert_eq!(
        visible(&router, "signature").await,
        serde_json::json!(["view_council"])
    );
    assert_eq!(
        visible(&router, "either").await,
        serde_json::json!(["view_council"])
    );
    assert_eq!(
        visible(&router, "root").await,
        serde_json::json!(["view_council"])
    );
}

#[tokio::test]
async fn council_publishes_into_the_web_of_cells() {
    // The proposal cell is exported as a real `dregg://` sturdyref — a council member on
    // another federation reacquires the proposal across the membrane.
    let (cclerk, executor) = agent(0xC2);
    let captp = CapTpServer::new(FederationId([0xC2; 32]));
    let base = council_app(&cclerk, &executor);
    let app = DeosApp::builder("polis-council", cclerk.clone(), executor.clone())
        .web_of_cells(captp)
        .cell(base.cells()[0].clone())
        .build();

    let uris = app.publish_all(100).await;
    assert_eq!(uris.len(), 1);
    assert!(
        uris[0].starts_with("dregg://"),
        "a real sturdyref: {}",
        uris[0]
    );
}

#[tokio::test]
async fn council_ships_a_web_component_and_a_manifest() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent(0xC3);
    let app = council_app(&cclerk, &executor);
    let router = app.mount();

    // GET /surface.js — the `<dregg-affordance-surface>` web component (anti-drift, from the
    // Rust source of truth).
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

    // GET /manifest — the whole composed surface, including the GATED affordances.
    let manifest = router
        .oneshot(Request::get("/manifest").body(Body::empty()).unwrap())
        .await
        .unwrap();
    assert_eq!(manifest.status(), StatusCode::OK);
    let bytes = axum::body::to_bytes(manifest.into_body(), usize::MAX)
        .await
        .unwrap();
    let m: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    assert_eq!(m["app"], "polis-council");
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
    assert!(names.contains(&"approve"), "approve is advertised as gated");
    assert!(names.contains(&"certify"), "certify is advertised as gated");
}

#[test]
fn council_register_deos_folds_the_seeded_surface_into_a_context() {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0xC4; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    let ctx = StarbridgeAppContext::new(cclerk.clone(), executor.clone());

    // `register_council_deos` builds the app, seeds a PROPOSED proposal cell, and folds the
    // surface into the context's affordance registry.
    let app = register_council_deos(&ctx, &council_2of3());
    assert_eq!(app.name(), "polis-council");
    assert_eq!(
        ctx.affordance_registry().len(),
        1,
        "the deos surface is registered"
    );
    // The seeded cell is PROPOSED (approvals open), so an approve fires immediately through
    // the mounted surface (the seam is live).
    let state = executor
        .cell_state(cclerk.cell_id())
        .expect("seeded cell exists");
    assert_eq!(
        state.fields[0],
        dregg_app_framework::field_from_u64(starbridge_polis::council::STATE_PROPOSED),
        "seeded into PROPOSED",
    );
}

// =============================================================================
// MANDATE (full) — surface split, per-viewer HTTP projection, publish, surface.js + manifest.
// =============================================================================

#[test]
fn mandate_is_one_composed_app_with_the_cap_only_and_gated_split() {
    let (cclerk, executor) = agent(0x3A);
    let app = mandate_app(&cclerk, &executor);

    assert_eq!(app.name(), "polis-mandate");
    let cell = &app.cells()[0];
    assert_eq!(cell.surface().all_names(), vec!["view_mandate".to_string()]);
    let mut gated: Vec<String> = cell
        .gated_surface()
        .affordances
        .iter()
        .map(|g| g.name().to_string())
        .collect();
    gated.sort();
    assert_eq!(gated, vec!["invoke".to_string(), "revoke".to_string()]);
    assert_eq!(cell.published_authority(), Some(&AuthRequired::Signature));
}

#[tokio::test]
async fn mandate_projects_per_viewer_over_http() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent(0x3B);
    let app = mandate_app(&cclerk, &executor);
    let router = app.mount();

    let resp = router
        .clone()
        .oneshot(
            Request::get("/worker-mandate/projected")
                .header(HELD_RIGHTS_HEADER, "either")
                .body(Body::empty())
                .unwrap(),
        )
        .await
        .unwrap();
    assert_eq!(resp.status(), StatusCode::OK);
    let bytes = axum::body::to_bytes(resp.into_body(), usize::MAX)
        .await
        .unwrap();
    let visible = serde_json::from_slice::<serde_json::Value>(&bytes).unwrap()["visible"].clone();
    // The cap-only surface holds only the read (invoke/revoke are gated, not on the cap-only
    // projection — they light on the gated surface against live state).
    assert_eq!(visible, serde_json::json!(["view_mandate"]));
}

#[tokio::test]
async fn mandate_publishes_into_the_web_of_cells() {
    let (cclerk, executor) = agent(0x3C);
    let captp = CapTpServer::new(FederationId([0x3C; 32]));
    let base = mandate_app(&cclerk, &executor);
    let app = DeosApp::builder("polis-mandate", cclerk.clone(), executor.clone())
        .web_of_cells(captp)
        .cell(base.cells()[0].clone())
        .build();

    let uris = app.publish_all(100).await;
    assert_eq!(uris.len(), 1);
    assert!(
        uris[0].starts_with("dregg://"),
        "a real sturdyref: {}",
        uris[0]
    );
}

#[tokio::test]
async fn mandate_ships_a_web_component_and_a_manifest() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent(0x3D);
    let app = mandate_app(&cclerk, &executor);
    let router = app.mount();

    let surface = router
        .clone()
        .oneshot(Request::get("/surface.js").body(Body::empty()).unwrap())
        .await
        .unwrap();
    assert_eq!(surface.status(), StatusCode::OK);
    let bytes = axum::body::to_bytes(surface.into_body(), usize::MAX)
        .await
        .unwrap();
    let js = String::from_utf8(bytes.to_vec()).unwrap();
    assert!(js.contains("customElements.define(\"dregg-affordance-surface\""));

    let manifest = router
        .oneshot(Request::get("/manifest").body(Body::empty()).unwrap())
        .await
        .unwrap();
    assert_eq!(manifest.status(), StatusCode::OK);
    let bytes = axum::body::to_bytes(manifest.into_body(), usize::MAX)
        .await
        .unwrap();
    let m: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    assert_eq!(m["app"], "polis-mandate");
    assert_eq!(
        m["discoverable"],
        serde_json::json!(["polis", "mandate", "orchestration"])
    );
    let gated = m["cells"][0]["gatedAffordances"]
        .as_array()
        .expect("gated affordances");
    let names: Vec<&str> = gated.iter().filter_map(|g| g["name"].as_str()).collect();
    assert!(names.contains(&"invoke"));
    assert!(names.contains(&"revoke"));
}

#[test]
fn mandate_register_deos_folds_the_seeded_surface_into_a_context() {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x3E; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    let ctx = StarbridgeAppContext::new(cclerk.clone(), executor.clone());
    let app = register_mandate_deos(&ctx, &worker_mandate());
    assert_eq!(app.name(), "polis-mandate");
    assert_eq!(ctx.affordance_registry().len(), 1);
    let state = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        state.fields[0],
        dregg_app_framework::field_from_u64(starbridge_polis::mandate::STATE_ACTIVE),
        "seeded into ACTIVE",
    );
}

// =============================================================================
// IDENTITY (full) — surface split, per-viewer HTTP projection, publish, surface.js + manifest.
// =============================================================================

#[test]
fn identity_is_one_composed_app_with_the_cap_only_and_gated_split() {
    let (cclerk, executor) = agent(0x1A);
    let app = identity_app(&cclerk, &executor);

    assert_eq!(app.name(), "polis-identity");
    let cell = &app.cells()[0];
    assert_eq!(
        cell.surface().all_names(),
        vec!["view_identity".to_string()]
    );
    let mut gated: Vec<String> = cell
        .gated_surface()
        .affordances
        .iter()
        .map(|g| g.name().to_string())
        .collect();
    gated.sort();
    assert_eq!(gated, vec!["attest".to_string(), "rotate".to_string()]);
    assert_eq!(cell.published_authority(), Some(&AuthRequired::Signature));
}

#[tokio::test]
async fn identity_projects_per_viewer_over_http() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent(0x1B);
    let app = identity_app(&cclerk, &executor);
    let router = app.mount();

    let resp = router
        .clone()
        .oneshot(
            Request::get("/identity/projected")
                .header(HELD_RIGHTS_HEADER, "signature")
                .body(Body::empty())
                .unwrap(),
        )
        .await
        .unwrap();
    assert_eq!(resp.status(), StatusCode::OK);
    let bytes = axum::body::to_bytes(resp.into_body(), usize::MAX)
        .await
        .unwrap();
    let visible = serde_json::from_slice::<serde_json::Value>(&bytes).unwrap()["visible"].clone();
    assert_eq!(visible, serde_json::json!(["view_identity"]));
}

#[tokio::test]
async fn identity_publishes_into_the_web_of_cells() {
    let (cclerk, executor) = agent(0x1C);
    let captp = CapTpServer::new(FederationId([0x1C; 32]));
    let base = identity_app(&cclerk, &executor);
    let app = DeosApp::builder("polis-identity", cclerk.clone(), executor.clone())
        .web_of_cells(captp)
        .cell(base.cells()[0].clone())
        .build();

    let uris = app.publish_all(100).await;
    assert_eq!(uris.len(), 1);
    assert!(
        uris[0].starts_with("dregg://"),
        "a real sturdyref: {}",
        uris[0]
    );
}

#[tokio::test]
async fn identity_ships_a_web_component_and_a_manifest() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent(0x1D);
    let app = identity_app(&cclerk, &executor);
    let router = app.mount();

    let surface = router
        .clone()
        .oneshot(Request::get("/surface.js").body(Body::empty()).unwrap())
        .await
        .unwrap();
    assert_eq!(surface.status(), StatusCode::OK);
    let bytes = axum::body::to_bytes(surface.into_body(), usize::MAX)
        .await
        .unwrap();
    let js = String::from_utf8(bytes.to_vec()).unwrap();
    assert!(js.contains("customElements.define(\"dregg-affordance-surface\""));

    let manifest = router
        .oneshot(Request::get("/manifest").body(Body::empty()).unwrap())
        .await
        .unwrap();
    assert_eq!(manifest.status(), StatusCode::OK);
    let bytes = axum::body::to_bytes(manifest.into_body(), usize::MAX)
        .await
        .unwrap();
    let m: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    assert_eq!(m["app"], "polis-identity");
    assert_eq!(
        m["discoverable"],
        serde_json::json!(["polis", "identity", "keri"])
    );
    let gated = m["cells"][0]["gatedAffordances"]
        .as_array()
        .expect("gated affordances");
    let names: Vec<&str> = gated.iter().filter_map(|g| g["name"].as_str()).collect();
    assert!(names.contains(&"attest"));
    assert!(names.contains(&"rotate"));
}

#[test]
fn identity_register_deos_folds_the_seeded_genesis_surface_into_a_context() {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x1E; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    let ctx = StarbridgeAppContext::new(cclerk.clone(), executor.clone());
    let g0 = key_set_commitment(&[[0x10; 32], [0x11; 32]]);
    let g1 = key_set_commitment(&[[0x20; 32], [0x21; 32]]);
    let app = register_identity_deos(&ctx, &identity_charter(), g0, g1);
    assert_eq!(app.name(), "polis-identity");
    assert_eq!(ctx.affordance_registry().len(), 1);
    let state = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        state.fields[0],
        dregg_app_framework::field_from_u64(starbridge_polis::identity::STATE_ACTIVE),
        "seeded into ACTIVE (genesis)",
    );
}

// =============================================================================
// AMENDMENT + CONSTITUTION (lighter) — build + register + a gated affordance present.
// =============================================================================

fn amendment_terms() -> AmendmentTerms {
    AmendmentTerms {
        charter: council_2of3(),
        new_constitution_hash: dregg_app_framework::field_from_u64(0xC0457),
        enact_not_before: 500,
    }
}

#[test]
fn amendment_builds_registers_and_presents_its_gated_ratify() {
    let (cclerk, executor) = agent(0xA0);
    let app = amendment_app(&cclerk, &executor);
    assert_eq!(app.name(), "polis-amendment");
    // The cap-only read + the gated `ratify` (the authority's decisive enact).
    assert_eq!(
        app.cells()[0].surface().all_names(),
        vec!["view_amendment".to_string()]
    );
    let gated: Vec<String> = app.cells()[0]
        .gated_surface()
        .affordances
        .iter()
        .map(|g| g.name().to_string())
        .collect();
    assert_eq!(
        gated,
        vec!["ratify".to_string()],
        "the gated authority transition is present"
    );

    // register_amendment_deos folds the seeded (APPROVED) surface into a context.
    let ctx = StarbridgeAppContext::new(cclerk.clone(), executor.clone());
    let reg = register_amendment_deos(&ctx, &amendment_terms());
    assert_eq!(reg.name(), "polis-amendment");
    assert_eq!(ctx.affordance_registry().len(), 1);
    let state = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        state.fields[0],
        dregg_app_framework::field_from_u64(starbridge_polis::council::STATE_APPROVED),
        "seeded into APPROVED (ready to ratify past the cooling gate)",
    );
}

fn params_v1() -> ConstitutionParams {
    ConstitutionParams {
        version: 1,
        council_threshold: 2,
        amendment_delay: 50,
        treasury_cap: 1_000,
    }
}

#[test]
fn constitution_builds_registers_and_presents_its_gated_amend() {
    let (cclerk, executor) = agent(0xC8);
    let app = constitution_app(&cclerk, &executor);
    assert_eq!(app.name(), "polis-constitution");
    assert_eq!(
        app.cells()[0].surface().all_names(),
        vec!["view_constitution".to_string()]
    );
    let gated: Vec<String> = app.cells()[0]
        .gated_surface()
        .affordances
        .iter()
        .map(|g| g.name().to_string())
        .collect();
    assert_eq!(
        gated,
        vec!["amend".to_string()],
        "the gated authority transition is present"
    );

    let ctx = StarbridgeAppContext::new(cclerk.clone(), executor.clone());
    let reg = register_constitution_deos(&ctx, &params_v1());
    assert_eq!(reg.name(), "polis-constitution");
    assert_eq!(ctx.affordance_registry().len(), 1);
    let state = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        state.fields[0],
        dregg_app_framework::field_from_u64(starbridge_polis::constitution::STATE_ACTIVE),
        "seeded into ACTIVE (parameters frozen)",
    );
}

// =============================================================================
// ALL FIVE at once — register_all_deos mounts the whole polis governance on one context.
// =============================================================================

#[test]
fn register_all_deos_mounts_every_family_on_one_context() {
    // The convenience host hook: build + seed + register all five families in order. (They
    // share the context's ONE cipherclerk cell, so each family's `seed_*` re-installs that
    // cell's program for the family it mounts — the last one wins on the shared cell, which is
    // the documented single-family-at-a-time / teaching-walkthrough shape; the registry
    // accumulates all five surfaces.)
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x5A; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    let ctx = StarbridgeAppContext::new(cclerk.clone(), executor.clone());

    let g0 = key_set_commitment(&[[0x10; 32], [0x11; 32]]);
    let g1 = key_set_commitment(&[[0x20; 32], [0x21; 32]]);
    let apps = register_all_deos(
        &ctx,
        &council_2of3(),
        &amendment_terms(),
        &params_v1(),
        &worker_mandate(),
        &identity_charter(),
        g0,
        g1,
    );
    assert_eq!(apps.len(), 5, "five families mounted");
    let names: Vec<&str> = apps.iter().map(|a| a.name()).collect();
    assert_eq!(
        names,
        vec![
            "polis-council",
            "polis-amendment",
            "polis-constitution",
            "polis-mandate",
            "polis-identity",
        ],
        "the five families, in family order",
    );
    // The five families share the context's ONE cipherclerk cell, and the affordance
    // registry is keyed by backing CELL — so a later family's surface REPLACES the prior
    // on that shared cell (the documented single-family-at-a-time shape). The registry
    // therefore holds ONE surface (the last-registered, identity); a host that wants
    // several families live concurrently mounts them on DISTINCT contexts.
    assert_eq!(
        ctx.affordance_registry().len(),
        1,
        "the five surfaces share one cell; the registry holds the last (identity)",
    );
    // The seeded cell is in the LAST family's state (identity genesis = ACTIVE).
    let state = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        state.fields[0],
        dregg_app_framework::field_from_u64(starbridge_polis::identity::STATE_ACTIVE),
        "the shared cell carries the last-registered family (identity, ACTIVE genesis)",
    );
}
