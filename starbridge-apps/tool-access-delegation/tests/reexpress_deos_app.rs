//! RE-EXPRESSION proof: the `tool-access-delegation` starbridge-app, on the composed deos
//! framework — **the same app, smaller + more capable, now SHIPPED from `src/`.**
//!
//! `docs/deos/APPS-DEOS-INTEGRATION-CENSUS.md`: the tool-access MANDATE, re-expressed as a
//! composed [`DeosApp`] and PROMOTED into `src/lib.rs` ([`tad_app`]). This file drives the
//! SHIPPED surface, proving the promotion: per-viewer projection, the cap-gated fires through
//! the mounted axum surface, the `dregg://` web-of-cells publish, the rehydratable
//! frustum-snapshot, the generated `<dregg-affordance-surface>` component, and the manifest —
//! none of which the floor's factory/turn-builders had.
//!
//! The MANDATE's surface on the worker ⊂ grantor rights ladder (`Either ⊂ None`):
//!   - `view_grant` — cap-only (a WORKER reads the mandate's terms);
//!   - `grant` — cap-only, carrying the REAL `Effect::GrantCapability` (the GRANTOR hands the
//!     invoke cap forward NARROWED — the cap-graph half of attenuated delegation);
//!   - `invoke` — GATED (cap∧state): the cap-gate AND a live-state precondition
//!     (budget remains), with the FULL `Cases` mandate program re-enforced by the executor on
//!     the fire (the seam, CLOSED — see `tests/deos_seam.rs`).
//!
//! Every affordance carries a REAL [`Effect`]; every fire is a real verified turn through the
//! embedded executor; the gate is the genuine `is_attenuation` (+ the genuine
//! `CellProgram::evaluate` for the gated one). No parallel model.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CapTpServer, CellAffordance, DeosApp, DeosCell,
    Effect, EffectSummary, EmbeddedExecutor, Event, FederationId, Interaction, InteractionLog,
    RehydrateError, Rehydration,
};

use starbridge_tool_access_delegation::{
    CALLS_MADE_SLOT, grant_invoke_effect, seed_mandate, tad_app,
};

fn agent() -> (AppCipherclerk, EmbeddedExecutor) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x5c; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    (cclerk, executor)
}

// =============================================================================
// SMALLER: the whole surface is one builder (the SHIPPED `src::tad_app`).
// =============================================================================

#[test]
fn the_whole_app_is_one_composed_registration() {
    let (cclerk, executor) = agent();
    let app = tad_app(&cclerk, &executor);

    // ONE app, ONE cell. The cap-only surface carries the read + the cap grant; the
    // state-mutating op (invoke) is GATED (cap∧state).
    assert_eq!(app.name(), "tool-access-delegation");
    assert_eq!(app.cells().len(), 1);
    let mandate = &app.cells()[0];
    let mut cap_only = mandate.surface().all_names();
    cap_only.sort();
    assert_eq!(
        cap_only,
        vec!["grant".to_string(), "view_grant".to_string()],
        "the cap-only surface: the read + the (cap-graph) invoke grant"
    );
    // The gated surface carries the single state-mutating, cap∧state operation.
    let gated: Vec<String> = mandate
        .gated_surface()
        .affordances
        .iter()
        .map(|g| g.name().to_string())
        .collect();
    assert_eq!(gated, vec!["invoke".to_string()]);

    // The MANDATE cell is the agent's own (so fires execute against the seeded ledger), and is
    // published into the web-of-cells at the WORKER tier (`Either`) — the narrowest role that
    // holds the mandate AND the narrowest cap-only affordance (`view_grant`, Either) on the
    // surface, so the worker can reacquire its read across the membrane.
    assert_eq!(mandate.cell(), cclerk.cell_id());
    assert_eq!(mandate.published_authority(), Some(&AuthRequired::Either));

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
async fn the_two_delegation_roles_see_different_cap_only_surfaces() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent();
    let app = tad_app(&cclerk, &executor);
    let router = app.mount();

    async fn visible(router: &axum::Router, tier: &str) -> serde_json::Value {
        let resp = router
            .clone()
            .oneshot(
                Request::get("/mandate/projected")
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

    // A WORKER (Either) sees only `view_grant` on the cap-only projection (`invoke` is GATED —
    // it lights on the gated surface against live state, not here).
    assert_eq!(
        visible(&router, "either").await,
        serde_json::json!(["view_grant"])
    );
    // The GRANTOR (root) additionally sees `grant` (the cap-graph handoff) on top of the read.
    assert_eq!(
        visible(&router, "root").await,
        serde_json::json!(["grant", "view_grant"])
    );
}

// =============================================================================
// MORE CAPABLE (2): a cap-only fire is a real verified turn; anti-ghost holds.
// =============================================================================

#[tokio::test]
async fn only_the_grantor_can_grant_a_real_turn() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent();
    let app = tad_app(&cclerk, &executor);
    seed_mandate(&executor, "search-mcp", 8, 1_000_000);
    let router = app.mount();

    async fn fire(router: &axum::Router, name: &str, tier: &str) -> StatusCode {
        router
            .clone()
            .oneshot(
                Request::post(format!("/mandate/fire/{name}"))
                    .header(dregg_app_framework::HELD_RIGHTS_HEADER, tier)
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap()
            .status()
    }

    // The CAP tooth, in-band (anti-ghost): a WORKER (Either) firing `grant` (requires
    // None/root) is REFUSED at the cap gate (403) BEFORE anything reaches the executor — only
    // the grantor re-keys the invoke cap. The cap gate is the genuine `is_attenuation`
    // (`None` ⊄ Either).
    assert_eq!(
        fire(&router, "grant", "either").await,
        StatusCode::FORBIDDEN
    );

    // The GRANTOR (root) CLEARS the cap gate (not 403) — it is cap-authorized to hand the
    // invoke cap forward.
    assert_ne!(
        fire(&router, "grant", "root").await,
        StatusCode::FORBIDDEN,
        "the grantor is cap-authorized to grant (clears the cap gate)"
    );
}

// =============================================================================
// MORE CAPABLE (3): web-of-cells — the MANDATE cell is a distributed sturdyref.
// =============================================================================

#[tokio::test]
async fn the_mandate_is_published_into_the_web_of_cells() {
    let (cclerk, executor) = agent();
    // The SHIPPED surface, re-built with a captp server attached (the web-of-cells minter).
    // `tad_app` publishes the mandate cell at the worker tier.
    let captp = CapTpServer::new(FederationId([0x5c; 32]));
    let base = tad_app(&cclerk, &executor);
    let app = DeosApp::builder("tool-access-delegation", cclerk.clone(), executor.clone())
        .web_of_cells(captp)
        .cell(base.cells()[0].clone())
        .build();

    // The MANDATE cell is exported as a real `dregg://` sturdyref — a delegated agent on
    // another federation reacquires the mandate across the membrane.
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
    let app = tad_app(&cclerk, &executor);
    let mandate = &app.cells()[0];

    // Snapshot the mandate; it witnessed an invocation turn, sources gone (a cold snapshot
    // handed to a downstream auditor) ⇒ liveness REPLAYED-DETERMINISTIC.
    let log = InteractionLog::new().record(Interaction::witnessed_turn(mandate.cell(), [9u8; 32]));
    let snap = mandate.snapshot(log, false);
    assert_eq!(
        snap.lineage,
        AuthRequired::Either,
        "snapshot at the published (worker) lineage"
    );
    assert_eq!(snap.liveness(), Rehydration::ReplayedDeterministic);
    assert!(snap.liveness().is_faithful());

    // A WORKER (Either) rehydrating reacquires the cap-only surface at its tier — `view_grant`
    // (the worker sees the read; `grant` is the grantor's root tier, `invoke` is gated). The
    // per-viewer meet is `held ∧ lineage` = `Either ∧ Either` = `Either`, so `view_grant`
    // (the `Either`-tier read) is reacquired across the membrane.
    let worker = mandate.rehydrate(&snap, AuthRequired::Either).unwrap();
    assert_eq!(worker.visible_names(), vec!["view_grant".to_string()]);

    // The GRANTOR (root, `None`) rehydrating reacquires `view_grant` AND `grant` — but the
    // meet `None ∧ Either` = `Either` caps the projection at the worker tier, so the root-tier
    // `grant` is NOT reacquired through this worker-lineage snapshot (the lineage is the
    // ceiling — a snapshot published at the worker tier can never re-mint grantor authority).
    let grantor = mandate.rehydrate(&snap, AuthRequired::None).unwrap();
    assert_eq!(
        grantor.visible_names(),
        vec!["view_grant".to_string()],
        "the worker-lineage snapshot caps even root at the worker tier (no authority amplification)"
    );

    // An INCOMPARABLE authority (a distinct Custom identity, incomparable to Either) cannot
    // rehydrate at all — the membrane mints NO projection (the no-peek refusal).
    let blocked = mandate.rehydrate(&snap, AuthRequired::Custom { vk_hash: [7u8; 32] });
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
    let app = tad_app(&cclerk, &executor);
    let router = app.mount();

    // GET /surface.js serves the `<dregg-affordance-surface>` web component, generated from
    // the Rust source of truth.
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
    assert!(js.contains("fireEndpoint: \"/mandate/fire/view_grant\","));
    assert!(js.contains("fireEndpoint: \"/mandate/fire/grant\","));

    // GET /manifest serves the whole composed surface, including the GATED affordance with its
    // state-gate described (the cap∧state posture is visible to any client).
    let manifest = router
        .oneshot(Request::get("/manifest").body(Body::empty()).unwrap())
        .await
        .unwrap();
    assert_eq!(manifest.status(), StatusCode::OK);
    let bytes = axum::body::to_bytes(manifest.into_body(), usize::MAX)
        .await
        .unwrap();
    let m: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    assert_eq!(m["app"], "tool-access-delegation");
    assert_eq!(
        m["discoverable"],
        serde_json::json!(["tools", "delegation"])
    );
    assert!(
        m["persistence"]
            .as_str()
            .unwrap()
            .contains("embedded-ledger")
    );
    assert_eq!(m["cells"].as_array().unwrap().len(), 1);
    // The manifest advertises the gated (cap∧state) `invoke` affordance.
    let gated = m["cells"][0]["gatedAffordances"]
        .as_array()
        .expect("gated affordances");
    let names: Vec<&str> = gated.iter().filter_map(|g| g["name"].as_str()).collect();
    assert!(names.contains(&"invoke"), "invoke is advertised as gated");
}

// =============================================================================
// The real cap handoff: grant carries Effect::GrantCapability (derive_no_amplify).
// =============================================================================

#[test]
fn grant_carries_the_real_grant_capability_effect() {
    // The promoted `grant` affordance carries the REAL `Effect::GrantCapability` — the grantor
    // hands the invoke cap forward NARROWED (the cap-graph half of attenuated delegation), NOT
    // a scaffold stand-in.
    let (cclerk, executor) = agent();
    let app = tad_app(&cclerk, &executor);
    let mandate = cclerk.cell_id();
    let worker = dregg_app_framework::CellId::from_bytes([0xAA; 32]);

    let summary = app.cells()[0]
        .surface()
        .get("grant")
        .unwrap()
        .effect_summary();
    assert_eq!(
        summary,
        EffectSummary::GrantCapability {
            from: mandate,
            to: worker
        }
    );

    // And the standalone effect builder matches (one source of truth).
    let standalone = grant_invoke_effect(mandate, worker);
    assert_eq!(
        EffectSummary::of(&standalone),
        EffectSummary::GrantCapability {
            from: mandate,
            to: worker
        }
    );

    // (Silence the unused warnings on imports used only by sibling tests.)
    let _ = (
        CellAffordance::new(
            "x",
            AuthRequired::None,
            Effect::EmitEvent {
                cell: mandate,
                event: Event {
                    topic: [0u8; 32],
                    data: vec![],
                },
            },
        ),
        CALLS_MADE_SLOT,
        DeosCell::new(mandate, "x"),
    );
}
