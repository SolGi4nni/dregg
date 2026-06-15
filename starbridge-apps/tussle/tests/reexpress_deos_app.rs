//! RE-EXPRESSION proof: TUSSLE, the Toribash-style verified joint-combat library, on the
//! composed deos framework — **a TWO-FIGURE app**, smaller + more capable, shipped from
//! `src/`.
//!
//! `docs/deos/APPS-DEOS-INTEGRATION-CENSUS.md`: TUSSLE re-expressed as a composed
//! [`DeosApp`] with **two figure cells** (figure A and figure B), each carrying the
//! commit→reveal→resolve verbs as affordances. This file drives the SHIPPED surface
//! ([`tussle_app`] from `src/`): per-viewer projection of each figure's surface, the
//! web-of-cells publish (each figure IS a `dregg://` sturdyref), the rehydratable
//! frustum-snapshot, the generated `<dregg-affordance-surface>` component, and the
//! manifest — none of which the library's bones had.
//!
//! The figures' surface on the spectator ⊂ fighter ⊂ referee rights ladder
//! (`Signature ⊂ Either ⊂ None`):
//!   - `view_figure` — cap-only (a SPECTATOR watches a figure's pose);
//!   - `commit_move` / `reveal_move` — GATED (cap∧state): a FIGHTER seals then opens its
//!     pose on its OWN figure, the phase precondition + the full figure program re-enforced;
//!   - `resolve_frame` — GATED (cap∧state): the REFEREE resolves the frame.
//!
//! Every affordance carries a REAL [`Effect`]; the gate is the genuine `is_attenuation` (+
//! the genuine `CellProgram::evaluate` for the gated ones). No parallel model.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CapTpServer, DeosApp, EmbeddedExecutor,
    FederationId, Interaction, InteractionLog, RehydrateError, Rehydration,
};

use starbridge_tussle::{figure_b_cell_id, seed_figure, seed_figure_b, tussle_app};

fn agent() -> (AppCipherclerk, EmbeddedExecutor) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x70; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    (cclerk, executor)
}

// =============================================================================
// SMALLER: the whole surface is one builder — TWO figure cells.
// =============================================================================

#[test]
fn the_whole_app_is_one_composed_registration_with_two_figures() {
    let (cclerk, executor) = agent();
    let app = tussle_app(&cclerk, &executor);

    // ONE app, TWO cells (figure A = the agent's own; figure B = the companion).
    assert_eq!(app.name(), "tussle");
    assert_eq!(app.cells().len(), 2, "two figure cells");

    let figure_a = &app.cells()[0];
    let figure_b = &app.cells()[1];
    assert_eq!(
        figure_a.cell(),
        cclerk.cell_id(),
        "figure A is the agent's own cell"
    );
    assert_eq!(
        figure_b.cell(),
        figure_b_cell_id(&cclerk.public_key().0),
        "figure B is the distinct companion cell"
    );
    assert_ne!(
        figure_a.cell(),
        figure_b.cell(),
        "the two figures have distinct CellIds"
    );

    // Each figure's cap-only surface carries the read; the three state-mutating verbs are
    // GATED (cap∧state) — per figure.
    for fig in app.cells() {
        assert_eq!(
            fig.surface().all_names(),
            vec!["view_figure".to_string()],
            "the cap-only surface per figure is the read"
        );
        let mut gated: Vec<String> = fig
            .gated_surface()
            .affordances
            .iter()
            .map(|g| g.name().to_string())
            .collect();
        gated.sort();
        assert_eq!(
            gated,
            vec![
                "commit_move".to_string(),
                "resolve_frame".to_string(),
                "reveal_move".to_string()
            ],
            "the gated surface per figure: commit → reveal → resolve"
        );
        // Each figure is published at the spectator tier (a dregg:// sturdyref).
        assert_eq!(fig.published_authority(), Some(&AuthRequired::Signature));
    }

    // ONE registration folds the whole two-figure surface into a shared host context.
    let ctx = dregg_app_framework::StarbridgeAppContext::new(cclerk.clone(), executor.clone());
    let keys = app.register(&ctx);
    assert_eq!(keys.len(), 2, "two figure cells registered");
    assert_eq!(ctx.affordance_registry().len(), 2);
}

// =============================================================================
// MORE CAPABLE (1): per-viewer projection of each figure's cap-only surface (HTTP).
// =============================================================================

#[tokio::test]
async fn each_figure_projects_its_cap_only_surface_per_viewer() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent();
    let app = tussle_app(&cclerk, &executor);
    let router = app.mount();

    async fn visible(router: &axum::Router, route: &str, tier: &str) -> serde_json::Value {
        let resp = router
            .clone()
            .oneshot(
                Request::get(format!("{route}/projected"))
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

    // Figure A is at `/figure_a` (the first cell's default route is the labelled one), figure
    // B at `/figure_b`. A SPECTATOR (Signature) sees only `view_figure` on each — the gated
    // verbs (commit/reveal/resolve) are NOT on the cap-only projection; they light on the
    // gated surface against live state.
    for route in ["/figure_a", "/figure_b"] {
        assert_eq!(
            visible(&router, route, "signature").await,
            serde_json::json!(["view_figure"]),
            "a spectator sees only view_figure on {route}"
        );
        // A FIGHTER (Either) sees the same cap-only set (commit/reveal are gated).
        assert_eq!(
            visible(&router, route, "either").await,
            serde_json::json!(["view_figure"]),
            "a fighter's cap-only projection on {route} is also just view_figure"
        );
    }
}

// =============================================================================
// MORE CAPABLE (2): web-of-cells — EACH figure cell is a distributed sturdyref.
// =============================================================================

#[tokio::test]
async fn both_figures_are_published_into_the_web_of_cells() {
    let (cclerk, executor) = agent();
    // The SHIPPED surface, re-built with a captp server attached (the web-of-cells minter).
    // `tussle_app` publishes BOTH figure cells at the spectator tier.
    let captp = CapTpServer::new(FederationId([0x70; 32]));
    let base = tussle_app(&cclerk, &executor);
    let app = DeosApp::builder("tussle", cclerk.clone(), executor.clone())
        .web_of_cells(captp)
        .cell(base.cells()[0].clone())
        .cell(base.cells()[1].clone())
        .build();

    // Each figure is exported as a real `dregg://` sturdyref — a spectator on another
    // federation watches a figure across the membrane.
    let uris = app.publish_all(100).await;
    assert_eq!(uris.len(), 2, "both figures published");
    for uri in &uris {
        assert!(uri.starts_with("dregg://"), "a real sturdyref: {uri}");
    }
}

// =============================================================================
// MORE CAPABLE (3): rehydratable frustum-snapshot of a figure, per-viewer.
// =============================================================================

#[test]
fn a_figure_snapshot_rehydrates_per_viewer_respecting_the_lattice() {
    let (cclerk, executor) = agent();
    let app = tussle_app(&cclerk, &executor);
    let figure = &app.cells()[0];

    // Snapshot figure A; it witnessed a frame turn, sources gone (a cold snapshot handed to a
    // downstream spectator) ⇒ liveness REPLAYED-DETERMINISTIC.
    let log = InteractionLog::new().record(Interaction::witnessed_turn(figure.cell(), [7u8; 32]));
    let snap = figure.snapshot(log, false);
    assert_eq!(
        snap.lineage,
        AuthRequired::Signature,
        "snapshot at the published lineage"
    );
    assert_eq!(snap.liveness(), Rehydration::ReplayedDeterministic);
    assert!(snap.liveness().is_faithful());

    // A SPECTATOR (Signature) rehydrating reacquires only `view_figure` (the cap-only surface
    // at its tier) — the figure snapshot respects the lattice.
    let spectator = figure.rehydrate(&snap, AuthRequired::Signature).unwrap();
    assert_eq!(spectator.visible_names(), vec!["view_figure".to_string()]);

    // An INCOMPARABLE authority (a distinct Custom identity) cannot rehydrate at all — the
    // membrane mints NO projection (the no-peek refusal).
    let blocked = figure.rehydrate(&snap, AuthRequired::Custom { vk_hash: [9u8; 32] });
    assert!(matches!(blocked, Err(RehydrateError::Amplification { .. })));
}

// =============================================================================
// MORE CAPABLE (4): the generated web component + the manifest (with the two figures).
// =============================================================================

#[tokio::test]
async fn the_app_ships_a_web_component_surface_and_a_manifest_for_two_figures() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent();
    let app = tussle_app(&cclerk, &executor);
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
    // The anti-drift affordance map names a figure's cap-only fire endpoint.
    assert!(js.contains("fireEndpoint: \"/figure_a/fire/view_figure\","));

    // GET /manifest serves the whole composed surface, including the GATED affordances per
    // figure with their state-gate described.
    let manifest = router
        .oneshot(Request::get("/manifest").body(Body::empty()).unwrap())
        .await
        .unwrap();
    assert_eq!(manifest.status(), StatusCode::OK);
    let bytes = axum::body::to_bytes(manifest.into_body(), usize::MAX)
        .await
        .unwrap();
    let m: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    assert_eq!(m["app"], "tussle");
    assert_eq!(m["discoverable"], serde_json::json!(["tussle", "combat"]));
    assert!(
        m["persistence"]
            .as_str()
            .unwrap()
            .contains("embedded-ledger")
    );
    assert_eq!(
        m["cells"].as_array().unwrap().len(),
        2,
        "two figure cells in the manifest"
    );

    // Each figure advertises the three gated (cap∧state) verbs.
    for c in m["cells"].as_array().unwrap() {
        let gated = c["gatedAffordances"].as_array().expect("gated affordances");
        let names: Vec<&str> = gated.iter().filter_map(|g| g["name"].as_str()).collect();
        for verb in ["commit_move", "reveal_move", "resolve_frame"] {
            assert!(
                names.contains(&verb),
                "{verb} is advertised as gated on a figure"
            );
        }
    }
}

// =============================================================================
// MORE CAPABLE (5): rehydration of the SEEDED figures (real live state).
// =============================================================================

#[test]
fn seeded_two_figure_app_rehydrates_with_live_state() {
    let (cclerk, executor) = agent();
    let app = tussle_app(&cclerk, &executor);
    // Seed BOTH figures (figure A is the agent's own; figure B the companion). After seeding
    // both carry live state — the gated fires can execute against them.
    seed_figure(&executor, cclerk.cell_id());
    let figure_b = seed_figure_b(&executor, &cclerk);

    // Both figures are in the ledger with live state now.
    assert!(
        executor.cell_state(cclerk.cell_id()).is_some(),
        "figure A is live"
    );
    assert!(executor.cell_state(figure_b).is_some(), "figure B is live");
    assert_eq!(figure_b, figure_b_cell_id(&cclerk.public_key().0));

    // The app's two cells match the seeded figures (the surface targets the live cells).
    assert_eq!(app.cells()[0].cell(), cclerk.cell_id());
    assert_eq!(app.cells()[1].cell(), figure_b);
}
