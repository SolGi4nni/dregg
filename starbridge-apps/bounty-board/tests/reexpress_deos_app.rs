//! RE-EXPRESSION proof: the `bounty-board` starbridge-app, on the composed deos
//! framework — **the same app, smaller + more capable, now SHIPPED from `src/`.**
//!
//! `docs/deos/APPS-DEOS-INTEGRATION-CENSUS.md`: the bounty-board — THE canonical 4-state
//! gated lifecycle — re-expressed as a composed [`DeosApp`] and PROMOTED into `src/lib.rs`.
//! This file drives the SHIPPED surface ([`bounty_app`] from `src/`), proving the
//! promotion: per-viewer projection, the cap-gated fires through the mounted axum surface,
//! the `dregg://` web-of-cells publish, the rehydratable frustum-snapshot, the generated
//! `<dregg-affordance-surface>` component, and the manifest — none of which the floor's
//! bones had.
//!
//! The BOUNTY's surface on the watcher ⊂ worker ⊂ poster rights ladder
//! (`Signature ⊂ Either ⊂ None`):
//!   - `view_bounty` — cap-only (a WATCHER reads the lifecycle state);
//!   - `claim` / `submit` / `payout` — GATED (cap∧state): the cap-gate AND a live-state
//!     precondition (the cell is in exactly the state the op advances FROM), with the FULL
//!     bounty program re-enforced by the executor on the fire (the seam, CLOSED — see
//!     `tests/deos_seam.rs`).
//!
//! Every affordance carries a REAL [`Effect`]; every fire is a real verified turn through
//! the embedded executor; the gate is the genuine `is_attenuation` (+ the genuine
//! `CellProgram::evaluate` for the gated ones). No parallel model.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CapTpServer, DeosApp, EmbeddedExecutor,
    FederationId, Interaction, InteractionLog, RehydrateError, Rehydration,
};

use starbridge_bounty_board::{bounty_app, seed_bounty};

fn agent() -> (AppCipherclerk, EmbeddedExecutor) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x4b; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    (cclerk, executor)
}

// =============================================================================
// SMALLER: the whole surface is one builder (the SHIPPED `src::bounty_app`).
// =============================================================================

#[test]
fn the_whole_app_is_one_composed_registration() {
    let (cclerk, executor) = agent();
    let app = bounty_app(&cclerk, &executor);

    // ONE app, ONE cell. The cap-only surface carries only the read; the three
    // state-advancing lifecycle ops (claim / submit / payout) are GATED (cap∧state).
    assert_eq!(app.name(), "bounty-board");
    assert_eq!(app.cells().len(), 1);
    let bounty = &app.cells()[0];
    assert_eq!(
        bounty.surface().all_names(),
        vec!["view_bounty".to_string()],
        "the cap-only surface: just the lifecycle read"
    );
    // The gated surface carries the three state-advancing, cap∧state lifecycle ops.
    let mut gated: Vec<String> = bounty
        .gated_surface()
        .affordances
        .iter()
        .map(|g| g.name().to_string())
        .collect();
    gated.sort();
    assert_eq!(
        gated,
        vec![
            "claim".to_string(),
            "payout".to_string(),
            "submit".to_string()
        ]
    );

    // The BOUNTY cell is the agent's own (so fires execute against the seeded ledger), and
    // is published into the web-of-cells at the watcher tier.
    assert_eq!(bounty.cell(), cclerk.cell_id());
    assert_eq!(bounty.published_authority(), Some(&AuthRequired::Signature));

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
async fn the_three_bounty_roles_see_different_cap_only_surfaces() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent();
    let app = bounty_app(&cclerk, &executor);
    let router = app.mount();

    async fn visible(router: &axum::Router, tier: &str) -> serde_json::Value {
        let resp = router
            .clone()
            .oneshot(
                Request::get("/bounty/projected")
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

    // The cap-only surface is just `view_bounty` — every tier at or above `Signature` sees
    // it (claim/submit/payout are GATED, not on the cap-only projection; they light on the
    // gated surface against live state).
    assert_eq!(
        visible(&router, "signature").await,
        serde_json::json!(["view_bounty"])
    );
    assert_eq!(
        visible(&router, "either").await,
        serde_json::json!(["view_bounty"])
    );
    assert_eq!(
        visible(&router, "root").await,
        serde_json::json!(["view_bounty"])
    );
}

// =============================================================================
// MORE CAPABLE (2): a cap-only fire is a real verified turn; the cap tooth bites in-band.
// =============================================================================

#[tokio::test]
async fn the_watcher_read_clears_the_cap_gate_a_real_turn() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent();
    let app = bounty_app(&cclerk, &executor);
    let _ = seed_bounty(&executor, "fix the bug", 500);
    let router = app.mount();

    async fn fire(router: &axum::Router, name: &str, tier: &str) -> StatusCode {
        router
            .clone()
            .oneshot(
                Request::post(format!("/bounty/fire/{name}"))
                    .header(dregg_app_framework::HELD_RIGHTS_HEADER, tier)
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap()
            .status()
    }

    // `view_bounty` requires `Signature` — a watcher/worker/poster (all ⊇ Signature) CLEAR
    // the cap gate (not 403). The cap gate is the genuine `is_attenuation`.
    assert_ne!(
        fire(&router, "view_bounty", "signature").await,
        StatusCode::FORBIDDEN,
        "a watcher is cap-authorized to read the bounty (clears the cap gate)"
    );
    assert_ne!(
        fire(&router, "view_bounty", "root").await,
        StatusCode::FORBIDDEN
    );
}

// =============================================================================
// MORE CAPABLE (3): web-of-cells — the BOUNTY cell is a distributed sturdyref.
// =============================================================================

#[tokio::test]
async fn the_bounty_is_published_into_the_web_of_cells() {
    let (cclerk, executor) = agent();
    // The SHIPPED surface, re-built with a captp server attached (the web-of-cells minter).
    // `bounty_app` publishes the bounty cell at the watcher tier.
    let captp = CapTpServer::new(FederationId([0x4b; 32]));
    let base = bounty_app(&cclerk, &executor);
    let app = DeosApp::builder("bounty-board", cclerk.clone(), executor.clone())
        .web_of_cells(captp)
        .cell(base.cells()[0].clone())
        .build();

    // The BOUNTY cell is exported as a real `dregg://` sturdyref — an indexer on another
    // federation reacquires the bounty's lifecycle across the membrane.
    let uris = app.publish_all(100).await;
    assert_eq!(uris.len(), 1);
    assert!(
        uris[0].starts_with("dregg://"),
        "a real sturdyref: {}",
        uris[0]
    );
}

// =============================================================================
// MORE CAPABLE (4): rehydratable frustum-snapshot of the bounty, per-viewer.
// =============================================================================

#[test]
fn a_bounty_snapshot_rehydrates_per_viewer_respecting_the_lattice() {
    let (cclerk, executor) = agent();
    let app = bounty_app(&cclerk, &executor);
    let bounty = &app.cells()[0];

    // Snapshot the bounty; it witnessed a lifecycle turn, sources gone (a cold snapshot
    // handed to a downstream indexer) => liveness REPLAYED-DETERMINISTIC.
    let log = InteractionLog::new().record(Interaction::witnessed_turn(bounty.cell(), [9u8; 32]));
    let snap = bounty.snapshot(log, false);
    assert_eq!(
        snap.lineage,
        AuthRequired::Signature,
        "snapshot at the published lineage"
    );
    assert_eq!(snap.liveness(), Rehydration::ReplayedDeterministic);
    assert!(snap.liveness().is_faithful());

    // A WATCHER (Signature) rehydrating reacquires only `view_bounty` (the cap-only surface
    // at its tier) — the bounty snapshot respects the lattice.
    let watcher = bounty.rehydrate(&snap, AuthRequired::Signature).unwrap();
    assert_eq!(watcher.visible_names(), vec!["view_bounty".to_string()]);

    // An INCOMPARABLE authority (a distinct Custom identity) cannot rehydrate at all — the
    // membrane mints NO projection (the no-peek refusal).
    let blocked = bounty.rehydrate(&snap, AuthRequired::Custom { vk_hash: [7u8; 32] });
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
    let app = bounty_app(&cclerk, &executor);
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
    assert!(js.contains("fireEndpoint: \"/bounty/fire/view_bounty\","));

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
    assert_eq!(m["app"], "bounty-board");
    assert_eq!(m["discoverable"], serde_json::json!(["bounties"]));
    assert!(
        m["persistence"]
            .as_str()
            .unwrap()
            .contains("embedded-ledger")
    );
    assert_eq!(m["cells"].as_array().unwrap().len(), 1);
    // The manifest advertises the three gated (cap∧state) lifecycle affordances.
    let gated = m["cells"][0]["gatedAffordances"]
        .as_array()
        .expect("gated affordances");
    let names: Vec<&str> = gated.iter().filter_map(|g| g["name"].as_str()).collect();
    assert!(names.contains(&"claim"), "claim is advertised as gated");
    assert!(names.contains(&"submit"), "submit is advertised as gated");
    assert!(names.contains(&"payout"), "payout is advertised as gated");
}
