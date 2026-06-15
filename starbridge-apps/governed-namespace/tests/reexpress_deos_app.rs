//! RE-EXPRESSION proof: the `governed-namespace` governance board, on the composed deos
//! framework — **the same app, smaller + more capable, now SHIPPED from `src/`.**
//!
//! `docs/deos/APPS-DEOS-INTEGRATION-CENSUS.md`: the governance BOARD, re-expressed as a
//! composed [`DeosApp`] ([`governance_app`] from `src/`) and PROMOTED into `src/lib.rs`.
//! This file drives the SHIPPED surface, proving the promotion: per-viewer projection,
//! the cap-gated fires through the mounted axum surface, the `dregg://` web-of-cells
//! publish, the rehydratable frustum-snapshot, the generated `<dregg-affordance-surface>`
//! component, and the manifest — none of which the floor's bones had.
//!
//! The board's surface on the viewer ⊂ committee ⊂ admin rights ladder
//! (`Signature ⊂ Either ⊂ None`):
//!   - `view_table` — cap-only (a VIEWER reads the live route table + version);
//!   - `register_service` — cap-only (a committee member publishes a service mount);
//!   - `commit_table_update` — cap-only (`None`/root), carrying the existing commit
//!     decisive effect; its happy-path fire needs the witnessed-verifier lane (the
//!     fail-closed `NotYetWiredVerifier`), so it is cap-authorization-only today (the
//!     `commit` seam, named honestly — see `tests/deos_seam.rs`);
//!   - `propose_table_update` / `vote_on_proposal` — GATED (cap∧state): the cap-gate AND
//!     a live-state precondition, with the FULL governance program re-enforced by the
//!     executor on the fire (the gateable seam, CLOSED — see `tests/deos_seam.rs`).
//!
//! Every affordance carries a REAL [`Effect`]; every gateable fire is a real verified
//! turn through the embedded executor; the gate is the genuine `is_attenuation` (+ the
//! genuine `CellProgram::evaluate` for the gated ones). No parallel model.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CapTpServer, DeosApp, EmbeddedExecutor,
    FederationId, Interaction, InteractionLog, RehydrateError, Rehydration, StarbridgeAppContext,
};

use dregg_app_framework::field_from_bytes;
use starbridge_governed_namespace::{governance_app, register_deos, seed_governance};

fn agent() -> (AppCipherclerk, EmbeddedExecutor) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x67; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    (cclerk, executor)
}

/// Seed a 2-of-N committee at version 1 with an initial route table (a quiescent board).
fn seed(executor: &EmbeddedExecutor) {
    seed_governance(
        executor,
        field_from_bytes(b"committee-v0"),
        2,
        1,
        field_from_bytes(b"genesis-route-table-root"),
    );
}

// =============================================================================
// SMALLER: the whole surface is one builder (the SHIPPED `src::governance_app`).
// =============================================================================

#[test]
fn the_whole_app_is_one_composed_registration() {
    let (cclerk, executor) = agent();
    let app = governance_app(&cclerk, &executor);

    // ONE app, ONE cell. The cap-only surface carries the read + the service mount + the
    // commit (cap-authorization-only); the gateable committee ops are GATED (cap∧state).
    assert_eq!(app.name(), "governed-namespace");
    assert_eq!(app.cells().len(), 1);
    let board = &app.cells()[0];
    let mut cap_only = board.surface().all_names();
    cap_only.sort();
    assert_eq!(
        cap_only,
        vec![
            "commit_table_update".to_string(),
            "register_service".to_string(),
            "view_table".to_string(),
        ],
        "the cap-only surface: the read + the service mount + the (witnessed-seam) commit"
    );
    // The gated surface carries the two gateable, cap∧state committee operations.
    let mut gated: Vec<String> = board
        .gated_surface()
        .affordances
        .iter()
        .map(|g| g.name().to_string())
        .collect();
    gated.sort();
    assert_eq!(
        gated,
        vec![
            "propose_table_update".to_string(),
            "vote_on_proposal".to_string()
        ]
    );

    // The governance cell is the agent's own (so fires execute against the seeded ledger),
    // and is published into the web-of-cells at the viewer tier.
    assert_eq!(board.cell(), cclerk.cell_id());
    assert_eq!(board.published_authority(), Some(&AuthRequired::Signature));

    // ONE registration folds the whole surface into a shared host context.
    let ctx = StarbridgeAppContext::new(cclerk.clone(), executor.clone());
    let keys = app.register(&ctx);
    assert_eq!(keys.len(), 1);
    assert_eq!(ctx.affordance_registry().len(), 1);
}

// =============================================================================
// MORE CAPABLE (1): per-viewer projection of the cap-only surface (HTTP).
// =============================================================================

#[tokio::test]
async fn the_three_governance_roles_see_different_cap_only_surfaces() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent();
    let app = governance_app(&cclerk, &executor);
    let router = app.mount();

    async fn visible(router: &axum::Router, tier: &str) -> serde_json::Value {
        let resp = router
            .clone()
            .oneshot(
                Request::get("/governance/projected")
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

    // A VIEWER (Signature) sees only `view_table` (the narrow read tier).
    assert_eq!(
        visible(&router, "signature").await,
        serde_json::json!(["view_table"])
    );
    // A COMMITTEE member (Either) additionally sees `register_service` (the cap-only mount);
    // `propose`/`vote` are GATED (not on the cap-only projection) — they light on the gated
    // surface against live state.
    assert_eq!(
        visible(&router, "either").await,
        serde_json::json!(["register_service", "view_table"])
    );
    // The ADMIN (root) additionally sees `commit_table_update` (the cap-authorization-only
    // commit).
    assert_eq!(
        visible(&router, "root").await,
        serde_json::json!(["commit_table_update", "register_service", "view_table"])
    );
}

// =============================================================================
// MORE CAPABLE (2): a cap-only fire is a real verified turn; anti-ghost holds.
// =============================================================================

#[tokio::test]
async fn only_a_committee_member_can_register_a_service_a_real_turn() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent();
    let app = governance_app(&cclerk, &executor);
    seed(&executor);
    let router = app.mount();

    async fn fire(router: &axum::Router, name: &str, tier: &str) -> StatusCode {
        router
            .clone()
            .oneshot(
                Request::post(format!("/governance/fire/{name}"))
                    .header(dregg_app_framework::HELD_RIGHTS_HEADER, tier)
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap()
            .status()
    }

    // The CAP tooth, in-band (anti-ghost): a VIEWER (Signature) firing `register_service`
    // (requires Either) is REFUSED at the cap gate (403) BEFORE anything reaches the
    // executor. The cap gate is the genuine `is_attenuation` (Either ⊄ Signature).
    assert_eq!(
        fire(&router, "register_service", "signature").await,
        StatusCode::FORBIDDEN
    );
    // A COMMITTEE member (Either) CLEARS the cap gate (not 403) — `register_service` is an
    // event-bearing turn the floor admits.
    assert_ne!(
        fire(&router, "register_service", "either").await,
        StatusCode::FORBIDDEN,
        "a committee member is cap-authorized to register a service (clears the cap gate)"
    );
}

// =============================================================================
// MORE CAPABLE (3): web-of-cells — the governance cell is a distributed sturdyref.
// =============================================================================

#[tokio::test]
async fn the_governance_cell_is_published_into_the_web_of_cells() {
    let (cclerk, executor) = agent();
    // The SHIPPED surface, re-built with a captp server attached (the web-of-cells minter).
    // `governance_app` publishes the governance cell at the viewer tier.
    let captp = CapTpServer::new(FederationId([0x67; 32]));
    let base = governance_app(&cclerk, &executor);
    let app = DeosApp::builder("governed-namespace", cclerk.clone(), executor.clone())
        .web_of_cells(captp)
        .cell(base.cells()[0].clone())
        .build();

    // The governance cell is exported as a real `dregg://` sturdyref — an auditor on another
    // federation reacquires the live table across the membrane.
    let uris = app.publish_all(100).await;
    assert_eq!(uris.len(), 1);
    assert!(
        uris[0].starts_with("dregg://"),
        "a real sturdyref: {}",
        uris[0]
    );
}

// =============================================================================
// MORE CAPABLE (4): rehydratable frustum-snapshot of the board, per-viewer.
// =============================================================================

#[test]
fn a_board_snapshot_rehydrates_per_viewer_respecting_the_lattice() {
    let (cclerk, executor) = agent();
    let app = governance_app(&cclerk, &executor);
    let board = &app.cells()[0];

    // Snapshot the board; it witnessed a propose turn, sources gone (a cold snapshot handed
    // to a downstream auditor) ⇒ liveness REPLAYED-DETERMINISTIC.
    let log = InteractionLog::new().record(Interaction::witnessed_turn(board.cell(), [9u8; 32]));
    let snap = board.snapshot(log, false);
    assert_eq!(
        snap.lineage,
        AuthRequired::Signature,
        "snapshot at the published lineage"
    );
    assert_eq!(snap.liveness(), Rehydration::ReplayedDeterministic);
    assert!(snap.liveness().is_faithful());

    // A VIEWER (Signature) rehydrating reacquires only `view_table` (the cap-only surface at
    // its tier) — the board snapshot respects the lattice.
    let viewer = board.rehydrate(&snap, AuthRequired::Signature).unwrap();
    assert_eq!(viewer.visible_names(), vec!["view_table".to_string()]);

    // An INCOMPARABLE authority (a distinct Custom identity) cannot rehydrate at all — the
    // membrane mints NO projection (the no-peek refusal).
    let blocked = board.rehydrate(&snap, AuthRequired::Custom { vk_hash: [7u8; 32] });
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
    let app = governance_app(&cclerk, &executor);
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
    // The anti-drift affordance map names the cap-only fire endpoints.
    assert!(js.contains("fireEndpoint: \"/governance/fire/view_table\","));
    assert!(js.contains("fireEndpoint: \"/governance/fire/commit_table_update\","));

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
    assert_eq!(m["app"], "governed-namespace");
    assert_eq!(
        m["discoverable"],
        serde_json::json!(["governance", "namespace"])
    );
    assert!(
        m["persistence"]
            .as_str()
            .unwrap()
            .contains("embedded-ledger")
    );
    assert_eq!(m["cells"].as_array().unwrap().len(), 1);
    // The manifest advertises the two gated (cap∧state) committee affordances.
    let gated = m["cells"][0]["gatedAffordances"]
        .as_array()
        .expect("gated affordances");
    let names: Vec<&str> = gated.iter().filter_map(|g| g["name"].as_str()).collect();
    assert!(
        names.contains(&"propose_table_update"),
        "propose is advertised as gated"
    );
    assert!(
        names.contains(&"vote_on_proposal"),
        "vote is advertised as gated"
    );
}

// =============================================================================
// register_deos mounts the SEEDED surface into the context (the promotion is live).
// =============================================================================

#[test]
fn register_deos_mounts_the_seeded_surface_into_the_context() {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x67; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    let ctx = StarbridgeAppContext::new(cclerk.clone(), executor.clone());

    // `register_deos` folds the DeosApp into the context's affordance registry AND seeds the
    // governance cell (program installed, constitutional state). After it, the deos surface
    // is the SHIPPED one (the census promotion) and the gated fires are live.
    let app = register_deos(&ctx);
    assert_eq!(app.name(), "governed-namespace");
    assert_eq!(
        ctx.affordance_registry().len(),
        1,
        "the deos surface is registered"
    );

    // The seeded board is quiescent (no in-flight proposal), so a committee member can open a
    // proposal through the mounted surface immediately (the gateable seam is closed + live).
    let receipt = starbridge_governed_namespace::fire_propose(
        &app,
        &AuthRequired::Either,
        &cclerk,
        &executor,
    )
    .expect("the mounted, seeded surface opens a proposal (the promotion is live)");
    assert_ne!(receipt.turn_hash, [0u8; 32]);
}
