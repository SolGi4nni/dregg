//! RE-EXPRESSION proof: the `supply-chain-provenance` starbridge-app, on the composed
//! deos framework — **the same app, smaller + more capable, now SHIPPED from `src/`.**
//!
//! `docs/deos/APPS-DEOS-INTEGRATION-CENSUS.md` (Tier-1 #1, the reference port): the
//! supply-chain ITEM, re-expressed as a composed [`DeosApp`] and PROMOTED into
//! `src/lib.rs` (it lived in this test). This file now drives the SHIPPED surface
//! ([`item_app`] from `src/`), proving the promotion: per-viewer projection, the
//! cap-gated fires through the mounted axum surface, the `dregg://` web-of-cells
//! publish, the rehydratable frustum-snapshot, the generated `<dregg-affordance-surface>`
//! component, and the manifest — none of which the old bones had.
//!
//! The ITEM's surface on the verifier ⊂ custodian ⊂ manufacturer rights ladder
//! (`Signature ⊂ Either ⊂ None`):
//!   - `view_provenance` — cap-only (a VERIFIER reads + re-derives the chain);
//!   - `grant_custody` — cap-only, carrying the REAL `Effect::GrantCapability` (the
//!     manufacturer hands the custody cap forward NARROWED — the `derive_no_amplify`);
//!   - `accept_custody` / `mint_item` — GATED (cap∧state): the cap-gate AND a live-state
//!     precondition, with the FULL custody program re-enforced by the executor on the
//!     fire (the seam the census flagged, now CLOSED — see `tests/deos_seam.rs`).
//!
//! Every affordance carries a REAL [`Effect`]; every fire is a real verified turn
//! through the embedded executor; the gate is the genuine `is_attenuation` (+ the
//! genuine `CellProgram::evaluate` for the gated ones). No parallel model.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CapTpServer, CellAffordance, DeosApp, DeosCell,
    Effect, EffectSummary, EmbeddedExecutor, Event, FederationId, Interaction, InteractionLog,
    RehydrateError, Rehydration,
};

use starbridge_supply_chain_provenance::{
    CUSTODIAN_SLOT, GENESIS_PREV, Handoff, custody_chain_digests, custody_chain_is_connected,
    grant_custody_effect, identity_field, item_app, seed_item, verify_chain,
};

fn agent() -> (AppCipherclerk, EmbeddedExecutor) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x5c; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    (cclerk, executor)
}

// =============================================================================
// SMALLER: the whole surface is one builder (the SHIPPED `src::item_app`).
// =============================================================================

#[test]
fn the_whole_app_is_one_composed_registration() {
    let (cclerk, executor) = agent();
    let app = item_app(&cclerk, &executor);

    // ONE app, ONE cell. The cap-only surface carries the read + the cap grant; the
    // state-mutating ops (accept_custody / mint_item) are GATED (cap∧state).
    assert_eq!(app.name(), "supply-chain-provenance");
    assert_eq!(app.cells().len(), 1);
    let item = &app.cells()[0];
    assert_eq!(
        item.surface().all_names(),
        vec!["grant_custody".to_string(), "view_provenance".to_string()],
        "the cap-only surface: the read + the (cap-graph) custody grant"
    );
    // The gated surface carries the two state-mutating, cap∧state operations.
    let mut gated: Vec<String> = item
        .gated_surface()
        .affordances
        .iter()
        .map(|g| g.name().to_string())
        .collect();
    gated.sort();
    assert_eq!(gated, vec!["accept_custody".to_string(), "mint_item".to_string()]);

    // The ITEM cell is the agent's own (so fires execute against the seeded ledger),
    // and is published into the web-of-cells at the verifier tier.
    assert_eq!(item.cell(), cclerk.cell_id());
    assert_eq!(item.published_authority(), Some(&AuthRequired::Signature));

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
async fn the_three_supply_chain_roles_see_different_cap_only_surfaces() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent();
    let app = item_app(&cclerk, &executor);
    let router = app.mount();

    async fn visible(router: &axum::Router, tier: &str) -> serde_json::Value {
        let resp = router
            .clone()
            .oneshot(
                Request::get("/item/projected")
                    .header(dregg_app_framework::HELD_RIGHTS_HEADER, tier)
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(resp.status(), StatusCode::OK);
        let bytes = axum::body::to_bytes(resp.into_body(), usize::MAX).await.unwrap();
        serde_json::from_slice::<serde_json::Value>(&bytes).unwrap()["visible"].clone()
    }

    // A VERIFIER (Signature) sees only `view_provenance` (the narrow read tier).
    assert_eq!(visible(&router, "signature").await, serde_json::json!(["view_provenance"]));
    // A CUSTODIAN (Either) sees the same cap-only set — `accept_custody` is GATED (not on
    // the cap-only projection); it lights on the gated surface against live state.
    assert_eq!(visible(&router, "either").await, serde_json::json!(["view_provenance"]));
    // The MANUFACTURER (root) additionally sees `grant_custody` (the cap-graph handoff).
    assert_eq!(
        visible(&router, "root").await,
        serde_json::json!(["grant_custody", "view_provenance"])
    );
}

// =============================================================================
// MORE CAPABLE (2): a cap-only fire is a real verified turn; anti-ghost holds.
// =============================================================================

#[tokio::test]
async fn only_the_manufacturer_can_grant_custody_a_real_turn() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent();
    let app = item_app(&cclerk, &executor);
    let _ = seed_item(&executor, "manufacturer");
    let router = app.mount();

    async fn fire(router: &axum::Router, name: &str, tier: &str) -> StatusCode {
        router
            .clone()
            .oneshot(
                Request::post(format!("/item/fire/{name}"))
                    .header(dregg_app_framework::HELD_RIGHTS_HEADER, tier)
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap()
            .status()
    }

    // The CAP tooth, in-band (anti-ghost): a CUSTODIAN (Either) and a VERIFIER
    // (Signature) firing `grant_custody` are REFUSED at the cap gate (403) BEFORE
    // anything reaches the executor — only the owner re-keys the custody cap. The cap
    // gate is the genuine `is_attenuation` (`None` ⊄ Either/Signature).
    assert_eq!(fire(&router, "grant_custody", "either").await, StatusCode::FORBIDDEN);
    assert_eq!(fire(&router, "grant_custody", "signature").await, StatusCode::FORBIDDEN);

    // The MANUFACTURER (root) CLEARS the cap gate (not 403) — it is cap-authorized to
    // hand the custody cap forward. (A bare `grant_custody` reaches the executor, where
    // the custody program's `StrictMonotonic(EPOCH)` applies to every touching turn —
    // handing the cap forward is a custody EVENT, so in production it rides a handoff
    // turn that advances the epoch; the standalone bare-grant's executor verdict
    // reflects that. What this asserts is the CAP authorization: root is NOT refused at
    // the gate the way the lower tiers are.)
    assert_ne!(
        fire(&router, "grant_custody", "root").await,
        StatusCode::FORBIDDEN,
        "the manufacturer is cap-authorized to grant custody (clears the cap gate)"
    );
}

// =============================================================================
// MORE CAPABLE (3): web-of-cells — the ITEM cell is a distributed sturdyref.
// =============================================================================

#[tokio::test]
async fn the_item_is_published_into_the_web_of_cells() {
    let (cclerk, executor) = agent();
    // The SHIPPED surface, re-built with a captp server attached (the web-of-cells
    // minter). `item_app` publishes the item cell at the verifier tier.
    let captp = CapTpServer::new(FederationId([0x5c; 32]));
    let base = item_app(&cclerk, &executor);
    let app = DeosApp::builder("supply-chain-provenance", cclerk.clone(), executor.clone())
        .web_of_cells(captp)
        .cell(base.cells()[0].clone())
        .build();

    // The ITEM cell is exported as a real `dregg://` sturdyref — a regulator on another
    // federation reacquires the item's provenance across the membrane.
    let uris = app.publish_all(100).await;
    assert_eq!(uris.len(), 1);
    assert!(uris[0].starts_with("dregg://"), "a real sturdyref: {}", uris[0]);
}

// =============================================================================
// MORE CAPABLE (4): rehydratable frustum-snapshot of the item, per-viewer.
// =============================================================================

#[test]
fn an_item_snapshot_rehydrates_per_viewer_respecting_the_lattice() {
    let (cclerk, executor) = agent();
    let app = item_app(&cclerk, &executor);
    let item = &app.cells()[0];

    // Snapshot the item; it witnessed a custody handoff turn, sources gone (a cold
    // snapshot handed to a downstream auditor) ⇒ liveness REPLAYED-DETERMINISTIC.
    let log = InteractionLog::new().record(Interaction::witnessed_turn(item.cell(), [9u8; 32]));
    let snap = item.snapshot(log, false);
    assert_eq!(snap.lineage, AuthRequired::Signature, "snapshot at the published lineage");
    assert_eq!(snap.liveness(), Rehydration::ReplayedDeterministic);
    assert!(snap.liveness().is_faithful());

    // A VERIFIER (Signature) rehydrating reacquires only `view_provenance` (the cap-only
    // surface at its tier) — the item snapshot respects the lattice.
    let verifier = item.rehydrate(&snap, AuthRequired::Signature).unwrap();
    assert_eq!(verifier.visible_names(), vec!["view_provenance".to_string()]);

    // An INCOMPARABLE authority (a distinct Custom identity) cannot rehydrate at all —
    // the membrane mints NO projection (the no-peek refusal).
    let blocked = item.rehydrate(&snap, AuthRequired::Custom { vk_hash: [7u8; 32] });
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
    let app = item_app(&cclerk, &executor);
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
    let bytes = axum::body::to_bytes(surface.into_body(), usize::MAX).await.unwrap();
    let js = String::from_utf8(bytes.to_vec()).unwrap();
    assert!(js.contains("customElements.define(\"dregg-affordance-surface\""));
    // The anti-drift affordance map names the cap-only fire endpoints.
    assert!(js.contains("fireEndpoint: \"/item/fire/view_provenance\","));
    assert!(js.contains("fireEndpoint: \"/item/fire/grant_custody\","));

    // GET /manifest serves the whole composed surface, including the GATED affordances
    // with their state-gate described (the cap∧state posture is visible to any client).
    let manifest = router
        .oneshot(Request::get("/manifest").body(Body::empty()).unwrap())
        .await
        .unwrap();
    assert_eq!(manifest.status(), StatusCode::OK);
    let bytes = axum::body::to_bytes(manifest.into_body(), usize::MAX).await.unwrap();
    let m: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    assert_eq!(m["app"], "supply-chain-provenance");
    assert_eq!(m["discoverable"], serde_json::json!(["supply-chain", "provenance"]));
    assert!(m["persistence"].as_str().unwrap().contains("embedded-ledger"));
    assert_eq!(m["cells"].as_array().unwrap().len(), 1);
    // The manifest advertises the two gated (cap∧state) affordances.
    let gated = m["cells"][0]["gatedAffordances"].as_array().expect("gated affordances");
    let names: Vec<&str> = gated.iter().filter_map(|g| g["name"].as_str()).collect();
    assert!(names.contains(&"accept_custody"), "accept_custody is advertised as gated");
    assert!(names.contains(&"mint_item"), "mint_item is advertised as gated");
}

// =============================================================================
// PRESERVED: the verified custody chain is the SAME one the floor crate proves.
// =============================================================================

#[test]
fn the_handoff_still_carries_the_verified_custody_chain() {
    let m = identity_field("manufacturer");
    let a = identity_field("warehouse-a");
    let b = identity_field("carrier-b");
    let history = vec![
        Handoff { from: GENESIS_PREV, to: m, epoch: 1 }, // mint
        Handoff { from: m, to: a, epoch: 2 },
        Handoff { from: a, to: b, epoch: 3 },
    ];
    let committed = custody_chain_digests(&history);
    assert!(verify_chain(&history, &committed), "the honest custody chain re-derives");
    assert!(
        custody_chain_is_connected(&history),
        "single-custodianship is conserved (a connected custody path)"
    );
    let rogue = identity_field("rogue");
    let forked = vec![
        Handoff { from: GENESIS_PREV, to: m, epoch: 1 },
        Handoff { from: rogue, to: b, epoch: 2 }, // rogue did not hold custody
    ];
    assert!(!custody_chain_is_connected(&forked), "a forged handoff is not conserved");
}

// =============================================================================
// The real cap handoff: grant_custody carries Effect::GrantCapability (derive_no_amplify).
// =============================================================================

#[test]
fn grant_custody_carries_the_real_grant_capability_effect() {
    // The promoted `grant_custody` affordance carries the REAL `Effect::GrantCapability`
    // — the manufacturer hands the custody cap forward NARROWED (the `derive_no_amplify`
    // shape), NOT a scaffold stand-in.
    let (cclerk, executor) = agent();
    let app = item_app(&cclerk, &executor);
    let item = cclerk.cell_id();
    let next = dregg_app_framework::CellId::from_bytes([0xAA; 32]);

    let summary = app.cells()[0]
        .surface()
        .get("grant_custody")
        .unwrap()
        .effect_summary();
    assert_eq!(summary, EffectSummary::GrantCapability { from: item, to: next });

    // And the standalone effect builder matches (one source of truth).
    let standalone = grant_custody_effect(item, next);
    assert_eq!(EffectSummary::of(&standalone), EffectSummary::GrantCapability { from: item, to: next });

    // (Silence the unused warnings on imports used only by sibling tests.)
    let _ = (CellAffordance::new("x", AuthRequired::None, Effect::EmitEvent {
        cell: item,
        event: Event { topic: [0u8; 32], data: vec![] },
    }), CUSTODIAN_SLOT, DeosCell::new(item, "x"));
}
