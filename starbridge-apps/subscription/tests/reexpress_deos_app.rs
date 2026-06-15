//! RE-EXPRESSION proof: the `subscription` starbridge-app, on the composed deos
//! framework — **the same app, smaller + more capable, now SHIPPED from `src/`.**
//!
//! `docs/deos/APPS-DEOS-INTEGRATION-CENSUS.md` (Tier-1 #2): subscription's deos
//! re-expression was the MOST complete of the leading cohort, but MISLOCATED — it lived
//! in `app-framework/tests/reexpress_subscription.rs` (the framework tree). This file is
//! that proof RELOCATED into the crate and driving the SHIPPED surface
//! ([`subscription_deos_app`] from `src/`), proving the promotion: per-viewer
//! projection, the cap-gated fires through the mounted axum surface, the `dregg://`
//! web-of-cells publish, the rehydratable frustum-snapshot, the generated
//! `<dregg-affordance-surface>` component, and the manifest — none of which the old
//! bones had.
//!
//! The FEED's surface on the consumer ⊂ publisher ⊂ owner rights ladder
//! (`Signature ⊂ Either ⊂ None`):
//!   - `view_feed` — cap-only (a CONSUMER reads the head-of-queue);
//!   - `grant_publisher` / `grant_consumer` — cap-only (the OWNER admits a member);
//!   - `publish` / `consume` — GATED (cap∧state): the cap-gate AND a live-state
//!     precondition, with the FULL queue invariants re-enforced by the executor on the
//!     fire (the seam the census flagged, now CLOSED — see `tests/deos_seam.rs`).
//!
//! Every affordance carries a REAL [`Effect`]; every fire is a real verified turn
//! through the embedded executor; the gate is the genuine `is_attenuation` (+ the
//! genuine `CellProgram::evaluate` for the gated ones). No parallel model.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CapTpServer, EmbeddedExecutor, FederationId,
    Interaction, InteractionLog, RehydrateError, Rehydration,
};

use starbridge_subscription::{seed_feed, subscription_deos_app};

fn agent() -> (AppCipherclerk, EmbeddedExecutor) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x5B; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    (cclerk, executor)
}

// =============================================================================
// SMALLER: the whole surface is one builder (the SHIPPED `src::subscription_deos_app`).
// =============================================================================

#[test]
fn the_whole_app_is_one_composed_registration() {
    let (cclerk, executor) = agent();
    let app = subscription_deos_app(&cclerk, &executor);

    // ONE app, ONE cell. The cap-only surface carries the read + the two grants; the
    // state-mutating ops (publish / consume) are GATED (cap∧state).
    assert_eq!(app.name(), "subscription");
    assert_eq!(app.cells().len(), 1);
    let feed = &app.cells()[0];
    assert_eq!(
        feed.surface().all_names(),
        vec![
            "grant_consumer".to_string(),
            "grant_publisher".to_string(),
            "view_feed".to_string(),
        ],
        "the cap-only surface: the read + the two membership grants"
    );
    // The gated surface carries the two state-mutating, cap∧state operations.
    let mut gated: Vec<String> = feed
        .gated_surface()
        .affordances
        .iter()
        .map(|g| g.name().to_string())
        .collect();
    gated.sort();
    assert_eq!(gated, vec!["consume".to_string(), "publish".to_string()]);

    // The FEED cell is the agent's own (so fires execute against the seeded ledger), and
    // is published into the web-of-cells at the consumer tier.
    assert_eq!(feed.cell(), cclerk.cell_id());
    assert_eq!(feed.published_authority(), Some(&AuthRequired::Signature));

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
async fn the_three_pubsub_roles_see_different_cap_only_surfaces() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent();
    let app = subscription_deos_app(&cclerk, &executor);
    let router = app.mount();

    async fn visible(router: &axum::Router, tier: &str) -> serde_json::Value {
        let resp = router
            .clone()
            .oneshot(
                Request::get("/feed/projected")
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

    // A CONSUMER (Signature) sees only `view_feed` (the narrow read tier; `consume` is
    // GATED — it lights on the gated surface against live state).
    assert_eq!(
        visible(&router, "signature").await,
        serde_json::json!(["view_feed"])
    );
    // A PUBLISHER (Either) sees the same cap-only set — `publish` is GATED.
    assert_eq!(
        visible(&router, "either").await,
        serde_json::json!(["view_feed"])
    );
    // The OWNER (root) additionally sees the two membership grants.
    assert_eq!(
        visible(&router, "root").await,
        serde_json::json!(["grant_consumer", "grant_publisher", "view_feed"])
    );
}

// =============================================================================
// MORE CAPABLE (2): a cap-only fire is a real verified turn; anti-ghost holds.
// =============================================================================

#[tokio::test]
async fn only_the_owner_can_grant_a_consumer_cannot() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent();
    let app = subscription_deos_app(&cclerk, &executor);
    let _ = seed_feed(&executor, 16, "owner");
    let router = app.mount();

    async fn fire(router: &axum::Router, name: &str, tier: &str) -> StatusCode {
        router
            .clone()
            .oneshot(
                Request::post(format!("/feed/fire/{name}"))
                    .header(dregg_app_framework::HELD_RIGHTS_HEADER, tier)
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap()
            .status()
    }

    // The CAP tooth, in-band (anti-ghost): a CONSUMER (Signature) and a PUBLISHER (Either)
    // firing `grant_publisher` are REFUSED at the cap gate (403) BEFORE anything reaches
    // the executor — only the owner admits members. The cap gate is the genuine
    // `is_attenuation` (`None` ⊄ Either/Signature).
    assert_eq!(
        fire(&router, "grant_publisher", "signature").await,
        StatusCode::FORBIDDEN
    );
    assert_eq!(
        fire(&router, "grant_publisher", "either").await,
        StatusCode::FORBIDDEN
    );

    // The OWNER (root) CLEARS the cap gate (not 403) — it is cap-authorized to admit a
    // publisher.
    assert_ne!(
        fire(&router, "grant_publisher", "root").await,
        StatusCode::FORBIDDEN,
        "the owner is cap-authorized to grant a publisher (clears the cap gate)"
    );
}

// =============================================================================
// MORE CAPABLE (3): web-of-cells — the FEED cell is a distributed sturdyref.
// =============================================================================

#[tokio::test]
async fn the_feed_is_published_into_the_web_of_cells() {
    let (cclerk, executor) = agent();
    // The SHIPPED surface, re-built with a captp server attached (the web-of-cells
    // minter). `subscription_deos_app` publishes the feed cell at the consumer tier.
    let captp = CapTpServer::new(FederationId([0x5B; 32]));
    let base = subscription_deos_app(&cclerk, &executor);
    let app =
        dregg_app_framework::DeosApp::builder("subscription", cclerk.clone(), executor.clone())
            .web_of_cells(captp)
            .cell(base.cells()[0].clone())
            .build();

    // The FEED cell is exported as a real `dregg://` sturdyref — a peer on another
    // federation reacquires the feed across the membrane.
    let uris = app.publish_all(100).await;
    assert_eq!(uris.len(), 1);
    assert!(
        uris[0].starts_with("dregg://"),
        "a real sturdyref: {}",
        uris[0]
    );
}

// =============================================================================
// MORE CAPABLE (4): rehydratable frustum-snapshot of the feed, per-viewer.
// =============================================================================

#[test]
fn a_feed_snapshot_rehydrates_per_viewer_respecting_the_lattice() {
    let (cclerk, executor) = agent();
    let app = subscription_deos_app(&cclerk, &executor);
    let feed = &app.cells()[0];

    // Snapshot the feed; it witnessed a publish turn, sources gone (a cold snapshot handed
    // to a downstream peer) ⇒ liveness REPLAYED-DETERMINISTIC.
    let log = InteractionLog::new().record(Interaction::witnessed_turn(feed.cell(), [9u8; 32]));
    let snap = feed.snapshot(log, false);
    assert_eq!(
        snap.lineage,
        AuthRequired::Signature,
        "snapshot at the published lineage"
    );
    assert_eq!(snap.liveness(), Rehydration::ReplayedDeterministic);
    assert!(snap.liveness().is_faithful());

    // A CONSUMER (Signature) rehydrating reacquires only `view_feed` (the cap-only surface
    // at its tier) — the feed snapshot respects the lattice; it cannot leak the owner's
    // grant affordances.
    let consumer = feed.rehydrate(&snap, AuthRequired::Signature).unwrap();
    assert_eq!(consumer.visible_names(), vec!["view_feed".to_string()]);

    // An INCOMPARABLE authority (a distinct Custom identity) cannot rehydrate at all — the
    // membrane mints NO projection (the no-peek refusal).
    let blocked = feed.rehydrate(&snap, AuthRequired::Custom { vk_hash: [7u8; 32] });
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
    let app = subscription_deos_app(&cclerk, &executor);
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
    assert!(js.contains("fireEndpoint: \"/feed/fire/view_feed\","));
    assert!(js.contains("fireEndpoint: \"/feed/fire/grant_publisher\","));

    // GET /manifest serves the whole composed surface, including the GATED affordances
    // with their state-gate described (the cap∧state posture is visible to any client).
    let manifest = router
        .oneshot(Request::get("/manifest").body(Body::empty()).unwrap())
        .await
        .unwrap();
    assert_eq!(manifest.status(), StatusCode::OK);
    let bytes = axum::body::to_bytes(manifest.into_body(), usize::MAX)
        .await
        .unwrap();
    let m: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    assert_eq!(m["app"], "subscription");
    assert_eq!(m["discoverable"], serde_json::json!(["pubsub", "feed"]));
    assert!(
        m["persistence"]
            .as_str()
            .unwrap()
            .contains("embedded-ledger")
    );
    assert_eq!(m["cells"].as_array().unwrap().len(), 1);
    // The manifest advertises the two gated (cap∧state) affordances.
    let gated = m["cells"][0]["gatedAffordances"]
        .as_array()
        .expect("gated affordances");
    let names: Vec<&str> = gated.iter().filter_map(|g| g["name"].as_str()).collect();
    assert!(names.contains(&"publish"), "publish is advertised as gated");
    assert!(names.contains(&"consume"), "consume is advertised as gated");
}
