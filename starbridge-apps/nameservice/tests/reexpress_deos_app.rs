//! RE-EXPRESSION proof: the `nameservice` starbridge-app, on the composed deos
//! framework — **the web-of-cells keystone.**
//!
//! `docs/deos/APPS-DEOS-INTEGRATION-CENSUS.md`: nameservice re-expressed as a composed
//! [`DeosApp`] ([`name_app`] from `src/`). The headline this app carries is the
//! **web-of-cells publish**: each NAME cell is exported as a real `dregg://` sturdyref
//! ([`the_name_cell_is_published_into_the_web_of_cells`] below), so a name's
//! `RESOLVE_TARGET` can point at a LIVE, reacquirable cell ref across a federation
//! membrane instead of an opaque `blake3(uri)` digest — the name directory becomes a web
//! OF cells. The framework also wires per-viewer projection, the cap-gated fires through
//! the mounted axum surface, the rehydratable frustum-snapshot, the generated
//! `<dregg-affordance-surface>` component, and the manifest — none of which the old bones
//! had.
//!
//! The NAME's surface on the resolver ⊂ owner rights ladder (`Signature ⊂ None`):
//!   - `resolve` — cap-only (a RESOLVER reads + reacquires the target);
//!   - `transfer` — cap-only (the OWNER re-keys the owner slot, a cap-graph re-key);
//!   - `renew` / `revoke` / `set_target` — GATED (cap∧state): the cap-gate AND a live-state
//!     precondition (`REVOKED == 0`), with the FULL name program re-enforced by the executor
//!     on the fire (the seam the census flagged, now CLOSED — see `tests/deos_seam.rs`).
//!
//! Every affordance carries a REAL [`Effect`]; every fire is a real verified turn through
//! the embedded executor; the gate is the genuine `is_attenuation` (+ the genuine
//! `CellProgram::evaluate` for the gated ones). No parallel model.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CapTpServer, DeosApp, EmbeddedExecutor,
    FederationId, Interaction, InteractionLog, RehydrateError, Rehydration,
};

use starbridge_nameservice::{
    DEFAULT_RENT_EPOCH_BLOCKS, EXPIRY_SLOT, name_app, name_cell_program, resolve_target, seed_name,
};

fn agent() -> (AppCipherclerk, EmbeddedExecutor) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x5c; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    (cclerk, executor)
}

fn owner_pk(cclerk: &AppCipherclerk) -> [u8; 32] {
    cclerk.public_key().0
}

// =============================================================================
// SMALLER: the whole surface is one builder (the SHIPPED `src::name_app`).
// =============================================================================

#[test]
fn the_whole_app_is_one_composed_registration() {
    let (cclerk, executor) = agent();
    let app = name_app(&cclerk, &executor);

    // ONE app, ONE cell. The cap-only surface carries the read + the owner re-key; the
    // three owner-only state-mutating ops (renew / revoke / set_target) are GATED (cap∧state).
    assert_eq!(app.name(), "nameservice");
    assert_eq!(app.cells().len(), 1);
    let name = &app.cells()[0];
    assert_eq!(
        name.surface().all_names(),
        vec!["resolve".to_string(), "transfer".to_string()],
        "the cap-only surface: the read + the (cap-graph) owner re-key"
    );
    // The gated surface carries the three owner state-mutating, cap∧state operations.
    let mut gated: Vec<String> = name
        .gated_surface()
        .affordances
        .iter()
        .map(|g| g.name().to_string())
        .collect();
    gated.sort();
    assert_eq!(
        gated,
        vec![
            "renew".to_string(),
            "revoke".to_string(),
            "set_target".to_string()
        ]
    );

    // The NAME cell is the agent's own (so fires execute against the seeded ledger), and is
    // published into the web-of-cells at the resolver tier.
    assert_eq!(name.cell(), cclerk.cell_id());
    assert_eq!(name.published_authority(), Some(&AuthRequired::Signature));

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
async fn the_two_name_roles_see_different_cap_only_surfaces() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent();
    let app = name_app(&cclerk, &executor);
    let router = app.mount();

    async fn visible(router: &axum::Router, tier: &str) -> serde_json::Value {
        let resp = router
            .clone()
            .oneshot(
                Request::get("/name/projected")
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

    // A RESOLVER (Signature) sees only `resolve` (the narrow read tier). `renew` / `revoke`
    // / `set_target` are GATED (not on the cap-only projection); they light on the gated
    // surface against live state.
    assert_eq!(
        visible(&router, "signature").await,
        serde_json::json!(["resolve"])
    );
    // The OWNER (root) additionally sees `transfer` (the cap-graph owner re-key).
    assert_eq!(
        visible(&router, "root").await,
        serde_json::json!(["resolve", "transfer"])
    );
}

// =============================================================================
// MORE CAPABLE (2): a cap-only fire is a real verified turn; anti-ghost holds.
// =============================================================================

#[tokio::test]
async fn only_the_owner_can_transfer_a_real_turn() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent();
    let app = name_app(&cclerk, &executor);
    let _ = seed_name(
        &executor,
        "deos.dregg",
        owner_pk(&cclerk),
        DEFAULT_RENT_EPOCH_BLOCKS,
    );
    let router = app.mount();

    async fn fire(router: &axum::Router, name: &str, tier: &str) -> StatusCode {
        router
            .clone()
            .oneshot(
                Request::post(format!("/name/fire/{name}"))
                    .header(dregg_app_framework::HELD_RIGHTS_HEADER, tier)
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap()
            .status()
    }

    // The CAP tooth, in-band (anti-ghost): a RESOLVER (Signature) firing `transfer` is
    // REFUSED at the cap gate (403) BEFORE anything reaches the executor — only the owner
    // re-keys the name. The cap gate is the genuine `is_attenuation` (`None` ⊄ Signature).
    assert_eq!(
        fire(&router, "transfer", "signature").await,
        StatusCode::FORBIDDEN
    );

    // The OWNER (root) CLEARS the cap gate (not 403) — it is cap-authorized to re-key.
    assert_ne!(
        fire(&router, "transfer", "root").await,
        StatusCode::FORBIDDEN,
        "the owner is cap-authorized to transfer (clears the cap gate)"
    );
}

// =============================================================================
// MORE CAPABLE (3): web-of-cells — the NAME cell is a distributed sturdyref. KEYSTONE.
// =============================================================================

#[tokio::test]
async fn the_name_cell_is_published_into_the_web_of_cells() {
    let (cclerk, executor) = agent();
    // The SHIPPED surface, re-built with a captp server attached (the web-of-cells minter).
    // `name_app` publishes the name cell at the resolver tier.
    let captp = CapTpServer::new(FederationId([0x5c; 32]));
    let base = name_app(&cclerk, &executor);
    let app = DeosApp::builder("nameservice", cclerk.clone(), executor.clone())
        .web_of_cells(captp)
        .cell(base.cells()[0].clone())
        .build();

    // THE KEYSTONE: the NAME cell is exported as a real `dregg://` sturdyref — a peer on
    // another federation reacquires the name cell across the membrane. Because the published
    // handle is a reacquirable `dregg://` ref (NOT an opaque `blake3(uri)` digest),
    // RESOLVE_TARGET now points a name at a LIVE, reacquirable cell ref — the name directory
    // is a web OF cells, the thing nameservice is the keystone for.
    let uris = app.publish_all(100).await;
    assert_eq!(uris.len(), 1);
    assert!(
        uris[0].starts_with("dregg://"),
        "a real sturdyref RESOLVE_TARGET can point at (not an opaque blake3(uri)): {}",
        uris[0]
    );
}

// =============================================================================
// MORE CAPABLE (4): rehydratable frustum-snapshot of the name, per-viewer.
// =============================================================================

#[test]
fn a_name_snapshot_rehydrates_per_viewer_respecting_the_lattice() {
    let (cclerk, executor) = agent();
    let app = name_app(&cclerk, &executor);
    let name = &app.cells()[0];

    // Snapshot the name; it witnessed a turn, sources gone (a cold snapshot handed to a
    // downstream resolver) ⇒ liveness REPLAYED-DETERMINISTIC.
    let log = InteractionLog::new().record(Interaction::witnessed_turn(name.cell(), [9u8; 32]));
    let snap = name.snapshot(log, false);
    assert_eq!(
        snap.lineage,
        AuthRequired::Signature,
        "snapshot at the published lineage"
    );
    assert_eq!(snap.liveness(), Rehydration::ReplayedDeterministic);
    assert!(snap.liveness().is_faithful());

    // A RESOLVER (Signature) rehydrating reacquires only `resolve` (the cap-only surface at
    // its tier) — the name snapshot respects the lattice.
    let resolver = name.rehydrate(&snap, AuthRequired::Signature).unwrap();
    assert_eq!(resolver.visible_names(), vec!["resolve".to_string()]);

    // An INCOMPARABLE authority (a distinct Custom identity) cannot rehydrate at all — the
    // membrane mints NO projection (the no-peek refusal).
    let blocked = name.rehydrate(&snap, AuthRequired::Custom { vk_hash: [7u8; 32] });
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
    let app = name_app(&cclerk, &executor);
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
    assert!(js.contains("fireEndpoint: \"/name/fire/resolve\","));
    assert!(js.contains("fireEndpoint: \"/name/fire/transfer\","));

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
    assert_eq!(m["app"], "nameservice");
    assert_eq!(m["discoverable"], serde_json::json!(["names"]));
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
    assert!(names.contains(&"renew"), "renew is advertised as gated");
    assert!(names.contains(&"revoke"), "revoke is advertised as gated");
    assert!(
        names.contains(&"set_target"),
        "set_target is advertised as gated"
    );
}

// =============================================================================
// PRESERVED: the seeded name carries the SAME program the floor crate proves.
// =============================================================================

#[test]
fn the_seeded_name_carries_the_floor_name_program() {
    let (cclerk, executor) = agent();
    // The seeded name cell carries `name_cell_program()` — the floor's WriteOnce(NAME_HASH)
    // + Monotonic(EXPIRY) + WriteOnce(REVOKED). Same program, now on the deos bones.
    let _ = seed_name(&executor, "deos.dregg", owner_pk(&cclerk), 5_000);
    let installed =
        executor.with_ledger_mut(|ledger| ledger.get(&cclerk.cell_id()).map(|c| c.program.clone()));
    assert_eq!(
        installed,
        Some(name_cell_program()),
        "the seeded name cell carries the floor's name program"
    );
    // ...and the seeded state is an active name at the seeded expiry.
    let state = executor
        .cell_state(cclerk.cell_id())
        .expect("seeded cell exists");
    assert_eq!(
        state.fields[EXPIRY_SLOT],
        dregg_app_framework::field_from_u64(5_000)
    );

    // (Silence the unused import on the resolve-target helper — used by sibling suites.)
    let _ = resolve_target("dregg://cell/x");
}
