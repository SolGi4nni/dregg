//! RE-EXPRESSION proof: the `identity` starbridge-app, on the composed deos framework —
//! **the same app, smaller + more capable, now SHIPPED from `src/`.**
//!
//! `docs/deos/APPS-DEOS-INTEGRATION-CENSUS.md`: identity is THE
//! credential-across-trust-boundary web-of-cells story. The ISSUER, re-expressed as a
//! composed [`DeosApp`] ([`identity_app`] from `src/`) and PROMOTED into `src/lib.rs`. This
//! file drives the SHIPPED surface, proving the promotion: per-viewer projection, the
//! cap-gated fires through the mounted axum surface, the `dregg://` web-of-cells publish (a
//! relying party — a verifier on ANOTHER federation — reacquires the issuer cell to verify
//! credentials across the trust boundary), the rehydratable frustum-snapshot, the generated
//! `<dregg-affordance-surface>` component, and the manifest — none of which the floor's
//! turn-builders had.
//!
//! The ISSUER's surface on the holder/verifier ⊂ presenter ⊂ issuer rights ladder
//! (`Signature ⊂ Either ⊂ None`):
//!   - `verify` — cap-only (a VERIFIER reads + re-derives a presentation);
//!   - `present` — cap-only (a PRESENTER produces a disclosure; a holder-side read path);
//!   - `issue` / `revoke` — GATED (cap∧state): the cap-gate AND a live-state precondition,
//!     with the issuer invariants re-enforced by the executor on the fire (the seam closed —
//!     see `tests/deos_seam.rs`).
//!
//! Every affordance carries a REAL [`Effect`]; every fire is a real verified turn through the
//! embedded executor; the gate is the genuine `is_attenuation` (+ the genuine
//! `CellProgram::evaluate` for the gated ones). No parallel model.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CapTpServer, DeosApp, EmbeddedExecutor,
    FederationId, Interaction, InteractionLog, RehydrateError, Rehydration,
};

use starbridge_identity::{identity_app, kyc_schema, seed_issuer};

fn agent() -> (AppCipherclerk, EmbeddedExecutor) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x1d; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    (cclerk, executor)
}

// =============================================================================
// SMALLER: the whole surface is one builder (the SHIPPED `src::identity_app`).
// =============================================================================

#[test]
fn the_whole_app_is_one_composed_registration() {
    let (cclerk, executor) = agent();
    let app = identity_app(&cclerk, &executor);

    // ONE app, ONE cell. The cap-only surface carries the two reads; the state-mutating ops
    // (issue / revoke) are GATED (cap∧state).
    assert_eq!(app.name(), "identity");
    assert_eq!(app.cells().len(), 1);
    let issuer = &app.cells()[0];
    assert_eq!(
        issuer.surface().all_names(),
        vec!["present".to_string(), "verify".to_string()],
        "the cap-only surface: the two read paths (present + verify)"
    );
    // The gated surface carries the two state-mutating, cap∧state operations.
    let mut gated: Vec<String> = issuer
        .gated_surface()
        .affordances
        .iter()
        .map(|g| g.name().to_string())
        .collect();
    gated.sort();
    assert_eq!(gated, vec!["issue".to_string(), "revoke".to_string()]);

    // The ISSUER cell is the agent's own (so fires execute against the seeded ledger), and is
    // published into the web-of-cells at the verifier tier.
    assert_eq!(issuer.cell(), cclerk.cell_id());
    assert_eq!(issuer.published_authority(), Some(&AuthRequired::Signature));

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
async fn the_three_identity_roles_see_different_cap_only_surfaces() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent();
    let app = identity_app(&cclerk, &executor);
    let router = app.mount();

    async fn visible(router: &axum::Router, tier: &str) -> serde_json::Value {
        let resp = router
            .clone()
            .oneshot(
                Request::get("/issuer/projected")
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

    // A VERIFIER / HOLDER (Signature) sees only `verify` (the narrow read tier; `present`
    // needs Either).
    assert_eq!(
        visible(&router, "signature").await,
        serde_json::json!(["verify"])
    );
    // A PRESENTER (Either) additionally sees `present`. `issue` / `revoke` are GATED (not on
    // the cap-only projection); they light on the gated surface against live state.
    assert_eq!(
        visible(&router, "either").await,
        serde_json::json!(["present", "verify"])
    );
    // The ISSUER (root) sees the same cap-only set (its extra power is the two GATED ops).
    assert_eq!(
        visible(&router, "root").await,
        serde_json::json!(["present", "verify"])
    );
}

// =============================================================================
// MORE CAPABLE (2): a cap-only fire is a real verified turn; anti-ghost holds.
// =============================================================================

#[tokio::test]
async fn a_holder_below_the_presenter_tier_cannot_present() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent();
    let app = identity_app(&cclerk, &executor);
    let _ = seed_issuer(&executor, &cclerk, &kyc_schema());
    let router = app.mount();

    async fn fire(router: &axum::Router, name: &str, tier: &str) -> StatusCode {
        router
            .clone()
            .oneshot(
                Request::post(format!("/issuer/fire/{name}"))
                    .header(dregg_app_framework::HELD_RIGHTS_HEADER, tier)
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap()
            .status()
    }

    // The CAP tooth, in-band (anti-ghost): a HOLDER/VERIFIER (Signature) firing `present`
    // (requires Either) is REFUSED at the cap gate (403) BEFORE anything reaches the executor.
    // The cap gate is the genuine `is_attenuation` (`Either` ⊄ Signature).
    assert_eq!(
        fire(&router, "present", "signature").await,
        StatusCode::FORBIDDEN
    );

    // A PRESENTER (Either) CLEARS the cap gate (not 403) — it is cap-authorized to present.
    assert_ne!(
        fire(&router, "present", "either").await,
        StatusCode::FORBIDDEN,
        "a presenter is cap-authorized to present (clears the cap gate)"
    );
}

// =============================================================================
// MORE CAPABLE (3): web-of-cells — the ISSUER cell is a distributed sturdyref.
//   THE KEYSTONE: a relying party on another federation reacquires the issuer to
//   verify credentials across the trust boundary.
// =============================================================================

#[tokio::test]
async fn the_issuer_is_published_into_the_web_of_cells() {
    let (cclerk, executor) = agent();
    // The SHIPPED surface, re-built with a captp server attached (the web-of-cells minter).
    // `identity_app` publishes the issuer cell at the verifier tier.
    let captp = CapTpServer::new(FederationId([0x1d; 32]));
    let base = identity_app(&cclerk, &executor);
    let app = DeosApp::builder("identity", cclerk.clone(), executor.clone())
        .web_of_cells(captp)
        .cell(base.cells()[0].clone())
        .build();

    // The ISSUER cell is exported as a real `dregg://` sturdyref — a RELYING PARTY (a verifier
    // on ANOTHER federation) reacquires the issuer cell to verify credentials ACROSS the trust
    // boundary. This is the credential-across-trust-boundary web-of-cells keystone.
    let uris = app.publish_all(100).await;
    assert_eq!(uris.len(), 1);
    assert!(
        uris[0].starts_with("dregg://"),
        "a real sturdyref: {}",
        uris[0]
    );
}

// =============================================================================
// MORE CAPABLE (4): rehydratable frustum-snapshot of the issuer, per-viewer.
// =============================================================================

#[test]
fn an_issuer_snapshot_rehydrates_per_viewer_respecting_the_lattice() {
    let (cclerk, executor) = agent();
    let app = identity_app(&cclerk, &executor);
    let issuer = &app.cells()[0];

    // Snapshot the issuer; it witnessed an issuance turn, sources gone (a cold snapshot handed
    // to a downstream relying party) ⇒ liveness REPLAYED-DETERMINISTIC.
    let log = InteractionLog::new().record(Interaction::witnessed_turn(issuer.cell(), [9u8; 32]));
    let snap = issuer.snapshot(log, false);
    assert_eq!(
        snap.lineage,
        AuthRequired::Signature,
        "snapshot at the published lineage"
    );
    assert_eq!(snap.liveness(), Rehydration::ReplayedDeterministic);
    assert!(snap.liveness().is_faithful());

    // A VERIFIER (Signature) rehydrating reacquires only `verify` (the cap-only surface at its
    // tier) — the issuer snapshot respects the lattice (the relying party sees the read path).
    let verifier = issuer.rehydrate(&snap, AuthRequired::Signature).unwrap();
    assert_eq!(verifier.visible_names(), vec!["verify".to_string()]);

    // An INCOMPARABLE authority (a distinct Custom identity) cannot rehydrate at all — the
    // membrane mints NO projection (the no-peek refusal across the trust boundary).
    let blocked = issuer.rehydrate(&snap, AuthRequired::Custom { vk_hash: [7u8; 32] });
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
    let app = identity_app(&cclerk, &executor);
    let router = app.mount();

    // GET /surface.js serves the `<dregg-affordance-surface>` web component, generated from the
    // Rust source of truth (the floor hand-wrote its JS).
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
    assert!(js.contains("fireEndpoint: \"/issuer/fire/verify\","));
    assert!(js.contains("fireEndpoint: \"/issuer/fire/present\","));

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
    assert_eq!(m["app"], "identity");
    assert_eq!(
        m["discoverable"],
        serde_json::json!(["identity", "credentials"])
    );
    assert!(
        m["persistence"]
            .as_str()
            .unwrap()
            .contains("embedded-ledger")
    );
    assert_eq!(m["cells"].as_array().unwrap().len(), 1);
    // The manifest advertises the two gated (cap∧state) affordances: issue + revoke.
    let gated = m["cells"][0]["gatedAffordances"]
        .as_array()
        .expect("gated affordances");
    let names: Vec<&str> = gated.iter().filter_map(|g| g["name"].as_str()).collect();
    assert!(names.contains(&"issue"), "issue is advertised as gated");
    assert!(names.contains(&"revoke"), "revoke is advertised as gated");
}
