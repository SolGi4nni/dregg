//! RE-EXPRESSION proof: the `swarm-orchestration` starbridge-app, on the composed deos
//! framework — **the same app, smaller + more capable, now SHIPPED from `src/`.**
//!
//! `docs/deos/APPS-DEOS-INTEGRATION-CENSUS.md` (Tier-1 #3, the multi-agent exemplar): the
//! swarm dispatch BOARD, re-expressed as a composed [`DeosApp`] and PROMOTED into
//! `src/lib.rs` (it lived in this test on the scaffold `emit`/`edit` placeholders). This
//! file now drives the SHIPPED surface ([`board_app`] from `src/`), proving the promotion:
//! per-viewer projection, the cap-gated fires through the mounted axum surface, the
//! `dregg://` web-of-cells publish, the rehydratable frustum-snapshot, the generated
//! `<dregg-affordance-surface>` component, and the manifest — none of which the old bones
//! had. DEOS-APPS.md §5 names this app directly: "the affordance set IS an agent's
//! attenuated action space" — the per-viewer projection makes it real.
//!
//! The BOARD's surface on the observer ⊂ worker ⊂ lead rights ladder
//! (`Signature ⊂ Either ⊂ None`):
//!   - `view_board` — cap-only (an OBSERVER audits lead/budget/meters/epoch);
//!   - `ack_dispatch` — cap-only (a WORKER drains a wake in its own receipted turn);
//!   - `grant_worker` — cap-only, carrying the REAL `Effect::GrantCapability` (the lead
//!     hands a worker an ATTENUATED slice — the `derive_no_amplify`);
//!   - `dispatch` / `open_board` — GATED (cap∧state): the cap-gate AND a live-state
//!     precondition, with the FULL swarm program re-enforced by the executor on the fire (so
//!     the `AffineLe` budget gate bites IN the fire path — the seam the census flagged, now
//!     CLOSED — see `tests/deos_seam.rs`).
//!
//! Every affordance carries a REAL [`Effect`]; every fire is a real verified turn through
//! the embedded executor; the gate is the genuine `is_attenuation` (+ the genuine
//! `CellProgram::evaluate` for the gated ones). No parallel model. Run `--release` (the
//! embedded executor is slow in debug).

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CapTpServer, CellId, DeosApp, EffectSummary,
    EmbeddedExecutor, FederationId, Interaction, InteractionLog, RehydrateError, Rehydration,
};

use starbridge_swarm_orchestration::{
    SPENT_A_SLOT, Worker, board_app, dispatch_within_budget, grant_worker_effect, seed_board,
};

fn agent() -> (AppCipherclerk, EmbeddedExecutor) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x5a; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    (cclerk, executor)
}

// =============================================================================
// SMALLER: the whole surface is one builder (the SHIPPED `src::board_app`).
// =============================================================================

#[test]
fn the_whole_app_is_one_composed_registration() {
    let (cclerk, executor) = agent();
    let app = board_app(&cclerk, &executor);

    // ONE app, ONE cell. The cap-only surface carries the audit read, the worker ack, and
    // the cap grant; the state-mutating ops (dispatch / open_board) are GATED (cap∧state).
    assert_eq!(app.name(), "swarm-orchestration");
    assert_eq!(app.cells().len(), 1);
    let board = &app.cells()[0];
    assert_eq!(
        board.surface().all_names(),
        vec![
            "ack_dispatch".to_string(),
            "grant_worker".to_string(),
            "view_board".to_string(),
        ],
        "the cap-only surface: the audit read, the worker ack, the (cap-graph) worker grant"
    );
    // The gated surface carries the two state-mutating, cap∧state operations.
    let mut gated: Vec<String> = board
        .gated_surface()
        .affordances
        .iter()
        .map(|g| g.name().to_string())
        .collect();
    gated.sort();
    assert_eq!(
        gated,
        vec!["dispatch".to_string(), "open_board".to_string()]
    );

    // The BOARD cell is the agent's own (so fires execute against the seeded ledger), and is
    // published into the web-of-cells at the observer tier.
    assert_eq!(board.cell(), cclerk.cell_id());
    assert_eq!(board.published_authority(), Some(&AuthRequired::Signature));

    // ONE registration folds the whole surface into a shared host context.
    let ctx = dregg_app_framework::StarbridgeAppContext::new(cclerk.clone(), executor.clone());
    let keys = app.register(&ctx);
    assert_eq!(keys.len(), 1);
    assert_eq!(ctx.affordance_registry().len(), 1);
}

// =============================================================================
// MORE CAPABLE (1): per-viewer projection of the cap-only surface (the attenuated
// action space, VISIBLE).
// =============================================================================

#[tokio::test]
async fn the_three_swarm_roles_see_different_cap_only_surfaces() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent();
    let app = board_app(&cclerk, &executor);
    let router = app.mount();

    async fn visible(router: &axum::Router, tier: &str) -> serde_json::Value {
        let resp = router
            .clone()
            .oneshot(
                Request::get("/board/projected")
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

    // An OBSERVER (Signature) sees only `view_board` — it can AUDIT but cannot ack, dispatch,
    // or open (`dispatch`/`open_board` are GATED, not on the cap-only projection).
    assert_eq!(
        visible(&router, "signature").await,
        serde_json::json!(["view_board"])
    );
    // A WORKER (Either) additionally sees `ack_dispatch` — its attenuated action space: it
    // can drain a wake, but it CANNOT dispatch (it is not the lead). This IS DEOS-APPS.md §5's
    // "the affordance set is an agent's attenuated action space."
    assert_eq!(
        visible(&router, "either").await,
        serde_json::json!(["ack_dispatch", "view_board"])
    );
    // The LEAD (root) additionally sees `grant_worker` (the cap-graph worker delegation).
    assert_eq!(
        visible(&router, "root").await,
        serde_json::json!(["ack_dispatch", "grant_worker", "view_board"])
    );
}

// =============================================================================
// MORE CAPABLE (2): cap-only fires are real verified turns; anti-ghost holds.
// =============================================================================

#[tokio::test]
async fn a_worker_acks_an_observer_cannot_and_only_the_lead_grants() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent();
    let app = board_app(&cclerk, &executor);
    let _ = seed_board(&executor, "lead", 1000);
    let router = app.mount();

    async fn fire(router: &axum::Router, name: &str, tier: &str) -> StatusCode {
        router
            .clone()
            .oneshot(
                Request::post(format!("/board/fire/{name}"))
                    .header(dregg_app_framework::HELD_RIGHTS_HEADER, tier)
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap()
            .status()
    }

    // A WORKER (Either) acks a dispatch (the async drain) — a real turn (not 403).
    assert_ne!(
        fire(&router, "ack_dispatch", "either").await,
        StatusCode::FORBIDDEN
    );
    // An OBSERVER (Signature) cannot ack — it only audits; the ack is a worker's own turn.
    assert_eq!(
        fire(&router, "ack_dispatch", "signature").await,
        StatusCode::FORBIDDEN
    );

    // The CAP tooth, in-band (anti-ghost): a WORKER and an OBSERVER firing `grant_worker` are
    // REFUSED at the cap gate (403) BEFORE anything reaches the executor — only the lead hands
    // a worker an attenuated slice (the no-amplification guarantee). The cap gate is the
    // genuine `is_attenuation` (`None` ⊄ Either/Signature).
    assert_eq!(
        fire(&router, "grant_worker", "either").await,
        StatusCode::FORBIDDEN
    );
    assert_eq!(
        fire(&router, "grant_worker", "signature").await,
        StatusCode::FORBIDDEN
    );
    // The LEAD (root) CLEARS the cap gate (not 403) — it is cap-authorized to grant.
    assert_ne!(
        fire(&router, "grant_worker", "root").await,
        StatusCode::FORBIDDEN,
        "the lead is cap-authorized to grant a worker slice (clears the cap gate)"
    );
}

// =============================================================================
// MORE CAPABLE (3): web-of-cells — the BOARD cell is a distributed sturdyref.
// =============================================================================

#[tokio::test]
async fn the_board_is_published_into_the_web_of_cells() {
    let (cclerk, executor) = agent();
    // The SHIPPED surface, re-built with a captp server attached (the web-of-cells minter).
    // `board_app` publishes the board cell at the observer tier.
    let captp = CapTpServer::new(FederationId([0x5a; 32]));
    let base = board_app(&cclerk, &executor);
    let app = DeosApp::builder("swarm-orchestration", cclerk.clone(), executor.clone())
        .web_of_cells(captp)
        .cell(base.cells()[0].clone())
        .build();

    // The BOARD cell is exported as a real `dregg://` sturdyref — a federated peer reacquires
    // the dispatch board across the membrane.
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
    let app = board_app(&cclerk, &executor);
    let board = &app.cells()[0];

    // Snapshot the board; it witnessed a dispatch turn, sources gone (a cold snapshot handed
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

    // An OBSERVER (Signature) rehydrating reacquires only `view_board` (the cap-only surface
    // at its tier) — the board snapshot respects the lattice; it cannot leak the lead's
    // grant or the worker's ack to a downstream auditor.
    let observer = board.rehydrate(&snap, AuthRequired::Signature).unwrap();
    assert_eq!(observer.visible_names(), vec!["view_board".to_string()]);

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
    let app = board_app(&cclerk, &executor);
    let router = app.mount();

    // GET /surface.js serves the `<dregg-affordance-surface>` web component, generated from
    // the Rust source of truth (the floor hand-wrote its JS via `web_constants()`).
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
    assert!(js.contains("fireEndpoint: \"/board/fire/view_board\","));
    assert!(js.contains("fireEndpoint: \"/board/fire/grant_worker\","));

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
    assert_eq!(m["app"], "swarm-orchestration");
    assert_eq!(
        m["discoverable"],
        serde_json::json!(["orchestration", "swarm"])
    );
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
    assert!(
        names.contains(&"dispatch"),
        "dispatch is advertised as gated"
    );
    assert!(
        names.contains(&"open_board"),
        "open_board is advertised as gated"
    );
}

// =============================================================================
// PRESERVED: the conserved two-meter budget gate is the SAME one the floor proves.
// =============================================================================

#[test]
fn the_budget_gate_still_refuses_an_overrun() {
    // The deos re-expression does NOT replace the floor crate's budget discipline — it
    // composes a richer surface ON it. The two-meter affine bound `spent_a + spent_b <=
    // budget` is the floor crate's REAL gate (the executor's `AffineLe` clause, re-enforced in
    // the fire path — see `tests/deos_seam.rs::the_executor_re_enforces_an_over_budget_dispatch_is_refused`).
    //
    // budget 1000; A at 600, a 300-to-B fits (900 <= 1000); a 500-to-B breaches.
    assert!(
        dispatch_within_budget(0, 300, 600, 1000),
        "900 <= 1000 admitted"
    );
    assert!(
        !dispatch_within_budget(0, 500, 600, 1000),
        "1100 > 1000 REFUSED — the budget tooth"
    );
    // The two meters are distinct columns the gate sums (no single-field counter sees it).
    assert_ne!(Worker::A.spend_slot(), Worker::B.spend_slot());
    assert_eq!(Worker::A.spend_slot(), SPENT_A_SLOT);
}

// =============================================================================
// The real cap handoff: grant_worker carries Effect::GrantCapability (derive_no_amplify).
// =============================================================================

#[test]
fn grant_worker_carries_the_real_grant_capability_effect() {
    // The promoted `grant_worker` affordance carries the REAL `Effect::GrantCapability` — the
    // lead hands a worker an ATTENUATED slice (the `derive_no_amplify` shape), NOT a scaffold
    // stand-in.
    let (cclerk, executor) = agent();
    let app = board_app(&cclerk, &executor);
    let board = cclerk.cell_id();
    let worker = CellId::from_bytes([0x9a; 32]);

    let summary = app.cells()[0]
        .surface()
        .get("grant_worker")
        .unwrap()
        .effect_summary();
    assert_eq!(
        summary,
        EffectSummary::GrantCapability {
            from: board,
            to: worker
        }
    );

    // And the standalone effect builder matches (one source of truth).
    let standalone = grant_worker_effect(board, worker);
    assert_eq!(
        EffectSummary::of(&standalone),
        EffectSummary::GrantCapability {
            from: board,
            to: worker
        }
    );
}
