//! RE-EXPRESSION proof: the `privacy-voting` starbridge-app, on the composed deos
//! framework — **the same app, now a composed TWO-CELL [`DeosApp`] shipped from `src/`.**
//!
//! `docs/deos/APPS-DEOS-INTEGRATION-CENSUS.md`: privacy-voting, re-expressed as a composed
//! [`DeosApp`] and PROMOTED into `src/lib.rs` (it lived only in the floor's factory-birth
//! tests). This file drives the SHIPPED surface ([`voting_app`] from `src/`), proving the
//! promotion: TWO cells (the POLL tally board + the BALLOT capability), per-viewer
//! projection, the cap-gated fires through the mounted axum surface, the `dregg://`
//! web-of-cells publish, the rehydratable frustum-snapshot, the generated
//! `<dregg-affordance-surface>` component, and the manifest — none of which the floor's
//! factory-born bones had.
//!
//! The surface on the viewer ⊂ voter ⊂ administrator rights ladder (`Signature ⊂ Either ⊂
//! None`):
//!   - `view_poll` — cap-only (a VIEWER reads the public tally board), on the POLL cell;
//!   - `cast_vote` — GATED (cap∧state), on the BALLOT cell (a VOTER casts one vote);
//!   - `record_tally` / `close_poll` — GATED (cap∧state), on the POLL cell (the
//!     ADMINISTRATOR bumps a tally / closes the poll), with the FULL slot caveats re-enforced
//!     by the executor on the fire (the seam, CLOSED — see `tests/deos_seam.rs`).
//!
//! Every affordance carries a REAL [`Effect`]; the gate is the genuine `is_attenuation` (+
//! the genuine `CellProgram::evaluate` for the gated ones). No parallel model.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CapTpServer, DeosApp, EmbeddedExecutor,
    FederationId, Interaction, InteractionLog, RehydrateError, Rehydration,
};

use starbridge_privacy_voting::{ballot_cell_id, seed_ballot, seed_poll, voting_app};

fn agent() -> (AppCipherclerk, EmbeddedExecutor) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x70; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    (cclerk, executor)
}

// =============================================================================
// SMALLER: the whole surface is one builder (the SHIPPED `src::voting_app`), TWO cells.
// =============================================================================

#[test]
fn the_whole_app_is_one_composed_two_cell_registration() {
    let (cclerk, executor) = agent();
    let app = voting_app(&cclerk, &executor);

    // ONE app, TWO cells: the POLL tally board (the agent's own cell) + the BALLOT
    // capability (a distinct companion).
    assert_eq!(app.name(), "privacy-voting");
    assert_eq!(app.cells().len(), 2, "two cells: poll + ballot");

    let poll = app
        .cell(&cclerk.cell_id())
        .expect("the poll cell is the agent's own");
    let ballot_id = ballot_cell_id(&cclerk.public_key().0);
    let ballot = app
        .cell(&ballot_id)
        .expect("the ballot is a distinct companion cell");
    assert_ne!(
        poll.cell(),
        ballot.cell(),
        "the two cells have distinct CellIds"
    );

    // The POLL cell's cap-only surface carries the read; its gated surface carries the two
    // administrator operations.
    assert_eq!(
        poll.surface().all_names(),
        vec!["view_poll".to_string()],
        "the poll cap-only surface: the public tally-board read"
    );
    let mut poll_gated: Vec<String> = poll
        .gated_surface()
        .affordances
        .iter()
        .map(|g| g.name().to_string())
        .collect();
    poll_gated.sort();
    assert_eq!(
        poll_gated,
        vec!["close_poll".to_string(), "record_tally".to_string()]
    );

    // The BALLOT cell's gated surface carries the single cast_vote operation (one vote per
    // ballot).
    let ballot_gated: Vec<String> = ballot
        .gated_surface()
        .affordances
        .iter()
        .map(|g| g.name().to_string())
        .collect();
    assert_eq!(ballot_gated, vec!["cast_vote".to_string()]);
    assert!(
        ballot.surface().all_names().is_empty(),
        "the ballot has no cap-only affordances"
    );

    // The POLL cell is published into the web-of-cells at the viewer tier.
    assert_eq!(poll.published_authority(), Some(&AuthRequired::Signature));

    // ONE registration folds BOTH cells' surfaces into a shared host context.
    let ctx = dregg_app_framework::StarbridgeAppContext::new(cclerk.clone(), executor.clone());
    let keys = app.register(&ctx);
    assert_eq!(keys.len(), 2, "two cell surfaces registered");
    assert_eq!(ctx.affordance_registry().len(), 2);
}

// =============================================================================
// MORE CAPABLE (1): per-viewer projection of the POLL cap-only surface (HTTP).
// =============================================================================

#[tokio::test]
async fn the_three_voting_roles_see_different_cap_only_surfaces() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent();
    let app = voting_app(&cclerk, &executor);
    let router = app.mount();

    async fn visible(router: &axum::Router, tier: &str) -> serde_json::Value {
        let resp = router
            .clone()
            .oneshot(
                Request::get("/poll/projected")
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

    // Every tier sees `view_poll` on the cap-only POLL surface — the administrator's
    // record_tally / close_poll are GATED (not on the cap-only projection); they light on
    // the gated surface against live state.
    assert_eq!(
        visible(&router, "signature").await,
        serde_json::json!(["view_poll"])
    );
    assert_eq!(
        visible(&router, "either").await,
        serde_json::json!(["view_poll"])
    );
    assert_eq!(
        visible(&router, "root").await,
        serde_json::json!(["view_poll"])
    );
}

// =============================================================================
// MORE CAPABLE (2): web-of-cells — the POLL cell is a distributed sturdyref.
// =============================================================================

#[tokio::test]
async fn the_poll_is_published_into_the_web_of_cells() {
    let (cclerk, executor) = agent();
    // The SHIPPED surface, re-built with a captp server attached (the web-of-cells minter).
    // `voting_app` publishes the POLL cell at the viewer tier; the BALLOT is local-only.
    let captp = CapTpServer::new(FederationId([0x70; 32]));
    let base = voting_app(&cclerk, &executor);
    let poll_cell = base.cell(&cclerk.cell_id()).unwrap().clone();
    let ballot_cell = base
        .cell(&ballot_cell_id(&cclerk.public_key().0))
        .unwrap()
        .clone();
    let app = DeosApp::builder("privacy-voting", cclerk.clone(), executor.clone())
        .web_of_cells(captp)
        .cell(poll_cell)
        .cell(ballot_cell)
        .build();

    // Exactly the POLL cell is exported as a real `dregg://` sturdyref (the ballot is not
    // published) — a peer on another federation reacquires the public tally board.
    let uris = app.publish_all(100).await;
    assert_eq!(uris.len(), 1, "only the poll is published");
    assert!(
        uris[0].starts_with("dregg://"),
        "a real sturdyref: {}",
        uris[0]
    );
}

// =============================================================================
// MORE CAPABLE (3): rehydratable frustum-snapshot of the poll, per-viewer.
// =============================================================================

#[test]
fn a_poll_snapshot_rehydrates_per_viewer_respecting_the_lattice() {
    let (cclerk, executor) = agent();
    let app = voting_app(&cclerk, &executor);
    let poll = app.cell(&cclerk.cell_id()).unwrap();

    // Snapshot the poll; it witnessed a tally turn, sources gone (a cold snapshot handed to
    // a downstream auditor) ⇒ liveness REPLAYED-DETERMINISTIC.
    let log = InteractionLog::new().record(Interaction::witnessed_turn(poll.cell(), [9u8; 32]));
    let snap = poll.snapshot(log, false);
    assert_eq!(
        snap.lineage,
        AuthRequired::Signature,
        "snapshot at the published lineage"
    );
    assert_eq!(snap.liveness(), Rehydration::ReplayedDeterministic);
    assert!(snap.liveness().is_faithful());

    // A VIEWER (Signature) rehydrating reacquires only `view_poll` (the cap-only surface at
    // its tier) — the poll snapshot respects the lattice.
    let viewer = poll.rehydrate(&snap, AuthRequired::Signature).unwrap();
    assert_eq!(viewer.visible_names(), vec!["view_poll".to_string()]);

    // An INCOMPARABLE authority (a distinct Custom identity) cannot rehydrate at all — the
    // membrane mints NO projection (the no-peek refusal).
    let blocked = poll.rehydrate(&snap, AuthRequired::Custom { vk_hash: [7u8; 32] });
    assert!(matches!(blocked, Err(RehydrateError::Amplification { .. })));
}

// =============================================================================
// MORE CAPABLE (4): the generated web component + the manifest (with gated state-gates).
// =============================================================================

#[tokio::test]
async fn the_app_ships_a_web_component_surface_and_a_manifest() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent();
    let app = voting_app(&cclerk, &executor);
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
    // The anti-drift affordance map names the POLL cap-only fire endpoint.
    assert!(js.contains("fireEndpoint: \"/poll/fire/view_poll\","));

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
    assert_eq!(m["app"], "privacy-voting");
    assert_eq!(m["discoverable"], serde_json::json!(["voting", "poll"]));
    assert!(
        m["persistence"]
            .as_str()
            .unwrap()
            .contains("embedded-ledger")
    );
    assert_eq!(
        m["cells"].as_array().unwrap().len(),
        2,
        "two cells in the manifest"
    );

    // Collect each cell's gated affordance names across both cells.
    let mut gated_names: Vec<String> = Vec::new();
    for cell in m["cells"].as_array().unwrap() {
        if let Some(gated) = cell["gatedAffordances"].as_array() {
            for g in gated {
                if let Some(name) = g["name"].as_str() {
                    gated_names.push(name.to_string());
                }
            }
        }
    }
    gated_names.sort();
    assert_eq!(
        gated_names,
        vec![
            "cast_vote".to_string(),
            "close_poll".to_string(),
            "record_tally".to_string()
        ],
        "the manifest advertises the three gated (cap∧state) affordances across the two cells"
    );
}

// =============================================================================
// PRESERVED: the seeded two-cell ledger gives both cells live state (the fire substrate).
// =============================================================================

#[test]
fn seeding_gives_both_cells_live_state() {
    use dregg_app_framework::field_from_u64;
    use starbridge_privacy_voting::{CLOSED_SLOT, QUESTION_HASH_SLOT, VOTE_SLOT, question_hash};

    let (cclerk, executor) = agent();
    let poll = cclerk.cell_id();
    seed_poll(&executor, "ship it?");
    let ballot = seed_ballot(&executor, &cclerk, poll);

    // The poll cell carries the question (open, CLOSED == 0).
    let poll_state = executor.cell_state(poll).expect("poll seeded");
    assert_eq!(
        poll_state.fields[QUESTION_HASH_SLOT],
        question_hash("ship it?")
    );
    assert_eq!(poll_state.fields[CLOSED_SLOT], field_from_u64(0), "open");

    // The ballot companion cell exists, distinct, and is unset (VOTE == 0).
    assert_eq!(ballot, ballot_cell_id(&cclerk.public_key().0));
    assert_ne!(ballot, poll, "the ballot is a distinct cell");
    let ballot_state = executor
        .cell_state(ballot)
        .expect("ballot companion seeded");
    assert_eq!(
        ballot_state.fields[VOTE_SLOT],
        field_from_u64(0),
        "the ballot is unset"
    );
}
