//! # The ADOS reference proof — agent orchestration as a LIVE, per-viewer, cap-gated web surface.
//!
//! This is the crown the memory describes: *ADOS = the OS that makes any loop's actions provably
//! authorized/recorded/budgeted/coordinated so a swarm becomes auditable WITHOUT trusting the loops.*
//! The orchestration board is mounted as a real axum surface; three viewers (auditor ⊂ worker ⊂
//! coordinator) fetch the SAME surface and SEE DIFFERENT button-sets by their caps alone; every fire is
//! a real verified turn; and a stranger (the auditor) re-derives the run and is never fooled.
//!
//! The four ADOS integrators (`buildr`/`builders`/`sig`/`simbi`) each hand-rolled this surface as a
//! mutable pane/council and punted on enforcement. Here the surface IS a set of capabilities, the
//! button-set IS the per-viewer cap projection, and the fire IS a verified turn — the wedge, closed.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CellId, EmbeddedExecutor, HELD_RIGHTS_HEADER,
    field_from_u64,
};
use starbridge_agent_orchestration::{
    coordinator_program,
    deos::{orchestration_app, AUDITOR_RIGHTS, COORDINATOR_RIGHTS, WORKER_RIGHTS},
    BUDGET_SLOT, EPOCH_SLOT, SPENT_A_SLOT,
};

fn agent() -> (AppCipherclerk, EmbeddedExecutor) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x5c; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    (cclerk, executor)
}

/// Open the board cell on the embedded ledger: install the budget program (the `AffineLe Σspend ≤
/// budget` policy the executor re-enforces) and set EPOCH >= 1 + a real swarm budget, so the gated
/// `worker_step` button lights (the htmx tooth) and the budget gate is non-vacuous.
fn open_board(executor: &EmbeddedExecutor, board: CellId, budget: u64) {
    executor.install_program(board, coordinator_program());
    executor.with_ledger_mut(|l| {
        if let Some(c) = l.get_mut(&board) {
            c.state.fields[EPOCH_SLOT as usize] = field_from_u64(1);
            c.state.fields[BUDGET_SLOT as usize] = field_from_u64(budget);
            c.state.fields[SPENT_A_SLOT as usize] = field_from_u64(0);
        }
    });
}

// =============================================================================
// 1. The rights ladder is real (auditor ⊂ worker ⊂ coordinator).
// =============================================================================

#[test]
fn the_three_tiers_are_the_attenuation_ladder() {
    use dregg_cell::is_attenuation;
    assert!(is_attenuation(&WORKER_RIGHTS, &AUDITOR_RIGHTS));
    assert!(is_attenuation(&COORDINATOR_RIGHTS, &WORKER_RIGHTS));
    assert!(!is_attenuation(&WORKER_RIGHTS, &COORDINATOR_RIGHTS));
}

// =============================================================================
// 2. Per-viewer cap-only projection over the mounted axum surface.
// =============================================================================

#[tokio::test]
async fn the_three_roles_see_different_cap_only_surfaces() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent();
    let app = orchestration_app(&cclerk, &executor);
    let router = app.mount();

    async fn visible(router: &axum::Router, tier: &str) -> serde_json::Value {
        let resp = router
            .clone()
            .oneshot(
                Request::get("/orchestration-board/projected")
                    .header(HELD_RIGHTS_HEADER, tier)
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(resp.status(), StatusCode::OK);
        let bytes = axum::body::to_bytes(resp.into_body(), usize::MAX).await.unwrap();
        serde_json::from_slice::<serde_json::Value>(&bytes).unwrap()["visible"].clone()
    }

    // An AUDITOR (Signature) sees only `view_audit` (the narrow read tier).
    assert_eq!(visible(&router, "signature").await, serde_json::json!(["view_audit"]));
    // A WORKER (Either) sees the same cap-only set — `worker_step` is GATED (lights on the gated
    // surface against live state, not the cap-only projection).
    assert_eq!(visible(&router, "either").await, serde_json::json!(["view_audit"]));
    // The COORDINATOR (root/None) additionally sees `delegate_mandate` (the cap-graph delegation).
    assert_eq!(
        visible(&router, "root").await,
        serde_json::json!(["delegate_mandate", "view_audit"])
    );
}

// =============================================================================
// 3. The gated `worker_step` button is DARK before open, LIT after (the htmx
//    tooth) — the gated surface is projected/fired IN-PROCESS (the
//    `DeosCell::project_gated_for` API; the cap-only surface is the HTTP half).
// =============================================================================

#[test]
fn worker_step_lights_only_when_the_board_is_open() {
    let (cclerk, executor) = agent();
    let app = orchestration_app(&cclerk, &executor);
    let board = cclerk.cell_id();
    let cell = &app.cells()[0];

    let worker_held = AuthRequired::Either;
    let auditor_held = AuthRequired::Signature;

    // BEFORE open: a worker's gated set is empty (the board is not open — state-gate dark).
    assert!(
        cell.gated_fireable_names(&worker_held, &executor).is_empty(),
        "worker_step is DARK before the board opens (htmx tooth)"
    );

    // OPEN the board.
    open_board(&executor, board, 1000);

    // AFTER open: a worker (Either) lights `worker_step`.
    assert!(
        cell.gated_fireable_names(&worker_held, &executor)
            .contains(&"worker_step".to_string()),
        "an open board LIGHTS worker_step for a worker (htmx tooth)"
    );
    // An auditor (Signature) still does NOT light it (caps too narrow for Either).
    assert!(
        !cell
            .gated_fireable_names(&auditor_held, &executor)
            .contains(&"worker_step".to_string()),
        "an auditor's caps are too narrow to fire worker_step"
    );
}

// =============================================================================
// 3b. A gated `worker_step` fire is a REAL verified turn (cap∧state in-band).
// =============================================================================

#[test]
fn a_gated_worker_step_fire_is_a_real_verified_turn() {
    use dregg_app_framework::FireExecuteError;

    let (cclerk, executor) = agent();
    let app = orchestration_app(&cclerk, &executor);
    let board = cclerk.cell_id();
    executor.with_ledger_mut(|l| {
        if let Some(c) = l.get_mut(&board) {
            c.state.set_balance(10_000_000);
        }
    });
    let cell = &app.cells()[0];

    let worker_held = AuthRequired::Either;
    let auditor_held = AuthRequired::Signature;

    // BEFORE open: even a capable worker's fire is refused at the STATE gate (anti-ghost — nothing
    // submitted, the board is not open).
    let dark = cell.fire_gated_through_executor("worker_step", &worker_held, &cclerk, &executor);
    assert!(
        matches!(dark, Err(FireExecuteError::Gate(_))),
        "a worker_step fire on a dark (un-opened) board is refused at the state gate; got {dark:?}"
    );

    // OPEN the board.
    open_board(&executor, board, 1000);

    // An AUDITOR (Signature) firing worker_step is refused at the CAP gate (caps too narrow) —
    // anti-ghost for the cap tooth.
    let unauth = cell.fire_gated_through_executor("worker_step", &auditor_held, &cclerk, &executor);
    assert!(
        matches!(unauth, Err(FireExecuteError::Gate(_))),
        "an auditor firing worker_step is refused at the cap gate; got {unauth:?}"
    );

    // A WORKER (Either) firing worker_step on the OPEN board COMMITS a real verified turn (both
    // gates pass) — returns the executor's own receipt.
    let receipt = cell
        .fire_gated_through_executor("worker_step", &worker_held, &cclerk, &executor)
        .expect("a worker's worker_step on the open board commits a verified turn");
    assert_ne!(receipt.receipt_hash(), [0u8; 32], "a real receipt hash");
}

// =============================================================================
// 4. A cap-gated fire is a real verified turn; anti-ghost holds (the cap tooth).
// =============================================================================

#[tokio::test]
async fn only_the_coordinator_can_delegate_a_mandate_a_real_turn() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent();
    let app = orchestration_app(&cclerk, &executor);
    let board = cclerk.cell_id();
    executor.with_ledger_mut(|l| {
        if let Some(c) = l.get_mut(&board) {
            c.state.set_balance(10_000_000);
        }
    });
    let router = app.mount();

    async fn fire(router: &axum::Router, name: &str, tier: &str) -> StatusCode {
        router
            .clone()
            .oneshot(
                Request::post(format!("/orchestration-board/fire/{name}"))
                    .header(HELD_RIGHTS_HEADER, tier)
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap()
            .status()
    }

    // The CAP tooth, in-band (anti-ghost): a WORKER (Either) and an AUDITOR (Signature) firing
    // `delegate_mandate` are REFUSED at the cap gate (403) BEFORE anything reaches the executor —
    // only a holder of the full `None` authority may delegate. The cap gate is the genuine
    // `is_attenuation` (`None` ⊄ Either/Signature).
    assert_eq!(fire(&router, "delegate_mandate", "either").await, StatusCode::FORBIDDEN);
    assert_eq!(fire(&router, "delegate_mandate", "signature").await, StatusCode::FORBIDDEN);

    // The COORDINATOR (root) CLEARS the cap gate (not 403) — it is cap-authorized to delegate.
    let coord_status = fire(&router, "delegate_mandate", "root").await;
    assert_ne!(
        coord_status,
        StatusCode::FORBIDDEN,
        "the coordinator is cap-authorized to delegate a mandate (cleared the cap gate, got {coord_status})"
    );
}

// =============================================================================
// 5. The auditor reads the manifest — the whole surface, including the durable
//    posture and the state-gate, VISIBLE from the Rust source of truth.
// =============================================================================

#[tokio::test]
async fn the_manifest_names_the_whole_surface_and_the_durable_posture() {
    use axum::body::Body;
    use axum::http::Request;
    use tower::ServiceExt;

    let (cclerk, executor) = agent();
    let app = orchestration_app(&cclerk, &executor);
    let router = app.mount();

    let resp = router
        .oneshot(Request::get("/manifest").body(Body::empty()).unwrap())
        .await
        .unwrap();
    let bytes = axum::body::to_bytes(resp.into_body(), usize::MAX).await.unwrap();
    let manifest: serde_json::Value = serde_json::from_slice(&bytes).unwrap();

    assert_eq!(manifest["app"], "agent-orchestration");
    // The durable posture is VISIBLE (pg-dregg), never silently faked.
    assert!(
        manifest["persistence"]
            .as_str()
            .unwrap()
            .contains("pg-dregg"),
        "the manifest advertises durable pg-dregg state: {}",
        manifest["persistence"]
    );
    let cell = &manifest["cells"][0];
    // The cap-only affordances (view_audit + delegate_mandate) are named with their required rights.
    let names: Vec<String> = cell["affordances"]
        .as_array()
        .unwrap()
        .iter()
        .map(|a| a["name"].as_str().unwrap().to_string())
        .collect();
    assert!(names.contains(&"view_audit".to_string()));
    assert!(names.contains(&"delegate_mandate".to_string()));
    // The GATED worker_step names its state-gate (the board-open condition) — the htmx half VISIBLE.
    let gated = cell["gatedAffordances"].as_array().unwrap();
    assert!(
        gated.iter().any(|g| g["name"] == "worker_step"
            && g["stateGate"].as_str().unwrap().contains("slot[")),
        "the manifest names worker_step's state-gate (the board-open condition): {gated:?}"
    );
}

// =============================================================================
// 6. The GATED surface is served OVER HTTP — the htmx tooth + cap/state teeth on the wire.
// =============================================================================

#[tokio::test]
async fn the_gated_surface_is_served_over_http() {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    let (cclerk, executor) = agent();
    let app = orchestration_app(&cclerk, &executor);
    let board = cclerk.cell_id();
    executor.with_ledger_mut(|l| {
        if let Some(c) = l.get_mut(&board) {
            c.state.set_balance(10_000_000);
        }
    });
    let router = app.mount();

    async fn gated_fireable(router: &axum::Router, tier: &str) -> Vec<String> {
        let resp = router
            .clone()
            .oneshot(
                Request::get("/orchestration-board/gated/projected")
                    .header(HELD_RIGHTS_HEADER, tier)
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(resp.status(), StatusCode::OK);
        let bytes = axum::body::to_bytes(resp.into_body(), usize::MAX).await.unwrap();
        let v: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
        v["fireable"]
            .as_array()
            .map(|a| a.iter().filter_map(|x| x.as_str().map(String::from)).collect())
            .unwrap_or_default()
    }

    async fn gated_fire(router: &axum::Router, tier: &str) -> StatusCode {
        router
            .clone()
            .oneshot(
                Request::post("/orchestration-board/gated/fire/worker_step")
                    .header(HELD_RIGHTS_HEADER, tier)
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap()
            .status()
    }

    // BEFORE open: /gated/projected is empty for everyone (the board is dark — state gate).
    assert!(
        gated_fireable(&router, "either").await.is_empty(),
        "worker_step is DARK over HTTP before the board opens"
    );
    // And a gated fire of worker_step on a dark board is 409 CONFLICT (the state tooth, anti-ghost).
    assert_eq!(
        gated_fire(&router, "either").await,
        StatusCode::CONFLICT,
        "a gated fire on a dark board is refused at the state gate (409)"
    );

    // OPEN the board.
    open_board(&executor, board, 1000);

    // AFTER open: a worker (Either) lights worker_step over HTTP.
    assert!(
        gated_fireable(&router, "either").await.contains(&"worker_step".to_string()),
        "an open board LIGHTS worker_step over HTTP for a worker"
    );
    // An auditor (Signature) does NOT (caps too narrow) — the cap tooth on the projection.
    assert!(
        !gated_fireable(&router, "signature").await.contains(&"worker_step".to_string()),
        "an auditor's caps are too narrow to light worker_step"
    );
    // An auditor firing worker_step over HTTP is 403 (the cap tooth, anti-ghost).
    assert_eq!(
        gated_fire(&router, "signature").await,
        StatusCode::FORBIDDEN,
        "an auditor's gated fire is refused at the cap gate (403)"
    );
    // A worker firing worker_step over HTTP on the OPEN board COMMITS (200) — a real verified turn.
    assert_eq!(
        gated_fire(&router, "either").await,
        StatusCode::OK,
        "a worker's gated fire on the open board commits over HTTP"
    );
}

// =============================================================================
// 7. The STATE-PARAMETERIZED fire drives a MULTI-STEP run from the SAME button.
// =============================================================================

#[test]
fn the_same_worker_step_button_advances_across_a_multi_step_run() {
    use starbridge_agent_orchestration::deos::fire_worker_step;
    use starbridge_agent_orchestration::WorkerSlot;

    let (cclerk, executor) = agent();
    let app = orchestration_app(&cclerk, &executor);
    let board = cclerk.cell_id();
    executor.with_ledger_mut(|l| {
        if let Some(c) = l.get_mut(&board) {
            c.state.set_balance(10_000_000);
        }
    });
    open_board(&executor, board, 1000);
    let cell = &app.cells()[0];
    let worker_held = AuthRequired::Either;

    fn spent_a(executor: &EmbeddedExecutor, board: CellId) -> u64 {
        let s = executor.cell_state(board).unwrap();
        let mut b = [0u8; 8];
        b.copy_from_slice(&s.fields[SPENT_A_SLOT as usize][24..32]);
        u64::from_be_bytes(b)
    }

    // The SAME `worker_step` button, fired three times, ADVANCES the worker's spend meter each time
    // (the state-parameterized effect reads live_spent + cost). Closes the single-fire gap.
    let r1 = fire_worker_step(cell, &worker_held, WorkerSlot::A, 100, &cclerk, &executor)
        .expect("first worker_step commits");
    assert_eq!(spent_a(&executor, board), 100);
    let r2 = fire_worker_step(cell, &worker_held, WorkerSlot::A, 150, &cclerk, &executor)
        .expect("second worker_step commits (button advances)");
    assert_eq!(spent_a(&executor, board), 250);
    let r3 = fire_worker_step(cell, &worker_held, WorkerSlot::A, 200, &cclerk, &executor)
        .expect("third worker_step commits");
    assert_eq!(spent_a(&executor, board), 450);
    // Three DISTINCT receipts — three verified turns from one published button.
    assert_ne!(r1.receipt_hash(), r2.receipt_hash());
    assert_ne!(r2.receipt_hash(), r3.receipt_hash());

    // The budget tooth still bites: a fire that would breach the swarm budget (450 + 600 > 1000)
    // is REFUSED in-band by the executor's AffineLe gate — nothing commits.
    let over = fire_worker_step(cell, &worker_held, WorkerSlot::A, 600, &cclerk, &executor);
    assert!(over.is_err(), "an over-budget gated fire is refused by the AffineLe gate");
    assert_eq!(spent_a(&executor, board), 450, "the refused fire moved nothing (fail-closed)");
}
