//! THE SEAM CLOSED — the deos-native `dispatch` / `open_board` fired through the executor
//! against the FULL swarm program, so the verified caveats BITE in the fire path itself.
//!
//! `docs/deos/APPS-DEOS-INTEGRATION-CENSUS.md` (Tier-1 #3): the re-expression's named gap
//! was that a fired affordance ran on the scaffold `emit`/`edit` placeholders, NOT against
//! a factory-born coordinator cell carrying `swarm_constraints()` — so the `AffineLe`
//! budget gate, `WriteOnce` mandate/lead, and `StrictMonotonic` epoch did NOT bite in the
//! deos path. This file proves that seam CLOSED. `src::register_deos` / `src::seed_board`
//! install [`coordinator_program`] (the full swarm policy) on the seeded board cell, and
//! the deos fire is a TWO-TEMPO bridge:
//!
//!   1. the deos PRECONDITION gate ([`DeosCell::gated_fireable_names`] — the cap-gate
//!      `is_attenuation` AND the live-state precondition `CellProgram::evaluate`) decides
//!      the button's verdict IN-BAND, nothing submitted on a miss (anti-ghost);
//!   2. on both passing, [`fire_dispatch`] / [`fire_open_board`] submit the FULL
//!      multi-effect dispatch/open turn, and the executor RE-ENFORCES the full swarm program
//!      on the produced transition — so an OVER-BUDGET dispatch (`AffineLe(spent_a + spent_b
//!      <= budget)`), a REPLAYED dispatch (`StrictMonotonic(epoch)`), and a meter ROLLBACK
//!      (`Monotonic(SPENT_*)`) are REAL executor refusals in the SUBMISSION path (the half
//!      the floor's `program.evaluate`-only tests never exercised through a real signed turn).
//!
//! Every fire is a real verified turn through the embedded executor; both gates are genuine
//! (`is_attenuation` + `CellProgram::evaluate`). No parallel model. Run `--release` (the
//! embedded executor is slow in debug).

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CellId, EmbeddedExecutor, FireExecuteError,
    StarbridgeAppContext, field_from_u64,
};

use starbridge_swarm_orchestration::{
    BUDGET_SLOT, EPOCH_SLOT, LEAD_SLOT, SPENT_A_SLOT, SPENT_B_SLOT, Worker, board_app,
    coordinator_program, dispatch_effects, fire_dispatch, fire_open_board, identity_field,
    register_deos, seed_board,
};

fn agent(seed: u8) -> (AppCipherclerk, EmbeddedExecutor) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    (cclerk, executor)
}

/// Birth a worker agent cell into the embedded ledger so the dispatch's async-notify wake
/// (an `EmitEvent` targeting the worker) lands on a real cell — mirror `factory_birth.rs`:
/// a Sovereign cell owned by the operator key, with the operator granted a cap to it.
/// Returns its id. Without this the wake's target is absent and `apply_emit_event` returns
/// `CellNotFound` BEFORE the swarm caveats are evaluated.
fn birth_worker(executor: &EmbeddedExecutor, cclerk: &AppCipherclerk, tag: &[u8]) -> CellId {
    let pk = cclerk.public_key().0;
    let token: [u8; 32] = *blake3::hash(tag).as_bytes();
    let mut cell = dregg_cell::Cell::new(pk, token);
    cell.state.set_balance(5_000);
    executor.ensure_cell(cell).expect("worker cell inserts");
    let id = CellId::derive_raw(&pk, &token);
    let agent = cclerk.cell_id();
    executor.with_ledger_mut(|ledger| {
        if let Some(a) = ledger.get_mut(&agent) {
            a.capabilities.grant(id, AuthRequired::Signature);
        }
    });
    id
}

// =============================================================================
// The seeded board carries the full swarm program (the executor re-enforces it).
// =============================================================================

#[test]
fn seeding_installs_the_full_swarm_program_on_the_board_cell() {
    let (cclerk, executor) = agent(0x5a);
    let _ = seed_board(&executor, "lead", 1000);

    // The seeded board cell carries `coordinator_program()` — the FULL swarm policy
    // (AffineLe budget + WriteOnce lead/budget + Monotonic meters + StrictMonotonic epoch),
    // installed so the executor re-enforces it on every touching turn.
    let installed =
        executor.with_ledger_mut(|ledger| ledger.get(&cclerk.cell_id()).map(|c| c.program.clone()));
    assert_eq!(
        installed,
        Some(coordinator_program()),
        "the seeded board cell carries the full swarm program (the seam's enforcement layer)"
    );
    // ...and the seeded genesis state is open at epoch 1, lead pinned, budget 1000.
    let state = executor
        .cell_state(cclerk.cell_id())
        .expect("seeded cell exists");
    assert_eq!(state.fields[EPOCH_SLOT as usize], field_from_u64(1));
    assert_eq!(state.fields[BUDGET_SLOT as usize], field_from_u64(1000));
    assert_eq!(state.fields[LEAD_SLOT as usize], identity_field("lead"));
}

// =============================================================================
// THE SEAM: the gated dispatch fires through the executor, the budget gate bites.
// =============================================================================

#[test]
fn the_lead_dispatches_through_the_gated_fire_a_real_verified_turn() {
    let (cclerk, executor) = agent(0x5a);
    let app = board_app(&cclerk, &executor);
    let _ = seed_board(&executor, "lead", 1000);
    let worker = birth_worker(&executor, &cclerk, b"worker-a");

    // The LEAD (root) fires `dispatch`: the cap-gate passes (None ⊇ None), the live-state
    // precondition passes (EPOCH == 1 >= 1, the board is open), and the FULL dispatch turn
    // advances worker-A's meter by 300, bumps the epoch 1 -> 2, and wakes the worker. The
    // executor RE-ENFORCES the full swarm program: `AffineLe(300 + 0 <= 1000)` holds. A real
    // verified turn — the executor's OWN receipt.
    let receipt = fire_dispatch(
        &app,
        &AuthRequired::None,
        &cclerk,
        &executor,
        Worker::A,
        worker,
        300,
        "index",
    )
    .expect("the lead dispatches (caps ∧ state ∧ budget gate all pass)");
    assert_ne!(
        receipt.turn_hash, [0u8; 32],
        "a real verified turn through the executor"
    );

    // The meter + epoch advanced (the dispatch committed).
    let state = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        state.fields[SPENT_A_SLOT as usize],
        field_from_u64(300),
        "the meter advanced"
    );
    assert_eq!(
        state.fields[EPOCH_SLOT as usize],
        field_from_u64(2),
        "the epoch advanced 1 -> 2"
    );
}

#[test]
fn a_worker_cannot_dispatch_the_cap_tooth_bites_in_band() {
    let (cclerk, executor) = agent(0x5a);
    let app = board_app(&cclerk, &executor);
    let _ = seed_board(&executor, "lead", 1000);

    // A WORKER (Either) firing `dispatch` (requires None/root): the CAP tooth refuses IN-BAND
    // — `is_attenuation(Either, None)` is false. Nothing is submitted (anti-ghost), so the wake
    // target is never reached. A worker cannot self-dispatch budget; only the lead dispatches.
    let refused = fire_dispatch(
        &app,
        &AuthRequired::Either,
        &cclerk,
        &executor,
        Worker::A,
        CellId::from_bytes([0x9a; 32]),
        1,
        "t",
    );
    assert!(
        matches!(
            refused,
            Err(FireExecuteError::Gate(
                dregg_app_framework::FireError::Unauthorized { .. }
            ))
        ),
        "a worker's dispatch is refused at the cap tooth in-band, got {refused:?}"
    );
}

#[test]
fn dispatch_is_dark_before_the_board_opens_the_state_tooth_bites_in_band() {
    // A FRESH (unopened) board: EPOCH == 0, so the `dispatch` live-state precondition
    // (`EPOCH >= 1`) FAILS. Even a fully-authorized lead's fire is refused IN-BAND at the
    // STATE tooth — the button is dark before the board opens (the htmx tooth), and nothing
    // is submitted (anti-ghost for the state tooth).
    let (cclerk, executor) = agent(0x5a);
    let app = board_app(&cclerk, &executor);
    // Install the program but DO NOT open (EPOCH stays 0).
    executor.install_program(cclerk.cell_id(), coordinator_program());

    // Refused IN-BAND at the state tooth before submission, so the wake target is never reached.
    let refused = fire_dispatch(
        &app,
        &AuthRequired::None,
        &cclerk,
        &executor,
        Worker::A,
        CellId::from_bytes([0x9a; 32]),
        1,
        "t",
    );
    assert!(
        matches!(
            refused,
            Err(FireExecuteError::Gate(
                dregg_app_framework::FireError::StateConditionUnmet { .. }
            ))
        ),
        "dispatch before the board opens is refused at the state tooth in-band, got {refused:?}"
    );
}

#[test]
fn the_executor_re_enforces_an_over_budget_dispatch_is_refused() {
    // THE seam closed: the executor RE-ENFORCES the full swarm program on every submitted
    // dispatch turn. We bypass the precondition (build the dispatch effects directly) and
    // submit a turn whose meter would breach the mandate (spent_a 600 + spent_b 500 > budget
    // 1000). The deos precondition is not consulted; the EXECUTOR's `AffineLe(spent_a +
    // spent_b <= budget)` (installed by `seed_board`) refuses it. This is the budget tooth
    // biting in the SUBMISSION path — the named gap, closed.
    let (cclerk, executor) = agent(0x5a);
    let _ = seed_board(&executor, "lead", 1000); // budget 1000, program installed
    let board = cclerk.cell_id();
    let worker = birth_worker(&executor, &cclerk, b"worker");

    // First, an honest dispatch to B of 500 (epoch 1 -> 2) — admitted (0 + 500 <= 1000).
    let honest = fire_dispatch(
        &board_app(&cclerk, &executor),
        &AuthRequired::None,
        &cclerk,
        &executor,
        Worker::B,
        worker,
        500,
        "b-task",
    )
    .expect("the first 500-to-B dispatch fits the budget");
    assert_ne!(honest.turn_hash, [0u8; 32]);

    // Now a dispatch to A of 600 (epoch 2 -> 3) would make spent_a + spent_b = 600 + 500 =
    // 1100 > 1000 — the `AffineLe` budget gate refuses it. (Built directly: meter := 600,
    // epoch := 3.)
    let over = dispatch_effects(board, Worker::A, worker, 600, 3, 600, "a-task");
    let action = cclerk.make_action(board, "dispatch", over);
    let refused = executor.submit_action(&cclerk, action);
    assert!(
        refused.is_err(),
        "an over-budget dispatch (1100 > 1000) must be refused by the executor"
    );
    let msg = format!("{:?}", refused.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("affine")
            || msg.contains("program")
            || msg.contains("budget")
            || msg.contains("constraint"),
        "the executor refuses on the AffineLe budget gate, got: {msg}"
    );

    // The over-budget meter did NOT move — the refused turn committed nothing (anti-ghost).
    let after = executor.cell_state(board).unwrap();
    assert_eq!(
        after.fields[SPENT_A_SLOT as usize],
        field_from_u64(0),
        "the refused over-budget dispatch committed nothing — worker-A's meter still holds 0"
    );
}

#[test]
fn the_executor_re_enforces_a_replayed_epoch_is_refused() {
    // The `StrictMonotonic(EPOCH)` no-replay caveat, biting in the submission path. Seed
    // (epoch 1), then submit a dispatch whose epoch does NOT advance (stale, == current 1).
    // The executor's `StrictMonotonic(EPOCH)` refuses 1 -> 1.
    let (cclerk, executor) = agent(0x5a);
    let _ = seed_board(&executor, "lead", 1000);
    let board = cclerk.cell_id();
    let worker = birth_worker(&executor, &cclerk, b"worker");

    // HONEST-ACCEPT FIRST: a dispatch that ADVANCES the epoch (1 -> 2) is admitted
    // — so the reject below is provably caused by the epoch NOT advancing (a
    // replay), not a setup error that fails every dispatch.
    fire_dispatch(
        &board_app(&cclerk, &executor),
        &AuthRequired::None,
        &cclerk,
        &executor,
        Worker::A,
        worker,
        100,
        "a-task",
    )
    .expect("an epoch-advancing dispatch (1 -> 2) must be admitted");

    // A STALE dispatch: meter advances (a within-budget 100) but epoch stays 1 (not 2).
    let stale = dispatch_effects(board, Worker::A, worker, 100, 1, 100, "a-task");
    let action = cclerk.make_action(board, "dispatch", stale);
    let refused = executor.submit_action(&cclerk, action);
    assert!(
        refused.is_err(),
        "a replayed (non-advancing) epoch dispatch must be refused"
    );
    let msg = format!("{:?}", refused.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("strictmonotonic")
            || msg.contains("strictly")
            || msg.contains("program")
            || msg.contains("field[4]"),
        "the executor refuses on the StrictMonotonic(EPOCH) caveat, got: {msg}"
    );

    // The meter did NOT move past the honest dispatch's 100 (anti-ghost — the
    // refused replay aborts the whole turn, committing nothing on top of it).
    let after = executor.cell_state(board).unwrap();
    assert_eq!(
        after.fields[SPENT_A_SLOT as usize],
        field_from_u64(100),
        "the refused replay committed nothing — the meter still holds the honest dispatch's 100"
    );
}

#[test]
fn the_executor_re_enforces_a_meter_rollback_is_refused() {
    // The `Monotonic(SPENT_A)` caveat, biting in the submission path. Seed, dispatch 400 to A
    // (meter 0 -> 400, epoch 1 -> 2), then submit a dispatch that ROLLS THE METER BACK to 100
    // (forging head-room) while advancing the epoch — the executor's `Monotonic(SPENT_A)`
    // refuses 400 -> 100.
    let (cclerk, executor) = agent(0x5a);
    let app = board_app(&cclerk, &executor);
    let _ = seed_board(&executor, "lead", 1000);
    let worker = birth_worker(&executor, &cclerk, b"worker");

    fire_dispatch(
        &app,
        &AuthRequired::None,
        &cclerk,
        &executor,
        Worker::A,
        worker,
        400,
        "a-task",
    )
    .expect("the first 400-to-A dispatch commits (meter 0 -> 400)");

    let board = cclerk.cell_id();
    // A rollback: meter := 100 (< the committed 400) while epoch advances 2 -> 3.
    let rollback = dispatch_effects(board, Worker::A, worker, 100, 3, 100, "a-task");
    let action = cclerk.make_action(board, "dispatch", rollback);
    let refused = executor.submit_action(&cclerk, action);
    assert!(
        refused.is_err(),
        "rolling a worker meter back to forge head-room must be refused"
    );
    let msg = format!("{:?}", refused.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("monotonic") || msg.contains("program") || msg.contains("field[2]"),
        "the executor refuses on the Monotonic(SPENT_A) caveat, got: {msg}"
    );

    // The meter still holds the committed 400 (anti-ghost).
    let after = executor.cell_state(board).unwrap();
    assert_eq!(
        after.fields[SPENT_A_SLOT as usize],
        field_from_u64(400),
        "the refused rollback committed nothing"
    );
    // Reference SPENT_B so the import is live (worker-B's meter is the other AffineLe column).
    assert_eq!(after.fields[SPENT_B_SLOT as usize], field_from_u64(0));
}

// =============================================================================
// open_board: the gated open fires, then goes DARK (the htmx tooth); re-open refused.
// =============================================================================

#[test]
fn the_lead_opens_the_board_through_the_gated_fire_then_the_button_goes_dark() {
    let (cclerk, executor) = agent(0x5a);
    let app = board_app(&cclerk, &executor);
    // Install the program; a FRESH board (EPOCH == 0, NOT seeded/opened).
    executor.install_program(cclerk.cell_id(), coordinator_program());

    // Before the open, the LEAD (root) sees `open_board` LIT (pre-open precondition EPOCH ==
    // 0 holds) and `dispatch` DARK (opened precondition EPOCH >= 1 fails). The htmx tooth.
    let lit_before = app.cells()[0].gated_fireable_names(&AuthRequired::None, &executor);
    assert_eq!(
        lit_before,
        vec!["open_board".to_string()],
        "pre-open: only open_board lights"
    );

    // The lead opens the board — the FULL open turn pins lead + budget, advances epoch 0 -> 1.
    let receipt = fire_open_board(&app, &AuthRequired::None, &cclerk, &executor, "lead", 1000)
        .expect("the lead opens the fresh board");
    assert_ne!(receipt.turn_hash, [0u8; 32], "a real verified open turn");

    // After the open, `open_board` goes DARK (pre-open precondition now fails) and `dispatch`
    // LIGHTS (opened precondition now holds). Same viewer, same caps, DIFFERENT button-set.
    let lit_after = app.cells()[0].gated_fireable_names(&AuthRequired::None, &executor);
    assert!(
        lit_after.contains(&"dispatch".to_string()),
        "post-open: dispatch lights"
    );
    assert!(
        !lit_after.contains(&"open_board".to_string()),
        "post-open: open_board darkens (the htmx tooth)"
    );

    // The genesis state is bound: epoch 1, budget 1000, lead pinned.
    let state = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(state.fields[EPOCH_SLOT as usize], field_from_u64(1));
    assert_eq!(state.fields[BUDGET_SLOT as usize], field_from_u64(1000));
}

#[test]
fn a_second_open_is_refused_at_the_state_tooth_in_band() {
    let (cclerk, executor) = agent(0x5a);
    let app = board_app(&cclerk, &executor);
    let _ = seed_board(&executor, "lead", 1000); // already open (EPOCH == 1)

    // `open_board`'s pre-open precondition (EPOCH == 0) FAILS on an already-open board — the
    // STATE tooth refuses IN-BAND; nothing is submitted. Even the lead cannot re-open (and the
    // installed `WriteOnce(BUDGET)` would refuse a budget rebind on the executor besides).
    let refused = fire_open_board(&app, &AuthRequired::None, &cclerk, &executor, "lead", 9999);
    assert!(
        matches!(
            refused,
            Err(FireExecuteError::Gate(
                dregg_app_framework::FireError::StateConditionUnmet { .. }
            ))
        ),
        "a second open is refused at the state tooth in-band, got {refused:?}"
    );
}

// =============================================================================
// register_deos mounts the surface AND seeds the cell (the promotion is live).
// =============================================================================

#[test]
fn register_deos_mounts_the_seeded_surface_into_the_context() {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x5a; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    let ctx = StarbridgeAppContext::new(cclerk.clone(), executor.clone());

    // `register_deos` folds the DeosApp into the context's affordance registry AND seeds the
    // board cell (program installed, opened state). After it, the deos surface is the SHIPPED
    // one (the census promotion) and the gated fires are live.
    let app = register_deos(&ctx);
    assert_eq!(app.name(), "swarm-orchestration");
    assert_eq!(
        ctx.affordance_registry().len(),
        1,
        "the deos surface is registered"
    );

    // The seeded board is open, so the lead can dispatch through the mounted surface
    // immediately (the seam is closed and live).
    let worker = birth_worker(&executor, &cclerk, b"worker");
    let receipt = fire_dispatch(
        &app,
        &AuthRequired::None,
        &cclerk,
        &executor,
        Worker::A,
        worker,
        100,
        "task",
    )
    .expect("the mounted, seeded surface dispatches (the promotion is live)");
    assert_ne!(receipt.turn_hash, [0u8; 32]);
}
