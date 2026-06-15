//! THE SEAM CLOSED — the deos-native `invoke` fired through the executor against the FULL
//! mandate `Cases` program, so the verified caveats BITE in the fire path itself.
//!
//! `docs/deos/APPS-DEOS-INTEGRATION-CENSUS.md`: the promotion's task is to close the
//! fire→full-`CellProgram` seam so an over-budget / past-deadline / rewind invocation is a
//! REAL executor refusal in the fire path, not a `program.evaluate`-only check. This file
//! proves that seam CLOSED. `src::register_deos` / `src::seed_mandate` install
//! [`tad_cell_program`] (the `Cases` floor: the `Always` invariants `WriteOnce(rate/tool/
//! deadline)` + `FieldLteField(calls <= rate)`, and the `invoke_tool`-scoped `Monotonic(calls)`
//! + `FieldLteHeight(deadline)`) on the seeded mandate cell, and the deos fire is a TWO-TEMPO
//! bridge:
//!
//!   1. the deos PRECONDITION gate ([`DeosCell::gated_fireable_names`] — the cap-gate
//!      `is_attenuation` AND the live-state precondition `CellProgram::evaluate`, the
//!      budget-remaining `calls < rate`) decides the button's verdict IN-BAND, nothing
//!      submitted on a miss (anti-ghost);
//!   2. on both passing, [`fire_invoke`] submits the FULL counter-advancing turn (reading the
//!      LIVE `calls_made`), and the executor RE-ENFORCES the full `Cases` program on the
//!      produced transition — so an OVER-BUDGET invocation (`calls` past `rate`,
//!      `FieldLteField(calls <= rate)`) and a COUNTER REWIND (`calls` rolled back to forge
//!      head-room, `Monotonic(calls)`) are REAL executor refusals in the SUBMISSION path (the
//!      half the floor's `evaluate`-only tests never exercised through a real signed turn).
//!
//! Every fire is a real verified turn through the embedded executor; both gates are genuine
//! (`is_attenuation` + `CellProgram::evaluate`). No parallel model.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, EmbeddedExecutor, FireExecuteError,
    StarbridgeAppContext, field_from_u64,
};

use starbridge_tool_access_delegation::{
    CALLS_MADE_SLOT, RATE_LIMIT_SLOT, fire_invoke, invoke_effects, register_deos, seed_mandate,
    tad_app, tad_cell_program,
};

fn agent() -> (AppCipherclerk, EmbeddedExecutor) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x5b; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    (cclerk, executor)
}

// Read a u64 from the last 8 big-endian bytes of a field element.
fn field_to_u64(f: &[u8; 32]) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&f[24..32]);
    u64::from_be_bytes(b)
}

// =============================================================================
// (a) The seeded mandate carries the full Cases program (the executor re-enforces it).
// =============================================================================

#[test]
fn seeding_installs_the_cases_program_and_zero_counter() {
    let (cclerk, executor) = agent();
    seed_mandate(&executor, "search-mcp", 8, 0);

    // The seeded mandate cell carries the FULL `Cases` program (the seam's enforcement layer
    // the executor re-enforces on every touching turn).
    let installed =
        executor.with_ledger_mut(|ledger| ledger.get(&cclerk.cell_id()).map(|c| c.program.clone()));
    assert_eq!(
        installed,
        Some(tad_cell_program()),
        "the seeded mandate cell carries the Cases program (the seam's enforcement layer)"
    );
    // ...and the counter is born at 0, with the rate ceiling bound.
    let state = executor
        .cell_state(cclerk.cell_id())
        .expect("seeded cell exists");
    assert_eq!(state.fields[CALLS_MADE_SLOT as usize], field_from_u64(0));
    assert_eq!(state.fields[RATE_LIMIT_SLOT as usize], field_from_u64(8));
}

// =============================================================================
// (b) THE SEAM: the gated invoke fires through the executor — a real turn, calls advance.
// =============================================================================

#[test]
fn a_worker_invokes_through_the_gated_fire_a_real_verified_turn() {
    let (cclerk, executor) = agent();
    let app = tad_app(&cclerk, &executor);
    seed_mandate(&executor, "search-mcp", 8, 0);

    // A WORKER (Either) fires `invoke`: the cap-gate passes (Either ⊇ Either), the live-state
    // precondition passes (calls 0 < rate 8, budget remains), and the FULL invocation turn
    // advances calls 0 -> 1. The executor RE-ENFORCES the `Cases` program: `Monotonic(calls)`
    // (0 -> 1), `FieldLteField(calls <= rate)` (1 <= 8), `FieldLteHeight(deadline)` (deadline 0
    // <= block_height 0) all hold. A real verified turn.
    let receipt = fire_invoke(&app, &AuthRequired::Either, &cclerk, &executor)
        .expect("a worker meters one call (caps ∧ state ∧ rate ∧ deadline all pass)");
    assert_ne!(
        receipt.turn_hash, [0u8; 32],
        "a real verified turn through the executor"
    );

    // The counter advanced (the invocation committed).
    let state = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        state.fields[CALLS_MADE_SLOT as usize],
        field_from_u64(1),
        "invoke advanced the rate counter 0 -> 1"
    );

    // A second invoke advances again (the accumulating fire reads the live counter).
    let _ = fire_invoke(&app, &AuthRequired::Either, &cclerk, &executor).expect("second call");
    let state = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        state.fields[CALLS_MADE_SLOT as usize],
        field_from_u64(2),
        "0 -> 1 -> 2"
    );
}

// =============================================================================
// (c) A viewer below Either firing invoke → the cap tooth bites IN-BAND (anti-ghost).
// =============================================================================

#[test]
fn a_viewer_below_the_worker_tier_cannot_invoke_the_cap_tooth_bites_in_band() {
    let (cclerk, executor) = agent();
    let app = tad_app(&cclerk, &executor);
    seed_mandate(&executor, "search-mcp", 8, 0);

    // A bearer holding NO comparable authority (`AuthRequired::Custom`, incomparable to Either)
    // firing `invoke` (requires Either): the CAP tooth refuses IN-BAND. Nothing is submitted
    // (anti-ghost).
    let refused = fire_invoke(
        &app,
        &AuthRequired::Custom { vk_hash: [7u8; 32] },
        &cclerk,
        &executor,
    );
    assert!(
        matches!(
            refused,
            Err(FireExecuteError::Gate(
                dregg_app_framework::FireError::Unauthorized { .. }
            ))
        ),
        "a sub-worker's invoke is refused at the cap tooth in-band, got {refused:?}"
    );

    // The counter did NOT move — the refused fire submitted nothing (anti-ghost).
    let state = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(state.fields[CALLS_MADE_SLOT as usize], field_from_u64(0));
}

// =============================================================================
// (d) THE seam — FieldLteField(calls <= rate): an over-budget invoke is REFUSED by the
//     executor on the submitted turn (the rate ceiling bites in the submission path).
// =============================================================================

#[test]
fn the_executor_re_enforces_an_over_budget_invocation_is_refused() {
    // THE seam closed: the executor RE-ENFORCES the rate ceiling on every submitted invocation
    // turn — not just the deos precondition. Seed RATE_LIMIT small (2), advance the counter UP
    // TO the limit through the honest gated fire, then BYPASS the precondition (build the
    // invoke effects directly) and submit a turn that pushes `calls` PAST `rate` (2 -> 3). The
    // deos precondition is not consulted; the EXECUTOR's `FieldLteField(CALLS_MADE <=
    // RATE_LIMIT)` (installed by `seed_mandate`) refuses the over-budget step. This is the same
    // tooth `tests/factory_birth.rs` proves on the born cell, now biting in the deos SUBMISSION
    // path.
    let (cclerk, executor) = agent();
    let app = tad_app(&cclerk, &executor);
    seed_mandate(&executor, "search-mcp", 2, 0); // rate ceiling == 2
    let mandate = cclerk.cell_id();

    // Spend the budget honestly: 0 -> 1 -> 2 (both pass; `calls <= rate` holds at each step).
    fire_invoke(&app, &AuthRequired::Either, &cclerk, &executor).expect("call 1 (0 -> 1)");
    fire_invoke(&app, &AuthRequired::Either, &cclerk, &executor).expect("call 2 (1 -> 2)");
    let state = executor.cell_state(mandate).unwrap();
    assert_eq!(
        state.fields[CALLS_MADE_SLOT as usize],
        field_from_u64(2),
        "budget exhausted at 2"
    );

    // The deos precondition now darkens the button (budget-remaining `calls < rate` is 2 < 2 =
    // false) — the honest gated fire is refused at the STATE tooth in-band.
    let darkened = fire_invoke(&app, &AuthRequired::Either, &cclerk, &executor);
    assert!(
        matches!(
            darkened,
            Err(FireExecuteError::Gate(
                dregg_app_framework::FireError::StateConditionUnmet { .. }
            ))
        ),
        "the invoke button darkens once the budget is exhausted (the htmx tooth), got {darkened:?}"
    );

    // Now FORGE the over-budget step directly (bypass the precondition): submit calls 2 -> 3.
    // The EXECUTOR's `FieldLteField(calls <= rate)` refuses the over-budget invocation.
    let overbudget = invoke_effects(mandate, 3); // calls := 3, but rate == 2
    let action = cclerk.make_action(mandate, "invoke_tool", overbudget);
    let refused = executor.submit_action(&cclerk, action);
    assert!(
        refused.is_err(),
        "an invocation past the rate ceiling must be refused by the executor"
    );
    let msg = format!("{:?}", refused.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("lte") || msg.contains("field") || msg.contains("program"),
        "the executor refuses on the FieldLteField(calls <= rate) caveat, got: {msg}"
    );

    // The counter did NOT move past 2 (anti-ghost).
    let after = executor.cell_state(mandate).unwrap();
    assert_eq!(
        after.fields[CALLS_MADE_SLOT as usize],
        field_from_u64(2),
        "the refused over-budget invocation committed nothing — the counter still holds 2"
    );
}

// =============================================================================
// (e) Monotonic(calls) REWIND: rolling the counter back to forge budget is REFUSED.
// =============================================================================

#[test]
fn the_executor_re_enforces_a_counter_rewind_is_refused() {
    // The `Monotonic(CALLS_MADE)` invariant (on the `invoke_tool` case), biting in the
    // submission path. `Monotonic` is `>=`, so the genuine stale tooth is a REWIND (a no-advance
    // step would be a no-op). Seed (rate 8), advance the counter to 2 honestly, then submit an
    // `invoke_tool` turn that ROLLS THE COUNTER BACK (2 -> 1) to forge fresh head-room — the
    // executor's `Monotonic(CALLS_MADE)` refuses the rewind.
    let (cclerk, executor) = agent();
    let app = tad_app(&cclerk, &executor);
    seed_mandate(&executor, "search-mcp", 8, 0);
    let mandate = cclerk.cell_id();

    fire_invoke(&app, &AuthRequired::Either, &cclerk, &executor).expect("call 1 (0 -> 1)");
    fire_invoke(&app, &AuthRequired::Either, &cclerk, &executor).expect("call 2 (1 -> 2)");
    assert_eq!(
        field_to_u64(&executor.cell_state(mandate).unwrap().fields[CALLS_MADE_SLOT as usize]),
        2
    );

    // A REWOUND counter: calls 2 -> 1, under the `invoke_tool` method. `Monotonic(CALLS_MADE)`
    // refuses the rewind.
    let rewind = invoke_effects(mandate, 1); // calls := 1, but the live counter is 2
    let action = cclerk.make_action(mandate, "invoke_tool", rewind);
    let refused = executor.submit_action(&cclerk, action);
    assert!(
        refused.is_err(),
        "rewinding the rate counter must be refused by the executor"
    );
    let msg = format!("{:?}", refused.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("monotonic") || msg.contains("program") || msg.contains("field[0]"),
        "the executor refuses on the Monotonic(CALLS_MADE) caveat, got: {msg}"
    );

    // The counter did NOT move — the refused rewind committed nothing (anti-ghost).
    let after = executor.cell_state(mandate).unwrap();
    assert_eq!(
        after.fields[CALLS_MADE_SLOT as usize],
        field_from_u64(2),
        "the refused rewind committed nothing — the counter still holds 2"
    );
}

// =============================================================================
// (f) NOTE on FieldLteHeight(DEADLINE) — the height-aware deadline tooth.
// =============================================================================
//
// The `invoke_tool` case ALSO carries `FieldLteHeight(DEADLINE, offset: 0)` (the time bound):
// the executor admits the invocation only while `DEADLINE <= block_height`. This caveat is
// HEIGHT-AWARE — it depends on the block height the turn is presented at, which a
// `(state, state)` precondition read does NOT see. So it CANNOT be gated by the deos
// `budget_remaining_precondition` (which reads only `calls < rate`); instead it bites in the
// EXECUTOR on the submitted turn — exactly as the over-budget (d) and rewind (e) teeth do, on
// the produced transition. The honest invokes above clear it because `seed_mandate` sets
// `DEADLINE = 0` and the embedded executor runs at `block_height == 0`, so `0 <= 0` holds
// (no-expiry at the embedded height). A mandate seeded with `DEADLINE > block_height` has its
// invoke REFUSED by the executor's `FieldLteHeight(DEADLINE)` EVEN THOUGH the deos precondition
// (`calls < rate`) passes — this is the gate the recipe flags: the deadline tooth lives in the
// executor's program re-enforcement, NOT in the deos precondition. The
// `the_deadline_tooth_bites_in_the_executor` test below witnesses exactly that refusal.

#[test]
fn the_deadline_tooth_bites_in_the_executor() {
    // A mandate seeded with `DEADLINE > block_height` (deadline 100, embedded height 0). The
    // deos `budget_remaining` precondition (calls 0 < rate 8) PASSES — it cannot read the
    // height — so the deos gate lets the fire through; but the EXECUTOR's
    // `FieldLteHeight(DEADLINE)` (100 <= 0 is false) REFUSES the submitted invocation. The
    // height-aware deadline tooth lives in the executor's program re-enforcement, not the
    // precondition (the recipe's subtlety, witnessed).
    let (cclerk, executor) = agent();
    let app = tad_app(&cclerk, &executor);
    seed_mandate(&executor, "search-mcp", 8, 100); // DEADLINE 100 > block_height 0

    let refused = fire_invoke(&app, &AuthRequired::Either, &cclerk, &executor);
    assert!(
        matches!(refused, Err(FireExecuteError::Executor(_))),
        "the invoke clears the deos cap∧state gate but the EXECUTOR refuses on the deadline, got {refused:?}"
    );
    let msg = format!("{refused:?}").to_lowercase();
    assert!(
        msg.contains("height") || msg.contains("field[2]") || msg.contains("program"),
        "the executor refuses on the FieldLteHeight(DEADLINE) caveat, got: {msg}"
    );

    // The counter did NOT move (anti-ghost) — the refused invocation committed nothing.
    let state = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(state.fields[CALLS_MADE_SLOT as usize], field_from_u64(0));
}

// =============================================================================
// register_deos mounts the surface AND seeds the cell (the promotion is live).
// =============================================================================

#[test]
fn register_deos_mounts_the_seeded_surface_into_the_context() {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x5b; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    let ctx = StarbridgeAppContext::new(cclerk.clone(), executor.clone());

    // `register_deos` folds the DeosApp into the context's affordance registry AND seeds the
    // mandate cell (program installed, granted state). After it, the deos surface is the SHIPPED
    // one (the census promotion) and the gated fire is live.
    let app = register_deos(&ctx);
    assert_eq!(app.name(), "tool-access-delegation");
    assert_eq!(
        ctx.affordance_registry().len(),
        1,
        "the deos surface is registered"
    );

    // The seeded mandate is granted with budget remaining, so a worker can meter a call through
    // the mounted surface immediately (the seam is closed + live).
    let receipt = fire_invoke(&app, &AuthRequired::Either, &cclerk, &executor)
        .expect("the mounted, seeded surface meters an invocation (the promotion is live)");
    assert_ne!(receipt.turn_hash, [0u8; 32]);

    // The counter advanced (a real metered invocation through the mounted surface).
    let state = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(state.fields[CALLS_MADE_SLOT as usize], field_from_u64(1));
}
