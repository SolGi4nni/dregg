//! THE SEAM CLOSED — the deos-native `advance_step` fired through the executor against
//! the FULL workflow program, so the verified caveats BITE in the fire path itself.
//!
//! `docs/deos/APPS-DEOS-INTEGRATION-CENSUS.md` (the workflow port): the promotion's task
//! is to close the fire→full-`CellProgram` seam so a skipped/rewound step or a
//! past-terminal advance is a REAL executor refusal in the fire path, not a
//! `cwm_advance_admits` / `evaluate`-only check. This file proves that seam CLOSED.
//! `src::register_deos` / `src::seed_workflow` install [`cwm_cell_program`] (the `Always`
//! invariants — `WriteOnce` config slots + `FieldLteField(STEP_CURSOR <= CHARTER_TERMINAL)`
//! — AND the `advance_step`-scoped `MonotonicSequence(STEP_CURSOR)` exact-`+1`) on the
//! seeded mandate cell, and the deos fire is a TWO-TEMPO bridge:
//!
//!   1. the deos PRECONDITION gate ([`DeosCell::gated_fireable_names`] — the cap-gate
//!      `is_attenuation` AND the live-state precondition `CellProgram::evaluate`) decides
//!      the button's verdict IN-BAND, nothing submitted on a miss (anti-ghost);
//!   2. on both passing, [`fire_advance_step`] submits the FULL multi-effect advance turn,
//!      and the executor RE-ENFORCES the full workflow program on the produced transition —
//!      so a SKIPPED/REPEATED step (a cursor that does not advance by exactly `+1`,
//!      `MonotonicSequence(STEP_CURSOR)`) and a PAST-TERMINAL advance (a cursor past the
//!      charter terminal, `FieldLteField(STEP_CURSOR <= CHARTER_TERMINAL)`) are REAL
//!      executor refusals in the SUBMISSION path (the half the floor's `evaluate`-only /
//!      `cwm_advance_admits`-only tests never exercised through a real signed turn).
//!
//! NOTE on the STEP caveat: the floor's `cwm_cell_program` is a `Cases` program whose
//! `advance_step` case carries `MonotonicSequence(STEP_CURSOR)` — the EXACT-`+1` advance.
//! So the genuine no-replay tooth here is a NO-ADVANCE / SKIP (not merely a rewind): a
//! cursor that holds or jumps is refused because it is not `old + 1`. (A rewind is refused
//! too — `MonotonicSequence` is also anti-rollback.) The `Always` case's
//! `FieldLteField(STEP_CURSOR <= CHARTER_TERMINAL)` is the past-terminal tooth.
//!
//! Every fire is a real verified turn through the embedded executor; both gates are
//! genuine (`is_attenuation` + `CellProgram::evaluate`). No parallel model.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, EmbeddedExecutor, FireExecuteError,
    StarbridgeAppContext, field_from_u64,
};

use starbridge_compartment_workflow_mandate::{
    CHARTER_TERMINAL_SLOT, STEP_CURSOR_SLOT, advance_effects, cwm_cell_program, fire_advance_step,
    register_deos, seed_workflow, workflow_app,
};

fn agent(seed: u8) -> (AppCipherclerk, EmbeddedExecutor) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    (cclerk, executor)
}

/// Seed a mandate with charter terminal 3 (review → redact → sign) and cursor 0.
fn seed(executor: &EmbeddedExecutor) -> u64 {
    seed_workflow(executor, 42, 3, [0x11; 32], 5)
}

// =============================================================================
// (a) The seeded mandate carries the full workflow program (executor re-enforces it).
// =============================================================================

#[test]
fn seeding_installs_the_workflow_program_and_cursor_zero() {
    let (cclerk, executor) = agent(0x3b);
    let _ = seed(&executor);

    // The seeded mandate cell carries `cwm_cell_program()` — the FULL workflow policy
    // (the `Always` invariants AND the `advance_step`-scoped `MonotonicSequence`),
    // installed so the executor re-enforces it on every touching turn.
    let installed =
        executor.with_ledger_mut(|ledger| ledger.get(&cclerk.cell_id()).map(|c| c.program.clone()));
    assert_eq!(
        installed,
        Some(cwm_cell_program()),
        "the seeded mandate cell carries the workflow program (the seam's enforcement layer)"
    );
    // ...and the seeded state is at cursor 0 with the charter terminal pinned (3).
    let state = executor
        .cell_state(cclerk.cell_id())
        .expect("seeded cell exists");
    assert_eq!(state.fields[STEP_CURSOR_SLOT as usize], field_from_u64(0));
    assert_eq!(
        state.fields[CHARTER_TERMINAL_SLOT as usize],
        field_from_u64(3)
    );
}

// =============================================================================
// (b) THE SEAM: the gated advance_step fires through the executor, cursor advances +1.
// =============================================================================

#[test]
fn an_operator_advances_a_step_through_the_gated_fire_a_real_verified_turn() {
    let (cclerk, executor) = agent(0x3b);
    let app = workflow_app(&cclerk, &executor);
    let _ = seed(&executor); // cursor 0, terminal 3

    // An OPERATOR (None/root) fires `advance_step`: the cap-gate passes (None ⊇ None), the
    // live-state precondition passes (cursor 0 < terminal 3), and the FULL advance turn
    // advances the cursor 0 -> 1. The executor RE-ENFORCES the workflow program:
    // `MonotonicSequence(STEP_CURSOR)` holds (0 -> 1, exact +1) and
    // `FieldLteField(STEP_CURSOR <= CHARTER_TERMINAL)` holds (1 <= 3). A real verified turn.
    let receipt = fire_advance_step(&app, &AuthRequired::None, &cclerk, &executor)
        .expect("an operator advances (caps ∧ state ∧ monotonic-sequence ∧ lte-terminal all pass)");
    assert_ne!(
        receipt.turn_hash, [0u8; 32],
        "a real verified turn through the executor"
    );

    // The charter cursor advanced (the step committed).
    let state = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        state.fields[STEP_CURSOR_SLOT as usize],
        field_from_u64(1),
        "advance_step advanced the charter cursor 0 -> 1"
    );
}

// =============================================================================
// (c) The htmx tooth: advance to the terminal, then advance_step goes DARK.
// =============================================================================

#[test]
fn advancing_to_the_terminal_darkens_advance_step() {
    let (cclerk, executor) = agent(0x3b);
    let app = workflow_app(&cclerk, &executor);
    let _ = seed(&executor); // cursor 0, terminal 3

    // Before reaching the terminal, the OPERATOR sees `advance_step` LIT (the not-at-terminal
    // precondition cursor < terminal holds: 0 < 3). The htmx tooth, off live state.
    let lit_before = app.cells()[0].gated_fireable_names(&AuthRequired::None, &executor);
    assert!(
        lit_before.contains(&"advance_step".to_string()),
        "steps remain: advance lights"
    );

    // Drive the cursor to the terminal: 0 -> 1 -> 2 -> 3 (three real verified fires).
    for expect in 1..=3u64 {
        let receipt = fire_advance_step(&app, &AuthRequired::None, &cclerk, &executor)
            .unwrap_or_else(|e| panic!("advance to cursor {expect} should commit, got {e:?}"));
        assert_ne!(receipt.turn_hash, [0u8; 32]);
        let state = executor.cell_state(cclerk.cell_id()).unwrap();
        assert_eq!(
            state.fields[STEP_CURSOR_SLOT as usize],
            field_from_u64(expect)
        );
    }

    // After reaching the terminal (cursor == 3 == terminal), `advance_step` goes DARK (the
    // not-at-terminal precondition cursor < terminal now fails). Same viewer, same caps,
    // DIFFERENT button-set — because the cell transitioned. The htmx tooth.
    let lit_after = app.cells()[0].gated_fireable_names(&AuthRequired::None, &executor);
    assert!(
        !lit_after.contains(&"advance_step".to_string()),
        "at the terminal: advance_step darkens (the htmx tooth)"
    );

    // ...and a fire AT the terminal is refused IN-BAND at the STATE tooth (anti-ghost) —
    // nothing submitted, the cursor holds at 3.
    let refused = fire_advance_step(&app, &AuthRequired::None, &cclerk, &executor);
    assert!(
        matches!(
            refused,
            Err(FireExecuteError::Gate(
                dregg_app_framework::FireError::StateConditionUnmet { .. }
            ))
        ),
        "advance at the terminal is refused at the state tooth in-band, got {refused:?}"
    );
    let after = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(after.fields[STEP_CURSOR_SLOT as usize], field_from_u64(3));
}

// =============================================================================
// (d) The cap tooth: an observer (Signature) firing advance_step (needs None) is refused.
// =============================================================================

#[test]
fn an_observer_below_the_operator_tier_cannot_advance_the_cap_tooth_bites_in_band() {
    let (cclerk, executor) = agent(0x3b);
    let app = workflow_app(&cclerk, &executor);
    let _ = seed(&executor);

    // An OBSERVER (Signature) firing `advance_step` (requires None/operator): the CAP tooth
    // refuses IN-BAND — `is_attenuation(Signature, None)` is false (None ⊄ Signature).
    // Nothing is submitted (anti-ghost). An auditor can read the cursor but cannot drive it.
    let refused = fire_advance_step(&app, &AuthRequired::Signature, &cclerk, &executor);
    assert!(
        matches!(
            refused,
            Err(FireExecuteError::Gate(
                dregg_app_framework::FireError::Unauthorized { .. }
            ))
        ),
        "an observer's advance_step is refused at the cap tooth in-band, got {refused:?}"
    );

    // The cursor did NOT move (anti-ghost).
    let after = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(after.fields[STEP_CURSOR_SLOT as usize], field_from_u64(0));
}

// =============================================================================
// (e) THE seam: the executor re-enforces MonotonicSequence(STEP_CURSOR) — a no-advance
//     (skip / repeat) AND a rewind are refused in the SUBMISSION path.
// =============================================================================

#[test]
fn the_executor_re_enforces_a_non_plus_one_advance_is_refused() {
    // THE seam closed: the executor RE-ENFORCES the workflow program on every submitted
    // advance turn — not just the deos precondition. We bypass the precondition (build the
    // advance effects directly) and submit a turn that does NOT advance the cursor by exactly
    // `+1`: a REPEAT/SKIP (cursor 0 -> 0, the value held) forged to re-enter the step. The
    // deos precondition is not consulted; the EXECUTOR's `advance_step`-scoped
    // `MonotonicSequence(STEP_CURSOR)` (installed by `seed_workflow`) refuses a non-`+1`
    // advance. This is the half the floor's `evaluate`-only tests never exercised through a
    // real signed turn.
    let (cclerk, executor) = agent(0x3b);
    let _ = seed(&executor); // cursor == 0, program installed
    let cell = cclerk.cell_id();

    // A NO-ADVANCE: cursor 0 -> 0 under the `advance_step` method. `MonotonicSequence`
    // requires exactly `old + 1`; 0 is not 0 + 1, so it is refused. (`advance_effects`
    // with new_cursor 0 writes the cursor := 0 unchanged.)
    let stale = advance_effects(cell, 0, [0u8; 32]);
    let action = cclerk.make_action(cell, "advance_step", stale);
    let refused = executor.submit_action(&cclerk, action);
    assert!(
        refused.is_err(),
        "a non-+1 (no-advance) step must be refused by the executor"
    );
    let msg = format!("{:?}", refused.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("monotonic")
            || msg.contains("sequence")
            || msg.contains("program")
            || msg.contains("field[0]"),
        "the executor refuses on the MonotonicSequence(STEP_CURSOR) caveat, got: {msg}"
    );

    // The cursor did NOT move — the refused turn committed nothing (anti-ghost).
    let after = executor.cell_state(cell).unwrap();
    assert_eq!(
        after.fields[STEP_CURSOR_SLOT as usize],
        field_from_u64(0),
        "the refused advance committed nothing — the cursor still holds 0"
    );
}

#[test]
fn the_executor_re_enforces_a_skip_ahead_advance_is_refused() {
    // The same `MonotonicSequence(STEP_CURSOR)` tooth on a SKIP-AHEAD: advance one real
    // step (0 -> 1), then submit a turn that jumps the cursor 1 -> 3 (skipping step 2).
    // `MonotonicSequence` requires exactly `old + 1` (here 2); 3 is refused.
    let (cclerk, executor) = agent(0x3b);
    let app = workflow_app(&cclerk, &executor);
    let _ = seed(&executor);
    let cell = cclerk.cell_id();

    // One honest step: 0 -> 1.
    fire_advance_step(&app, &AuthRequired::None, &cclerk, &executor)
        .expect("first advance commits (0 -> 1)");

    // A SKIP-AHEAD: cursor 1 -> 3 (should be 2). MonotonicSequence refuses.
    let skip = advance_effects(cell, 3, [0u8; 32]);
    let action = cclerk.make_action(cell, "advance_step", skip);
    let refused = executor.submit_action(&cclerk, action);
    assert!(refused.is_err(), "skipping a step (non-+1) must be refused");
    let msg = format!("{:?}", refused.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("monotonic")
            || msg.contains("sequence")
            || msg.contains("program")
            || msg.contains("field[0]"),
        "the executor refuses the skip on MonotonicSequence(STEP_CURSOR), got: {msg}"
    );

    // The cursor still holds 1 (anti-ghost).
    let after = executor.cell_state(cell).unwrap();
    assert_eq!(after.fields[STEP_CURSOR_SLOT as usize], field_from_u64(1));
}

// =============================================================================
// (f) THE seam: the executor re-enforces FieldLteField(STEP_CURSOR <= CHARTER_TERMINAL)
//     — an advance PAST the charter terminal is refused in the SUBMISSION path.
// =============================================================================

#[test]
fn the_executor_re_enforces_an_advance_past_the_terminal_is_refused() {
    // The `FieldLteField(STEP_CURSOR <= CHARTER_TERMINAL)` invariant, biting in the
    // submission path. Drive the cursor to the terminal (3), then submit an advance to 4
    // (the honest +1 from 3) — which OVERRUNS the charter terminal. The executor's
    // `Always`-case `FieldLteField(STEP_CURSOR <= CHARTER_TERMINAL)` refuses the overrun
    // (the cursor may never pass the pinned terminal), even though it IS a legal `+1` step
    // (so this is the LTE tooth, distinct from the MonotonicSequence tooth above).
    let (cclerk, executor) = agent(0x3b);
    let app = workflow_app(&cclerk, &executor);
    let _ = seed(&executor); // terminal 3
    let cell = cclerk.cell_id();

    // Drive 0 -> 1 -> 2 -> 3 through honest fires (each a real +1).
    for _ in 0..3 {
        fire_advance_step(&app, &AuthRequired::None, &cclerk, &executor)
            .expect("honest advance commits");
    }
    let state = executor.cell_state(cell).unwrap();
    assert_eq!(
        state.fields[STEP_CURSOR_SLOT as usize],
        field_from_u64(3),
        "at the terminal"
    );

    // A PAST-TERMINAL advance: cursor 3 -> 4 (a legal +1 for MonotonicSequence, but 4 > 3
    // terminal). `FieldLteField(STEP_CURSOR <= CHARTER_TERMINAL)` refuses it.
    let overrun = advance_effects(cell, 4, [0u8; 32]);
    let action = cclerk.make_action(cell, "advance_step", overrun);
    let refused = executor.submit_action(&cclerk, action);
    assert!(
        refused.is_err(),
        "advancing past the charter terminal must be refused"
    );
    let msg = format!("{:?}", refused.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("lte")
            || msg.contains("field")
            || msg.contains("program")
            || msg.contains("terminal"),
        "the executor refuses on the FieldLteField(STEP_CURSOR <= CHARTER_TERMINAL) caveat, got: {msg}"
    );

    // The cursor did NOT move past 3 (anti-ghost).
    let after = executor.cell_state(cell).unwrap();
    assert_eq!(
        after.fields[STEP_CURSOR_SLOT as usize],
        field_from_u64(3),
        "the refused overrun committed nothing — the cursor still holds 3 (the terminal)"
    );
}

// =============================================================================
// register_deos mounts the surface AND seeds the cell (the promotion is live).
// =============================================================================

#[test]
fn register_deos_mounts_the_seeded_surface_into_the_context() {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x3b; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    let ctx = StarbridgeAppContext::new(cclerk.clone(), executor.clone());

    // `register_deos` folds the DeosApp into the context's affordance registry AND seeds
    // the mandate cell (program installed, charter config). After it, the deos surface is
    // the SHIPPED one (the census promotion) and the gated fire is live.
    let app = register_deos(&ctx);
    assert_eq!(app.name(), "compartment-workflow-mandate");
    assert_eq!(
        ctx.affordance_registry().len(),
        1,
        "the deos surface is registered"
    );

    // The seeded mandate is at cursor 0 with a charter terminal, so an operator can advance
    // through the mounted surface immediately (the seam is closed + live).
    let receipt = fire_advance_step(&app, &AuthRequired::None, &cclerk, &executor)
        .expect("the mounted, seeded surface advances a step (the promotion is live)");
    assert_ne!(receipt.turn_hash, [0u8; 32]);

    // The cursor advanced 0 -> 1 (the step committed through the live surface).
    let state = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(state.fields[STEP_CURSOR_SLOT as usize], field_from_u64(1));
}
