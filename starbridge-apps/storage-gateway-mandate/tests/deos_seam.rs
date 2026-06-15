//! THE SEAM CLOSED — the deos-native `put` fired through the executor against the FULL
//! gateway invariants, so the volume budget BITES in the fire path itself (a LIVE gate).
//!
//! `docs/deos/APPS-DEOS-INTEGRATION-CENSUS.md`: the storage-gateway mandate's scaffold
//! floor proved the volume-budget caveats on a born cell via predicate evaluation only.
//! This file proves the deos fire→full-`CellProgram` seam CLOSED: a STALE/over-budget
//! write is a REAL executor refusal in the fire path. `src::register_deos` /
//! `src::seed_gateway` install [`gateway_invariants_program`] (the descriptor's flat
//! `state_constraints`: `WriteOnce` anchor/ceiling/prefix/compartment + `Monotonic`
//! VOLUME_SPENT + `FieldLteField(VOLUME_SPENT <= VOLUME_CEILING)`) on the seeded gateway
//! cell, and the deos fire is a TWO-TEMPO bridge:
//!
//!   1. the deos PRECONDITION gate ([`DeosCell::gated_fireable_names`] — the cap-gate
//!      `is_attenuation` AND the live-state precondition `CellProgram::evaluate`) decides
//!      the button's verdict IN-BAND, nothing submitted on a miss (anti-ghost);
//!   2. on both passing, [`fire_put`] submits the FULL metered-write turn (reading the live
//!      VOLUME_SPENT + adding the object size), and the executor RE-ENFORCES the full
//!      gateway invariants on the produced transition — so an OVER-BUDGET write (spend
//!      pushed past the ceiling, `FieldLteField(VOLUME_SPENT <= VOLUME_CEILING)`) and a
//!      REWOUND meter (spend rolled back to forge free budget, `Monotonic(VOLUME_SPENT)`)
//!      are REAL executor refusals in the SUBMISSION path (the half the floor's
//!      predicate-only tests never exercised through a real signed turn).
//!
//! Every fire is a real verified turn through the embedded executor; both gates are
//! genuine (`is_attenuation` + `CellProgram::evaluate`). No parallel model.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, EmbeddedExecutor, FireExecuteError,
    StarbridgeAppContext, field_from_u64,
};

use starbridge_storage_gateway_mandate::{
    DEFAULT_COMMITMENT_ANCHOR, DEFAULT_KEY_PREFIX, DEFAULT_READ_COMPARTMENT, VOLUME_CEILING_SLOT,
    VOLUME_SPENT_SLOT, fire_put, gateway_app, gateway_invariants_program, put_effects,
    register_deos, seed_gateway,
};

fn agent(seed: u8) -> (AppCipherclerk, EmbeddedExecutor) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    (cclerk, executor)
}

/// Seed the gateway with a small `ceiling` (to exercise the over-budget tooth quickly).
fn seed_with_ceiling(executor: &EmbeddedExecutor, ceiling: u64) {
    seed_gateway(
        executor,
        DEFAULT_COMMITMENT_ANCHOR,
        ceiling,
        DEFAULT_KEY_PREFIX,
        DEFAULT_READ_COMPARTMENT,
    );
}

/// Force the live `VOLUME_SPENT` to `spent` (so the over-budget / rewind teeth can be set
/// up at a precise meter reading without a chain of fires).
fn set_spent(executor: &EmbeddedExecutor, spent: u64) {
    let gateway = executor.cell_id();
    executor.with_ledger_mut(|ledger| {
        if let Some(cell) = ledger.get_mut(&gateway) {
            cell.state
                .set_field(VOLUME_SPENT_SLOT as usize, field_from_u64(spent));
        }
    });
}

// =============================================================================
// (a) The seeded gateway carries the full volume invariants + a funded budget.
// =============================================================================

#[test]
fn seeding_installs_the_volume_invariants_and_a_funded_budget() {
    let (cclerk, executor) = agent(0x71);
    seed_with_ceiling(&executor, 10);

    // The seeded gateway cell carries the volume invariants (WriteOnce anchor/ceiling/
    // prefix/compartment + Monotonic VOLUME_SPENT + FieldLteField(spent <= ceiling)),
    // installed so the executor re-enforces them.
    let installed =
        executor.with_ledger_mut(|ledger| ledger.get(&cclerk.cell_id()).map(|c| c.program.clone()));
    assert_eq!(
        installed,
        Some(gateway_invariants_program()),
        "the seeded gateway cell carries the volume invariants (the seam's enforcement layer)"
    );
    // ...and the seeded state is the WriteOnce-bound ceiling (10) with a fresh budget
    // (VOLUME_SPENT == 0, nothing spent yet).
    let state = executor
        .cell_state(cclerk.cell_id())
        .expect("seeded cell exists");
    assert_eq!(
        state.fields[VOLUME_CEILING_SLOT as usize],
        field_from_u64(10)
    );
    assert_eq!(state.fields[VOLUME_SPENT_SLOT as usize], field_from_u64(0));
}

// =============================================================================
// (b) A writer puts through the gated fire — a real turn, VOLUME_SPENT advances.
// =============================================================================

#[test]
fn a_writer_puts_through_the_gated_fire_a_real_verified_turn() {
    let (cclerk, executor) = agent(0x71);
    let app = gateway_app(&cclerk, &executor);
    seed_with_ceiling(&executor, 10);

    // A WRITER (Either) fires `put` with object_size 4: the cap-gate passes (Either ⊇
    // Either), the live-state precondition passes (VOLUME_SPENT 0 < VOLUME_CEILING 10,
    // budget remains), and the FULL metered write advances the meter 0 -> 4. The executor
    // RE-ENFORCES the invariants: `FieldLteField(4 <= 10)` holds, `Monotonic(0 -> 4)` holds.
    // A real verified turn.
    let receipt = fire_put(
        &app,
        &AuthRequired::Either,
        &cclerk,
        &executor,
        "uploads/doc.txt",
        4,
    )
    .expect("a writer performs a metered write (caps ∧ budget ∧ invariants all pass)");
    assert_ne!(
        receipt.turn_hash, [0u8; 32],
        "a real verified turn through the executor"
    );

    // The volume meter advanced (the metered debit committed).
    let state = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        state.fields[VOLUME_SPENT_SLOT as usize],
        field_from_u64(4),
        "put advanced the volume meter 0 -> 4 (the metered debit)"
    );
}

// =============================================================================
// (c) THE htmx tooth — when the budget is exhausted, `put` goes DARK.
// =============================================================================

#[test]
fn put_darkens_when_the_budget_is_exhausted_the_htmx_tooth() {
    let (cclerk, executor) = agent(0x71);
    let app = gateway_app(&cclerk, &executor);
    seed_with_ceiling(&executor, 3); // a tiny 3-byte budget

    // Before exhaustion, a WRITER (Either) sees `put` LIT (budget-remaining precondition
    // VOLUME_SPENT < VOLUME_CEILING holds: 0 < 3). The htmx tooth, off live state.
    let lit_before = app.cells()[0].gated_fireable_names(&AuthRequired::Either, &executor);
    assert!(
        lit_before.contains(&"put".to_string()),
        "budget remains: put lights"
    );

    // Spend the budget right up to the ceiling (VOLUME_SPENT := 3 == VOLUME_CEILING).
    set_spent(&executor, 3);

    // Now the budget-remaining precondition (VOLUME_SPENT < VOLUME_CEILING, 3 < 3) FAILS,
    // so `put` goes DARK. Same viewer, same caps, DIFFERENT button-set — because the meter
    // reached the ceiling. The htmx tooth.
    let lit_after = app.cells()[0].gated_fireable_names(&AuthRequired::Either, &executor);
    assert!(
        !lit_after.contains(&"put".to_string()),
        "exhausted: put darkens (the htmx tooth)"
    );

    // And a fire is refused IN-BAND at the STATE tooth (anti-ghost — nothing submitted).
    let refused = fire_put(
        &app,
        &AuthRequired::Either,
        &cclerk,
        &executor,
        "uploads/x.txt",
        1,
    );
    assert!(
        matches!(
            refused,
            Err(FireExecuteError::Gate(
                dregg_app_framework::FireError::StateConditionUnmet { .. }
            ))
        ),
        "an exhausted-budget put is refused at the state tooth in-band, got {refused:?}"
    );
}

// =============================================================================
// (d) The cap tooth — a reader (Signature) firing put (needs Either) is refused in-band.
// =============================================================================

#[test]
fn a_reader_below_the_writer_tier_cannot_put_the_cap_tooth_bites_in_band() {
    let (cclerk, executor) = agent(0x71);
    let app = gateway_app(&cclerk, &executor);
    seed_with_ceiling(&executor, 10);

    // A READER holding `AuthRequired::Signature` (⊄ Either) firing `put`: the CAP tooth
    // refuses IN-BAND — `is_attenuation(Signature, Either)` is false. Nothing is submitted
    // (anti-ghost). A reader can read but cannot perform a metered write.
    let refused = fire_put(
        &app,
        &AuthRequired::Signature,
        &cclerk,
        &executor,
        "uploads/x.txt",
        1,
    );
    assert!(
        matches!(
            refused,
            Err(FireExecuteError::Gate(
                dregg_app_framework::FireError::Unauthorized { .. }
            ))
        ),
        "a reader's put is refused at the cap tooth in-band, got {refused:?}"
    );
}

// =============================================================================
// (e) THE seam — FieldLteField(VOLUME_SPENT <= VOLUME_CEILING): an over-budget write,
//     submitted directly through the executor, is REFUSED (budget exhausted).
// =============================================================================

#[test]
fn the_executor_re_enforces_an_over_budget_write_is_refused() {
    // THE seam closed: the executor RE-ENFORCES the volume budget on every submitted write
    // turn — not just the deos precondition. We bypass the precondition (build the put
    // effects directly) and submit a write that pushes the spend PAST the ceiling
    // (VOLUME_SPENT := 5 > VOLUME_CEILING 3). The deos precondition is not consulted; the
    // EXECUTOR's `FieldLteField(VOLUME_SPENT <= VOLUME_CEILING)` (installed by `seed_gateway`)
    // refuses the over-budget write — the budget can never be over-spent. This is the half
    // the floor's predicate-only tests never exercised through a real signed turn.
    let (cclerk, executor) = agent(0x71);
    seed_with_ceiling(&executor, 3); // a 3-byte ceiling, invariants installed
    set_spent(&executor, 2); // 2 spent, 1 byte of budget remaining
    let gateway = cclerk.cell_id();

    // An OVER-BUDGET write: VOLUME_SPENT := 5, but the ceiling is 3. `FieldLteField` refuses.
    let overspend = put_effects(gateway, "uploads/huge.bin", 5, [9u8; 32]);
    let action = cclerk.make_action(gateway, "put", overspend);
    let refused = executor.submit_action(&cclerk, action);
    assert!(
        refused.is_err(),
        "an over-budget write must be refused by the executor"
    );
    let msg = format!("{:?}", refused.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("lte") || msg.contains("field") || msg.contains("program"),
        "the executor refuses on the FieldLteField(VOLUME_SPENT <= VOLUME_CEILING) caveat, got: {msg}"
    );

    // The volume meter did NOT move — the refused write committed nothing (anti-ghost).
    let after = executor.cell_state(gateway).unwrap();
    assert_eq!(
        after.fields[VOLUME_SPENT_SLOT as usize],
        field_from_u64(2),
        "the refused over-budget write committed nothing — the meter still holds 2"
    );
}

// =============================================================================
// (f) Monotonic(VOLUME_SPENT) REWIND — rolling the spend back to free budget is REFUSED
//     (Monotonic is >=, so a rewind is a real refusal, not a no-op).
// =============================================================================

#[test]
fn the_executor_re_enforces_a_rewound_volume_meter_is_refused() {
    // The `Monotonic(VOLUME_SPENT)` invariant, biting in the submission path. Seed (ceiling
    // 10, spent 6), then submit a write that REWINDS the meter (VOLUME_SPENT := 2 < 6) to
    // forge free budget. `Monotonic` is `>=`, so a rewind (NOT a no-op) is refused — a
    // consumer cannot roll the meter back to re-spend an already-spent slice. (The new spend
    // 2 satisfies `2 <= 10`, so ONLY the Monotonic tooth bites — the rewind is isolated.)
    let (cclerk, executor) = agent(0x71);
    seed_with_ceiling(&executor, 10);
    set_spent(&executor, 6);
    let gateway = cclerk.cell_id();

    // A REWOUND meter: VOLUME_SPENT 6 -> 2. `Monotonic(VOLUME_SPENT)` refuses the rewind.
    let rewind = put_effects(gateway, "uploads/cheat.txt", 2, [8u8; 32]);
    let action = cclerk.make_action(gateway, "put", rewind);
    let refused = executor.submit_action(&cclerk, action);
    assert!(
        refused.is_err(),
        "rewinding the volume meter must be refused by the executor"
    );
    let msg = format!("{:?}", refused.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("monotonic") || msg.contains("program") || msg.contains("field[2]"),
        "the executor refuses on the Monotonic(VOLUME_SPENT) caveat, got: {msg}"
    );

    // The meter did NOT move (anti-ghost).
    let after = executor.cell_state(gateway).unwrap();
    assert_eq!(
        after.fields[VOLUME_SPENT_SLOT as usize],
        field_from_u64(6),
        "the refused rewind committed nothing — the meter still holds 6"
    );
}

// =============================================================================
// register_deos mounts the surface AND seeds the cell (the promotion is live).
// =============================================================================

#[test]
fn register_deos_mounts_the_seeded_surface_into_the_context() {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x71; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    let ctx = StarbridgeAppContext::new(cclerk.clone(), executor.clone());

    // `register_deos` folds the DeosApp into the context's affordance registry AND seeds the
    // gateway cell (program installed, configured state with a funded budget). After it, the
    // deos surface is the SHIPPED one (the census promotion) and the gated `put` fire is live.
    let app = register_deos(&ctx);
    assert_eq!(app.name(), "storage-gateway-mandate");
    assert_eq!(
        ctx.affordance_registry().len(),
        1,
        "the deos surface is registered"
    );

    // The seeded gateway is configured with a funded budget, so a writer can perform a
    // metered write through the mounted surface immediately (the seam is closed + live).
    let receipt = fire_put(
        &app,
        &AuthRequired::Either,
        &cclerk,
        &executor,
        "uploads/first.txt",
        2,
    )
    .expect("the mounted, seeded surface performs a metered write (the promotion is live)");
    assert_ne!(receipt.turn_hash, [0u8; 32]);

    // The volume meter advanced (a real metered debit on the write).
    let state = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        state.fields[VOLUME_SPENT_SLOT as usize],
        field_from_u64(2),
        "the metered write advanced the volume meter 0 -> 2"
    );
}
