//! THE SEAM CLOSED — the deos-native `bid` / `settle` fired through the executor
//! against the FULL job program, so the verified caveats BITE in the fire path itself.
//!
//! The promotion's task is to close the fire->full-`CellProgram` seam so an over-budget
//! bid / a value-conjuring settle / a non-advancing state is a REAL executor refusal in
//! the fire path, not a `program.evaluate`-only check. This file proves that seam CLOSED.
//! `src::register_deos` / `src::seed_job` install [`job_program`] (the canonical
//! method-dispatched `Cases`: `Always`-case BUDGET `FieldLteField(BID <= BUDGET)` +
//! ACCEPTED `WriteOnce(BID)` + the universal no-mint `AffineLe` + LIFECYCLE
//! `StrictMonotonic(STATE)`, plus the settle-scoped FLASHWELL `AffineEq`) on the seeded
//! job cell, and the deos fire is a TWO-TEMPO bridge:
//!
//!   1. the deos PRECONDITION gate ([`DeosCell::gated_fireable_names`] — the cap-gate
//!      `is_attenuation` AND the live-state STATE-code precondition `CellProgram::evaluate`)
//!      decides the button's verdict IN-BAND, nothing submitted on a miss (anti-ghost);
//!   2. on both passing, [`fire_bid`] / [`fire_settle`] submit the FULL multi-effect
//!      lifecycle turn (built from the cell's LIVE state), and the executor RE-ENFORCES
//!      the full job program on the produced transition.
//!
//! THE THREE HEADLINE TEETH, each a real executor refusal in the SUBMISSION path:
//!   - LIFECYCLE: `StrictMonotonic(STATE)` — a settle that does not advance STATE is REFUSED
//!     (strict: even a no-advance bites);
//!   - BUDGET: `FieldLteField(BID <= BUDGET)` — a bid that breaches the budget is REFUSED;
//!   - FLASHWELL: `AffineEq` / `AffineLe` — a settle where `PAID + REFUNDED != BUDGET` (value
//!     conjured or destroyed) is REFUSED.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, EmbeddedExecutor, FireExecuteError,
    StarbridgeAppContext, field_from_u64,
};

use starbridge_compute_exchange::{
    BID_SLOT, BUDGET_SLOT, PAID_SLOT, REFUNDED_SLOT, STATE_BID, STATE_POSTED, STATE_SETTLED,
    STATE_SLOT, fire_bid, fire_settle, job_app, job_program, register_deos, seed_job,
    settle_effects,
};

fn agent() -> (AppCipherclerk, EmbeddedExecutor) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x71; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    (cclerk, executor)
}

/// Drive the honest lifecycle up to (but not including) settle: seed POSTED, bid as the
/// PROVIDER. Returns nothing; leaves STATE == BID with a bound accepted price.
fn post_and_bid(
    app: &dregg_app_framework::DeosApp,
    cclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
) {
    let _ = seed_job(executor, "requester-corp", 1000);
    fire_bid(
        app,
        &AuthRequired::Either,
        "provider-pat",
        800,
        cclerk,
        executor,
    )
    .expect("a provider bids (cap Either ⊇ Either, state POSTED, bid 800 <= budget 1000)");
}

// =============================================================================
// (a) The seeded job carries the full job program (the executor re-enforces it).
// =============================================================================

#[test]
fn seeding_installs_the_job_program_and_posted_state() {
    let (cclerk, executor) = agent();
    let _ = seed_job(&executor, "requester-corp", 1000);

    let installed =
        executor.with_ledger_mut(|ledger| ledger.get(&cclerk.cell_id()).map(|c| c.program.clone()));
    assert_eq!(
        installed,
        Some(job_program()),
        "the seeded job cell carries the job program (the seam's enforcement layer)"
    );
    let state = executor
        .cell_state(cclerk.cell_id())
        .expect("seeded cell exists");
    assert_eq!(
        state.fields[STATE_SLOT as usize],
        field_from_u64(STATE_POSTED)
    );
    assert_eq!(state.fields[BUDGET_SLOT as usize], field_from_u64(1000));
    assert_eq!(state.fields[BID_SLOT as usize], field_from_u64(0));
}

// =============================================================================
// (b) THE HONEST LIFECYCLE: bid → settle, each a real verified turn, STATE advancing.
// =============================================================================

#[test]
fn the_honest_lifecycle_runs_bid_settle_through_the_gated_fires() {
    let (cclerk, executor) = agent();
    let app = job_app(&cclerk, &executor);
    let _ = seed_job(&executor, "requester-corp", 1000);

    // BID (the PROVIDER, Either): cap passes, state POSTED passes, bid 800 <= budget 1000.
    let r1 = fire_bid(
        &app,
        &AuthRequired::Either,
        "provider-pat",
        800,
        &cclerk,
        &executor,
    )
    .expect("a provider bids within the budget");
    assert_ne!(r1.turn_hash, [0u8; 32], "a real verified bid turn");
    let s = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        s.fields[STATE_SLOT as usize],
        field_from_u64(STATE_BID),
        "STATE advanced POSTED -> BID"
    );
    assert_eq!(
        s.fields[BID_SLOT as usize],
        field_from_u64(800),
        "the bid committed"
    );

    // SETTLE (the REQUESTER, None): cap passes, state BID passes; the fire reads live BID (800)
    // + BUDGET (1000) and pays the provider IN FULL (paid 800, refunded 200), so the FLASHWELL
    // AffineEq (paid + refunded == budget) holds.
    let r2 = fire_settle(&app, &AuthRequired::None, &cclerk, &executor)
        .expect("a requester settles, conserving the budget on the honest path");
    assert_ne!(r2.turn_hash, [0u8; 32], "a real verified settle turn");
    let s = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        s.fields[STATE_SLOT as usize],
        field_from_u64(STATE_SETTLED),
        "STATE advanced BID -> SETTLED"
    );
    assert_eq!(
        s.fields[PAID_SLOT as usize],
        field_from_u64(800),
        "the provider was paid the accepted bid"
    );
    assert_eq!(
        s.fields[REFUNDED_SLOT as usize],
        field_from_u64(200),
        "the requester was refunded the remainder"
    );
}

// =============================================================================
// (c) THE HTMX TOOTH: on POSTED only `bid` lights; after bid, bid darkens + settle lights.
// =============================================================================

#[test]
fn the_lit_button_set_tracks_the_lifecycle_state_the_htmx_tooth() {
    let (cclerk, executor) = agent();
    let app = job_app(&cclerk, &executor);
    let _ = seed_job(&executor, "requester-corp", 1000);
    let cell = &app.cells()[0];

    // On POSTED: a PROVIDER (Either) sees `bid` LIT (posted precondition holds); `settle` is
    // DARK (its BID precondition fails). The htmx tooth off live state.
    let lit_posted = cell.gated_fireable_names(&AuthRequired::Either, &executor);
    assert!(
        lit_posted.contains(&"bid".to_string()),
        "POSTED: bid lights"
    );
    assert!(
        !lit_posted.contains(&"settle".to_string()),
        "POSTED: settle dark"
    );

    // Bid it (a real turn) — the cell transitions to BID.
    fire_bid(
        &app,
        &AuthRequired::Either,
        "provider-pat",
        800,
        &cclerk,
        &executor,
    )
    .expect("the provider bids");

    // After bid: as the REQUESTER (None, the top tier), `bid` DARKENS (POSTED precondition now
    // fails) and `settle` LIGHTS (BID precondition holds). Same cell, DIFFERENT button-set.
    let lit_bid = cell.gated_fireable_names(&AuthRequired::None, &executor);
    assert!(
        !lit_bid.contains(&"bid".to_string()),
        "BID: bid darkens (the htmx tooth)"
    );
    assert!(
        lit_bid.contains(&"settle".to_string()),
        "BID: settle lights (the htmx tooth)"
    );
}

// =============================================================================
// (d) THE CAP TOOTH, in-band: a provider firing `settle` (needs None) is refused.
// =============================================================================

#[test]
fn a_provider_cannot_fire_settle_the_cap_tooth_bites_in_band() {
    let (cclerk, executor) = agent();
    let app = job_app(&cclerk, &executor);
    let _ = seed_job(&executor, "requester-corp", 1000);
    // Bid first so the BID precondition for `settle` would otherwise hold — isolating the CAP tooth.
    fire_bid(
        &app,
        &AuthRequired::Either,
        "provider-pat",
        800,
        &cclerk,
        &executor,
    )
    .expect("the provider bids");

    // A PROVIDER (Either) firing `settle` (requires None/root): the CAP tooth refuses IN-BAND
    // (Either does not attenuate to None). Nothing is submitted (anti-ghost), even though the
    // state precondition holds.
    let refused = fire_settle(&app, &AuthRequired::Either, &cclerk, &executor);
    assert!(
        matches!(
            refused,
            Err(FireExecuteError::Gate(
                dregg_app_framework::FireError::Unauthorized { .. }
            ))
        ),
        "a provider's settle is refused at the cap tooth in-band, got {refused:?}"
    );
    let s = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        s.fields[STATE_SLOT as usize],
        field_from_u64(STATE_BID),
        "still BID — settle never fired"
    );
}

// =============================================================================
// (e) HEADLINE TOOTH #1 — LIFECYCLE: StrictMonotonic(STATE). A no-advance settle is REFUSED.
// =============================================================================

#[test]
fn the_executor_re_enforces_a_non_advancing_state_is_refused_strictmonotonic() {
    let (cclerk, executor) = agent();
    let app = job_app(&cclerk, &executor);
    post_and_bid(&app, &cclerk, &executor); // STATE == BID, bid 800, budget 1000
    let cell = cclerk.cell_id();

    // A settle that conserves the budget (800 + 200 == 1000) but leaves STATE at BID (no advance).
    // The FLASHWELL AffineEq holds, so it is the LIFECYCLE StrictMonotonic that bites.
    let mut effects = settle_effects(cell, 800, 200);
    for e in effects.iter_mut() {
        if let dregg_app_framework::Effect::SetField { index, value, .. } = e {
            if *index == STATE_SLOT as usize {
                *value = field_from_u64(STATE_BID);
            }
        }
    }
    let action = cclerk.make_action(cell, "settle", effects);
    let refused = executor.submit_action(&cclerk, action);
    assert!(
        refused.is_err(),
        "a non-advancing settle must be refused by the executor"
    );
    let msg = format!("{:?}", refused.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("strictmonotonic")
            || msg.contains("strictly")
            || msg.contains("monotonic")
            || msg.contains("program"),
        "the executor refuses on the StrictMonotonic(STATE) caveat, got: {msg}"
    );
    let after = executor.cell_state(cell).unwrap();
    assert_eq!(
        after.fields[STATE_SLOT as usize],
        field_from_u64(STATE_BID),
        "the refused settle committed nothing — STATE still holds BID"
    );
}

// =============================================================================
// (f) HEADLINE TOOTH #2 — BUDGET: FieldLteField(BID <= BUDGET). An over-budget bid is REFUSED.
// =============================================================================

#[test]
fn the_executor_re_enforces_an_over_budget_bid_is_refused_budget_gate() {
    let (cclerk, executor) = agent();
    let _ = seed_job(&executor, "requester-corp", 1000);
    let cell = cclerk.cell_id();

    // BID := 1500, but BUDGET == 1000. The bid advances STATE POSTED -> BID (so the method
    // case fires) and writes the over-budget price.
    let over = starbridge_compute_exchange::bid_effects(cell, "provider-pat", 1500);
    let action = cclerk.make_action(cell, "bid", over);
    let refused = executor.submit_action(&cclerk, action);
    assert!(refused.is_err(), "bidding past the budget must be refused");
    let msg = format!("{:?}", refused.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("lte") || msg.contains("field") || msg.contains("program"),
        "the executor refuses on the FieldLteField(BID <= BUDGET) caveat, got: {msg}"
    );
    let after = executor.cell_state(cell).unwrap();
    assert_eq!(
        after.fields[BID_SLOT as usize],
        field_from_u64(0),
        "the refused over-budget bid committed nothing — BID still holds 0"
    );
    assert_eq!(
        after.fields[STATE_SLOT as usize],
        field_from_u64(STATE_POSTED),
        "the refused bid committed nothing — STATE still holds POSTED"
    );
}

// =============================================================================
// (g) HEADLINE TOOTH #3 — FLASHWELL conservation: AffineEq / AffineLe. A value-conjuring settle is REFUSED.
// =============================================================================

#[test]
fn the_executor_re_enforces_a_non_conserving_settle_is_refused_flashwell() {
    let (cclerk, executor) = agent();
    let app = job_app(&cclerk, &executor);
    post_and_bid(&app, &cclerk, &executor); // STATE == BID, bid 800, budget 1000
    let cell = cclerk.cell_id();

    // MINT: pay 900 + refund 200 == 1100 against a 1000 budget (advancing STATE to SETTLED).
    let mint = settle_effects(cell, 900, 200);
    let refused = executor.submit_action(&cclerk, cclerk.make_action(cell, "settle", mint));
    assert!(refused.is_err(), "a value-minting settle must be refused");
    let msg = format!("{:?}", refused.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("affine")
            || msg.contains("conserv")
            || msg.contains("sum")
            || msg.contains("program"),
        "the executor refuses the mint on the AffineLe no-mint caveat, got: {msg}"
    );

    // BURN: pay 700 + refund 200 == 900 against a 1000 budget — destroys 100. Passes no-mint,
    // caught by no-burn AffineEq.
    let burn = settle_effects(cell, 700, 200);
    let refused = executor.submit_action(&cclerk, cclerk.make_action(cell, "settle", burn));
    assert!(refused.is_err(), "a value-burning settle must be refused");
    let msg = format!("{:?}", refused.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("affine")
            || msg.contains("conserv")
            || msg.contains("sum")
            || msg.contains("program"),
        "the executor refuses the burn on the AffineEq no-burn caveat, got: {msg}"
    );

    let after = executor.cell_state(cell).unwrap();
    assert_eq!(
        after.fields[STATE_SLOT as usize],
        field_from_u64(STATE_BID),
        "the refused settles committed nothing — STATE still holds BID"
    );

    // And the HONEST conserving settle (800 + 200 == 1000) DOES commit through the same path.
    let r = fire_settle(&app, &AuthRequired::None, &cclerk, &executor)
        .expect("the conserving settle commits");
    assert_ne!(r.turn_hash, [0u8; 32], "a real verified conserving settle");
    let after = executor.cell_state(cell).unwrap();
    assert_eq!(
        after.fields[STATE_SLOT as usize],
        field_from_u64(STATE_SETTLED),
        "the deal SETTLED"
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

    let app = register_deos(&ctx);
    assert_eq!(app.name(), "compute-exchange");
    assert_eq!(
        ctx.affordance_registry().len(),
        1,
        "the deos surface is registered"
    );

    // The seeded job is POSTED with a budget, so a provider can bid through the mounted surface
    // immediately (the seam is closed + live).
    let receipt = fire_bid(
        &app,
        &AuthRequired::Either,
        "provider-pat",
        500,
        &cclerk,
        &executor,
    )
    .expect("the mounted, seeded surface bids (the promotion is live)");
    assert_ne!(receipt.turn_hash, [0u8; 32]);
    let s = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        s.fields[BID_SLOT as usize],
        field_from_u64(500),
        "the bid committed through the mounted surface"
    );
}
