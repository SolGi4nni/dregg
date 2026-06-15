//! THE SEAM CLOSED — the deos-native `fund` / `ship` / `settle` fired through the executor
//! against the FULL escrow program, so the verified caveats BITE in the fire path itself.
//!
//! `docs/deos/APPS-DEOS-INTEGRATION-CENSUS.md`: the promotion's task is to close the
//! fire→full-`CellProgram` seam so an over-ceiling fund / a value-conjuring settle / a
//! non-advancing state is a REAL executor refusal in the fire path, not a `program.evaluate`-only
//! check. This file proves that seam CLOSED. `src::register_deos` / `src::seed_escrow` install
//! [`escrow_program`] (the canonical method-dispatched `Cases`: `Always`-case TRUSTLINE
//! `FieldLteField(ESCROWED <= CEILING)` + MAILBOX `WriteOnce(DELIVERY)` + the universal no-mint
//! `AffineLe` + LIFECYCLE `StrictMonotonic(STATE)`, plus the settle-scoped FLASHWELL `AffineEq`)
//! on the seeded escrow cell, and the deos fire is a TWO-TEMPO bridge:
//!
//!   1. the deos PRECONDITION gate ([`DeosCell::gated_fireable_names`] — the cap-gate
//!      `is_attenuation` AND the live-state STATE-code precondition `CellProgram::evaluate`) decides
//!      the button's verdict IN-BAND, nothing submitted on a miss (anti-ghost);
//!   2. on both passing, [`fire_fund`] / [`fire_ship`] / [`fire_settle`] submit the FULL
//!      multi-effect lifecycle turn (built from the cell's LIVE state), and the executor
//!      RE-ENFORCES the full escrow program on the produced transition.
//!
//! THE THREE HEADLINE TEETH, each a real executor refusal in the SUBMISSION path:
//!   - LIFECYCLE: `StrictMonotonic(STATE)` — a settle that does not advance STATE is REFUSED
//!     (strict: even a no-advance bites);
//!   - TRUSTLINE: `FieldLteField(ESCROWED <= CEILING)` — a fund whose escrow breaches the ceiling
//!     is REFUSED;
//!   - FLASHWELL: `AffineEq` / `AffineLe` — a settle where `RELEASED + REFUNDED != ESCROWED` (value
//!     conjured or destroyed) is REFUSED.
//!
//! Every fire is a real verified turn through the embedded executor; both gates are genuine
//! (`is_attenuation` + `CellProgram::evaluate`). No parallel model. The installed `Cases` program
//! carries the method symbol, re-enforced on the submitted full turn; the precondition is a SEPARATE
//! small `Predicate` (a STATE check) the gated affordance evaluates in-band.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, EmbeddedExecutor, FireExecuteError,
    StarbridgeAppContext, field_from_u64,
};

use starbridge_escrow_market::{
    CEILING_SLOT, ESCROWED_SLOT, RELEASED_SLOT, STATE_LISTED, STATE_SETTLED, STATE_SHIPPED,
    STATE_SLOT, escrow_app, escrow_program, fire_fund, fire_settle, fire_ship, register_deos,
    sealed_delivery_digest, seed_escrow, settle_effects,
};

fn agent() -> (AppCipherclerk, EmbeddedExecutor) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x62; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    (cclerk, executor)
}

/// Drive the honest lifecycle up to (but not including) settle: seed LISTED, fund as the BUYER,
/// ship as the SELLER. Returns the configured ceiling.
fn fund_and_ship(
    app: &dregg_app_framework::DeosApp,
    cclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
) {
    let _ = seed_escrow(executor, "acme-corp", 1000);
    fire_fund(
        app,
        &AuthRequired::Either,
        "buyer-bob",
        800,
        cclerk,
        executor,
    )
    .expect("a buyer funds (cap Either ⊇ Either, state LISTED, escrowed 800 <= ceiling 1000)");
    let delivery = sealed_delivery_digest(b"the-goods-ciphertext");
    fire_ship(app, &AuthRequired::None, delivery, cclerk, executor)
        .expect("a seller ships (cap None ⊇ None, state FUNDED)");
}

// =============================================================================
// (a) The seeded escrow carries the full escrow program (the executor re-enforces it).
// =============================================================================

#[test]
fn seeding_installs_the_escrow_program_and_listed_state() {
    let (cclerk, executor) = agent();
    let _ = seed_escrow(&executor, "acme-corp", 1000);

    // The seeded escrow cell carries the canonical escrow program (the Cases shape carrying the
    // TRUSTLINE / MAILBOX / FLASHWELL / LIFECYCLE caveats), installed so the executor re-enforces it.
    let installed =
        executor.with_ledger_mut(|ledger| ledger.get(&cclerk.cell_id()).map(|c| c.program.clone()));
    assert_eq!(
        installed,
        Some(escrow_program()),
        "the seeded escrow cell carries the escrow program (the seam's enforcement layer)"
    );
    // ...and the seeded state is LISTED with a bound ceiling and zero escrow.
    let state = executor
        .cell_state(cclerk.cell_id())
        .expect("seeded cell exists");
    assert_eq!(
        state.fields[STATE_SLOT as usize],
        field_from_u64(STATE_LISTED)
    );
    assert_eq!(state.fields[CEILING_SLOT as usize], field_from_u64(1000));
    assert_eq!(state.fields[ESCROWED_SLOT as usize], field_from_u64(0));
}

// =============================================================================
// (b) THE HONEST LIFECYCLE: fund → ship → settle, each a real verified turn, STATE advancing.
// =============================================================================

#[test]
fn the_honest_lifecycle_runs_fund_ship_settle_through_the_gated_fires() {
    let (cclerk, executor) = agent();
    let app = escrow_app(&cclerk, &executor);
    let _ = seed_escrow(&executor, "acme-corp", 1000);

    // FUND (the BUYER, Either): cap passes, state LISTED passes, escrowed 800 <= ceiling 1000.
    let r1 = fire_fund(
        &app,
        &AuthRequired::Either,
        "buyer-bob",
        800,
        &cclerk,
        &executor,
    )
    .expect("a buyer funds within the ceiling");
    assert_ne!(r1.turn_hash, [0u8; 32], "a real verified fund turn");
    let s = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        s.fields[STATE_SLOT as usize],
        field_from_u64(2),
        "STATE advanced LISTED -> FUNDED"
    );
    assert_eq!(
        s.fields[ESCROWED_SLOT as usize],
        field_from_u64(800),
        "the escrow committed"
    );

    // SHIP (the SELLER, None): cap passes, state FUNDED passes; the sealed delivery commits.
    let delivery = sealed_delivery_digest(b"the-goods-ciphertext");
    let r2 =
        fire_ship(&app, &AuthRequired::None, delivery, &cclerk, &executor).expect("a seller ships");
    assert_ne!(r2.turn_hash, [0u8; 32], "a real verified ship turn");
    let s = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        s.fields[STATE_SLOT as usize],
        field_from_u64(3),
        "STATE advanced FUNDED -> SHIPPED"
    );

    // SETTLE (the SELLER, None): cap passes, state SHIPPED passes; the fire reads live ESCROWED (800)
    // and releases it IN FULL, so the FLASHWELL AffineEq (released + refunded == escrowed) holds.
    let r3 = fire_settle(&app, &AuthRequired::None, &cclerk, &executor)
        .expect("a seller settles, conserving the escrow on the honest path");
    assert_ne!(r3.turn_hash, [0u8; 32], "a real verified settle turn");
    let s = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        s.fields[STATE_SLOT as usize],
        field_from_u64(STATE_SETTLED),
        "STATE advanced SHIPPED -> SETTLED"
    );
    assert_eq!(
        s.fields[RELEASED_SLOT as usize],
        field_from_u64(800),
        "the seller received the full escrow"
    );
}

// =============================================================================
// (c) THE HTMX TOOTH: on LISTED only `fund` lights; after fund, fund darkens + ship lights.
// =============================================================================

#[test]
fn the_lit_button_set_tracks_the_lifecycle_state_the_htmx_tooth() {
    let (cclerk, executor) = agent();
    let app = escrow_app(&cclerk, &executor);
    let _ = seed_escrow(&executor, "acme-corp", 1000);
    let cell = &app.cells()[0];

    // On LISTED: a BUYER (Either) sees `fund` LIT (listed precondition holds); `ship`/`settle` are
    // DARK (their FUNDED/SHIPPED preconditions fail). The htmx tooth off live state.
    let lit_listed = cell.gated_fireable_names(&AuthRequired::Either, &executor);
    assert!(
        lit_listed.contains(&"fund".to_string()),
        "LISTED: fund lights"
    );
    assert!(
        !lit_listed.contains(&"ship".to_string()),
        "LISTED: ship dark"
    );
    assert!(
        !lit_listed.contains(&"settle".to_string()),
        "LISTED: settle dark"
    );

    // Fund it (a real turn) — the cell transitions to FUNDED.
    fire_fund(
        &app,
        &AuthRequired::Either,
        "buyer-bob",
        800,
        &cclerk,
        &executor,
    )
    .expect("the buyer funds");

    // After fund: as the SELLER (None, the top tier), `fund` DARKENS (LISTED precondition now fails)
    // and `ship` LIGHTS (FUNDED precondition holds). Same cell, DIFFERENT button-set — because the
    // cell transitioned. The htmx tooth.
    let lit_funded = cell.gated_fireable_names(&AuthRequired::None, &executor);
    assert!(
        !lit_funded.contains(&"fund".to_string()),
        "FUNDED: fund darkens (the htmx tooth)"
    );
    assert!(
        lit_funded.contains(&"ship".to_string()),
        "FUNDED: ship lights (the htmx tooth)"
    );
    assert!(
        !lit_funded.contains(&"settle".to_string()),
        "FUNDED: settle still dark"
    );
}

// =============================================================================
// (d) THE CAP TOOTH, in-band: a buyer firing `ship` (needs None) is refused.
// =============================================================================

#[test]
fn a_buyer_cannot_fire_ship_the_cap_tooth_bites_in_band() {
    let (cclerk, executor) = agent();
    let app = escrow_app(&cclerk, &executor);
    let _ = seed_escrow(&executor, "acme-corp", 1000);
    // Fund first so the FUNDED precondition for `ship` would otherwise hold — isolating the CAP tooth.
    fire_fund(
        &app,
        &AuthRequired::Either,
        "buyer-bob",
        800,
        &cclerk,
        &executor,
    )
    .expect("the buyer funds");

    // A BUYER (Either) firing `ship` (requires None/root): the CAP tooth refuses IN-BAND (Either does
    // not attenuate to None). Nothing is submitted (anti-ghost), even though the state precondition holds.
    let refused = fire_ship(
        &app,
        &AuthRequired::Either,
        sealed_delivery_digest(b"goods"),
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
        "a buyer's ship is refused at the cap tooth in-band, got {refused:?}"
    );
    // The state did NOT advance — the refused fire committed nothing (anti-ghost).
    let s = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        s.fields[STATE_SLOT as usize],
        field_from_u64(2),
        "still FUNDED — ship never fired"
    );
}

// =============================================================================
// (e) HEADLINE TOOTH #1 — LIFECYCLE: StrictMonotonic(STATE). A no-advance/rewind settle is REFUSED.
// =============================================================================

#[test]
fn the_executor_re_enforces_a_non_advancing_state_is_refused_strictmonotonic() {
    // THE seam closed: the executor RE-ENFORCES `StrictMonotonic(STATE)` on every submitted lifecycle
    // turn. We bypass the deos precondition (build the settle effects directly) and submit a settle
    // that DOES NOT ADVANCE the state (STATE stays SHIPPED). `StrictMonotonic` is STRICT, so even a
    // no-advance bites — the executor refuses. A real executor refusal in the SUBMISSION path.
    let (cclerk, executor) = agent();
    let app = escrow_app(&cclerk, &executor);
    fund_and_ship(&app, &cclerk, &executor); // STATE == SHIPPED, escrowed 800
    let cell = cclerk.cell_id();

    // A settle that conserves the escrow (800 + 0 == 800) but leaves STATE at SHIPPED (no advance).
    // The FLASHWELL AffineEq holds, so it is the LIFECYCLE StrictMonotonic that bites.
    let mut effects = settle_effects(cell, 800, 0);
    // Rewrite the STATE effect to NOT advance (stay SHIPPED instead of SETTLED).
    for e in effects.iter_mut() {
        if let dregg_app_framework::Effect::SetField { index, value, .. } = e {
            if *index == STATE_SLOT as usize {
                *value = field_from_u64(STATE_SHIPPED);
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

    // The state did NOT change — the refused turn committed nothing (anti-ghost).
    let after = executor.cell_state(cell).unwrap();
    assert_eq!(
        after.fields[STATE_SLOT as usize],
        field_from_u64(STATE_SHIPPED),
        "the refused settle committed nothing — STATE still holds SHIPPED"
    );
}

// =============================================================================
// (f) HEADLINE TOOTH #2 — TRUSTLINE: FieldLteField(ESCROWED <= CEILING). An over-ceiling fund is REFUSED.
// =============================================================================

#[test]
fn the_executor_re_enforces_an_over_ceiling_fund_is_refused_trustline() {
    // The TRUSTLINE `FieldLteField(ESCROWED <= CEILING)` invariant, biting in the submission path. Seed
    // LISTED with ceiling 1000, then submit a fund whose ESCROWED (1500) BREACHES the ceiling — the
    // executor's `FieldLteField(ESCROWED <= CEILING)` refuses the over-draw (the buyer cannot escrow
    // past the listing's ceiling — the trustline `drawn <= line`).
    let (cclerk, executor) = agent();
    let _ = seed_escrow(&executor, "acme-corp", 1000);
    let cell = cclerk.cell_id();

    // ESCROWED := 1500, but CEILING == 1000. The fund advances STATE LISTED -> FUNDED (so the method
    // case fires) and writes the over-ceiling escrow.
    let over = starbridge_escrow_market::fund_effects(cell, "buyer-bob", 1500);
    let action = cclerk.make_action(cell, "fund", over);
    let refused = executor.submit_action(&cclerk, action);
    assert!(
        refused.is_err(),
        "escrowing past the ceiling must be refused"
    );
    let msg = format!("{:?}", refused.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("lte") || msg.contains("field") || msg.contains("program"),
        "the executor refuses on the FieldLteField(ESCROWED <= CEILING) caveat, got: {msg}"
    );

    // The escrow did NOT move (anti-ghost).
    let after = executor.cell_state(cell).unwrap();
    assert_eq!(
        after.fields[ESCROWED_SLOT as usize],
        field_from_u64(0),
        "the refused over-ceiling fund committed nothing — ESCROWED still holds 0"
    );
    assert_eq!(
        after.fields[STATE_SLOT as usize],
        field_from_u64(STATE_LISTED),
        "the refused fund committed nothing — STATE still holds LISTED"
    );
}

// =============================================================================
// (g) HEADLINE TOOTH #3 — FLASHWELL conservation: AffineEq / AffineLe. A value-conjuring settle is REFUSED.
// =============================================================================

#[test]
fn the_executor_re_enforces_a_non_conserving_settle_is_refused_flashwell() {
    // The FLASHWELL conservation teeth, biting in the submission path. The escrow holds 800. We submit
    // two non-conserving settles, each refused:
    //   - a MINTING settle (900 + 0 > 800): caught by the universal no-mint `AffineLe`;
    //   - a BURNING settle (700 + 0 < 800): passes the no-mint AffineLe but is caught by the
    //     settle-scoped no-burn `AffineEq` (the exact conservation released + refunded == escrowed).
    let (cclerk, executor) = agent();
    let app = escrow_app(&cclerk, &executor);
    fund_and_ship(&app, &cclerk, &executor); // STATE == SHIPPED, escrowed 800
    let cell = cclerk.cell_id();

    // MINT: release 900 against an 800 escrow (advancing STATE to SETTLED so the method case fires).
    let mint = settle_effects(cell, 900, 0);
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

    // BURN: release 700 against an 800 escrow — destroys 100. Passes no-mint, caught by no-burn AffineEq.
    let burn = settle_effects(cell, 700, 0);
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

    // Neither refused settle moved the state (anti-ghost) — the deal is still SHIPPED, unsettled.
    let after = executor.cell_state(cell).unwrap();
    assert_eq!(
        after.fields[STATE_SLOT as usize],
        field_from_u64(STATE_SHIPPED),
        "the refused settles committed nothing — STATE still holds SHIPPED"
    );

    // And the HONEST conserving settle (800 + 0 == 800) DOES commit through the same path.
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
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x62; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    let ctx = StarbridgeAppContext::new(cclerk.clone(), executor.clone());

    // `register_deos` folds the DeosApp into the context's affordance registry AND seeds the escrow
    // cell (program installed, LISTED state). After it, the deos surface is the SHIPPED one (the census
    // promotion) and the gated fires are live.
    let app = register_deos(&ctx);
    assert_eq!(app.name(), "escrow-market");
    assert_eq!(
        ctx.affordance_registry().len(),
        1,
        "the deos surface is registered"
    );

    // The seeded escrow is LISTED with a ceiling, so a buyer can fund through the mounted surface
    // immediately (the seam is closed + live).
    let receipt = fire_fund(
        &app,
        &AuthRequired::Either,
        "buyer-bob",
        500,
        &cclerk,
        &executor,
    )
    .expect("the mounted, seeded surface funds (the promotion is live)");
    assert_ne!(receipt.turn_hash, [0u8; 32]);
    let s = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        s.fields[ESCROWED_SLOT as usize],
        field_from_u64(500),
        "the fund committed through the mounted surface"
    );
}
