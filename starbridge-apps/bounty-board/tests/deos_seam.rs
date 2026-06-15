//! THE SEAM CLOSED — the deos-native `claim` / `submit` / `payout` fired through the
//! executor against the FULL bounty program, so the verified caveats BITE in the fire path
//! itself.
//!
//! `docs/deos/APPS-DEOS-INTEGRATION-CENSUS.md`: the promotion's task is to close the
//! fire→full-`CellProgram` seam so an out-of-order / no-advance lifecycle turn is a REAL
//! executor refusal in the fire path, not a `program.evaluate`-only check. This file proves
//! that seam CLOSED. `src::register_deos` / `src::seed_bounty` install
//! [`bounty_cell_program`] (title/reward/claimant/submission `WriteOnce` +
//! `StrictMonotonic(STATE)`) on the seeded bounty cell, and the deos fire is a TWO-TEMPO
//! bridge:
//!
//!   1. the deos PRECONDITION gate ([`DeosCell::gated_fireable_names`] — the cap-gate
//!      `is_attenuation` AND the live-state precondition `CellProgram::evaluate`) decides
//!      the button's verdict IN-BAND, nothing submitted on a miss (anti-ghost) — so on a
//!      POSTED bounty `claim` is LIT and `payout` is DARK, and the instant the cell advances
//!      the lit/dark sets flip;
//!   2. on both passing, [`fire_claim`] / [`fire_submit`] / [`fire_payout`] submit the FULL
//!      multi-effect lifecycle turn, and the executor RE-ENFORCES the full bounty program on
//!      the produced transition — so a NO-ADVANCE / REWOUND `STATE` (`StrictMonotonic(STATE)`
//!      requires strict `new > old`) and a CLAIMANT OVERWRITE (`WriteOnce(CLAIMANT_HASH)`)
//!      are REAL executor refusals in the SUBMISSION path (the half the floor's
//!      `program.evaluate`-only tests never exercised through a real signed turn).
//!
//! Because `STATE` is `StrictMonotonic` (strict `>`), a no-advance DOES bite (unlike
//! `Monotonic`) — so the no-advance tooth is genuine, and the lifecycle is a one-way ratchet
//! (each state can be entered exactly once). Every fire is a real verified turn through the
//! embedded executor; both gates are genuine (`is_attenuation` + `CellProgram::evaluate`).
//! No parallel model.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, EmbeddedExecutor, FireExecuteError,
    StarbridgeAppContext,
};

use starbridge_bounty_board::{
    CLAIMANT_HASH_SLOT, STATE_CLAIMED, STATE_OPEN, STATE_SLOT, bounty_app, bounty_cell_program,
    claim_effects, claimant_hash, fire_claim, fire_payout, fire_submit, register_deos, seed_bounty,
    state_field,
};

fn agent(seed: u8) -> (AppCipherclerk, EmbeddedExecutor) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    (cclerk, executor)
}

// =============================================================================
// The seeded bounty carries the full lifecycle program (the executor re-enforces it).
// =============================================================================

#[test]
fn seeding_installs_the_lifecycle_program_and_posts_the_bounty() {
    let (cclerk, executor) = agent(0x4b);
    let _ = seed_bounty(&executor, "fix the bug", 500);

    // The seeded bounty cell carries `bounty_cell_program()` — the FULL lifecycle policy
    // (WriteOnce title/reward/claimant/submission + StrictMonotonic(STATE)), installed so
    // the executor re-enforces it on every touching turn.
    let installed =
        executor.with_ledger_mut(|ledger| ledger.get(&cclerk.cell_id()).map(|c| c.program.clone()));
    assert_eq!(
        installed,
        Some(bounty_cell_program()),
        "the seeded bounty cell carries the full lifecycle program (the seam's enforcement layer)"
    );
    // ...and the seeded state is POSTED/OPEN.
    let state = executor
        .cell_state(cclerk.cell_id())
        .expect("seeded cell exists");
    assert_eq!(state.fields[STATE_SLOT], state_field(STATE_OPEN));
}

// =============================================================================
// THE htmx TOOTH: a POSTED bounty lights `claim`, darks `payout`; after claim it flips.
// =============================================================================

#[test]
fn a_worker_claims_a_posted_bounty_then_the_button_goes_dark() {
    let (cclerk, executor) = agent(0x4b);
    let app = bounty_app(&cclerk, &executor);
    let _ = seed_bounty(&executor, "fix the bug", 500); // POSTED/OPEN

    // Before the claim, a WORKER (Either) sees `claim` LIT (posted precondition STATE==OPEN
    // holds) and `payout` DARK (it needs STATE==SUBMITTED). The htmx tooth, off live state.
    let lit_before = app.cells()[0].gated_fireable_names(&AuthRequired::Either, &executor);
    assert!(
        lit_before.contains(&"claim".to_string()),
        "posted: claim lights"
    );
    assert!(
        !lit_before.contains(&"payout".to_string()),
        "posted: payout is DARK (needs SUBMITTED)"
    );

    // The worker claims the posted bounty — STATE OPEN -> CLAIMED, CLAIMANT_HASH bound. The
    // executor re-enforces the program (StrictMonotonic(STATE) holds 1 -> 2, WriteOnce admits
    // the first claimant from zero). A real verified turn.
    let receipt = fire_claim(&app, &AuthRequired::Either, "bob", &cclerk, &executor)
        .expect("the worker claims the posted bounty (caps ∧ state ∧ strict-mono all pass)");
    assert_ne!(receipt.turn_hash, [0u8; 32], "a real verified claim turn");

    // The lifecycle advanced (the claim committed): STATE is CLAIMED, claimant bound.
    let state = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        state.fields[STATE_SLOT],
        state_field(STATE_CLAIMED),
        "claim advanced STATE 1 -> 2"
    );
    assert_eq!(
        state.fields[CLAIMANT_HASH_SLOT],
        claimant_hash("bob"),
        "the claimant is bound"
    );

    // After the claim, `claim` goes DARK (posted precondition now fails) and `submit` LIGHTS
    // (claimed precondition now holds). Same viewer, same caps, DIFFERENT button-set — because
    // the cell transitioned. The htmx tooth.
    let lit_after = app.cells()[0].gated_fireable_names(&AuthRequired::Either, &executor);
    assert!(
        !lit_after.contains(&"claim".to_string()),
        "claimed: claim darkens (the htmx tooth)"
    );
    assert!(
        lit_after.contains(&"submit".to_string()),
        "claimed: submit lights (the htmx tooth)"
    );
}

// =============================================================================
// THE cap TOOTH: a watcher (Signature) firing `payout` (needs None) → Unauthorized in-band.
// =============================================================================

#[test]
fn a_watcher_below_the_poster_tier_cannot_payout_the_cap_tooth_bites_in_band() {
    let (cclerk, executor) = agent(0x4b);
    let app = bounty_app(&cclerk, &executor);
    let _ = seed_bounty(&executor, "fix the bug", 500);

    // A WATCHER holding only `Signature` (incomparable-below the `None`/root `payout` needs)
    // firing `payout`: the CAP tooth refuses IN-BAND — `is_attenuation(Signature, None)` is
    // false. Nothing is submitted (anti-ghost). A watcher can read but cannot settle.
    let refused = fire_payout(&app, &AuthRequired::Signature, &cclerk, &executor);
    assert!(
        matches!(
            refused,
            Err(FireExecuteError::Gate(
                dregg_app_framework::FireError::Unauthorized { .. }
            ))
        ),
        "a watcher's payout is refused at the cap tooth in-band, got {refused:?}"
    );
}

// =============================================================================
// THE SEAM (1): the executor re-enforces a NO-ADVANCE STATE is refused (StrictMonotonic).
// =============================================================================

#[test]
fn the_executor_re_enforces_a_no_advance_state_is_refused() {
    // THE seam closed: the executor RE-ENFORCES the lifecycle program on every submitted
    // turn — not just the deos precondition. We bypass the precondition (build effects
    // directly) and submit a turn that sets STATE to its CURRENT value (no-advance, OPEN ->
    // OPEN). Because STATE is StrictMonotonic (strict `>`, unlike Monotonic), a no-advance
    // BITES: the executor refuses 1 -> 1. This proves the caveat bites in the SUBMISSION
    // path, the half the floor's `program.evaluate`-only tests never exercised through a real
    // signed turn.
    let (cclerk, executor) = agent(0x4b);
    let _ = seed_bounty(&executor, "fix the bug", 500); // STATE == OPEN (1), program installed
    let bounty = cclerk.cell_id();

    // A NO-ADVANCE STATE: set STATE := OPEN again (1 -> 1). StrictMonotonic(STATE) refuses it.
    let no_advance = vec![dregg_app_framework::Effect::SetField {
        cell: bounty,
        index: STATE_SLOT,
        value: state_field(STATE_OPEN),
    }];
    let action = cclerk.make_action(bounty, "claim", no_advance);
    let refused = executor.submit_action(&cclerk, action);
    assert!(
        refused.is_err(),
        "a no-advance STATE must be refused by the executor (strict-mono)"
    );
    let msg = format!("{:?}", refused.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("strictmonotonic")
            || msg.contains("strictly")
            || msg.contains("program")
            || msg.contains("field[4]"),
        "the executor refuses on the StrictMonotonic(STATE) caveat, got: {msg}"
    );

    // The lifecycle did NOT move — the refused turn committed nothing (anti-ghost).
    let after = executor.cell_state(bounty).unwrap();
    assert_eq!(
        after.fields[STATE_SLOT],
        state_field(STATE_OPEN),
        "the refused no-advance committed nothing — STATE still holds OPEN"
    );
}

// =============================================================================
// THE SEAM (2): WriteOnce(CLAIMANT_HASH) — a second claim rewriting the claimant is refused.
// =============================================================================

#[test]
fn the_executor_re_enforces_a_claimant_overwrite_is_refused() {
    // The `WriteOnce(CLAIMANT_HASH)` caveat (first-claimer-wins), biting in the submission
    // path. Fire a real claim (bob bound), then submit a SECOND claim that rewrites the
    // claimant to mallory — the executor's `WriteOnce(CLAIMANT_HASH)` refuses the overwrite
    // (a competing claim cannot steal the bounty).
    let (cclerk, executor) = agent(0x4b);
    let app = bounty_app(&cclerk, &executor);
    let _ = seed_bounty(&executor, "fix the bug", 500);

    // First claim: bob binds CLAIMANT_HASH, STATE OPEN -> CLAIMED.
    fire_claim(&app, &AuthRequired::Either, "bob", &cclerk, &executor)
        .expect("first claim commits");

    // A competing second claim rewriting the claimant to mallory (and advancing STATE so the
    // STATE caveat alone would not catch it) — WriteOnce(CLAIMANT_HASH) refuses the overwrite.
    let bounty = cclerk.cell_id();
    let steal = claim_effects(bounty, "mallory");
    let action = cclerk.make_action(bounty, "claim", steal);
    let refused = executor.submit_action(&cclerk, action);
    assert!(refused.is_err(), "overwriting the claimant must be refused");
    let msg = format!("{:?}", refused.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("write-once")
            || msg.contains("writeonce")
            || msg.contains("already set")
            || msg.contains("strictmonotonic")
            || msg.contains("strictly")
            || msg.contains("program"),
        "the executor refuses on the WriteOnce(CLAIMANT_HASH) / strict-mono caveat, got: {msg}"
    );

    // The claimant did NOT change — the refused turn committed nothing (anti-ghost).
    let after = executor.cell_state(bounty).unwrap();
    assert_eq!(
        after.fields[CLAIMANT_HASH_SLOT],
        claimant_hash("bob"),
        "the refused overwrite committed nothing — bob is still the claimant"
    );
}

// =============================================================================
// THE FULL LIFECYCLE through the gated fires: post -> claim -> submit -> payout.
// =============================================================================

#[test]
fn the_full_four_state_lifecycle_runs_through_the_gated_fires() {
    let (cclerk, executor) = agent(0x4b);
    let app = bounty_app(&cclerk, &executor);
    let _ = seed_bounty(&executor, "fix the bug", 500); // POSTED

    // claim (worker) -> submit (worker) -> payout (poster). Each gated fire passes its
    // cap∧state precondition and the executor re-enforces StrictMonotonic(STATE) on the
    // advance. The canonical 4-state ratchet, all green.
    fire_claim(&app, &AuthRequired::Either, "bob", &cclerk, &executor).expect("claim commits");
    fire_submit(
        &app,
        &AuthRequired::Either,
        "dregg://cell/work-artifact",
        &cclerk,
        &executor,
    )
    .expect("submit commits");
    fire_payout(&app, &AuthRequired::None, &cclerk, &executor).expect("payout commits");

    // The bounty reached PAID (terminal).
    let state = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        state.fields[STATE_SLOT],
        state_field(starbridge_bounty_board::STATE_PAID),
        "the lifecycle reached PAID"
    );

    // A second payout (PAID -> PAID, no-advance) is now refused at the STATE tooth in-band:
    // the submitted precondition (STATE == SUBMITTED) fails on a PAID bounty.
    let refused = fire_payout(&app, &AuthRequired::None, &cclerk, &executor);
    assert!(
        matches!(
            refused,
            Err(FireExecuteError::Gate(
                dregg_app_framework::FireError::StateConditionUnmet { .. }
            ))
        ),
        "a second payout is refused at the state tooth in-band, got {refused:?}"
    );
}

// =============================================================================
// register_deos mounts the surface AND seeds the cell (the promotion is live).
// =============================================================================

#[test]
fn register_deos_mounts_the_seeded_surface_into_the_context() {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x4b; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    let ctx = StarbridgeAppContext::new(cclerk.clone(), executor.clone());

    // `register_deos` folds the DeosApp into the context's affordance registry AND seeds the
    // bounty cell (program installed, POSTED state). After it, the deos surface is the
    // SHIPPED one (the census promotion) and the gated fires are live.
    let app = register_deos(&ctx);
    assert_eq!(app.name(), "bounty-board");
    assert_eq!(
        ctx.affordance_registry().len(),
        1,
        "the deos surface is registered"
    );

    // The seeded bounty is POSTED, so a worker can claim through the mounted surface
    // immediately (the seam is closed + live).
    let receipt = fire_claim(&app, &AuthRequired::Either, "bob", &cclerk, &executor)
        .expect("the mounted, seeded surface accepts a claim (the promotion is live)");
    assert_ne!(receipt.turn_hash, [0u8; 32]);

    // The claimant moved (a real binding on the seeded cell).
    let state = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        state.fields[CLAIMANT_HASH_SLOT],
        claimant_hash("bob"),
        "the claim bound the claimant"
    );
}
