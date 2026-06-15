//! THE SEAM CLOSED — the deos-native `commit_bid` / `close_commit` / `reveal_bid` /
//! `resolve` fired through the executor against the FULL auction program, so the
//! verified caveats BITE in the fire path itself.
//!
//! The promotion's task is to close the fire→full-`CellProgram` seam so OVERWRITING a
//! committed sealed bid / rewinding the phase is a REAL executor refusal in the fire
//! path, not a `program.evaluate`-only check. `src::register_deos` / `src::seed_auction`
//! install [`auction_program`] (the canonical method-dispatched `Cases`: the
//! `WriteOnce` commit board + result registers in `Always`, the `StrictMonotonic(PHASE)`
//! lifecycle in the `close_commit` / `resolve` cases) on the seeded auction cell, and the
//! deos fire is a TWO-TEMPO bridge:
//!
//!   1. the deos PRECONDITION gate ([`DeosCell::gated_fireable_names`] — the cap-gate
//!      `is_attenuation` AND the live-state PHASE precondition `CellProgram::evaluate`)
//!      decides the button's verdict IN-BAND, nothing submitted on a miss (anti-ghost);
//!   2. on both passing, the `fire_*` fns submit the FULL multi-effect turn (built from
//!      the cell's LIVE state), and the executor RE-ENFORCES the full auction program.
//!
//! THE HEADLINE TEETH, each a real executor refusal in the SUBMISSION path:
//!   - ANTI-FRONT-RUNNING: `WriteOnce(COMMIT_BASE + i)` — overwriting a committed sealed
//!     bid is REFUSED (now an EXECUTOR refusal, not a `BTreeMap` membership check);
//!   - LIFECYCLE: `StrictMonotonic(PHASE)` — a phase that rewinds / does not advance is
//!     REFUSED (strict).
//!
//! Every fire is a real verified turn through the embedded executor; both gates are
//! genuine. No parallel model.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, Effect, EmbeddedExecutor, FireExecuteError,
    StarbridgeAppContext, field_from_u64,
};

use starbridge_sealed_auction::{
    Bid, PHASE_COMMIT, PHASE_RESOLVED, PHASE_REVEAL, PHASE_SLOT, SELLER_SLOT, WINNER_SLOT,
    auction_app, auction_program, commit_bid_effects, commit_slot, fire_close_commit,
    fire_commit_bid, fire_resolve, fire_reveal_bid, register_deos, seed_auction,
};

fn agent() -> (AppCipherclerk, EmbeddedExecutor) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x5a; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    (cclerk, executor)
}

// =============================================================================
// (a) Seeding installs the full auction program + PHASE = COMMIT.
// =============================================================================

#[test]
fn seeding_installs_the_auction_program_and_commit_phase() {
    let (cclerk, executor) = agent();
    let _ = seed_auction(&executor, "auctioneer");

    // The seeded auction cell carries the canonical auction program (the Cases shape with
    // the WriteOnce commit board + StrictMonotonic(PHASE) lifecycle), installed so the
    // executor re-enforces it.
    let installed =
        executor.with_ledger_mut(|ledger| ledger.get(&cclerk.cell_id()).map(|c| c.program.clone()));
    assert_eq!(
        installed,
        Some(auction_program()),
        "the seeded auction cell carries the auction program (the seam's enforcement layer)"
    );
    // ...and the seeded state is in COMMIT with a bound seller.
    let state = executor
        .cell_state(cclerk.cell_id())
        .expect("seeded cell exists");
    assert_eq!(
        state.fields[PHASE_SLOT],
        field_from_u64(PHASE_COMMIT),
        "PHASE seeded to COMMIT"
    );
    assert_ne!(state.fields[SELLER_SLOT], [0u8; 32], "the seller is bound");
}

// =============================================================================
// (b) commit_bid through the gated fire writes a sealed commit slot (a real turn).
// =============================================================================

#[test]
fn a_bidder_commits_a_sealed_bid_through_the_gated_fire_a_real_verified_turn() {
    let (cclerk, executor) = agent();
    let app = auction_app(&cclerk, &executor);
    let _ = seed_auction(&executor, "auctioneer");

    // A BIDDER (Either) fires `commit_bid`: the cap-gate passes (Either ⊇ Either), the
    // COMMIT precondition passes, and the FULL commit turn writes the next free WriteOnce
    // commit slot. The executor RE-ENFORCES the board. A real verified turn.
    let bid = Bid::new(10, 50, 8);
    let receipt = fire_commit_bid(&app, &AuthRequired::Either, bid.seal(), &cclerk, &executor)
        .expect("a bidder seals a bid (caps ∧ state ∧ WriteOnce board all pass)");
    assert_ne!(
        receipt.turn_hash, [0u8; 32],
        "a real verified turn through the executor"
    );

    // The seal landed on the first commit slot.
    let state = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        state.fields[commit_slot(0)],
        bid.seal(),
        "the sealed bid is on the on-ledger commit board"
    );

    // A SECOND bidder's commit lands on the NEXT free slot (the fire reads live state).
    let bid2 = Bid::new(11, 40, 9);
    fire_commit_bid(&app, &AuthRequired::Either, bid2.seal(), &cclerk, &executor)
        .expect("a second bidder seals into the next free slot");
    let state = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        state.fields[commit_slot(1)],
        bid2.seal(),
        "the second seal landed on the next free slot"
    );
    assert_eq!(
        state.fields[commit_slot(0)],
        bid.seal(),
        "the first seal is untouched (frozen)"
    );
}

// =============================================================================
// (c) THE HTMX TOOTH: in COMMIT only commit_bid/close_commit light; after close, reveal lights.
// =============================================================================

#[test]
fn the_lit_button_set_tracks_the_phase_the_htmx_tooth() {
    let (cclerk, executor) = agent();
    let app = auction_app(&cclerk, &executor);
    let _ = seed_auction(&executor, "auctioneer");
    let cell = &app.cells()[0];

    // In COMMIT: the AUCTIONEER (None, the top tier) sees `commit_bid` + `close_commit` LIT
    // (their COMMIT precondition holds); `reveal_bid` + `resolve` are DARK (their REVEAL
    // precondition fails). The htmx tooth off live state.
    let lit_commit = cell.gated_fireable_names(&AuthRequired::None, &executor);
    assert!(
        lit_commit.contains(&"commit_bid".to_string()),
        "COMMIT: commit_bid lights"
    );
    assert!(
        lit_commit.contains(&"close_commit".to_string()),
        "COMMIT: close_commit lights"
    );
    assert!(
        !lit_commit.contains(&"reveal_bid".to_string()),
        "COMMIT: reveal_bid dark"
    );
    assert!(
        !lit_commit.contains(&"resolve".to_string()),
        "COMMIT: resolve dark"
    );

    // Close the commit phase (a real turn) — the cell transitions to REVEAL.
    fire_close_commit(&app, &AuthRequired::None, &cclerk, &executor)
        .expect("the auctioneer closes the commit phase");

    // After close: `commit_bid`/`close_commit` DARKEN (COMMIT precondition now fails) and
    // `reveal_bid`/`resolve` LIGHT (REVEAL precondition holds). Same cell, DIFFERENT
    // button-set — because the cell transitioned. The htmx tooth.
    let lit_reveal = cell.gated_fireable_names(&AuthRequired::None, &executor);
    assert!(
        !lit_reveal.contains(&"commit_bid".to_string()),
        "REVEAL: commit_bid darkens (the htmx tooth)"
    );
    assert!(
        !lit_reveal.contains(&"close_commit".to_string()),
        "REVEAL: close_commit darkens"
    );
    assert!(
        lit_reveal.contains(&"reveal_bid".to_string()),
        "REVEAL: reveal_bid lights (the htmx tooth)"
    );
    assert!(
        lit_reveal.contains(&"resolve".to_string()),
        "REVEAL: resolve lights"
    );
}

// =============================================================================
// (d) THE CAP TOOTH, in-band: an observer firing `resolve` (needs None) is refused.
// =============================================================================

#[test]
fn an_observer_cannot_fire_resolve_the_cap_tooth_bites_in_band() {
    let (cclerk, executor) = agent();
    let app = auction_app(&cclerk, &executor);
    let _ = seed_auction(&executor, "auctioneer");
    // Advance to REVEAL so the `resolve` REVEAL precondition would otherwise hold —
    // isolating the CAP tooth.
    fire_close_commit(&app, &AuthRequired::None, &cclerk, &executor)
        .expect("the auctioneer closes the commit phase");

    // An OBSERVER (Signature) firing `resolve` (requires None/root): the CAP tooth refuses
    // IN-BAND (Signature does not attenuate to None). Nothing is submitted (anti-ghost),
    // even though the state precondition holds.
    let refused = fire_resolve(
        &app,
        &AuthRequired::Signature,
        field_from_u64(11),
        50,
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
        "an observer's resolve is refused at the cap tooth in-band, got {refused:?}"
    );
    // The phase did NOT advance — the refused fire committed nothing (anti-ghost).
    let s = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        s.fields[PHASE_SLOT],
        field_from_u64(PHASE_REVEAL),
        "still REVEAL — resolve never fired"
    );
}

// =============================================================================
// (e) HEADLINE TOOTH #1 — ANTI-FRONT-RUNNING: WriteOnce(commit slot). Overwrite is REFUSED.
// =============================================================================

#[test]
fn the_executor_re_enforces_overwriting_a_committed_bid_is_refused_writeonce() {
    // THE seam closed: the executor RE-ENFORCES `WriteOnce(COMMIT_BASE + i)` on every
    // submitted commit turn — not just the deos precondition. We bypass the precondition
    // (build the commit effects directly) and submit a turn that OVERWRITES an already-
    // committed bid slot. The deos precondition is not consulted; the EXECUTOR's
    // `WriteOnce(commit slot)` (installed by `seed_auction`) refuses the overwrite. This is
    // the anti-front-running headline — now an executor refusal, not a BTreeMap check.
    let (cclerk, executor) = agent();
    let app = auction_app(&cclerk, &executor);
    let _ = seed_auction(&executor, "auctioneer");
    let cell = cclerk.cell_id();

    // First, an honest sealed commit lands on slot 0.
    let bid = Bid::new(10, 50, 8);
    fire_commit_bid(&app, &AuthRequired::Either, bid.seal(), &cclerk, &executor)
        .expect("the honest sealed commit lands");

    // A peeker submits a turn OVERWRITING the committed bid slot with a different (higher) bid.
    let switched = Bid::new(10, 70, 8);
    let overwrite = commit_bid_effects(cell, commit_slot(0), &switched.seal());
    let action = cclerk.make_action(cell, "commit_bid", overwrite);
    let refused = executor.submit_action(&cclerk, action);
    assert!(
        refused.is_err(),
        "overwriting a committed sealed bid must be refused by the executor"
    );
    let msg = format!("{:?}", refused.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("writeonce") || msg.contains("write-once") || msg.contains("program"),
        "the executor refuses on the WriteOnce(commit slot) caveat, got: {msg}"
    );

    // The committed bid did NOT change (anti-ghost) — the seal stands frozen.
    let after = executor.cell_state(cell).unwrap();
    assert_eq!(
        after.fields[commit_slot(0)],
        bid.seal(),
        "the refused overwrite committed nothing — the original sealed bid stands"
    );
}

// =============================================================================
// (f) HEADLINE TOOTH #2 — LIFECYCLE: StrictMonotonic(PHASE). A rewind / no-advance is REFUSED.
// =============================================================================

#[test]
fn the_executor_re_enforces_a_phase_rewind_is_refused_strictmonotonic() {
    // The LIFECYCLE `StrictMonotonic(PHASE)` invariant, biting in the submission path. Seed
    // (PHASE COMMIT), advance to REVEAL, then submit a `resolve` that REWINDS the phase
    // (REVEAL → COMMIT) — the executor's `StrictMonotonic(PHASE)` refuses the rewind. Also a
    // reveal-phase reveal that tries to SKIP straight past (a resolve that does NOT advance)
    // bites because StrictMonotonic is strict.
    let (cclerk, executor) = agent();
    let app = auction_app(&cclerk, &executor);
    let _ = seed_auction(&executor, "auctioneer");
    let cell = cclerk.cell_id();

    fire_close_commit(&app, &AuthRequired::None, &cclerk, &executor)
        .expect("close_commit commits (PHASE 0 -> 1)");

    // REWIND: a resolve that drives PHASE REVEAL → COMMIT (the method case fires, so the
    // StrictMonotonic clause bites).
    let rewind = vec![Effect::SetField {
        cell,
        index: PHASE_SLOT,
        value: field_from_u64(PHASE_COMMIT),
    }];
    let action = cclerk.make_action(cell, "resolve", rewind);
    let refused = executor.submit_action(&cclerk, action);
    assert!(refused.is_err(), "rewinding the phase must be refused");
    let msg = format!("{:?}", refused.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("strictmonotonic")
            || msg.contains("strict")
            || msg.contains("monotonic")
            || msg.contains("program"),
        "the executor refuses on the StrictMonotonic(PHASE) caveat, got: {msg}"
    );

    // STALL: a resolve that leaves PHASE at REVEAL (no advance) — strict bites.
    let stall = vec![Effect::SetField {
        cell,
        index: PHASE_SLOT,
        value: field_from_u64(PHASE_REVEAL),
    }];
    let action = cclerk.make_action(cell, "resolve", stall);
    let refused = executor.submit_action(&cclerk, action);
    assert!(
        refused.is_err(),
        "a no-advance phase must be refused (StrictMonotonic is strict)"
    );

    // The phase did NOT change (anti-ghost).
    let after = executor.cell_state(cell).unwrap();
    assert_eq!(
        after.fields[PHASE_SLOT],
        field_from_u64(PHASE_REVEAL),
        "the refused turns committed nothing — PHASE still holds REVEAL"
    );

    // And the HONEST resolve (REVEAL → RESOLVED) DOES commit through the same path.
    let r = fire_resolve(
        &app,
        &AuthRequired::None,
        field_from_u64(11),
        50,
        &cclerk,
        &executor,
    )
    .expect("the honest resolve commits");
    assert_ne!(r.turn_hash, [0u8; 32], "a real verified resolve turn");
    let after = executor.cell_state(cell).unwrap();
    assert_eq!(
        after.fields[PHASE_SLOT],
        field_from_u64(PHASE_RESOLVED),
        "the sale RESOLVED"
    );
    assert_eq!(
        after.fields[WINNER_SLOT],
        field_from_u64(11),
        "the winner is announced"
    );
}

// =============================================================================
// (g) The full honest lifecycle through the gated fires (commit → close → reveal → resolve).
// =============================================================================

#[test]
fn the_honest_lifecycle_runs_through_the_gated_fires() {
    let (cclerk, executor) = agent();
    let app = auction_app(&cclerk, &executor);
    let _ = seed_auction(&executor, "auctioneer");

    // COMMIT (a BIDDER, Either): seal two bids.
    let bid_a = Bid::new(10, 30, 7);
    let bid_b = Bid::new(11, 50, 8);
    fire_commit_bid(
        &app,
        &AuthRequired::Either,
        bid_a.seal(),
        &cclerk,
        &executor,
    )
    .expect("A commits");
    fire_commit_bid(
        &app,
        &AuthRequired::Either,
        bid_b.seal(),
        &cclerk,
        &executor,
    )
    .expect("B commits");

    // CLOSE (the AUCTIONEER, None): seal the commit phase.
    fire_close_commit(&app, &AuthRequired::None, &cclerk, &executor).expect("close commits");

    // REVEAL (a BIDDER, Either): open the bids.
    fire_reveal_bid(
        &app,
        &AuthRequired::Either,
        field_from_u64(10),
        30,
        &cclerk,
        &executor,
    )
    .expect("A reveals");
    fire_reveal_bid(
        &app,
        &AuthRequired::Either,
        field_from_u64(11),
        50,
        &cclerk,
        &executor,
    )
    .expect("B reveals");

    // RESOLVE (the AUCTIONEER, None): announce B as the winner with the top bid.
    let r = fire_resolve(
        &app,
        &AuthRequired::None,
        field_from_u64(11),
        50,
        &cclerk,
        &executor,
    )
    .expect("resolve commits");
    assert_ne!(r.turn_hash, [0u8; 32], "a real verified resolve turn");

    let s = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        s.fields[PHASE_SLOT],
        field_from_u64(PHASE_RESOLVED),
        "RESOLVED"
    );
    assert_eq!(s.fields[WINNER_SLOT], field_from_u64(11), "B won");
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
    // auction cell (program installed, COMMIT state). After it, the deos surface is the
    // SHIPPED one and the gated fires are live.
    let app = register_deos(&ctx);
    assert_eq!(app.name(), "sealed-auction");
    assert_eq!(
        ctx.affordance_registry().len(),
        1,
        "the deos surface is registered"
    );

    // The seeded auction is in COMMIT, so a bidder can seal a bid through the mounted surface
    // immediately (the seam is closed + live).
    let bid = Bid::new(10, 50, 8);
    let receipt = fire_commit_bid(&app, &AuthRequired::Either, bid.seal(), &cclerk, &executor)
        .expect("the mounted, seeded surface seals a bid (the promotion is live)");
    assert_ne!(receipt.turn_hash, [0u8; 32]);
    let s = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        s.fields[commit_slot(0)],
        bid.seal(),
        "the sealed bid committed through the mounted surface"
    );
}
