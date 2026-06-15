//! THE SEAM CLOSED — the deos-native `submit` / `close_submissions` / `reveal` /
//! `curate` fired through the executor against the FULL gallery program, so the
//! verified caveats BITE in the fire path itself.
//!
//! The promotion's task is to close the fire->full-`CellProgram` seam so SWAPPING a
//! committed sealed submission / rewinding the phase is a REAL executor refusal in the
//! fire path, not a `program.evaluate`-only check. `src::register_deos` /
//! `src::seed_gallery` install [`gallery_program`] (the canonical method-dispatched
//! `Cases`: the `WriteOnce` submission board + result registers in `Always`, the
//! `StrictMonotonic(PHASE)` lifecycle in the `close_submissions` / `curate` cases) on
//! the seeded gallery cell, and the deos fire is a TWO-TEMPO bridge:
//!
//!   1. the deos PRECONDITION gate ([`DeosCell::gated_fireable_names`] — the cap-gate
//!      `is_attenuation` AND the live-state PHASE precondition `CellProgram::evaluate`)
//!      decides the button's verdict IN-BAND, nothing submitted on a miss (anti-ghost);
//!   2. on both passing, the `fire_*` fns submit the FULL multi-effect turn (built from
//!      the cell's LIVE state), and the executor RE-ENFORCES the full gallery program.
//!
//! THE HEADLINE TEETH, each a real executor refusal in the SUBMISSION path:
//!   - ANTI-TAMPER: `WriteOnce(SUBMIT_BASE + i)` — swapping a committed sealed
//!     submission is REFUSED (an EXECUTOR refusal, not a membership check);
//!   - LIFECYCLE: `StrictMonotonic(PHASE)` — a phase that rewinds / does not advance is
//!     REFUSED (strict).

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, Effect, EmbeddedExecutor, FireExecuteError,
    StarbridgeAppContext, field_from_u64,
};

use starbridge_gallery::{
    CURATOR_SLOT, FEATURED_SLOT, PHASE_CURATED, PHASE_REVEAL, PHASE_SLOT, PHASE_SUBMISSION,
    Submission, fire_close_submissions, fire_curate, fire_reveal, fire_submit, gallery_app,
    gallery_program, register_deos, seed_gallery, submit_effects, submit_slot,
};

fn agent() -> (AppCipherclerk, EmbeddedExecutor) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x6a; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    (cclerk, executor)
}

// =============================================================================
// (a) Seeding installs the full gallery program + PHASE = SUBMISSION.
// =============================================================================

#[test]
fn seeding_installs_the_gallery_program_and_submission_phase() {
    let (cclerk, executor) = agent();
    let _ = seed_gallery(&executor, "curator");

    let installed =
        executor.with_ledger_mut(|ledger| ledger.get(&cclerk.cell_id()).map(|c| c.program.clone()));
    assert_eq!(
        installed,
        Some(gallery_program()),
        "the seeded gallery cell carries the gallery program (the seam's enforcement layer)"
    );
    let state = executor
        .cell_state(cclerk.cell_id())
        .expect("seeded cell exists");
    assert_eq!(
        state.fields[PHASE_SLOT],
        field_from_u64(PHASE_SUBMISSION),
        "PHASE seeded to SUBMISSION"
    );
    assert_ne!(
        state.fields[CURATOR_SLOT], [0u8; 32],
        "the curator is bound"
    );
}

// =============================================================================
// (b) submit through the gated fire writes a sealed submission slot (a real turn).
// =============================================================================

#[test]
fn an_artist_submits_a_sealed_piece_through_the_gated_fire_a_real_verified_turn() {
    let (cclerk, executor) = agent();
    let app = gallery_app(&cclerk, &executor);
    let _ = seed_gallery(&executor, "curator");

    // An ARTIST (Either) fires `submit`: the cap-gate passes (Either ⊇ Either), the SUBMISSION
    // precondition passes, and the FULL submit turn writes the next free WriteOnce submission
    // slot. The executor RE-ENFORCES the board. A real verified turn.
    let sub = Submission::new(10, 50, 8);
    let receipt = fire_submit(&app, &AuthRequired::Either, sub.seal(), &cclerk, &executor)
        .expect("an artist seals a piece (caps ∧ state ∧ WriteOnce board all pass)");
    assert_ne!(
        receipt.turn_hash, [0u8; 32],
        "a real verified turn through the executor"
    );

    let state = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        state.fields[submit_slot(0)],
        sub.seal(),
        "the sealed submission is on the on-ledger board"
    );

    // A SECOND artist's submit lands on the NEXT free slot (the fire reads live state).
    let sub2 = Submission::new(11, 40, 9);
    fire_submit(&app, &AuthRequired::Either, sub2.seal(), &cclerk, &executor)
        .expect("a second artist seals into the next free slot");
    let state = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        state.fields[submit_slot(1)],
        sub2.seal(),
        "the second seal landed on the next free slot"
    );
    assert_eq!(
        state.fields[submit_slot(0)],
        sub.seal(),
        "the first seal is untouched (frozen)"
    );
}

// =============================================================================
// (c) THE HTMX TOOTH: in SUBMISSION only submit/close light; after close, reveal lights.
// =============================================================================

#[test]
fn the_lit_button_set_tracks_the_phase_the_htmx_tooth() {
    let (cclerk, executor) = agent();
    let app = gallery_app(&cclerk, &executor);
    let _ = seed_gallery(&executor, "curator");
    let cell = &app.cells()[0];

    // In SUBMISSION: the CURATOR (None, the top tier) sees `submit` + `close_submissions` LIT;
    // `reveal` + `curate` are DARK (their REVEAL precondition fails). The htmx tooth off live state.
    let lit_submission = cell.gated_fireable_names(&AuthRequired::None, &executor);
    assert!(
        lit_submission.contains(&"submit".to_string()),
        "SUBMISSION: submit lights"
    );
    assert!(
        lit_submission.contains(&"close_submissions".to_string()),
        "SUBMISSION: close lights"
    );
    assert!(
        !lit_submission.contains(&"reveal".to_string()),
        "SUBMISSION: reveal dark"
    );
    assert!(
        !lit_submission.contains(&"curate".to_string()),
        "SUBMISSION: curate dark"
    );

    // Close submissions (a real turn) — the cell transitions to REVEAL.
    fire_close_submissions(&app, &AuthRequired::None, &cclerk, &executor)
        .expect("the curator closes submissions");

    // After close: `submit`/`close` DARKEN and `reveal`/`curate` LIGHT. Same cell, DIFFERENT
    // button-set — because the cell transitioned. The htmx tooth.
    let lit_reveal = cell.gated_fireable_names(&AuthRequired::None, &executor);
    assert!(
        !lit_reveal.contains(&"submit".to_string()),
        "REVEAL: submit darkens (the htmx tooth)"
    );
    assert!(
        !lit_reveal.contains(&"close_submissions".to_string()),
        "REVEAL: close darkens"
    );
    assert!(
        lit_reveal.contains(&"reveal".to_string()),
        "REVEAL: reveal lights (the htmx tooth)"
    );
    assert!(
        lit_reveal.contains(&"curate".to_string()),
        "REVEAL: curate lights"
    );
}

// =============================================================================
// (d) THE CAP TOOTH, in-band: a visitor firing `curate` (needs None) is refused.
// =============================================================================

#[test]
fn a_visitor_cannot_fire_curate_the_cap_tooth_bites_in_band() {
    let (cclerk, executor) = agent();
    let app = gallery_app(&cclerk, &executor);
    let _ = seed_gallery(&executor, "curator");
    // Advance to REVEAL so the `curate` REVEAL precondition would otherwise hold — isolating the CAP tooth.
    fire_close_submissions(&app, &AuthRequired::None, &cclerk, &executor)
        .expect("the curator closes submissions");

    // A VISITOR (Signature) firing `curate` (requires None/root): the CAP tooth refuses IN-BAND
    // (Signature does not attenuate to None). Nothing is submitted (anti-ghost).
    let refused = fire_curate(
        &app,
        &AuthRequired::Signature,
        field_from_u64(11),
        Submission::new(11, 50, 8).seal(),
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
        "a visitor's curate is refused at the cap tooth in-band, got {refused:?}"
    );
    let s = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        s.fields[PHASE_SLOT],
        field_from_u64(PHASE_REVEAL),
        "still REVEAL — curate never fired"
    );
}

// =============================================================================
// (e) HEADLINE TOOTH #1 — ANTI-TAMPER: WriteOnce(submission slot). A swap is REFUSED.
// =============================================================================

#[test]
fn the_executor_re_enforces_swapping_a_committed_submission_is_refused_writeonce() {
    // THE seam closed: the executor RE-ENFORCES `WriteOnce(SUBMIT_BASE + i)` on every submitted
    // submit turn — not just the deos precondition. We bypass the precondition (build the submit
    // effects directly) and submit a turn that SWAPS an already-committed submission slot. The
    // EXECUTOR's `WriteOnce(submission slot)` refuses the swap. This is the anti-tamper headline.
    let (cclerk, executor) = agent();
    let app = gallery_app(&cclerk, &executor);
    let _ = seed_gallery(&executor, "curator");
    let cell = cclerk.cell_id();

    // First, an honest sealed submission lands on slot 0.
    let sub = Submission::new(10, 50, 8);
    fire_submit(&app, &AuthRequired::Either, sub.seal(), &cclerk, &executor)
        .expect("the honest sealed submission lands");

    // A swapper submits a turn SWAPPING the committed slot with a different piece.
    let swapped = Submission::new(10, 70, 8);
    let overwrite = submit_effects(cell, submit_slot(0), &swapped.seal());
    let action = cclerk.make_action(cell, "submit", overwrite);
    let refused = executor.submit_action(&cclerk, action);
    assert!(
        refused.is_err(),
        "swapping a committed sealed submission must be refused by the executor"
    );
    let msg = format!("{:?}", refused.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("writeonce") || msg.contains("write-once") || msg.contains("program"),
        "the executor refuses on the WriteOnce(submission slot) caveat, got: {msg}"
    );

    let after = executor.cell_state(cell).unwrap();
    assert_eq!(
        after.fields[submit_slot(0)],
        sub.seal(),
        "the refused swap committed nothing — the original sealed submission stands"
    );
}

// =============================================================================
// (f) HEADLINE TOOTH #2 — LIFECYCLE: StrictMonotonic(PHASE). A rewind / no-advance is REFUSED.
// =============================================================================

#[test]
fn the_executor_re_enforces_a_phase_rewind_is_refused_strictmonotonic() {
    let (cclerk, executor) = agent();
    let app = gallery_app(&cclerk, &executor);
    let _ = seed_gallery(&executor, "curator");
    let cell = cclerk.cell_id();

    fire_close_submissions(&app, &AuthRequired::None, &cclerk, &executor)
        .expect("close_submissions commits (PHASE 0 -> 1)");

    // REWIND: a curate that drives PHASE REVEAL -> SUBMISSION (the method case fires).
    let rewind = vec![Effect::SetField {
        cell,
        index: PHASE_SLOT,
        value: field_from_u64(PHASE_SUBMISSION),
    }];
    let action = cclerk.make_action(cell, "curate", rewind);
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

    // STALL: a curate that leaves PHASE at REVEAL (no advance) — strict bites.
    let stall = vec![Effect::SetField {
        cell,
        index: PHASE_SLOT,
        value: field_from_u64(PHASE_REVEAL),
    }];
    let action = cclerk.make_action(cell, "curate", stall);
    let refused = executor.submit_action(&cclerk, action);
    assert!(
        refused.is_err(),
        "a no-advance phase must be refused (StrictMonotonic is strict)"
    );

    let after = executor.cell_state(cell).unwrap();
    assert_eq!(
        after.fields[PHASE_SLOT],
        field_from_u64(PHASE_REVEAL),
        "the refused turns committed nothing — PHASE still holds REVEAL"
    );

    // And the HONEST curate (REVEAL -> CURATED) DOES commit through the same path.
    let featured = Submission::new(11, 50, 8);
    let r = fire_curate(
        &app,
        &AuthRequired::None,
        field_from_u64(11),
        featured.seal(),
        &cclerk,
        &executor,
    )
    .expect("the honest curate commits");
    assert_ne!(r.turn_hash, [0u8; 32], "a real verified curate turn");
    let after = executor.cell_state(cell).unwrap();
    assert_eq!(
        after.fields[PHASE_SLOT],
        field_from_u64(PHASE_CURATED),
        "the call CURATED"
    );
    assert_eq!(
        after.fields[FEATURED_SLOT],
        field_from_u64(11),
        "the featured artist is announced"
    );
}

// =============================================================================
// (g) The full honest lifecycle through the gated fires (submit → close → reveal → curate).
// =============================================================================

#[test]
fn the_honest_lifecycle_runs_through_the_gated_fires() {
    let (cclerk, executor) = agent();
    let app = gallery_app(&cclerk, &executor);
    let _ = seed_gallery(&executor, "curator");

    // SUBMISSION (an ARTIST, Either): seal two pieces.
    let sub_a = Submission::new(10, 30, 7);
    let sub_b = Submission::new(11, 50, 8);
    fire_submit(
        &app,
        &AuthRequired::Either,
        sub_a.seal(),
        &cclerk,
        &executor,
    )
    .expect("A submits");
    fire_submit(
        &app,
        &AuthRequired::Either,
        sub_b.seal(),
        &cclerk,
        &executor,
    )
    .expect("B submits");

    // CLOSE (the CURATOR, None): close the call.
    fire_close_submissions(&app, &AuthRequired::None, &cclerk, &executor).expect("close commits");

    // REVEAL (an ARTIST, Either): open the pieces.
    fire_reveal(
        &app,
        &AuthRequired::Either,
        field_from_u64(10),
        30,
        &cclerk,
        &executor,
    )
    .expect("A reveals");
    fire_reveal(
        &app,
        &AuthRequired::Either,
        field_from_u64(11),
        50,
        &cclerk,
        &executor,
    )
    .expect("B reveals");

    // CURATE (the CURATOR, None): feature B's piece.
    let r = fire_curate(
        &app,
        &AuthRequired::None,
        field_from_u64(11),
        sub_b.seal(),
        &cclerk,
        &executor,
    )
    .expect("curate commits");
    assert_ne!(r.turn_hash, [0u8; 32], "a real verified curate turn");

    let s = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        s.fields[PHASE_SLOT],
        field_from_u64(PHASE_CURATED),
        "CURATED"
    );
    assert_eq!(s.fields[FEATURED_SLOT], field_from_u64(11), "B is featured");
}

// =============================================================================
// register_deos mounts the surface AND seeds the cell (the promotion is live).
// =============================================================================

#[test]
fn register_deos_mounts_the_seeded_surface_into_the_context() {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x6a; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    let ctx = StarbridgeAppContext::new(cclerk.clone(), executor.clone());

    let app = register_deos(&ctx);
    assert_eq!(app.name(), "gallery");
    assert_eq!(
        ctx.affordance_registry().len(),
        1,
        "the deos surface is registered"
    );

    // The seeded gallery is in SUBMISSION, so an artist can seal a piece through the mounted
    // surface immediately (the seam is closed + live).
    let sub = Submission::new(10, 50, 8);
    let receipt = fire_submit(&app, &AuthRequired::Either, sub.seal(), &cclerk, &executor)
        .expect("the mounted, seeded surface seals a piece (the promotion is live)");
    assert_ne!(receipt.turn_hash, [0u8; 32]);
    let s = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        s.fields[submit_slot(0)],
        sub.seal(),
        "the sealed submission committed through the mounted surface"
    );
}
