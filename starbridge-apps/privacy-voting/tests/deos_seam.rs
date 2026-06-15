//! THE SEAM CLOSED — the deos-native `cast_vote` / `record_tally` / `close_poll` fired
//! through the executor against the FULL slot caveats, so the verified caveats BITE in the
//! fire path itself.
//!
//! `docs/deos/APPS-DEOS-INTEGRATION-CENSUS.md`: the promotion's task is to close the
//! fire→full-`CellProgram` seam so a double vote / tally rewind / poll re-open is a REAL
//! executor refusal in the fire path, not an `evaluate`-only check. This file proves that
//! seam CLOSED on a TWO-CELL app. `src::register_deos` / `src::seed_poll` / `src::seed_ballot`
//! install the poll program (`Monotonic(TALLY_*)` + `WriteOnce(CLOSED)`) and the ballot
//! program (`WriteOnce(VOTE)`) on the seeded cells, and the deos fire is a TWO-TEMPO bridge:
//!
//!   1. the deos PRECONDITION gate ([`DeosCell::gated_fireable_names`] — the cap-gate
//!      `is_attenuation` AND the live-state precondition `CellProgram::evaluate`) decides the
//!      button's verdict IN-BAND, nothing submitted on a miss (anti-ghost);
//!   2. on both passing, [`fire_cast_vote`] / [`fire_record_tally`] / [`fire_close_poll`]
//!      submit the FULL turn, and the executor RE-ENFORCES the installed caveats on the
//!      produced transition — so a SECOND cast_vote rewriting `VOTE` (`WriteOnce(VOTE)`), a
//!      tally REWIND (`Monotonic(TALLY_YES)`), and a poll RE-OPEN (`CLOSED` 1->0,
//!      `WriteOnce(CLOSED)`) are REAL executor refusals in the SUBMISSION path (the half the
//!      floor's `evaluate`-only tests never exercised through a real signed turn).
//!
//! Every fire is a real verified turn through the embedded executor; both gates are genuine
//! (`is_attenuation` + `CellProgram::evaluate`). No parallel model. Run `--release` (the
//! embedded executor is slow in debug).

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, EmbeddedExecutor, FireExecuteError,
    StarbridgeAppContext, field_from_u64,
};

use starbridge_privacy_voting::{
    CLOSED_SLOT, POLL_REF_SLOT, TALLY_YES_SLOT, VOTE_NO, VOTE_SLOT, VOTE_YES, ballot_cell_id,
    ballot_cell_program, fire_cast_vote, fire_close_poll, fire_record_tally, poll_cell_program,
    poll_ref, register_deos, seed_ballot, seed_poll, voting_app,
};

fn agent(seed: u8) -> (AppCipherclerk, EmbeddedExecutor) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    (cclerk, executor)
}

// =============================================================================
// (a) Seeding installs BOTH programs + state (the executor re-enforces them).
// =============================================================================

#[test]
fn seeding_installs_both_programs_and_state() {
    let (cclerk, executor) = agent(0x71);
    let poll = cclerk.cell_id();
    seed_poll(&executor, "ship it?");
    let ballot = seed_ballot(&executor, &cclerk, poll);

    // The POLL cell carries the poll program (Monotonic tallies + WriteOnce question/closed).
    let poll_program_installed =
        executor.with_ledger_mut(|ledger| ledger.get(&poll).map(|c| c.program.clone()));
    assert_eq!(
        poll_program_installed,
        Some(poll_cell_program()),
        "the seeded poll cell carries the poll program (the seam's enforcement layer)"
    );

    // The BALLOT companion cell carries the ballot program (WriteOnce poll_ref/vote), and is
    // bound to the poll (POLL_REF set) with VOTE unset.
    let ballot_program_installed =
        executor.with_ledger_mut(|ledger| ledger.get(&ballot).map(|c| c.program.clone()));
    assert_eq!(
        ballot_program_installed,
        Some(ballot_cell_program()),
        "the seeded ballot companion cell carries the ballot program"
    );
    let ballot_state = executor.cell_state(ballot).expect("ballot seeded");
    assert_eq!(
        ballot_state.fields[POLL_REF_SLOT],
        poll_ref(poll),
        "the ballot is bound to the poll"
    );
    assert_eq!(
        ballot_state.fields[VOTE_SLOT],
        field_from_u64(0),
        "the ballot is unset"
    );
}

// =============================================================================
// (b) cast_vote through the gated fire writes VOTE (a real verified turn).
// =============================================================================

#[test]
fn a_voter_casts_a_vote_through_the_gated_fire_a_real_verified_turn() {
    let (cclerk, executor) = agent(0x71);
    let app = voting_app(&cclerk, &executor);
    let poll = cclerk.cell_id();
    seed_poll(&executor, "ship it?");
    let ballot = seed_ballot(&executor, &cclerk, poll);

    // A VOTER (Either) fires `cast_vote`: the cap-gate passes (Either ⊇ Either), the
    // live-state precondition passes (VOTE == 0, the ballot is unset), and the FULL vote turn
    // writes the choice. The executor RE-ENFORCES `WriteOnce(VOTE)` (admits the first write
    // from zero). A real verified turn.
    let receipt = fire_cast_vote(&app, &AuthRequired::Either, VOTE_YES, &cclerk, &executor)
        .expect("a voter casts a vote (caps ∧ state ∧ write-once-from-zero all pass)");
    assert_ne!(
        receipt.turn_hash, [0u8; 32],
        "a real verified turn through the executor"
    );

    // The ballot's VOTE slot now holds the choice (the vote committed).
    let state = executor.cell_state(ballot).unwrap();
    assert_eq!(
        state.fields[VOTE_SLOT],
        field_from_u64(VOTE_YES),
        "cast_vote wrote the choice into the ballot VOTE slot"
    );
}

// =============================================================================
// (c) the htmx tooth: a second cast_vote is DARK; the cap tooth: a viewer cannot vote.
// =============================================================================

#[test]
fn a_second_cast_vote_is_dark_the_htmx_tooth() {
    let (cclerk, executor) = agent(0x71);
    let app = voting_app(&cclerk, &executor);
    let poll = cclerk.cell_id();
    seed_poll(&executor, "ship it?");
    let ballot = seed_ballot(&executor, &cclerk, poll);
    let ballot_cell = app.cell(&ballot).expect("the ballot cell");

    // Before voting, a VOTER (Either) sees `cast_vote` LIT (unset precondition VOTE == 0).
    let lit_before = ballot_cell.gated_fireable_names(&AuthRequired::Either, &executor);
    assert!(
        lit_before.contains(&"cast_vote".to_string()),
        "unset ballot: cast_vote lights"
    );

    // Cast the vote — VOTE 0 -> YES.
    fire_cast_vote(&app, &AuthRequired::Either, VOTE_YES, &cclerk, &executor)
        .expect("the first vote commits");

    // After voting, the unset precondition (VOTE == 0) now FAILS, so `cast_vote` goes DARK.
    // Same viewer, same caps, DIFFERENT button-set — one vote per ballot, visible in the
    // surface (the htmx tooth).
    let lit_after = ballot_cell.gated_fireable_names(&AuthRequired::Either, &executor);
    assert!(
        !lit_after.contains(&"cast_vote".to_string()),
        "voted ballot: cast_vote darkens (the htmx tooth — one vote per ballot)"
    );
}

#[test]
fn a_viewer_below_the_voter_tier_cannot_cast_vote_the_cap_tooth_bites_in_band() {
    let (cclerk, executor) = agent(0x71);
    let app = voting_app(&cclerk, &executor);
    let poll = cclerk.cell_id();
    seed_poll(&executor, "ship it?");
    let _ = seed_ballot(&executor, &cclerk, poll);

    // A bearer holding NO authority (`AuthRequired::Custom`, incomparable to Either) firing
    // `cast_vote` (requires Either): the CAP tooth refuses IN-BAND. Nothing submitted
    // (anti-ghost). A viewer can read but not vote.
    let refused = fire_cast_vote(
        &app,
        &AuthRequired::Custom { vk_hash: [7u8; 32] },
        VOTE_YES,
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
        "a sub-voter's cast_vote is refused at the cap tooth in-band, got {refused:?}"
    );
}

// =============================================================================
// (d) THE seam: WriteOnce(VOTE) — a turn rewriting the ballot's VOTE is REFUSED.
// =============================================================================

#[test]
fn the_executor_re_enforces_a_double_vote_is_refused() {
    // THE seam closed: the executor RE-ENFORCES `WriteOnce(VOTE)` on every submitted turn
    // touching the ballot — not just the deos precondition. We cast once through the gated
    // fire, then bypass the precondition (build the rewrite directly) and submit a turn that
    // REWRITES the committed VOTE (YES -> NO) — the no-double-vote tooth. The deos
    // precondition is not consulted; the EXECUTOR's `WriteOnce(VOTE)` (installed by
    // `seed_ballot`) refuses it.
    let (cclerk, executor) = agent(0x71);
    let app = voting_app(&cclerk, &executor);
    let poll = cclerk.cell_id();
    seed_poll(&executor, "ship it?");
    let ballot = seed_ballot(&executor, &cclerk, poll);

    // First vote through the gated fire: YES, committed.
    fire_cast_vote(&app, &AuthRequired::Either, VOTE_YES, &cclerk, &executor)
        .expect("the first vote commits (VOTE 0 -> YES)");

    // A double vote: rewrite the committed VOTE from YES to NO. `WriteOnce(VOTE)` refuses it.
    let rewrite = vec![dregg_app_framework::Effect::SetField {
        cell: ballot,
        index: VOTE_SLOT,
        value: field_from_u64(VOTE_NO),
    }];
    let action = cclerk.make_action(ballot, "cast_vote", rewrite);
    let refused = executor.submit_action(&cclerk, action);
    assert!(
        refused.is_err(),
        "rewriting a committed vote (a double vote) must be refused"
    );
    let msg = format!("{:?}", refused.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("writeonce")
            || msg.contains("write-once")
            || msg.contains("program")
            || msg.contains("field[3]"),
        "the executor refuses on the WriteOnce(VOTE) caveat, got: {msg}"
    );

    // The committed vote did NOT change — the refused turn committed nothing (anti-ghost).
    let after = executor.cell_state(ballot).unwrap();
    assert_eq!(
        after.fields[VOTE_SLOT],
        field_from_u64(VOTE_YES),
        "the refused double vote committed nothing — the ballot still holds YES"
    );
}

// =============================================================================
// (e) Monotonic(TALLY_YES) — a tally that REWINDS a count is REFUSED (rewind, not no-op).
// =============================================================================

#[test]
fn the_executor_re_enforces_a_tally_rewind_is_refused() {
    // The `Monotonic(TALLY_YES)` caveat, biting in the submission path. Seed (open poll,
    // tallies 0), bump the YES tally to 1 through the gated fire, then submit a tally turn
    // that ROLLS THE COUNT BACK to 0 (forging room to erase a vote). `Monotonic` is `>=`, so
    // a REWIND (not a no-op) is refused.
    let (cclerk, executor) = agent(0x71);
    let app = voting_app(&cclerk, &executor);
    let poll = cclerk.cell_id();
    seed_poll(&executor, "ship it?");
    let _ = seed_ballot(&executor, &cclerk, poll);

    // The ADMINISTRATOR (root) bumps the YES tally 0 -> 1 through the gated fire.
    fire_record_tally(&app, &AuthRequired::None, VOTE_YES, &cclerk, &executor)
        .expect("the administrator records a YES tally (0 -> 1)");
    let mid = executor.cell_state(poll).unwrap();
    assert_eq!(
        mid.fields[TALLY_YES_SLOT],
        field_from_u64(1),
        "the tally advanced 0 -> 1"
    );

    // A rewind: tally := 0 (< the committed 1). `Monotonic(TALLY_YES)` refuses 1 -> 0.
    let rewind = vec![dregg_app_framework::Effect::SetField {
        cell: poll,
        index: TALLY_YES_SLOT,
        value: field_from_u64(0),
    }];
    let action = cclerk.make_action(poll, "record_tally", rewind);
    let refused = executor.submit_action(&cclerk, action);
    assert!(
        refused.is_err(),
        "rewinding a tally to erase a vote must be refused"
    );
    let msg = format!("{:?}", refused.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("monotonic") || msg.contains("program") || msg.contains("field[3]"),
        "the executor refuses on the Monotonic(TALLY_YES) caveat, got: {msg}"
    );

    // The tally still holds the committed 1 (anti-ghost).
    let after = executor.cell_state(poll).unwrap();
    assert_eq!(
        after.fields[TALLY_YES_SLOT],
        field_from_u64(1),
        "the refused rewind committed nothing — the tally still holds 1"
    );
}

// =============================================================================
// (f) WriteOnce(CLOSED) — reopening a closed poll (CLOSED 1 -> 0) is REFUSED.
// =============================================================================

#[test]
fn the_executor_re_enforces_reopening_a_closed_poll_is_refused() {
    // The `WriteOnce(CLOSED)` caveat, biting in the submission path. Seed (open, CLOSED 0),
    // close through the gated fire (CLOSED 0 -> 1), then submit a turn that REOPENS the poll
    // (CLOSED 1 -> 0). `WriteOnce(CLOSED)` refuses it — a poll closes exactly once.
    let (cclerk, executor) = agent(0x71);
    let app = voting_app(&cclerk, &executor);
    let poll = cclerk.cell_id();
    seed_poll(&executor, "ship it?");
    let _ = seed_ballot(&executor, &cclerk, poll);
    let poll_cell = app.cell(&poll).expect("the poll cell");

    // The ADMINISTRATOR (root) closes the poll through the gated fire — CLOSED 0 -> 1.
    let receipt = fire_close_poll(&app, &AuthRequired::None, &cclerk, &executor)
        .expect("the administrator closes the poll");
    assert_ne!(receipt.turn_hash, [0u8; 32], "a real verified close turn");
    let closed = executor.cell_state(poll).unwrap();
    assert_eq!(
        closed.fields[CLOSED_SLOT],
        field_from_u64(1),
        "the poll is closed"
    );

    // After closing, `close_poll` AND `record_tally` go DARK (the open precondition CLOSED ==
    // 0 now fails). The htmx tooth: a closed poll's administrator buttons darken.
    let lit_after = poll_cell.gated_fireable_names(&AuthRequired::None, &executor);
    assert!(
        !lit_after.contains(&"close_poll".to_string()),
        "closed poll: close_poll darkens"
    );
    assert!(
        !lit_after.contains(&"record_tally".to_string()),
        "closed poll: record_tally darkens"
    );

    // A reopen: CLOSED := 0 (rewriting the committed 1). `WriteOnce(CLOSED)` refuses 1 -> 0.
    let reopen = vec![dregg_app_framework::Effect::SetField {
        cell: poll,
        index: CLOSED_SLOT,
        value: field_from_u64(0),
    }];
    let action = cclerk.make_action(poll, "close_poll", reopen);
    let refused = executor.submit_action(&cclerk, action);
    assert!(refused.is_err(), "reopening a closed poll must be refused");
    let msg = format!("{:?}", refused.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("writeonce")
            || msg.contains("write-once")
            || msg.contains("program")
            || msg.contains("field[6]"),
        "the executor refuses on the WriteOnce(CLOSED) caveat, got: {msg}"
    );

    // CLOSED still holds 1 (anti-ghost).
    let after = executor.cell_state(poll).unwrap();
    assert_eq!(
        after.fields[CLOSED_SLOT],
        field_from_u64(1),
        "the refused reopen committed nothing — the poll stays closed"
    );
}

// =============================================================================
// register_deos mounts the surface AND seeds both cells (the promotion is live).
// =============================================================================

#[test]
fn register_deos_mounts_the_seeded_two_cell_surface_into_the_context() {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x71; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    let ctx = StarbridgeAppContext::new(cclerk.clone(), executor.clone());

    // `register_deos` folds the two-cell DeosApp into the context's affordance registry AND
    // seeds BOTH cells. After it, the deos surface is the SHIPPED one (the census promotion)
    // and the gated fires are live.
    let app = register_deos(&ctx);
    assert_eq!(app.name(), "privacy-voting");
    assert_eq!(
        ctx.affordance_registry().len(),
        2,
        "the two-cell deos surface is registered"
    );

    // The seeded ballot is unset, so a voter can cast through the mounted surface immediately
    // (the seam is closed + live).
    let receipt = fire_cast_vote(&app, &AuthRequired::Either, VOTE_YES, &cclerk, &executor)
        .expect("the mounted, seeded surface casts a vote (the promotion is live)");
    assert_ne!(receipt.turn_hash, [0u8; 32]);

    // The ballot VOTE moved (a real vote committed).
    let ballot = ballot_cell_id(&cclerk.public_key().0);
    let state = executor.cell_state(ballot).unwrap();
    assert_eq!(
        state.fields[VOTE_SLOT],
        field_from_u64(VOTE_YES),
        "the vote committed"
    );
}
