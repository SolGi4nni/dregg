//! THE COLONIST-JOB SEAM — the job (gather → make → hand-off) advanced through the REAL embedded
//! executor, so all THREE admission legs BITE in the submission path itself.
//!
//! `src/colonist_job.rs` installs [`job_cell_program`] on the seeded job cell and drives it with
//! [`advance_job_step`] (a real signed turn). The executor RE-ENFORCES the full program on every
//! produced transition, so the colonist advances step-by-step IFF:
//!   - DAG / no-skip — `MonotonicSequence(JOB_CURSOR)` exact-`+1` + `FieldLteField(cursor<=terminal)`;
//!   - CLEARANCE — `ClearanceDominates` (a hauler is refused at the `make` verb);
//!   - SPEND BUDGET — `FieldLteField(SPEND_ACCUM <= BUDGET)` (an overspend is refused).
//!
//! Both polarities, real executor:
//!   - GENUINE ✓ — a crafter on the full budget advances the whole job gather→make→hand-off;
//!   - CHEAT ✗ — a SKIP (non-`+1`), an OUT-OF-CLEARANCE verb (hauler crafting), and an OVERSPEND
//!     (tight budget) are each REFUSED in-band, committing nothing (anti-ghost).

use dregg_app_framework::{AgentCipherclerk, AppCipherclerk, EmbeddedExecutor, field_from_u64};

use starbridge_compartment_workflow_mandate::colonist_job::{
    BUDGET_SLOT, FULL_BUDGET, JOB_CURSOR_SLOT, JOB_TERMINAL, SPEND_ACCUM_SLOT, TIGHT_BUDGET,
    WorkflowVerb, advance_effects, advance_job_step, crafter_label, hauler_label, job_cell_program,
    job_clearance_root, seed_job,
};

fn agent(seed: u8) -> (AppCipherclerk, EmbeddedExecutor) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    (cclerk, executor)
}

fn cursor_of(executor: &EmbeddedExecutor, cell: dregg_app_framework::CellId) -> u64 {
    let s = executor.cell_state(cell).unwrap();
    let mut b = [0u8; 8];
    b.copy_from_slice(&s.fields[JOB_CURSOR_SLOT as usize][24..32]);
    u64::from_be_bytes(b)
}

fn spend_of(executor: &EmbeddedExecutor, cell: dregg_app_framework::CellId) -> u64 {
    let s = executor.cell_state(cell).unwrap();
    let mut b = [0u8; 8];
    b.copy_from_slice(&s.fields[SPEND_ACCUM_SLOT as usize][24..32]);
    u64::from_be_bytes(b)
}

// =============================================================================
// (a) Seeding installs the job program + the config (terminal, root, budget, spend 0).
// =============================================================================

#[test]
fn seeding_installs_the_job_program_and_config() {
    let (cclerk, executor) = agent(0x51);
    let budget = seed_job(&executor, JOB_TERMINAL, job_clearance_root(), FULL_BUDGET);
    assert_eq!(budget, FULL_BUDGET);

    let installed =
        executor.with_ledger_mut(|l| l.get(&cclerk.cell_id()).map(|c| c.program.clone()));
    assert_eq!(
        installed,
        Some(job_cell_program()),
        "the seeded job cell carries the job program (the seam's enforcement layer)"
    );
    let state = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(state.fields[JOB_CURSOR_SLOT as usize], field_from_u64(0));
    assert_eq!(state.fields[SPEND_ACCUM_SLOT as usize], field_from_u64(0));
    assert_eq!(
        state.fields[BUDGET_SLOT as usize],
        field_from_u64(FULL_BUDGET)
    );
}

// =============================================================================
// (b) GENUINE ✓ — a crafter on the full budget advances the WHOLE job (3 real verified turns).
// =============================================================================

#[test]
fn a_crafter_advances_the_whole_job_on_the_full_budget() {
    let (cclerk, executor) = agent(0x51);
    let _ = seed_job(&executor, JOB_TERMINAL, job_clearance_root(), FULL_BUDGET);
    let cell = cclerk.cell_id();

    // gather (0 -> 1, spend 3), make (1 -> 2, spend 7), hand-off (2 -> 3, spend 9). Each leg passes:
    // exact +1, crafter clears the verb, cumulative spend stays <= 9.
    let expected_spend = [3u64, 7, 9];
    for step in 0..3usize {
        let receipt = advance_job_step(&cclerk, &executor, crafter_label())
            .unwrap_or_else(|e| panic!("crafter step {step} should commit, got {e:?}"));
        assert_ne!(receipt.turn_hash, [0u8; 32], "a real verified turn");
        assert_eq!(cursor_of(&executor, cell), (step + 1) as u64);
        assert_eq!(spend_of(&executor, cell), expected_spend[step]);
    }
    // The job reached hand-off (cursor 3 == terminal), total spend 9 == budget.
    assert_eq!(cursor_of(&executor, cell), 3);
    assert_eq!(spend_of(&executor, cell), 9);
}

// =============================================================================
// (c) CHEAT ✗ — OUT-OF-CLEARANCE: a hauler gathers, but is REFUSED at the `make` (crafting) verb.
// =============================================================================

#[test]
fn a_hauler_is_refused_at_the_make_verb_clearance_tooth() {
    let (cclerk, executor) = agent(0x51);
    let _ = seed_job(&executor, JOB_TERMINAL, job_clearance_root(), FULL_BUDGET);
    let cell = cclerk.cell_id();

    // The hauler clears gather: 0 -> 1 commits.
    advance_job_step(&cclerk, &executor, hauler_label())
        .expect("hauler clears gather (hauler -> gather edge): admitted");
    assert_eq!(cursor_of(&executor, cell), 1);

    // The hauler does NOT clear `make` (no hauler -> make edge): the ClearanceDominates tooth refuses.
    let refused = advance_job_step(&cclerk, &executor, hauler_label());
    assert!(
        refused.is_err(),
        "a hauler crafting must be refused (hauler does not clear make), got {refused:?}"
    );
    let msg = format!("{:?}", refused.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("dominate") || msg.contains("clearance") || msg.contains("program"),
        "refused on the ClearanceDominates tooth, got: {msg}"
    );
    // Anti-ghost: cursor holds at 1, spend holds at 3.
    assert_eq!(cursor_of(&executor, cell), 1);
    assert_eq!(spend_of(&executor, cell), 3);

    // ...whereas a CRAFTER (clears make) advancing 1 -> 2 IS admitted — same live cursor, same step,
    // a dominating clearance. Both polarities, real executor.
    advance_job_step(&cclerk, &executor, crafter_label())
        .expect("a crafter clears make (crafter -> make edge): admitted");
    assert_eq!(cursor_of(&executor, cell), 2);
}

// =============================================================================
// (d) CHEAT ✗ — OVERSPEND: a crafter on a TIGHT budget gathers, but `make` OVERRUNS the budget.
//     The genuinely-new SPEND-BUDGET tooth, biting in the submission path.
// =============================================================================

#[test]
fn an_overspend_is_refused_by_the_budget_tooth() {
    let (cclerk, executor) = agent(0x51);
    // Tight budget 6: gather (spend 3) fits, make (spend 7) does NOT.
    let _ = seed_job(&executor, JOB_TERMINAL, job_clearance_root(), TIGHT_BUDGET);
    let cell = cclerk.cell_id();

    // The crafter clears make AND gather is a legal +1 in budget (3 <= 6): 0 -> 1 commits.
    advance_job_step(&cclerk, &executor, crafter_label())
        .expect("gather fits the tight budget (3 <= 6): admitted");
    assert_eq!(cursor_of(&executor, cell), 1);
    assert_eq!(spend_of(&executor, cell), 3);

    // make: a legal +1, the crafter clears it, but it sets SPEND_ACCUM = 7 > 6 = budget. The
    // FieldLteField(SPEND_ACCUM <= BUDGET) tooth refuses — distinct from clearance (crafter clears
    // make) and from monotonic (+1 holds): ONLY the budget leg bites.
    let refused = advance_job_step(&cclerk, &executor, crafter_label());
    assert!(
        refused.is_err(),
        "an overspend (make: 7 > 6) must be refused by the budget tooth, got {refused:?}"
    );
    let msg = format!("{:?}", refused.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("lte") || msg.contains("field") || msg.contains("program") || msg.contains("budget"),
        "refused on the FieldLteField(SPEND_ACCUM <= BUDGET) tooth, got: {msg}"
    );
    // Anti-ghost: cursor holds at 1, spend holds at 3 (the overspend committed nothing).
    assert_eq!(cursor_of(&executor, cell), 1);
    assert_eq!(spend_of(&executor, cell), 3);

    // ...and the SAME make step (1 -> 2) on the FULL budget IS admitted — isolating the budget leg
    // as load-bearing (a fresh full-budget job, crafter, drives gather then make).
    let (cclerk2, executor2) = agent(0x52);
    let _ = seed_job(&executor2, JOB_TERMINAL, job_clearance_root(), FULL_BUDGET);
    advance_job_step(&cclerk2, &executor2, crafter_label()).expect("gather"); // 0->1, spend 3
    advance_job_step(&cclerk2, &executor2, crafter_label())
        .expect("make fits the full budget (7 <= 9): admitted");
    assert_eq!(cursor_of(&executor2, cclerk2.cell_id()), 2);
    assert_eq!(spend_of(&executor2, cclerk2.cell_id()), 7);
}

// =============================================================================
// (e) CHEAT ✗ — SKIP A PREREQUISITE: a non-+1 cursor jump is refused (the DAG / MonotonicSequence
//     tooth). The colonist cannot skip gather and jump to a later step.
// =============================================================================

#[test]
fn a_skip_ahead_is_refused_by_the_monotonic_sequence_tooth() {
    let (cclerk, executor) = agent(0x51);
    let _ = seed_job(&executor, JOB_TERMINAL, job_clearance_root(), FULL_BUDGET);
    let cell = cclerk.cell_id();

    // A SKIP: cursor 0 -> 2 (skipping gather). MonotonicSequence(JOB_CURSOR) requires exactly +1
    // (here 1); 2 is refused. We build the effects directly to bypass the +1 derivation. Crafter +
    // the make compartment so clearance + budget would pass — ONLY the skip bites.
    let skip = advance_effects(cell, 2, crafter_label(), WorkflowVerb::Make.compartment_label());
    let action = cclerk.make_action(cell, "advance_step", skip);
    let refused = executor.submit_action(&cclerk, action);
    assert!(
        refused.is_err(),
        "skipping a prerequisite (non-+1) must be refused"
    );
    let msg = format!("{:?}", refused.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("monotonic") || msg.contains("sequence") || msg.contains("program") || msg.contains("field[0]"),
        "refused on the MonotonicSequence(JOB_CURSOR) tooth, got: {msg}"
    );
    // Anti-ghost: nothing committed.
    assert_eq!(cursor_of(&executor, cell), 0);
    assert_eq!(spend_of(&executor, cell), 0);
}

// =============================================================================
// (f) THE ROOT TOOTH — the clearance check consults the stored graph root: a wrong root fails
//     closed even for a fully-cleared crafter.
// =============================================================================

#[test]
fn a_wrong_clearance_root_fails_closed() {
    let (cclerk, executor) = agent(0x51);
    // Seed with a BOGUS clearance-graph root (not job_clearance_root()).
    let _ = seed_job(&executor, JOB_TERMINAL, [0xAB; 32], FULL_BUDGET);
    let cell = cclerk.cell_id();

    // Even a fully-cleared crafter's gather is refused — the carried graph no longer commits to the
    // stored root. Proves the root slot is LOAD-BEARING.
    let refused = advance_job_step(&cclerk, &executor, crafter_label());
    assert!(
        refused.is_err(),
        "a wrong stored root must fail closed even for a crafter, got {refused:?}"
    );
    assert_eq!(cursor_of(&executor, cell), 0);
}
