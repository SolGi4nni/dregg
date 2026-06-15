//! THE SEAM CLOSED — the deos-native commit→reveal→resolve verbs fired through the executor
//! against the FULL figure program, so the verified caveats BITE in the fire path itself.
//!
//! `docs/deos/APPS-DEOS-INTEGRATION-CENSUS.md`: the promotion's task is to close the
//! fire→full-`CellProgram` seam so an ILLEGAL joint reveal is a REAL executor refusal in the
//! fire path, not a `program.evaluate`-only check. This file proves that seam CLOSED.
//! `src::register_deos` / `src::seed_figure` install [`figure_deos_program`] (the typed `sym`
//! enum tooth — `SymMemberOf` on every joint slot — CONJOINED with `Monotonic(PHASE_SLOT)`) on
//! the seeded figure cells, and the deos fire is a TWO-TEMPO bridge:
//!
//!   1. the deos PRECONDITION gate (the cap-gate `is_attenuation` AND the live-state
//!      precondition `CellProgram::evaluate` — e.g. `PHASE == COMMIT`) decides the button's
//!      verdict IN-BAND, nothing submitted on a miss (anti-ghost);
//!   2. on both passing, [`fire_commit_move`] / [`fire_reveal_move`] / [`fire_resolve_frame`]
//!      submit the FULL turn, and the executor RE-ENFORCES the figure program — so a
//!      `reveal_move` writing an ILLEGAL joint `sym` (a value outside
//!      `{Relax,Contract,Hold,Extend}`) is a REAL `SymMemberOf` executor refusal in the
//!      SUBMISSION path (msg "sym … not in enum set"), and a PHASE rewind is a real
//!      `Monotonic(PHASE)` refusal.
//!
//! **THE HEADLINE:** deos's hyperadvanced TYPED `sym` enum atom (`SymMemberOf`) bites a REAL
//! signed turn in the deos fire path — an out-of-enum joint value is refused by the EXECUTOR,
//! not by app bookkeeping. Plus the "set joints only on YOUR figure" cap tooth (a foreign-figure
//! fire is refused) and the phase gate. Every fire is a real verified turn; both gates are
//! genuine (`is_attenuation` + `CellProgram::evaluate`). No parallel model.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CellProgram, EmbeddedExecutor, FireError,
    FireExecuteError, StarbridgeAppContext, StateConstraint, field_from_u64,
};

use starbridge_tussle::{
    COMMIT, COMMIT_SEAL_SLOT, JointState, N_JOINTS, PHASE_SLOT, RESOLVED, REST_POSE, REVEAL,
    figure_b_cell_id, figure_deos_program, fire_commit_move, fire_resolve_frame, fire_reveal_move,
    register_deos, seed_figure, seed_figure_b, slot, tussle_app,
};

fn agent(seed: u8) -> (AppCipherclerk, EmbeddedExecutor) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    (cclerk, executor)
}

/// Read a `u64` from the last 8 big-endian bytes of a field element.
fn field_to_u64(f: &[u8; 32]) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&f[24..32]);
    u64::from_be_bytes(b)
}

// =============================================================================
// (a) Seeding installs the figure program + PHASE=COMMIT on BOTH figures.
// =============================================================================

#[test]
fn seeding_installs_the_figure_program_and_commit_phase_on_both_figures() {
    let (cclerk, executor) = agent(0x70);
    seed_figure(&executor, cclerk.cell_id());
    let figure_b = seed_figure_b(&executor, &cclerk);

    // BOTH figures carry the figure program (the SymMemberOf joint tooth + the phase gate),
    // installed so the executor re-enforces it on every touching turn.
    for fig in [cclerk.cell_id(), figure_b] {
        let installed =
            executor.with_ledger_mut(|ledger| ledger.get(&fig).map(|c| c.program.clone()));
        assert_eq!(
            installed,
            Some(figure_deos_program()),
            "the seeded figure carries the figure program (the seam's enforcement layer)"
        );
        // ...and the figure starts in the commit phase, in the Relax rest pose.
        let state = executor.cell_state(fig).expect("seeded figure exists");
        assert_eq!(
            state.fields[PHASE_SLOT],
            field_from_u64(COMMIT),
            "figure starts in COMMIT"
        );
        for j in 0..N_JOINTS {
            assert_eq!(
                state.fields[slot::JOINT_BASE + j],
                field_from_u64(JointState::Relax.sym()),
                "joints start at the Relax default"
            );
        }
    }

    // The figure program really is the per-joint SymMemberOf conjoined with Monotonic(PHASE).
    let CellProgram::Predicate(cs) = figure_deos_program() else {
        panic!("figure program must be a flat Predicate");
    };
    let n_sym = cs
        .iter()
        .filter(|c| matches!(c, StateConstraint::SymMemberOf { .. }))
        .count();
    assert_eq!(n_sym, N_JOINTS, "one SymMemberOf per joint slot");
    assert!(
        cs.iter().any(
            |c| matches!(c, StateConstraint::Monotonic { index } if *index == PHASE_SLOT as u8)
        ),
        "the phase gate Monotonic(PHASE_SLOT) is a clause"
    );
}

// =============================================================================
// (b) commit_move through the gated fire writes a sealed commit (a real turn).
// =============================================================================

#[test]
fn a_fighter_commits_a_move_through_the_gated_fire_a_real_verified_turn() {
    let (cclerk, executor) = agent(0x70);
    let app = tussle_app(&cclerk, &executor);
    seed_figure(&executor, cclerk.cell_id());
    let _ = seed_figure_b(&executor, &cclerk);
    let figure_a = cclerk.cell_id();

    // The seal slot is empty before the commit.
    let before = executor.cell_state(figure_a).unwrap();
    assert_eq!(
        before.fields[COMMIT_SEAL_SLOT],
        field_from_u64(0),
        "no sealed commit yet"
    );

    // A FIGHTER (Either) fires `commit_move` on its OWN figure: the cap-gate passes
    // (Either ⊇ Either), the live-state precondition passes (PHASE == COMMIT), and the FULL
    // commit turn writes the sealed BLAKE3 digest. The executor re-enforces the figure program
    // (Monotonic(PHASE) holds — the phase is unchanged at COMMIT). A real verified turn.
    let pose = [
        JointState::Contract,
        JointState::Hold,
        JointState::Extend,
        JointState::Relax,
    ];
    let receipt = fire_commit_move(
        &app,
        figure_a,
        &AuthRequired::Either,
        &pose,
        0xC0FFEE,
        &cclerk,
        &executor,
    )
    .expect("a fighter commits (caps ∧ state ∧ monotonic phase all pass)");
    assert_ne!(
        receipt.turn_hash, [0u8; 32],
        "a real verified turn through the executor"
    );

    // The sealed commit landed (the fog-of-war digest is on the figure cell now).
    let after = executor.cell_state(figure_a).unwrap();
    assert_ne!(
        after.fields[COMMIT_SEAL_SLOT],
        field_from_u64(0),
        "the sealed commit was written"
    );
    // ...and the phase did NOT advance (a commit keeps the figure in the commit phase).
    assert_eq!(
        after.fields[PHASE_SLOT],
        field_from_u64(COMMIT),
        "still COMMIT after a commit"
    );
}

// =============================================================================
// (c) THE HTMX TOOTH — in COMMIT only commit_move lights; after phase→REVEAL,
//     reveal_move lights. Same viewer, same caps, DIFFERENT button-set.
// =============================================================================

#[test]
fn the_lit_verb_set_follows_the_phase_the_htmx_tooth() {
    let (cclerk, executor) = agent(0x70);
    let app = tussle_app(&cclerk, &executor);
    seed_figure(&executor, cclerk.cell_id());
    let _ = seed_figure_b(&executor, &cclerk);
    let figure_a = cclerk.cell_id();
    let cell = app.cell(&figure_a).expect("figure A is in the app");

    // In COMMIT, a FIGHTER (Either) sees `commit_move` LIT and `reveal_move` DARK (the phase
    // precondition `PHASE == REVEAL` fails). The htmx tooth, off live state.
    let lit_commit = cell.gated_fireable_names(&AuthRequired::Either, &executor);
    assert!(
        lit_commit.contains(&"commit_move".to_string()),
        "COMMIT: commit_move lights"
    );
    assert!(
        !lit_commit.contains(&"reveal_move".to_string()),
        "COMMIT: reveal_move is dark"
    );

    // Advance the phase to REVEAL (a referee would; here we set it directly to drive the htmx
    // transition under test — the phase-advance Monotonic tooth is exercised by the resolve fire).
    executor.with_ledger_mut(|ledger| {
        if let Some(c) = ledger.get_mut(&figure_a) {
            c.state.set_field(PHASE_SLOT, field_from_u64(REVEAL));
        }
    });

    // SAME viewer, SAME caps, DIFFERENT button-set — because the figure transitioned. Now
    // `reveal_move` lights and `commit_move` darkens.
    let lit_reveal = cell.gated_fireable_names(&AuthRequired::Either, &executor);
    assert!(
        lit_reveal.contains(&"reveal_move".to_string()),
        "REVEAL: reveal_move lights"
    );
    assert!(
        !lit_reveal.contains(&"commit_move".to_string()),
        "REVEAL: commit_move is dark"
    );
}

// =============================================================================
// (d) THE CAP TOOTH — "set joints only on YOUR figure": a fighter firing on a
//     figure cell it does NOT hold a cap to is REFUSED (foreign-figure refusal).
// =============================================================================

#[test]
fn a_stranger_cannot_set_joints_on_a_figure_it_does_not_hold_the_wrong_figure_cap_tooth() {
    let (owner, executor) = agent(0x70);
    let app = tussle_app(&owner, &executor);
    seed_figure(&executor, owner.cell_id());
    let figure_b = seed_figure_b(&executor, &owner); // owned by `owner`; only `owner` holds a cap to it

    // A STRANGER (a distinct cipherclerk) holds the fighter rights tier (Either) but holds NO
    // capability reaching figure B (it was never granted one — only the owner's agent was). It
    // tries to set joints on figure B (a figure it does NOT hold). The cap-gate passes on the
    // RIGHTS tier (Either ⊇ Either), but the EXECUTOR refuses the turn signed by the stranger
    // against the owner's Sovereign figure cell (no reaching cap) — the wrong-figure tooth.
    let stranger = AppCipherclerk::new(AgentCipherclerk::new(), [0xBB; 32]);
    let pose = [JointState::Contract; N_JOINTS];
    let refused = fire_commit_move(
        &app,
        figure_b,
        &AuthRequired::Either,
        &pose,
        7,
        &stranger, // signs as a stranger with no cap to figure B
        &executor,
    );
    assert!(
        matches!(
            refused,
            Err(FireExecuteError::Executor(_))
                | Err(FireExecuteError::Gate(FireError::Unauthorized { .. }))
        ),
        "a stranger setting joints on a figure it does not hold must be refused, got {refused:?}"
    );

    // Anti-ghost: the foreign figure's seal slot did NOT change (the refused turn committed
    // nothing).
    let after = executor.cell_state(figure_b).unwrap();
    assert_eq!(
        after.fields[COMMIT_SEAL_SLOT],
        field_from_u64(0),
        "the refused foreign-figure commit wrote nothing (anti-ghost)"
    );
}

// =============================================================================
// (e) THE STATE SEAM — SymMemberOf: a reveal writing an ILLEGAL joint value is
//     REFUSED by the executor's typed-enum caveat. ★ THE HEADLINE ★
// =============================================================================

#[test]
fn a_reveal_with_an_illegal_joint_value_is_refused_by_the_symmemberof_caveat() {
    let (cclerk, executor) = agent(0x70);
    let app = tussle_app(&cclerk, &executor);
    seed_figure(&executor, cclerk.cell_id());
    let _ = seed_figure_b(&executor, &cclerk);
    let figure_a = cclerk.cell_id();

    // Advance figure A to the REVEAL phase so the reveal precondition is satisfied (we isolate
    // the SymMemberOf tooth: the gate passes, then the executor's typed-enum caveat bites).
    executor.with_ledger_mut(|ledger| {
        if let Some(c) = ledger.get_mut(&figure_a) {
            c.state.set_field(PHASE_SLOT, field_from_u64(REVEAL));
        }
    });

    // FIRE a reveal whose first joint carries an ILLEGAL `sym` (7 ∉ {0,1,2,3}). The cap∧state
    // gate passes (Either ⊇ Either AND PHASE == REVEAL), so the FULL reveal turn is SUBMITTED —
    // and the EXECUTOR's installed `SymMemberOf` REFUSES the produced transition. The typed
    // enum atom bites a real signed turn (NOT a side check). ★ THE HEADLINE ★
    let illegal = [7u64, 1, 2, 0]; // 7 is out-of-enum
    let refused = fire_reveal_move(
        &app,
        figure_a,
        &AuthRequired::Either,
        illegal,
        &cclerk,
        &executor,
    );
    assert!(
        matches!(refused, Err(FireExecuteError::Executor(_))),
        "an illegal joint reveal must be refused by the EXECUTOR (the SymMemberOf caveat), got {refused:?}"
    );
    let msg = format!("{refused:?}").to_lowercase();
    assert!(
        msg.contains("sym")
            || msg.contains("member")
            || msg.contains("enum")
            || msg.contains("program"),
        "the executor refuses on the SymMemberOf typed-enum caveat, got: {msg}"
    );

    // Anti-ghost: the refused illegal reveal wrote nothing — the joint slot still holds the
    // Relax default.
    let after = executor.cell_state(figure_a).unwrap();
    assert_eq!(
        after.fields[slot::JOINT_BASE],
        field_from_u64(JointState::Relax.sym()),
        "the refused illegal reveal committed nothing (anti-ghost)"
    );

    // Non-vacuity: a LEGAL reveal (all in-enum) is ACCEPTED by the same caveat — the gate is
    // not always-false.
    let legal = [
        JointState::Contract.sym(),
        JointState::Hold.sym(),
        JointState::Extend.sym(),
        JointState::Relax.sym(),
    ];
    let ok = fire_reveal_move(
        &app,
        figure_a,
        &AuthRequired::Either,
        legal,
        &cclerk,
        &executor,
    )
    .expect("a legal reveal (all joints in-enum) is accepted by the SymMemberOf caveat");
    assert_ne!(
        ok.turn_hash, [0u8; 32],
        "the legal reveal is a real verified turn"
    );
    let after_legal = executor.cell_state(figure_a).unwrap();
    assert_eq!(
        after_legal.fields[slot::JOINT_BASE],
        field_from_u64(JointState::Contract.sym()),
        "the legal reveal wrote the Contract joint"
    );
}

// =============================================================================
// (f) THE PHASE GATE — a reveal in COMMIT phase is refused in-band (state tooth);
//     a resolve advances the phase, and a rewind is refused by Monotonic(PHASE).
// =============================================================================

#[test]
fn a_reveal_in_the_commit_phase_is_refused_in_band_the_phase_state_tooth() {
    let (cclerk, executor) = agent(0x70);
    let app = tussle_app(&cclerk, &executor);
    seed_figure(&executor, cclerk.cell_id());
    let _ = seed_figure_b(&executor, &cclerk);
    let figure_a = cclerk.cell_id();

    // Figure A is in the COMMIT phase (seeded). A FIGHTER firing `reveal_move` is refused
    // IN-BAND at the STATE tooth (the precondition `PHASE == REVEAL` fails) — the button is
    // dark in the commit phase (the htmx tooth), and NOTHING is submitted (anti-ghost).
    let legal = [JointState::Contract.sym(); N_JOINTS];
    let refused = fire_reveal_move(
        &app,
        figure_a,
        &AuthRequired::Either,
        legal,
        &cclerk,
        &executor,
    );
    assert!(
        matches!(
            refused,
            Err(FireExecuteError::Gate(
                FireError::StateConditionUnmet { .. }
            ))
        ),
        "a reveal in the commit phase is refused at the state tooth in-band, got {refused:?}"
    );

    // Anti-ghost: nothing was written (the joint slot still holds the Relax default).
    let after = executor.cell_state(figure_a).unwrap();
    assert_eq!(
        after.fields[slot::JOINT_BASE],
        field_from_u64(JointState::Relax.sym())
    );
}

#[test]
fn the_referee_resolves_the_frame_advancing_the_phase_and_a_rewind_is_refused() {
    let (cclerk, executor) = agent(0x70);
    let app = tussle_app(&cclerk, &executor);
    seed_figure(&executor, cclerk.cell_id());
    let figure_b = seed_figure_b(&executor, &cclerk);
    let figure_a = cclerk.cell_id();

    // Stage a frame: both figures in the REVEAL phase with revealed poses (figure A pushes 3,
    // figure B pushes 1 — figure A out-pushes). The referee resolves it.
    for fig in [figure_a, figure_b] {
        executor.with_ledger_mut(|ledger| {
            if let Some(c) = ledger.get_mut(&fig) {
                c.state.set_field(PHASE_SLOT, field_from_u64(REVEAL));
            }
        });
    }
    // Figure A revealed: push 3 (three Contract joints). Figure B revealed: push 1.
    executor.with_ledger_mut(|ledger| {
        if let Some(c) = ledger.get_mut(&figure_a) {
            for j in 0..3 {
                c.state.set_field(
                    slot::JOINT_BASE + j,
                    field_from_u64(JointState::Contract.sym()),
                );
            }
            c.state.set_field(slot::POSITION, field_from_u64(0));
        }
        if let Some(c) = ledger.get_mut(&figure_b) {
            c.state
                .set_field(slot::JOINT_BASE, field_from_u64(JointState::Contract.sym()));
            c.state.set_field(slot::POSITION, field_from_u64(2));
        }
    });

    // THE REFEREE (root) fires `resolve_frame` on figure A (the coordinator) — the cap∧state
    // gate passes (None ⊇ everything AND PHASE == REVEAL), and the FULL resolve turn advances
    // PHASE → RESOLVED, folding contact off both figures. The executor re-enforces
    // Monotonic(PHASE) (REVEAL → RESOLVED is a forward advance). A real verified turn.
    let receipt = fire_resolve_frame(
        &app,
        figure_a,
        figure_b,
        &AuthRequired::None,
        &cclerk,
        &executor,
    )
    .expect("the referee resolves the frame (caps ∧ state ∧ monotonic phase all pass)");
    assert_ne!(receipt.turn_hash, [0u8; 32], "a real verified resolve turn");

    // The phase advanced to RESOLVED.
    let after = executor.cell_state(figure_a).unwrap();
    assert_eq!(
        after.fields[PHASE_SLOT],
        field_from_u64(RESOLVED),
        "PHASE advanced to RESOLVED"
    );

    // THE PHASE-REWIND TOOTH: a turn that REWINDS the phase (RESOLVED → REVEAL) is refused by
    // the executor's Monotonic(PHASE_SLOT) — the frame machine never runs backward. We submit
    // the rewind directly (bypassing the precondition) to isolate the Monotonic tooth.
    let rewind = cclerk.make_action(
        figure_a,
        "rewind_phase",
        vec![dregg_app_framework::Effect::SetField {
            cell: figure_a,
            index: PHASE_SLOT,
            value: field_from_u64(REVEAL), // 2 < 3 — a rewind
        }],
    );
    let refused = executor.submit_action(&cclerk, rewind);
    assert!(
        refused.is_err(),
        "rewinding the frame phase must be refused by the executor"
    );
    let msg = format!("{:?}", refused.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("monotonic") || msg.contains("program") || msg.contains("field"),
        "the executor refuses on the Monotonic(PHASE) caveat, got: {msg}"
    );

    // Anti-ghost: the phase did NOT move (still RESOLVED).
    let still = executor.cell_state(figure_a).unwrap();
    assert_eq!(
        still.fields[PHASE_SLOT],
        field_from_u64(RESOLVED),
        "the refused rewind committed nothing — the phase still holds RESOLVED"
    );
    let _ = REST_POSE; // (named in the module's surface; silence unused-import)
}

// =============================================================================
// register_deos mounts the surface AND seeds BOTH figures (the promotion is live).
// =============================================================================

#[test]
fn register_deos_mounts_the_seeded_two_figure_surface_into_the_context() {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x70; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    let ctx = StarbridgeAppContext::new(cclerk.clone(), executor.clone());

    // `register_deos` folds the two-figure DeosApp into the context's affordance registry AND
    // seeds BOTH figures (programs installed, COMMIT phase). After it, the deos surface is the
    // SHIPPED one and the gated fires are live.
    let app = register_deos(&ctx);
    assert_eq!(app.name(), "tussle");
    assert_eq!(
        ctx.affordance_registry().len(),
        2,
        "two figure cells registered"
    );

    // Both seeded figures are live and in the COMMIT phase — a fighter can commit on either
    // through the mounted surface immediately (the seam is closed + live).
    let figure_a = cclerk.cell_id();
    let figure_b = figure_b_cell_id(&cclerk.public_key().0);
    for fig in [figure_a, figure_b] {
        let state = executor.cell_state(fig).expect("seeded figure is live");
        assert_eq!(state.fields[PHASE_SLOT], field_from_u64(COMMIT));
    }

    // A fighter commits on figure A through the mounted, seeded surface (the promotion is live).
    let pose = [
        JointState::Contract,
        JointState::Relax,
        JointState::Hold,
        JointState::Extend,
    ];
    let receipt = fire_commit_move(
        &app,
        figure_a,
        &AuthRequired::Either,
        &pose,
        1,
        &cclerk,
        &executor,
    )
    .expect("the mounted, seeded surface accepts a commit (the promotion is live)");
    assert_ne!(receipt.turn_hash, [0u8; 32]);
    let state = executor.cell_state(figure_a).unwrap();
    assert_ne!(
        state.fields[COMMIT_SEAL_SLOT],
        field_from_u64(0),
        "the commit folded the seal"
    );
    let _ = field_to_u64; // (a helper used by sibling assertions; keep it referenced)
}
