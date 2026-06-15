//! End-to-end exercise of the TUSSLE joint-combat match, with the load-bearing TEETH:
//!   - FOG-OF-WAR: the opponent's joint vector is unreadable from the sealed commitment.
//!   - CAP-GATING: a player cannot set the opponent's joints (a reveal posing the wrong figure is
//!     refused).
//!   - REPRODUCIBILITY: the deterministic resolution gives the same outcome for the same moves.
//!   - THE TYPED-`sym` ENUM TOOTH: a joint driven out of the [`JointState`] enum is refused by the
//!     figure's joint-state-enum cell program (the Rust image of the Lean `Pred.symMemberOf`).
//!   - THE VERIFIED JOINT TURN: the score deltas settle through the verified per-asset executor
//!     (atomic + conserving).

use super::*;
use crate::resolution::{SCORE_BANK, brace, forward_drive, resolve_contact};

const P0: FigureId = 10;
const P1: FigureId = 11;

// Convenience: a full joint vector from four states.
fn pose(a: JointState, b: JointState, c: JointState, d: JointState) -> JointVector {
    [a, b, c, d]
}

// A pose with `k` Contract joints (the rest Relax) — forward drive `k`, no brace.
fn push(k: usize) -> JointVector {
    let mut v = REST_POSE;
    for slot in v.iter_mut().take(k) {
        *slot = JointState::Contract;
    }
    v
}

// ─────────────────────────────────────────────────────────────────────────────
// JointState ↔ sym round-trip (the enum is the `sym` set the typed atom pins to).
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn jointstate_sym_roundtrips() {
    for s in JointState::ALL {
        assert_eq!(JointState::from_sym(s.sym()), Some(s));
    }
    // Out-of-enum sym values decode to None — exactly what SymMemberOf refuses.
    assert_eq!(JointState::from_sym(4), None);
    assert_eq!(JointState::from_sym(99), None);
    // The enum set is the four cases 0..3.
    assert_eq!(JointState::enum_set(), vec![0, 1, 2, 3]);
}

#[test]
fn figure_pose_reads_back_through_sym_slots() {
    let mut f = Figure::spawn(P0, 0);
    let p = pose(
        JointState::Contract,
        JointState::Hold,
        JointState::Extend,
        JointState::Relax,
    );
    f.pose_checked(&p).unwrap();
    // The joints are stored in `sym` slots and read back identically.
    assert_eq!(f.pose(), p);
    // The figure cell really holds the interned sym values in its joint slots.
    assert_eq!(
        field_to_u64(&f.cell.fields[slot::JOINT_BASE]),
        JointState::Contract.sym()
    );
    assert_eq!(
        field_to_u64(&f.cell.fields[slot::JOINT_BASE + 1]),
        JointState::Hold.sym()
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// THE TYPED-`sym` ENUM TOOTH — a joint out of the enum is refused by the REAL
// CellProgram::evaluate (SymMemberOf), the Rust image of the Lean Pred.symMemberOf.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn joint_program_is_symmemberof_per_joint() {
    // The figure's joint program is exactly Predicate([SymMemberOf{slot_j, {0,1,2,3}} ; j]).
    let prog = Figure::joint_program();
    match prog {
        CellProgram::Predicate(cs) => {
            assert_eq!(cs.len(), N_JOINTS);
            for (j, c) in cs.iter().enumerate() {
                match c {
                    StateConstraint::SymMemberOf { index, set } => {
                        assert_eq!(*index as usize, slot::JOINT_BASE + j);
                        assert_eq!(set, &vec![0u64, 1, 2, 3]);
                    }
                    other => panic!("joint constraint {j} is not SymMemberOf: {other:?}"),
                }
            }
        }
        other => panic!("joint program is not a Predicate: {other:?}"),
    }
}

#[test]
fn out_of_enum_joint_is_refused_by_the_cell_program() {
    // Hand-craft a transition that drives a joint slot to sym 7 (NOT a JointState case) and feed it
    // to the REAL evaluator. It must be refused — the SymMemberOf tooth biting.
    let old = Figure::spawn(P0, 0).cell;
    let mut bad = old.clone();
    bad.set_field(slot::JOINT_BASE, field_from_u64(7)); // 7 ∉ {0,1,2,3}
    let verdict = Figure::joint_program().evaluate(&bad, Some(&old), None);
    assert!(
        verdict.is_err(),
        "the cell program admitted an out-of-enum joint (sym 7) — the SymMemberOf tooth did not bite"
    );

    // And a legal pose IS admitted (non-vacuity: the gate is not always-false).
    let mut good = old.clone();
    good.set_field(slot::JOINT_BASE, field_from_u64(JointState::Contract.sym()));
    assert!(
        Figure::joint_program()
            .evaluate(&good, Some(&old), None)
            .is_ok()
    );
}

#[test]
fn pose_checked_is_the_in_band_enum_gate() {
    // `pose_checked` runs the figure's joint program (SymMemberOf) over the candidate transition and
    // refuses in-band on an out-of-enum joint — the same gate `Frame::reveal` runs at reveal time.
    // A safe `JointVector` is always enum-valid, so we ALSO confirm a valid pose commits (accept),
    // and that the figure's program — the gate `pose_checked` invokes — refuses an out-of-enum slot
    // (refuse). Together: the reveal-time enum check is a real, non-vacuous in-band tooth.
    let mut f = Figure::spawn(P0, 0);
    let old = f.cell.clone();

    // ACCEPT: a valid pose passes the in-band gate and mutates the figure cell.
    f.pose_checked(&push(2)).unwrap();
    assert_ne!(f.cell, old);
    assert_eq!(f.pose(), push(2));

    // REFUSE: the very gate pose_checked invokes (Figure::joint_program) bites an out-of-enum slot.
    let mut corrupt = f.cell.clone();
    corrupt.set_field(slot::JOINT_BASE + 1, field_from_u64(5)); // 5 ∉ {0,1,2,3}
    assert!(
        Figure::joint_program()
            .evaluate(&corrupt, Some(&f.cell), None)
            .is_err(),
        "the in-band enum gate did not refuse an out-of-enum joint"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// FOG-OF-WAR — the opponent's joints are unreadable from the sealed commitment.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn opponent_move_is_unreadable_before_reveal() {
    let secret = MoveCommit::new(P1, push(3), 0xDEADBEEF);
    let seal = secret.seal();

    let mut frame = Frame::new(P0, P1);
    frame.commit(P1, seal).unwrap();
    frame
        .commit(P0, MoveCommit::new(P0, push(1), 1).seal())
        .unwrap();
    frame.seal_commit_phase();

    // From P0's vantage, all that is observable about P1's move is the seal.
    let observed = frame.opponent_move_is_sealed(P0);
    assert_eq!(observed, Some(seal));

    // FOG-OF-WAR BINDING: no guess at P1's joints recovers them from the seal. We brute-force every
    // possible joint vector + a small nonce window; ONLY the true (joints, nonce) reproduces the
    // seal — i.e. the seal does not leak the joints (you'd need the secret nonce too).
    let mut matches_without_secret = 0usize;
    for combo in all_joint_vectors() {
        // Try the WRONG nonce (the attacker doesn't know the secret 0xDEADBEEF).
        for nonce in 0u64..64 {
            let guess = MoveCommit::new(P1, combo, nonce);
            if guess.seal() == seal {
                // Only the genuine secret should ever match; our window excludes it.
                matches_without_secret += 1;
            }
        }
    }
    assert_eq!(
        matches_without_secret, 0,
        "a guess WITHOUT the secret nonce reproduced the seal — the commitment is not hiding"
    );

    // And the genuine opening DOES match (binding is real, not vacuous).
    assert_eq!(MoveCommit::new(P1, push(3), 0xDEADBEEF).seal(), seal);
}

#[test]
fn peek_then_switch_is_refused() {
    // P1 commits to push(3). After "peeking", P1 tries to reveal a DIFFERENT move (push(2)). Its
    // seal is not among the commitments → refused (the binding tooth). This is the no-late-switch
    // guarantee.
    let committed = MoveCommit::new(P1, push(3), 7);
    let mut frame = Frame::new(P0, P1);
    frame
        .commit(P0, MoveCommit::new(P0, push(1), 1).seal())
        .unwrap();
    frame.commit(P1, committed.seal()).unwrap();
    frame.seal_commit_phase();

    let switched = MoveCommit::new(P1, push(2), 7); // changed joints, same figure+nonce
    assert_eq!(frame.reveal(switched), Err(TussleError::NotCommitted));

    // The honest reveal of the committed move is accepted.
    assert!(frame.reveal(committed).is_ok());
}

#[test]
fn reveal_before_commit_phase_closes_is_refused() {
    let mv = MoveCommit::new(P0, push(1), 1);
    let mut frame = Frame::new(P0, P1);
    frame.commit(P0, mv.seal()).unwrap();
    // Still in Commit phase — a reveal is refused (the state half of cap∧state).
    assert_eq!(frame.reveal(mv), Err(TussleError::NotRevealPhase));
}

// ─────────────────────────────────────────────────────────────────────────────
// CAP-GATING — a player cannot set the OPPONENT'S joints.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn player_cannot_pose_the_opponents_figure() {
    // P0 commits a move bound to its OWN figure. Then tries to reveal a move that poses P1's figure
    // (with the same joints+nonce) — the seal differs (figure is in the preimage), so it is not a
    // committed seal, AND if it somehow matched a commitment under P1 it would be WrongFigure.
    let mut frame = Frame::new(P0, P1);

    // A malicious P0 commits, under figure P0, a seal — then reveals a move claiming figure P1.
    let honest_p0 = MoveCommit::new(P0, push(2), 5);
    frame.commit(P0, honest_p0.seal()).unwrap();
    // P1 commits honestly too.
    let honest_p1 = MoveCommit::new(P1, push(1), 6);
    frame.commit(P1, honest_p1.seal()).unwrap();
    frame.seal_commit_phase();

    // P0 attempts to OVERRIDE P1's figure: a move posing figure P1 with P0's secret. Its seal is the
    // seal of (P1, push(2), 5), which is NOT the seal filed under P1 (that's (P1, push(1), 6)) →
    // refused. The opponent's figure is not P0's to set.
    let hijack = MoveCommit::new(P1, push(2), 5);
    let verdict = frame.reveal(hijack);
    assert!(
        matches!(
            verdict,
            Err(TussleError::NotCommitted) | Err(TussleError::WrongFigure { .. })
        ),
        "a player posing the opponent's figure was not refused: {verdict:?}"
    );

    // The honest moves both reveal fine.
    assert!(frame.reveal(honest_p0).is_ok());
    assert!(frame.reveal(honest_p1).is_ok());
}

#[test]
fn wrong_figure_binding_fires_on_a_mismatched_filing() {
    // The explicit WrongFigure arm: the move POSES figure P0 (so it has no commitment under P0's
    // key) yet its seal MATCHES a commitment filed under P1's key — a mismatched filing. The reveal
    // detects that the seal binds to a DIFFERENT figure than the one the move claims, and refuses
    // with WrongFigure. This is the cap tooth catching a move whose committed figure ≠ posed figure.
    let mut frame = Frame::new(P0, P1);

    // The move targets figure P0 (the seal's preimage carries P0).
    let move_for_p0 = MoveCommit::new(P0, push(2), 9);
    let seal_of_move_for_p0 = move_for_p0.seal();

    // …but it is filed under P1's key (the mismatched filing). Nothing is filed under P0.
    frame.commit(P1, seal_of_move_for_p0).unwrap();
    frame.seal_commit_phase();

    // Revealing the move (which claims figure P0) finds no commitment under P0, but its seal matches
    // the commitment filed under P1 → WrongFigure { revealed: P0, bound: P1 }.
    match frame.reveal(move_for_p0) {
        Err(TussleError::WrongFigure { revealed, bound }) => {
            assert_eq!(revealed, P0);
            assert_eq!(bound, P1);
        }
        other => panic!("expected WrongFigure, got {other:?}"),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// THE DETERMINISTIC RESOLUTION + REPRODUCIBILITY.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn drive_and_brace_are_pure_sums() {
    assert_eq!(forward_drive(&push(3)), 3);
    assert_eq!(forward_drive(&REST_POSE), 0);
    let mixed = pose(
        JointState::Contract, // +1
        JointState::Extend,   // -1
        JointState::Hold,     // 0, braces
        JointState::Relax,    // 0
    );
    assert_eq!(forward_drive(&mixed), 0);
    assert_eq!(brace(&mixed), 1);
    assert_eq!(brace(&push(3)), 0);
}

#[test]
fn stronger_pusher_scores_on_contact() {
    // Two figures one apart; P0 pushes hard (3), P1 pushes weakly (1). They make contact; P0's
    // effective hit (3) beats P1's (1) → P0 scores the margin (2).
    let a = push(3);
    let b = push(1);
    let r = resolve_contact((P0, -1, &a), (P1, 1, &b));
    let c = r.contact.expect("figures should have made contact");
    assert_eq!(c.striker, P0);
    assert_eq!(c.struck, P1);
    assert_eq!(c.points, 2);
    // One balanced score leg: bank → P0, amount 2.
    assert_eq!(r.score_legs.len(), 1);
    assert_eq!(r.score_legs[0].from, SCORE_BANK);
    assert_eq!(r.score_legs[0].to, P0);
    assert_eq!(r.score_legs[0].amount, 2);
}

#[test]
fn brace_cancels_the_opponents_drive() {
    // P0 pushes 2; P1 holds two joints (brace 2) and pushes the other two (drive 2). P0's effective
    // hit = 2 − 2 = 0; P1's = 2 − 0 = 2 → P1 scores 2. The brace negated P0's attack.
    let a = push(2);
    let mut b = REST_POSE;
    b[0] = JointState::Hold;
    b[1] = JointState::Hold;
    b[2] = JointState::Contract;
    b[3] = JointState::Contract;
    let r = resolve_contact((P0, -1, &a), (P1, 1, &b));
    let c = r.contact.expect("contact expected");
    assert_eq!(c.striker, P1);
    assert_eq!(c.points, 2);
}

#[test]
fn equal_clash_cancels_no_score() {
    // Both push 2 with no brace → equal effective hits → cancelled clash, no contact, empty ring.
    let a = push(2);
    let b = push(2);
    let r = resolve_contact((P0, -1, &a), (P1, 1, &b));
    assert_eq!(r.contact, None);
    assert!(r.score_legs.is_empty());
}

#[test]
fn no_contact_when_figures_stay_apart() {
    // Far apart, both Relax (no drive) → no contact, empty ring, positions unchanged.
    let a = REST_POSE;
    let b = REST_POSE;
    let r = resolve_contact((P0, -5, &a), (P1, 5, &b));
    assert_eq!(r.contact, None);
    assert!(r.score_legs.is_empty());
    assert_eq!(r.new_positions, (-5, 5));
}

#[test]
fn resolution_is_reproducible() {
    // THE REPRODUCIBILITY TOOTH: the same revealed moves + positions always give byte-identical
    // outcomes (a pure function — no clock, no randomness).
    let a = pose(
        JointState::Contract,
        JointState::Hold,
        JointState::Extend,
        JointState::Contract,
    );
    let b = pose(
        JointState::Extend,
        JointState::Contract,
        JointState::Hold,
        JointState::Relax,
    );
    let r1 = resolve_contact((P0, -1, &a), (P1, 1, &b));
    let r2 = resolve_contact((P0, -1, &a), (P1, 1, &b));
    let r3 = resolve_contact((P0, -1, &a), (P1, 1, &b));
    assert_eq!(r1, r2);
    assert_eq!(r2, r3);
}

// ─────────────────────────────────────────────────────────────────────────────
// THE VERIFIED JOINT TURN + a full match.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn frame_resolves_through_the_verified_executor() {
    // One frame, end to end, through the verified per-asset executor. P0 out-pushes P1 and scores.
    let mut m = Match::new(P0, P1, 1, 5, 8);
    let before_bank = m.ledger.get(SCORE_BANK, &SCORE_ASSET);
    let before_total = m.ledger.total_asset(&SCORE_ASSET);

    let r = m
        .play_frame(
            MoveCommit::new(P0, push(3), 1),
            MoveCommit::new(P1, push(1), 2),
        )
        .expect("frame should resolve through the verified executor");
    let c = r.contact.expect("contact expected");
    assert_eq!(c.striker, P0);
    assert_eq!(c.points, 2);

    // The verified ledger moved exactly the points, bank → P0, and CONSERVED the total supply.
    assert_eq!(m.score0(), 2);
    assert_eq!(m.score1(), 0);
    assert_eq!(m.ledger.get(SCORE_BANK, &SCORE_ASSET), before_bank - 2);
    assert_eq!(m.ledger.total_asset(&SCORE_ASSET), before_total);

    // The figure cell's score slot mirrors the verified ledger column.
    assert_eq!(m.f0.score(), 2);
}

#[test]
fn empty_ring_frame_is_a_conserving_noop() {
    // A frame with no contact (both far + Relax) folds an empty ring — a conserving no-op that still
    // advances the match (a logged frame, unchanged scores).
    let mut m = Match::new(P0, P1, 5, 10, 8);
    let total0 = m.ledger.total_asset(&SCORE_ASSET);
    m.play_frame(
        MoveCommit::new(P0, REST_POSE, 1),
        MoveCommit::new(P1, REST_POSE, 2),
    )
    .unwrap();
    assert_eq!(m.score0(), 0);
    assert_eq!(m.score1(), 0);
    assert_eq!(m.ledger.total_asset(&SCORE_ASSET), total0);
    assert_eq!(m.log.len(), 1);
}

#[test]
fn full_match_plays_to_a_knockout() {
    // A scripted match: P0 keeps out-pushing P1 across frames until it reaches the target score.
    // Every frame is a verified joint turn; the match ends on a knockout.
    let mut m = Match::new(P0, P1, 1, 4, 16);
    let mut nonce = 0u64;
    while m.outcome().is_none() {
        nonce += 1;
        // P0 pushes 3, P1 pushes 1 → P0 scores 2 each contact frame. After contact they're touching;
        // P0 keeps pushing (3) and P1 relaxes, so P0 keeps landing.
        let _ = m.play_frame(
            MoveCommit::new(P0, push(3), nonce),
            MoveCommit::new(P1, push(1), nonce + 1000),
        );
    }
    match m.outcome().unwrap() {
        MatchEnd::TargetReached(w) => assert_eq!(w, P0, "P0 should win the knockout"),
        other => panic!("expected a knockout, got {other:?}"),
    }
    assert!(m.score0() >= m.target);
    // Conservation across the WHOLE match: the total point supply never changed.
    // (bank seeded 2*target+2; figures + bank still sum to that.)
    assert_eq!(
        m.ledger.total_asset(&SCORE_ASSET),
        (m.target * 2 + 2),
        "the match did not conserve points"
    );
}

#[test]
fn match_is_reproducible_end_to_end() {
    // THE MATCH-LEVEL REPRODUCIBILITY TOOTH: the same scripted moves produce the same final scores
    // and the same frame log — a deterministic, verifiable match.
    fn play_scripted() -> (i128, i128, usize) {
        let mut m = Match::new(P0, P1, 1, 6, 20);
        let script: [(JointVector, JointVector); 4] = [
            (push(3), push(1)),
            (push(2), push(2)), // cancels
            (push(3), push(0)),
            (push(1), push(3)),
        ];
        for (i, (a, b)) in script.iter().enumerate() {
            if m.outcome().is_some() {
                break;
            }
            let _ = m.play_frame(
                MoveCommit::new(P0, *a, i as u64),
                MoveCommit::new(P1, *b, (i + 100) as u64),
            );
        }
        (m.score0(), m.score1(), m.log.len())
    }
    let run1 = play_scripted();
    let run2 = play_scripted();
    assert_eq!(run1, run2, "the same scripted match diverged between runs");
}

// ─────────────────────────────────────────────────────────────────────────────
// Helpers.
// ─────────────────────────────────────────────────────────────────────────────

/// Every possible joint vector (4 joints × 4 states = 256) — for the fog-of-war brute force.
fn all_joint_vectors() -> Vec<JointVector> {
    let states = JointState::ALL;
    let mut out = Vec::with_capacity(256);
    for &a in &states {
        for &b in &states {
            for &c in &states {
                for &d in &states {
                    out.push([a, b, c, d]);
                }
            }
        }
    }
    out
}
