//! ⚑ **THE CONFLICT FOLD IS REACHABLE FROM THE PLAYED SURFACE.**
//!
//! `tests/multi_round_fold.rs` proves the Leg C braid folds — from HAND-BUILT `MultiRoundTurn`
//! fixtures. That was the whole gap: `MultiRoundTurn::new` / `conflict_only` appeared ONLY in tests,
//! because no surface could produce a turn with conflict rounds in it. The played surface resolved a
//! clash by forcing `roundStep`'s clean arm, which (the fork/collide clauses living in `roundStep`
//! and NOT in `resolveMoves`) executed whichever move survived the path check and discarded the
//! other — so a conflicting turn was both the audited-WRONG game AND unfoldable by either path.
//!
//! This test closes the loop from the other end. It PLAYS a real match through
//! [`AutomataflOffering`] — every advance a committed executor turn — forces a clash, re-submits,
//! resolves, and hands the session's own recorded [`PlayedTurn`] straight to
//! [`MultiRoundTurn`]. Then it mints the leaves.
//!
//! ## What minting the leaves already proves (it is not a shape check)
//!
//! Every leaf is gated, BEFORE any proving, by the fail-closed witness-gen canary that runs the real
//! row-local `Ir2Air` evaluator against the PROVEN Lean descriptor:
//!
//! * each conflict round through `legc_trace_accepts` / `automataflLegCDescN 11`, and the 32-lane
//!   RoundState window is cross-checked against the descriptor's own PI layout
//!   (`MatchError::NoDescriptor` otherwise);
//! * the terminating round through `resolve_marks_trace_accepts` / `automataflResolveMarksDescN 11`
//!   — which carries `AutomataflResolveMarksCapstone.resolveMarksMoveLegal`, the M6 marks-legality
//!   NOR pin. So the surface's marks RE-CHECK is not only enforced off-circuit at the commit gate;
//!   the AIR itself refuses a terminating move that names an accumulated mark;
//! * the automaton step through `step_marks_trace_accepts` / `automataflStepMarksDescN 11`.
//!
//! And the accumulated marks are read back off the Leg C TRACE, never re-derived — so asserting they
//! equal the coordinate the SURFACE marked is a real coherence check between the played board and
//! the circuit.
//!
//! ## HONEST SCOPE
//!
//! The full recursive fold ([`MultiRoundTurn::prove`]) is `#[ignore]`d with its cost — the sibling
//! `multi_round_fold.rs::the_whole_multi_round_turn_folds_to_one_verifying_proof` is the ~1663 s
//! green gate for that, over the same shape. What is asserted un-ignored here is what a default gate
//! can afford: the leaves MINT from surface-played data, the windows line up, and the marks agree.
//! The STARK still inherits the undischarged FRI/STARK soundness floor.

use dregg_automatafl::AutomataflOffering;
use dregg_automatafl::board::{Coord, Move};
use dregg_automatafl::game::{COMMIT, RESOLVE, REVEAL, SELECT, index_of};
use dregg_automatafl::surface::{AutomataflSession, Phase, Seat};
use dreggnet_game_board::MultiRoundTurn;
use dreggnet_offerings::{Action, DreggIdentity, Offering, Outcome, SessionConfig};

/// The stock opening's `y = 1` attractor both seats fork.
const FORK_SRC: Coord = (3, 1);

fn act(turn: &str, arg: i64) -> Action {
    Action::new(turn, turn, arg, true)
}

fn seat(s: Seat) -> DreggIdentity {
    AutomataflOffering::seat_identity(s)
}

/// Drive one seat's whole submission (select → seal), asserting both land real executor turns.
fn seal(off: &AutomataflOffering, s: &mut AutomataflSession, who: Seat, frm: Coord, to: Coord) {
    for (turn, c) in [(SELECT, frm), (COMMIT, to)] {
        let out = off.advance(
            s,
            act(turn, index_of(c).expect("in bounds") as i64),
            seat(who),
        );
        assert!(
            out.landed(),
            "seat {} `{turn}` at {c:?} must land a real turn, got {out:?}",
            who.label()
        );
    }
}

/// One whole round: both seats seal, both open, one resolve.
fn round(
    off: &AutomataflOffering,
    s: &mut AutomataflSession,
    a: (Coord, Coord),
    b: (Coord, Coord),
) -> Outcome {
    seal(off, s, Seat::A, a.0, a.1);
    seal(off, s, Seat::B, b.0, b.1);
    for who in [Seat::A, Seat::B] {
        assert!(off.advance(s, act(REVEAL, 0), seat(who)).landed());
    }
    off.advance(s, act(RESOLVE, 0), seat(Seat::A))
}

/// The played turn this whole file is about: ONE turn, ONE conflict round, ONE terminating clean
/// round — produced by driving the real offering, not assembled by hand.
fn play_a_conflicted_turn() -> MultiRoundTurn {
    let off = AutomataflOffering;
    let mut s = off
        .open(SessionConfig::with_seed(0xC1A5))
        .expect("the automatafl offering opens (the Lean game oracle answers)");

    // ROUND 1 — a FORK on the attractor at (3,1). The ruleset marks it and re-opens the round.
    assert!(round(&off, &mut s, (FORK_SRC, (3, 3)), (FORK_SRC, (5, 1))).landed());
    assert_eq!(
        s.phase(),
        Phase::Resubmit,
        "the clash RE-ENTERED the round rather than resolving it"
    );
    assert_eq!(
        s.marks(),
        [FORK_SRC].as_slice(),
        "the Lean marked the fork source"
    );
    assert_eq!(s.turn_no(), 0, "and the turn did not advance");

    // ROUND 2 — a clean pair off the `y = 9` rank; neither move names the mark.
    assert!(round(&off, &mut s, ((3, 9), (3, 7)), ((7, 9), (7, 7))).landed());
    assert_eq!(s.turn_no(), 1, "NOW the turn resolved");
    assert!(s.marks().is_empty(), "and the markers died with it");

    let turns = s.turns_played();
    assert_eq!(turns.len(), 1, "one played turn, two rounds");
    let t = &turns[0];
    assert_eq!(
        t.conflict_subs,
        vec![[
            Move {
                who: 0,
                frm: FORK_SRC,
                to: (3, 3)
            },
            Move {
                who: 1,
                frm: FORK_SRC,
                to: (5, 1)
            },
        ]],
        "the conflict round's submissions are recorded — the Leg C braid's input"
    );
    assert_eq!(
        t.clean_subs,
        [
            Move {
                who: 0,
                frm: (3, 9),
                to: (3, 7)
            },
            Move {
                who: 1,
                frm: (7, 9),
                to: (7, 7)
            },
        ]
    );
    MultiRoundTurn::new(t.start.clone(), t.conflict_subs.clone(), t.clean_subs)
}

/// ⚑ **A SURFACE-PLAYED CONFLICTED TURN MINTS THE WHOLE `MultiRoundTurn` LEAF SET** — the conflict
/// braid, the marks-aware terminating round, and the marks the two agree on.
///
/// This is the assertion the gap was about: before the re-submission loop existed, there was no way
/// to GET this object out of a played match, so `MultiRoundTurn` was fixture-only.
#[test]
fn a_conflicted_turn_played_on_the_surface_mints_the_conflict_braid_and_the_clean_handoff() {
    let turn = play_a_conflicted_turn();

    // ── (1) THE MARKS AGREE. `accumulated_marks` fills each conflict round's Leg C trace (gated by
    // the fail-closed `legc_trace_accepts`) and reads the LAST round's `marksOut` off the trace's own
    // per-cell column — never re-derived from an oracle. So this is the CIRCUIT's marks equalling
    // the coordinate the played surface burned.
    let marks = turn
        .accumulated_marks()
        .expect("the conflict braid fills and its Leg C traces are accepted");
    assert_eq!(
        marks,
        vec![FORK_SRC],
        "the marks the Leg C TRACE produced are the square the surface marked"
    );

    // ── (2) THE CONFLICT BRAID MINTS. One Leg C leaf per conflict round, each already verified
    // against the PROVEN `automataflLegCDescN 11` by the row-local evaluator, each declaring the
    // 32-lane RoundState window (cross-checked against the descriptor's PI layout inside).
    let conflict = turn
        .conflict_leaves()
        .expect("every conflict round mints a Leg C leaf the Lean descriptor accepts");
    assert_eq!(
        conflict.len(),
        turn.conflict_subs.len(),
        "one Leg C leaf per conflict round"
    );

    // ── (3) THE TERMINATING ROUND MINTS, MARKS AND ALL. Leg RM (marks-aware resolve, carrying the
    // M6 legality NOR pin) then the marks-carrying Leg A — both 20-lane, so the clean sub-chain is
    // uniform and the whole window chain has exactly ONE width change (the 32 → 20 handoff), which
    // is what the deployed mixed-width root admits.
    let clean = turn
        .clean_leaves()
        .expect("the terminating round mints Leg RM + Leg A against the accumulated marks");
    assert_eq!(clean.len(), 2, "Leg RM then Leg A");

    // ── (4) THE NEGATIVE, and it is the one that matters: a terminating move that NAMES the
    // accumulated mark is refused BY THE AIR, not merely by the surface's commit gate. Same braid,
    // same marks — only the terminating pair changed, to one that moves the marked piece.
    let illegal = MultiRoundTurn::new(
        turn.start.clone(),
        turn.conflict_subs.clone(),
        [
            Move {
                who: 0,
                frm: FORK_SRC,
                to: (3, 4),
            },
            Move {
                who: 1,
                frm: (7, 9),
                to: (7, 7),
            },
        ],
    );
    assert!(
        illegal.clean_leaves().is_err(),
        "a terminating move OFF an accumulated mark must be refused by the marks-legality pin, \
         not minted"
    );
}

/// The full recursive fold of the surface-played turn — the conflict braid ∘ Leg RM ∘ Leg A welded
/// into ONE `WholeChainProof` a pure light client accepts.
///
/// `#[ignore]`d for COST, not for doubt: the sibling
/// `multi_round_fold.rs::the_whole_multi_round_turn_folds_to_one_verifying_proof` is the green gate
/// for this shape at ~1663 s (~28 min) on a warm box, and this run is the same order — a
/// two-round turn is 3 leaves through the mixed-width clean-handoff root. Run it with
/// `--ignored` when you want the end-to-end number for a surface-played turn specifically.
#[test]
#[ignore = "the real recursive STARK fold: ~1600 s+ (see multi_round_fold.rs for the green gate)"]
fn the_surface_played_conflicted_turn_folds_to_one_verifying_proof() {
    let turn = play_a_conflicted_turn();
    let proof = turn
        .prove()
        .expect("the surface-played conflict turn folds to one self-attested proof");
    assert!(
        !proof.proof_bytes.is_empty(),
        "the fold produced a real proof envelope"
    );
}
