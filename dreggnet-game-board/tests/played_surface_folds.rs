//! # THE PAYOFF — a match PLAYED on the deployed surface now LOWERS to the proven descriptors.
//!
//! Before this, the playable automatafl surface hosted an invented 5×5 mini-variant while every
//! emitted Lean descriptor (and every theorem) lived at n=11. Two consequences, both fatal to the
//! crown:
//!
//! 1. `descriptor_by_name("dregg-automatafl-step-d1-n5")` returned `None`, so EVERY fold of a
//!    played match was `MatchError::NoDescriptor`-blocked. No automatafl match had ever ranked, or
//!    could;
//! 2. the surface kept no move history, so the only shape left to fold was
//!    `AutomataflMatch::automaton_only` — which, in the game-board crate's own words, "attests K
//!    INDEPENDENT automaton steps and NO MOVE AT ALL".
//!
//! This file drives the REAL offering (`select → commit ×2 → reveal ×2 → resolve`, every step a
//! committed executor turn), takes the genesis board + the recorded rounds straight off the
//! session, and shows that object lowering: both Lean descriptors RESOLVE by name at the played
//! board size, the witness generator fills them, both traces SATISFY the descriptors, and Leg R's
//! OUT window equals Leg A's IN window (the mid seam the fold `connect`s).
//!
//! WHAT THIS DOES NOT SHOW: the recursion fold itself. `AutomataflMatch::leaves()` fills each
//! leaf's state door via `fixture_rotated_roots`, which MINTS a real wide Custom leg (~50s per
//! leaf, ~100s per round) — so the full-`leaves()` gate is `#[ignore]`d with that cost named, and
//! the light-client accept over the folded artifact is the separate (tens of minutes)
//! `end_to_end.rs` gate. What runs here is the lowering, which is exactly the step that was
//! IMPOSSIBLE before.

use dregg_automatafl::game::{COMMIT, RESOLVE, REVEAL, SELECT, index_of};
use dregg_automatafl::reference::{Coord, Move};
use dregg_automatafl::surface::{AutomataflOffering, AutomataflSession, Seat};
use dregg_circuit::field::BabyBear;
use dreggnet_game_board::{AutomataflMatch, MatchError};
use dreggnet_offerings::{Action, DreggIdentity, Offering, SessionConfig};

fn act(turn: &str, arg: i64) -> Action {
    Action::new(turn, turn, arg, true)
}

fn seat(s: Seat) -> DreggIdentity {
    AutomataflOffering::seat_identity(s)
}

/// Seal one seat's move through the real surface (select, then commit) — both real turns.
fn seal(off: &AutomataflOffering, s: &mut AutomataflSession, who: Seat, frm: Coord, to: Coord) {
    assert!(
        off.advance(
            s,
            act(SELECT, index_of(frm).expect("in bounds") as i64),
            seat(who)
        )
        .landed(),
        "the select lands a real turn"
    );
    assert!(
        off.advance(
            s,
            act(COMMIT, index_of(to).expect("in bounds") as i64),
            seat(who)
        )
        .landed(),
        "the seal lands a real turn"
    );
}

/// Drive ONE full round of the real offering with the given moves, returning the live session.
fn play_one_round(seed: u64, a: Move, b: Move) -> AutomataflSession {
    let off = AutomataflOffering;
    let mut s = off.open(SessionConfig::with_seed(seed)).expect("open");
    seal(&off, &mut s, Seat::A, a.frm, a.to);
    seal(&off, &mut s, Seat::B, b.frm, b.to);
    assert!(off.advance(&mut s, act(REVEAL, 0), seat(Seat::A)).landed());
    assert!(off.advance(&mut s, act(REVEAL, 0), seat(Seat::B)).landed());
    assert!(
        off.advance(&mut s, act(RESOLVE, 0), seat(Seat::A)).landed(),
        "the resolution lands one real turn"
    );
    s
}

/// The CLEAN stock round: two independent, unoccluded attractor moves off the `y = 1` rank (the
/// pair `resolve_witness::clean_resolve_satisfies` pins against the Lean descriptor).
fn clean_round() -> (Move, Move) {
    (
        Move {
            who: 0,
            frm: (3, 1),
            to: (3, 3),
        },
        Move {
            who: 1,
            frm: (7, 1),
            to: (7, 3),
        },
    )
}

/// **THE PAYOFF, RUN.** A round played on the deployed surface lowers: both descriptors resolve by
/// name at the played size, the witness generator fills them, both traces SATISFY the PROVEN Lean
/// descriptors, and the mid seam (`R.OUT == A.IN`) holds. At the old 5×5 board this test could not
/// even reach its first assertion — `descriptor_by_name` returned `None`.
#[test]
fn a_round_played_on_the_surface_lowers_to_the_proven_lean_descriptors() {
    use dregg_automatafl::resolve_witness::{
        automatafl_resolve_trace, resolve_board_window, resolve_descriptor_ident,
        resolve_trace_accepts,
    };
    use dregg_automatafl::witness::{
        automatafl_step_trace, step_board_window, step_descriptor_name, step_trace_accepts,
    };
    use dregg_circuit::descriptor_by_name::descriptor_by_name;
    use dregg_circuit::effect_vm::custom_state_binding::extract_custom_pi_board_window;

    let (ma, mb) = clean_round();
    let session = play_one_round(0xC1EA, ma, mb);

    // The surface RECORDED the round (the change that makes any of this possible).
    assert_eq!(
        session.rounds(),
        &[(ma, mb)],
        "the played round is on the session, in seat order"
    );
    assert_eq!(session.unfoldable_round(), None, "the round is clean");

    let start = session.start_board().clone();
    let n = start.n;
    assert_eq!(n, 11, "the PLAYED board is the stock 11x11 game");

    // ── THE THING THAT USED TO RETURN `None`.
    let rdesc = descriptor_by_name(resolve_descriptor_ident(n))
        .expect("the n=11 RESOLVE descriptor dispatches by name (at n=5 this was None)");
    let sdesc = descriptor_by_name(&step_descriptor_name(n))
        .expect("the n=11 STEP descriptor dispatches by name (at n=5 this was None)");
    assert_eq!(sdesc.name, "dregg-automatafl-step-d1-n11");
    assert_eq!(sdesc.public_input_count, 38);

    // ── Leg R: the players' own moves, adjudicated by the Lean resolve descriptor.
    let rt = automatafl_resolve_trace(&start, &[ma, mb], &rdesc)
        .expect("the witness generator fills Leg R for the played round");
    assert!(
        resolve_trace_accepts(&rdesc, &rt),
        "Leg R SATISFIES the proven Lean resolve descriptor — the players' moves, in-circuit"
    );

    // The adjudicated mid is the board the surface itself played through (`resolve_mid`).
    let layout = dregg_automatafl::resolve_layout::ResolveLayout::new(n);
    let mid = rt.mid_board(&layout);
    let oracle_mid = dregg_automatafl::reference::resolve_mid(&start, &[ma, mb]);
    assert_eq!(
        mid.cells, oracle_mid.cells,
        "the descriptor's adjudicated mid IS the board the surface resolved"
    );

    // ── Leg A: the automaton's step.
    let st = automatafl_step_trace(&mid, &sdesc).expect("the witness generator fills Leg A");
    assert!(
        step_trace_accepts(&sdesc, &st),
        "Leg A SATISFIES the proven Lean step descriptor"
    );

    // ── THE MID SEAM: Leg R's OUT window is Leg A's IN window — the equality the fold `connect`s.
    let rwin = resolve_board_window(n, &rdesc).expect("Leg R declares a board window");
    let awin = step_board_window(n, &sdesc).expect("Leg A declares a board window");
    let (r_in, r_out): (Vec<BabyBear>, Vec<BabyBear>) =
        extract_custom_pi_board_window(&rt.public_inputs, &rwin)
            .expect("Leg R's window is expressible in its PIs");
    let (a_in, a_out): (Vec<BabyBear>, Vec<BabyBear>) =
        extract_custom_pi_board_window(&st.public_inputs, &awin)
            .expect("Leg A's window is expressible in its PIs");
    assert_eq!(r_in.len(), 11, "the window is pack(9) ‖ auto(2)");
    assert_eq!(
        r_out, a_in,
        "R.OUT == A.IN — the mid seam (hseamPack ∧ hseamAutoX ∧ hseamAutoY)"
    );

    // …and the chain's OUT is the board the players are looking at right now.
    let final_board = session.board();
    let mut expect_out: Vec<BabyBear> = Vec::new();
    let k = final_board.n * final_board.n;
    for f in 0..k.div_ceil(15) {
        let mut acc: u64 = 0;
        for i in 0..15usize {
            let c = f * 15 + i;
            if c < k {
                acc += u64::from(final_board.cells[c]) * 4u64.pow(i as u32);
            }
        }
        expect_out.push(BabyBear::from_u64(acc));
    }
    expect_out.push(BabyBear::from_u64(final_board.auto.0 as u64));
    expect_out.push(BabyBear::from_u64(final_board.auto.1 as u64));
    assert_eq!(
        a_out, expect_out,
        "the chain's final OUT window IS the committed board the surface shows"
    );
}

/// **A CONFLICTING ROUND REFUSES TO FOLD, BY NAME.** Both seats fork the same source: the surface
/// resolves it by DROPPING both moves (the audited-WRONG rule — the ruleset marks the contested
/// square and re-enters the round, the Leg C braid that is not wired to the surface). The round is
/// genuinely played and genuinely recorded, and the fold refuses it as
/// [`MatchError::ConflictingRound`] rather than mint a proof of a transition the rules never
/// licensed. Fast: the gate fires before any witness generation.
#[test]
fn a_conflicting_round_refuses_to_fold_blocked_not_faked() {
    let ma = Move {
        who: 0,
        frm: (3, 1),
        to: (3, 3),
    };
    let mb = Move {
        who: 1,
        frm: (3, 1),
        to: (5, 1),
    };
    let session = play_one_round(0xC0DE, ma, mb);
    assert_eq!(
        session.rounds().len(),
        1,
        "the round WAS played and recorded"
    );
    assert_eq!(
        session.unfoldable_round(),
        Some(0),
        "the session names the round that blocks the crown"
    );

    let err = AutomataflMatch::played(session.start_board().clone(), session.rounds().to_vec())
        .leaves()
        .err();
    assert!(
        matches!(err, Some(MatchError::ConflictingRound(0))),
        "a conflicting round is BLOCKED by name, not folded and not faked; got {err:?}"
    );
}

/// **THE FULL LOWERING, INCLUDING THE MINTED STATE DOORS.** `leaves()` fills each leaf's
/// `[old8 ‖ new8]` door with the REAL rotated roots of the leg the fold will mint for that chain
/// position (`fixture_rotated_roots` → `mint_custom_leg`), which is a real wide Custom leg per
/// leaf. That is the only slow part: the lowering itself is the `#[test]` above.
#[test]
#[ignore = "SLOW (~50s per leaf, ~100s for the one round): leaves() mints a real wide Custom leg \
            per leaf to fill its state door (fixture_rotated_roots). Run with --ignored."]
fn the_played_round_mints_two_chained_leaves() {
    let (ma, mb) = clean_round();
    let session = play_one_round(0xF01D, ma, mb);
    let m = AutomataflMatch::played(session.start_board().clone(), session.rounds().to_vec());
    let leaves = m.leaves().expect("the played clean round lowers at n=11");

    assert_eq!(leaves.len(), 2, "ONE round == TWO chained legs (R then A)");
    let names: Vec<String> = leaves
        .iter()
        .map(|l| {
            l.descriptor_state_leaf
                .as_ref()
                .expect("every round leaf proves a Lean descriptor")
                .descriptor
                .name
                .clone()
        })
        .collect();
    assert!(names[0].contains("resolve"), "leg 0 is RESOLVE: {names:?}");
    assert!(names[1].contains("step"), "leg 1 is STEP: {names:?}");
}
