//! **THE MULTI-ROUND CONFLICT BRAID (M7, Rust half)** — the canaries for a turn that resolves over
//! `k` CONFLICT rounds (each a `roundStep` `.again` re-entry) before its terminating clean round.
//!
//! A conflict round lowers to ONE **Leg C** leaf (`automataflLegCDescN 11`, HASH-FREE, ZERO
//! lookups) that declares the whole 32-lane RoundState window
//! `[board(9) ‖ marks(9) ‖ locked(10) ‖ waiting(2) ‖ auto(2)]`
//! ([`leg_c_roundstate_window_n11`]). The ONLY cross-leaf rule is
//!
//! ```text
//!     C_i.OUT  ==  C_{i+1}.IN
//! ```
//!
//! which the deployed `aggregate_tree` connects lane-by-lane (the width is auto-derived from the
//! exposed shape — a same-width Leg C chain folds through `fold_match` with NO M7-specific prover
//! code). The chain accumulates the marks overlay (`marksIn_0 = ∅`, `marksIn_{i+1} = marksOut_i`),
//! so a DROPPED round (a downstream `marksIn` the upstream never produced) or a SUBSTITUTED round
//! (a forged `marksOut`) is a broken seam — a `WitnessConflict`, a witness that does not exist.
//!
//! **THE SUBSTRATE, SAID OUT LOUD:** every constraint object here — the Leg C descriptor, its
//! pack/marks layout, its PI ABI — is **Lean-authored AIR** (`AutomataflLegCEmit.lean`, emitted
//! through `EmitByName.lean` into `circuit/descriptors/by-name/automatafl-legc-n11.json`, refined by
//! `legC_sat_imp_roundAgainN`). This file fills traces and drives the seam. It authors zero
//! constraints.
//!
//! **WHAT A GREEN HERE MEANS — READ BEFORE TRUSTING ONE.** Three tiers, only the first two run:
//!
//! 1. **PI / host-mirror level (runs, green, FAST — no leg mint).** For real clashing 11×11 rounds
//!    through the real Lean Leg C descriptor: each round SATISFIES the descriptor (the fail-closed
//!    witness-gen canary), `C_i.OUT == C_{i+1}.IN` over the whole 32-lane RoundState window, the
//!    chain exposes `[first.IN ‖ last.OUT]`, and each negative (dropped / substituted / marked-move)
//!    moves a lane the seam or the descriptor bites on. That is the seam's *content* and the
//!    negatives' *bite*. These fill traces directly, bypassing the ~50s-per-leg door mint (the
//!    RoundState window lives at PI ≥ 16; the door at PI [0,16) is irrelevant to it).
//! 2. **Producer, one round (runs, green, ~50s — mints ONE real leg).**
//!    `conflict_leaves_mints_a_foldable_leg_c_leaf` exercises the deployed `MultiRoundTurn::
//!    conflict_leaves` end to end: door + descriptor source + 32-lane window, foldable.
//! 3. **Deployed prover, whole braid (`#[ignore]`d, NOT RUN).** A real conflict-chain fold, tens of
//!    minutes.
//!
//! **THE CLEAN-ROUND HANDOFF — the marks half is CLOSED at mint, and the sub-chain is UNIFORM-20.**
//! The terminating clean round is the marks-aware **Leg RM** (`automataflResolveMarksDescN 11`, EMITTED
//! as `automatafl-resolve-marks-n11.json` + `automatafl_resolve_marks_trace`) then the marks-carrying
//! automaton **Leg A** step (`automataflStepMarksDescN 11`, EMITTED as `automatafl-step-marks-n11.json`
//! + `automatafl_step_marks_trace`). `MultiRoundTurn::clean_leaves` mints it with `marksIn` = the
//! conflict chain's `marksOut`; BOTH legs declare the 20-lane `[board(9) ‖ marks(9) ‖ auto(2)]` window
//! (Leg A carries the marks FROZEN), whose 18-lane `board ‖ marks` prefix matches the conflict rounds'
//! RoundState handoff lanes. So BOTH halves of the `C_last → R` handoff line up, Leg RM re-checks the
//! terminating move against the accumulated marks (the M6 legality NOR pin), and the clean sub-chain
//! `RM(20) → A(20)` is UNIFORM. The canaries below assert the marks half holds, `marksIn` equals the
//! conflict `marksOut`, a dropped round breaks the MARKS seam, and a clean-round move onto a mark is
//! UNSAT.
//!
//! **THE WHOLE TURN WELDS INTO ONE ROOT (residuals CLOSED).** (2) The `WholeChainProof` assembler for
//! the clean-handoff root is BUILT (`fold_clean_handoff_match` / `prove_clean_handoff_chain_recursive`,
//! driven by `MultiRoundTurn::prove`) — section (d) drives its host claim (the mixed `[32 ‖ 20]` window
//! + turn count) fast. (1) The clean sub-chain is now UNIFORM-20 (Leg RM 20 ∘ the marks-carrying Leg A
//! 20), so it folds through the deployed uniform `aggregate_tree` and the assembler's host board-window
//! mirror ACCEPTS it (exactly one C→R width change); the former mixed-20/11 refusal is now a REGRESSION
//! guard on the retired 11-lane plain step (section (d)). The whole-turn end-to-end is un-blocked — the
//! tier-3 gate in section (d) is `#[ignore]`-free. See `MultiRoundTurn`'s type doc.

use dregg_automatafl::legc_layout::LegCLayout;
use dregg_automatafl::legc_witness::{
    LegCTrace, RoundStateIn, automatafl_legc_trace, legc_descriptor_ident, legc_trace_accepts,
};
use dregg_automatafl::reference::{ATT, AUTO, Board, Coord, Move, VAC};
use dregg_circuit::descriptor_by_name::descriptor_by_name;
use dregg_circuit::descriptor_ir2::EffectVmDescriptor2;
use dregg_circuit::effect_vm::custom_state_binding::{
    extract_custom_pi_board_window, leg_c_roundstate_window_n11, roundstate_window_n11,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::ivc_turn_chain::clean_handoff_root_board_window;
use dreggnet_game_board::MultiRoundTurn;

const N: usize = 11;

/// The shared `board ‖ marks` prefix the `C_last → R` clean handoff connects (18 = board(9) ‖
/// marks(9) at n = 11).
const HANDOFF: usize = roundstate_window_n11::HANDOFF_LANES;

// The 32-lane RoundState sub-window offsets (the layout `leg_c_roundstate_window_n11` extracts in
// order): board ‖ marks ‖ locked ‖ waiting ‖ auto.
const BOARD: std::ops::Range<usize> = 0..9;
const MARKS: std::ops::Range<usize> = 9..18;

fn mv(who: u32, frm: Coord, to: Coord) -> Move {
    Move { who, frm, to }
}

/// A blank `11×11` board with the automaton parked at `auto` and the listed attractors placed.
fn board_with(auto: Coord, attractors: &[Coord]) -> Board {
    let mut cells = vec![VAC; N * N];
    for &(x, y) in attractors {
        cells[(y as usize) * N + (x as usize)] = ATT;
    }
    cells[(auto.1 as usize) * N + (auto.0 as usize)] = AUTO;
    Board {
        n: N,
        cells,
        auto,
        col_rule: true,
    }
}

/// **THE 3-CONFLICT-ROUND TURN.** Three forks — at `(0,0)`, `(5,5)`, `(8,8)` — each a `roundStep`
/// `.again` re-entry that marks its clashed source and freezes the board; then a clean round moving
/// two attractors (`(0,7)`, `(7,0)`) that were never marked. Disjoint sources/paths so the forks and
/// the clean resolution never interact.
fn three_conflict_turn() -> MultiRoundTurn {
    let start = board_with((10, 10), &[(0, 0), (5, 5), (8, 8), (0, 7), (7, 0)]);
    let conflict_subs = vec![
        [mv(0, (0, 0), (0, 2)), mv(1, (0, 0), (2, 0))], // fork at (0,0)
        [mv(0, (5, 5), (5, 7)), mv(1, (5, 5), (7, 5))], // fork at (5,5)
        [mv(0, (8, 8), (8, 10)), mv(1, (8, 8), (10, 8))], // fork at (8,8)
    ];
    let clean = [mv(0, (0, 7), (2, 7)), mv(1, (7, 0), (7, 2))];
    MultiRoundTurn::new(start, conflict_subs, clean)
}

fn legc_desc() -> EffectVmDescriptor2 {
    descriptor_by_name(&legc_descriptor_ident(N)).expect("the n=11 Leg C descriptor dispatches")
}

/// Decode a Leg C trace's per-cell `marksOut` overlay into a coordinate list (the next round's
/// `marksIn`) — the same ground-truth accumulation `conflict_leaves` does, read off the trace.
fn marks_out(tr: &LegCTrace, l: &LegCLayout) -> Vec<Coord> {
    (0..N * N)
        .filter(|&c| tr.row[l.c_marks_out_cell(c)] == BabyBear::ONE)
        .map(|c| ((c % N) as i32, (c / N) as i32))
        .collect()
}

/// **FILL A TURN'S CONFLICT BRAID DIRECTLY** — the k Leg C traces (accumulating marks round to
/// round), gated by `legc_trace_accepts`, WITHOUT minting the door legs. The fast host-mirror path
/// for every window/seam canary (mirrors the two-leg file's `round_windows_direct`).
fn conflict_traces(turn: &MultiRoundTurn) -> Vec<LegCTrace> {
    let cdesc = legc_desc();
    let l = LegCLayout::new(N);
    let mut marks: Vec<Coord> = Vec::new(); // marksIn_0 = ∅
    let mut out = Vec::with_capacity(turn.conflict_subs.len());
    for (i, subs) in turn.conflict_subs.iter().enumerate() {
        let rs = RoundStateIn {
            board: turn.start.clone(),
            marks: marks.clone(),
        };
        let tr = automatafl_legc_trace(&rs, subs, &cdesc)
            .unwrap_or_else(|e| panic!("conflict round {i} fill: {e}"));
        assert!(
            legc_trace_accepts(&cdesc, &tr),
            "conflict round {i} must satisfy the PROVEN Leg C descriptor"
        );
        marks = marks_out(&tr, &l);
        out.push(tr);
    }
    out
}

/// The declared `(IN, OUT)` 32-lane RoundState windows of a Leg C trace, through the SAME extractor
/// the fold uses (reads the trace's own public inputs; the door lanes are irrelevant).
fn legc_window(tr: &LegCTrace) -> (Vec<BabyBear>, Vec<BabyBear>) {
    extract_custom_pi_board_window(&tr.public_inputs, &leg_c_roundstate_window_n11())
        .expect("a Leg C trace expresses the 32-lane RoundState window")
}

/// An independent base-4 positional pack of the board (the value the Lean descriptor publishes),
/// written out here so the window assertions compare against a value derived from the BOARD, not the
/// code path that produced it.
fn pack(board: &Board) -> Vec<BabyBear> {
    let k = board.n * board.n;
    (0..k.div_ceil(15))
        .map(|f| {
            let mut acc: u64 = 0;
            for i in 0..15usize {
                let c = f * 15 + i;
                if c < k {
                    acc += u64::from(board.cells[c]) * 4u64.pow(i as u32);
                }
            }
            BabyBear::from_u64(acc)
        })
        .collect()
}

// ============================================================================
// (a) THE HONEST CONFLICT BRAID — chains, and exposes first.IN / last.OUT
// ============================================================================

/// **THE FAIL-CLOSED CANARY + SHAPE.** Every conflict round SATISFIES the PROVEN
/// `automataflLegCDescN 11` (the accept-gate inside `conflict_traces`), publishes the 78-PI Leg C
/// shape, and declares the 32-lane RoundState window.
#[test]
fn each_conflict_round_satisfies_the_legc_descriptor_and_declares_the_32_lane_window() {
    let turn = three_conflict_turn();
    let traces = conflict_traces(&turn);
    assert_eq!(traces.len(), 3, "k conflict rounds == k Leg C traces");
    for (i, tr) in traces.iter().enumerate() {
        assert_eq!(
            tr.public_inputs.len(),
            78,
            "round {i} publishes the 78-PI Leg C shape"
        );
        let (win_in, win_out) = legc_window(tr);
        assert_eq!(win_in.len(), 32, "round {i} IN is the 32-lane RoundState");
        assert_eq!(win_out.len(), 32, "round {i} OUT is the 32-lane RoundState");
    }
}

/// **THE ROUNDSTATE SEAM (C→C).** `C_i.OUT == C_{i+1}.IN` over the WHOLE 32-lane RoundState window —
/// the exact equality the aggregation node `connect`s. Non-vacuous: the marks overlay GROWS across
/// the braid (round 0 enters with `marksIn = ∅`; the last round leaves with 3 marks), so the seam is
/// not trivially "everything equal".
#[test]
fn the_roundstate_seam_chains_conflict_round_to_round() {
    let turn = three_conflict_turn();
    let wins: Vec<(Vec<BabyBear>, Vec<BabyBear>)> =
        conflict_traces(&turn).iter().map(legc_window).collect();

    for i in 0..wins.len() - 1 {
        assert_eq!(
            wins[i].1,
            wins[i + 1].0,
            "C_{i}.OUT == C_{}.IN — the 32-lane RoundState seam",
            i + 1
        );
    }

    // NON-VACUITY: the board is FROZEN (equal IN/OUT board every round) but the MARKS accumulate.
    for (i, (win_in, win_out)) in wins.iter().enumerate() {
        assert_eq!(
            win_in[BOARD], win_out[BOARD],
            "round {i}: the board is frozen"
        );
        assert_eq!(
            &win_in[BOARD],
            pack(&turn.start).as_slice(),
            "round {i}: the frozen board IS pack(start)"
        );
    }
    assert!(
        wins[0].0[MARKS].iter().all(|m| *m == BabyBear::ZERO),
        "the first round enters with marksIn = ∅"
    );
    assert_ne!(
        wins.last().unwrap().1[MARKS],
        wins[0].0[MARKS],
        "the marks overlay GREW across the braid — the seam is non-vacuously carrying it"
    );
}

/// **THE CHAIN EXPOSES `[first.IN ‖ last.OUT]`.** The host mirror of the fold's root claim: the
/// braid begins at `(pack(start), marksIn = ∅)` and ends at `(pack(start), marksOut = the
/// accumulated marks)` — the RoundState the terminating clean round consumes. Because pack is
/// injective, the board halves decode in the clear.
#[test]
fn the_conflict_chain_exposes_first_in_and_last_out() {
    let turn = three_conflict_turn();
    let wins: Vec<(Vec<BabyBear>, Vec<BabyBear>)> =
        conflict_traces(&turn).iter().map(legc_window).collect();

    let first_in = &wins[0].0;
    let last_out = &wins.last().unwrap().1;

    assert_eq!(
        &first_in[BOARD],
        pack(&turn.start).as_slice(),
        "first.IN board IS the genesis position"
    );
    assert_eq!(
        &last_out[BOARD],
        pack(&turn.start).as_slice(),
        "last.OUT board IS the (frozen) genesis position"
    );
    assert!(
        first_in[MARKS].iter().all(|m| *m == BabyBear::ZERO),
        "first.IN marks = ∅"
    );
    assert!(
        last_out[MARKS].iter().any(|m| *m != BabyBear::ZERO),
        "last.OUT marks packs the 3 accumulated clash coordinates"
    );
}

/// Fill the terminating clean round's marks-aware **Leg RM** directly (no leg mint) with the given
/// `marks`, and read its 20-lane `[board(9) ‖ marks(9) ‖ auto(2)]` `(IN, OUT)` window through the
/// SAME extractor the fold uses. Panics if the marks-illegal fill is refused (callers pass a
/// marks-legal clean pair).
fn clean_rm_window(
    start: &Board,
    subs: &[Move; 2],
    marks: &[Coord],
) -> (Vec<BabyBear>, Vec<BabyBear>) {
    use dregg_automatafl::resolve_marks_witness::{
        automatafl_resolve_marks_trace, resolve_marks_board_window, resolve_marks_descriptor_ident,
        resolve_marks_trace_accepts,
    };
    let rmdesc =
        descriptor_by_name(resolve_marks_descriptor_ident(N)).expect("the n=11 resolve-marks desc");
    let rt = automatafl_resolve_marks_trace(start, subs, marks, &rmdesc)
        .expect("the terminating clean round fills");
    assert!(
        resolve_marks_trace_accepts(&rmdesc, &rt),
        "a marks-LEGAL terminating clean round must satisfy the resolve-marks descriptor"
    );
    let rmwin = resolve_marks_board_window(N, &rmdesc).expect("the resolve-marks board window");
    extract_custom_pi_board_window(&rt.public_inputs, &rmwin).expect("20-lane window")
}

/// **THE FULL `board ‖ marks` HALF OF THE `C_last → R` HANDOFF.** The clean round consumes the
/// accumulated marks: `MultiRoundTurn::accumulated_marks` reads them off the conflict chain, and Leg
/// RM's 20-lane IN window carries `board(9) ‖ marks(9) ‖ auto(2)`. Both halves of the 18-lane handoff
/// prefix line up — `C_last.OUT[board ‖ marks] == R.IN[board ‖ marks]` — the exact lanes
/// `board_window_clean_handoff_connects` welds.
#[test]
fn the_board_and_marks_halves_of_the_clean_handoff_hold() {
    let turn = three_conflict_turn();
    let c_last_out = legc_window(conflict_traces(&turn).last().unwrap()).1;

    let clean = turn.clean_subs.expect("the turn carries a clean round");
    let marks = turn
        .accumulated_marks()
        .expect("the conflict braid accumulates marks");
    // The braid marked all three fork sources.
    assert_eq!(
        marks.len(),
        3,
        "three conflict forks accumulate three marks"
    );

    let (rm_in, _rm_out) = clean_rm_window(&turn.start, &clean, &marks);
    assert_eq!(
        rm_in.len(),
        20,
        "clean Leg RM IN is board(9) ‖ marks(9) ‖ auto(2)"
    );

    // (a) the BOARD half — both sides the frozen turn-start board.
    assert_eq!(
        c_last_out[BOARD], rm_in[BOARD],
        "C_last.OUT board(9) == clean RM.IN board(9)"
    );
    assert_eq!(
        &rm_in[BOARD],
        pack(&turn.start).as_slice(),
        "the clean round starts from the frozen turn-start board"
    );
    // (b) the MARKS half — non-vacuous (the braid grew 3 marks), and it MATCHES.
    assert!(
        rm_in[MARKS].iter().any(|m| *m != BabyBear::ZERO),
        "the clean round enters with the accumulated marks (non-empty)"
    );
    assert_eq!(
        c_last_out[MARKS], rm_in[MARKS],
        "C_last.OUT marks(9) == clean RM.IN marks(9) — the MARKS half of the handoff, now closed"
    );
    // Together: the whole 18-lane board||marks prefix the clean handoff connects.
    assert_eq!(
        c_last_out[0..18],
        rm_in[0..18],
        "the full board ‖ marks handoff prefix agrees lane-for-lane"
    );
}

/// **`marksIn` IS THE CONFLICT CHAIN'S `marksOut`.** The clean round's `marksIn` (packed into Leg
/// RM's marks window) equals the marks the LAST conflict round produced — read back from the trace,
/// not re-derived. This is the datum the handoff binds; the next canary shows dropping a round makes
/// it disagree.
#[test]
fn the_clean_marks_in_equals_the_conflict_chain_marks_out() {
    let turn = three_conflict_turn();
    let wins: Vec<(Vec<BabyBear>, Vec<BabyBear>)> =
        conflict_traces(&turn).iter().map(legc_window).collect();
    let c_last_marks_out = &wins.last().unwrap().1[MARKS];

    let marks = turn.accumulated_marks().expect("marks accumulate");
    let clean = turn.clean_subs.unwrap();
    let (rm_in, _) = clean_rm_window(&turn.start, &clean, &marks);
    assert_eq!(
        &rm_in[MARKS], c_last_marks_out,
        "clean RM.IN marks(9) IS pack(C_last.marksOut) — the accumulated overlay, read off the trace"
    );
}

// ============================================================================
// (b) THE LOAD-BEARING NEGATIVES — each a WitnessConflict / UNSAT
// ============================================================================

/// **A DROPPED CONFLICT ROUND BREAKS THE SEAM.** Drop the MIDDLE round `C_1`: the remaining chain
/// `[C_0, C_2]` has `C_0.OUT.marks = {(0,0)}` but `C_2.IN.marks = {(0,0),(5,5)}` — `C_2` expects a
/// mark `C_0` never produced. In the fold that lane is a per-lane `connect` CONFLICT (UNSAT node ⇒
/// no root ⇒ no verifying artifact); here it is a marks-lane inequality we see in milliseconds. This
/// is the "skip a Leg C, feed the next a `marksIn` missing the accumulated mark" forgery.
#[test]
fn a_dropped_conflict_round_breaks_the_roundstate_seam() {
    let turn = three_conflict_turn();
    let wins: Vec<(Vec<BabyBear>, Vec<BabyBear>)> =
        conflict_traces(&turn).iter().map(legc_window).collect();
    // Control: the honest adjacent seam holds.
    assert_eq!(wins[1].1, wins[2].0, "control: C_1.OUT == C_2.IN honestly");

    // Drop C_1 — the chain is now [C_0, C_2].
    let c0_out = &wins[0].1;
    let c2_in = &wins[2].0;

    assert_ne!(
        c0_out, c2_in,
        "a dropped round leaves a broken RoundState seam (no witness in the fold)"
    );
    // And it is the MARKS overlay that diverges — the accumulated mark C_1 produced is missing.
    assert_ne!(
        c0_out[MARKS], c2_in[MARKS],
        "C_0.OUT.marks lacks the mark C_2.IN expects — the dropped round's clash coordinate"
    );
    assert_eq!(
        c0_out[BOARD], c2_in[BOARD],
        "the board is still frozen — only the marks seam catches the drop"
    );
}

/// **A DROPPED CONFLICT ROUND BREAKS THE `C_last → R` CLEAN HANDOFF (the marks half).** The clean
/// round's `marksIn` was accumulated over the WHOLE braid `[C_0, C_1, C_2]`; a prover who drops the
/// last round `C_2` presents `C_1` as `C_last`, whose `marksOut` LACKS `C_2`'s clash. The clean Leg
/// RM's IN marks — the full-braid overlay — then disagrees with the shortened chain's `C_last.OUT`
/// marks on the handoff prefix, so `board_window_clean_handoff_connects` is UNSAT (no root). The
/// board half stays equal (the board is frozen across the whole braid), so ONLY the marks half of the
/// handoff catches the drop — which is exactly why the marks must be in the handoff window.
#[test]
fn a_dropped_conflict_round_breaks_the_clean_handoff_marks_seam() {
    let turn = three_conflict_turn();
    // The honest clean round consumes the FULL-braid accumulated marks.
    let full_marks = turn.accumulated_marks().expect("full braid marks");
    let clean = turn.clean_subs.unwrap();
    let (rm_in, _) = clean_rm_window(&turn.start, &clean, &full_marks);

    let wins: Vec<(Vec<BabyBear>, Vec<BabyBear>)> =
        conflict_traces(&turn).iter().map(legc_window).collect();

    // CONTROL: against the honest last round C_2, the whole 18-lane prefix agrees.
    assert_eq!(
        wins[2].1[0..18],
        rm_in[0..18],
        "control: the honest C_2.OUT board||marks == clean RM.IN board||marks"
    );

    // DROP C_2: the shortened chain's last round is C_1. Its board||marks prefix now disagrees with
    // the clean round's full-braid marksIn — the broken clean handoff.
    let dropped_last_out = &wins[1].1;
    assert_ne!(
        dropped_last_out[0..18],
        rm_in[0..18],
        "a dropped last round leaves a broken clean handoff (no witness in the fold)"
    );
    // It is the MARKS half that diverges; the board is frozen so its half still matches.
    assert_ne!(
        dropped_last_out[MARKS], rm_in[MARKS],
        "C_1.OUT.marks lacks C_2's clash that the clean round's marksIn expects"
    );
    assert_eq!(
        dropped_last_out[BOARD], rm_in[BOARD],
        "the board half stays equal (frozen) — only the marks half catches the drop"
    );
}

/// **THE CLEAN-ROUND MARKS RE-CHECK (M6) — a terminating move onto an accumulated mark is UNSAT.**
/// Now reachable because the marks-aware Leg RM is emitted. A DIFFERENTIAL isolating marks as the
/// sole cause: the honest clean pair `[(0,7)→(2,7), (7,0)→(7,2)]` SATISFIES against marks that avoid
/// its endpoints, but the SAME pair against marks that additionally include move 0's destination
/// `(2,7)` is REJECTED — the only thing that changed is the mark set, so the rejection IS the M6
/// legality NOR pin (`roundStep`'s fresh filter refusing a move onto a mark), the terminating-move
/// re-check that was the named residual.
#[test]
fn a_clean_round_move_onto_an_accumulated_mark_is_unsat() {
    use dregg_automatafl::resolve_marks_witness::{
        automatafl_resolve_marks_trace, resolve_marks_descriptor_ident, resolve_marks_trace_accepts,
    };
    let turn = three_conflict_turn();
    let clean = turn.clean_subs.unwrap();
    let base_marks = turn.accumulated_marks().expect("marks accumulate");
    // The clean endpoints are (0,7),(2,7),(7,0),(7,2); the accumulated marks {(0,0),(5,5),(8,8)}
    // avoid them all.
    for e in [(0, 7), (2, 7), (7, 0), (7, 2)] {
        assert!(
            !base_marks.contains(&e),
            "the honest marks avoid the clean endpoints"
        );
    }
    let rmdesc =
        descriptor_by_name(resolve_marks_descriptor_ident(N)).expect("resolve-marks descriptor");

    // CONTROL: the clean pair against the honest (endpoint-avoiding) marks SATISFIES.
    let ok = automatafl_resolve_marks_trace(&turn.start, &clean, &base_marks, &rmdesc)
        .expect("the honest clean round fills");
    assert!(
        resolve_marks_trace_accepts(&rmdesc, &ok),
        "control: the clean pair against endpoint-avoiding marks is marks-LEGAL"
    );

    // ONLY-CHANGE: add move 0's DESTINATION (2,7) to the marks — now the SAME pair is UNSAT.
    let mut marked = base_marks.clone();
    marked.push((2, 7));
    let bad = automatafl_resolve_marks_trace(&turn.start, &clean, &marked, &rmdesc)
        .expect("the trace still FILLS (geometry unchanged); the legality gate bites on accept");
    assert!(
        !resolve_marks_trace_accepts(&rmdesc, &bad),
        "the SAME clean pair against marks that include a move's destination is REJECTED — the M6 \
         marks re-check, isolated (only the mark set changed)"
    );
}

/// **A SUBSTITUTED ROUND WITH A FORGED `marksOut` IS UNSAT.** Fill an honest fork round, then DROP
/// its new mark from `marksOut` (the "the turn never terminates" forgery). The Leg C OR gate
/// `marksOut = marksIn ∨ cs` bites at the conflicted cell — the descriptor no longer accepts, so the
/// leaf never proves. Per-leaf validity is exactly what catches this one (the seam catches the
/// consistent-but-wrong forgery; the descriptor catches the internally-inconsistent one).
#[test]
fn a_substituted_round_with_a_forged_marks_out_is_unsat() {
    let cdesc = legc_desc();
    let l = LegCLayout::new(N);
    let start = three_conflict_turn().start;
    // Round 0 in isolation: fork at (0,0), marksIn = ∅.
    let rs = RoundStateIn {
        board: start,
        marks: vec![],
    };
    let subs = [mv(0, (0, 0), (0, 2)), mv(1, (0, 0), (2, 0))];
    let mut tr = automatafl_legc_trace(&rs, &subs, &cdesc).expect("the fork round fills");
    assert!(
        legc_trace_accepts(&cdesc, &tr),
        "the honest fork round accepts"
    );

    // The clash coordinate is the fork SOURCE (0,0), linear index 0. Drop its OUT mark.
    let clash = 0 * N + 0;
    assert_eq!(
        tr.row[l.c_marks_out_cell(clash)],
        BabyBear::ONE,
        "the honest new mark is set at the clash coordinate"
    );
    tr.row[l.c_marks_out_cell(clash)] = BabyBear::ZERO;
    assert!(
        !legc_trace_accepts(&cdesc, &tr),
        "a forged marksOut that drops the new mark fails the OR gate — UNSAT, the leaf never proves"
    );
}

/// **A SUBMISSION ONTO A MARKED SQUARE IS REFUSED (the CONFLICT-round re-check).** A round entered
/// with `marksIn` holding a submission's SOURCE is illegal (`moveLegalB` refuses it) — the `legal =
/// 1` pin fails, `automataflLegCDescN` is UNSAT. This is the marks re-check the braid enforces at
/// EVERY conflict round.
///
/// This is the CONFLICT-round re-check. Its CLEAN-round twin — the terminating-move re-check
/// (`AutomataflResolveMarksCapstone.resolveMarksMoveLegal`, M6) — is now also live via the emitted
/// marks-aware Leg RM (`a_clean_round_move_onto_an_accumulated_mark_is_unsat`).
#[test]
fn a_submission_onto_a_marked_square_is_refused_at_the_conflict_recheck() {
    let cdesc = legc_desc();
    let start = three_conflict_turn().start;
    // Enter the fork round with its source (0,0) ALREADY marked.
    let rs = RoundStateIn {
        board: start,
        marks: vec![(0, 0)],
    };
    let subs = [mv(0, (0, 0), (0, 2)), mv(1, (0, 0), (2, 0))];
    let tr = automatafl_legc_trace(&rs, &subs, &cdesc)
        .expect("the generator still fills a trace (the accept-gate rejects it)");
    assert!(
        !legc_trace_accepts(&cdesc, &tr),
        "a submission naming a marked source fails the Leg C marksIn-legality pin — UNSAT"
    );
}

/// **A NON-CLASHING ROUND IS NOT A CONFLICT ROUND.** A clean (fork/collide-free) pair has `cSurv =
/// 1`; the clash pin gates it to 0, so it is structurally UNSAT as a Leg C — the prover cannot pad a
/// turn with spurious identity re-entry rounds. Filled directly and refused by `legc_trace_accepts`.
#[test]
fn a_non_clashing_round_is_unsat_as_a_leg_c() {
    let cdesc = legc_desc();
    let start = board_with((10, 10), &[(0, 0), (4, 0)]);
    // Distinct sources, distinct destinations, disjoint rows/cols — no clash.
    let rs = RoundStateIn {
        board: start,
        marks: vec![],
    };
    let subs = [mv(0, (0, 0), (0, 2)), mv(1, (4, 0), (4, 2))];
    let tr = automatafl_legc_trace(&rs, &subs, &cdesc).expect("the generator fills a trace");
    assert!(
        !legc_trace_accepts(&cdesc, &tr),
        "a non-clashing round has cSurv = 1, gated to 0 by the clash pin — UNSAT as a Leg C"
    );
}

// ============================================================================
// (b′) THE PRODUCER — MultiRoundTurn::conflict_leaves, one real minted leg
// ============================================================================

/// **THE DEPLOYED PRODUCER, ONE ROUND.** `conflict_leaves` mints a real, foldable Leg C leaf: the
/// `[old8 ‖ new8]` door carries the REAL rotated roots of the leg the fold will mint for it (a
/// placeholder door is an UNSAT state tooth), the descriptor source is the Lean Leg C descriptor,
/// and the declared window is the 32-lane RoundState. ~50s (one wide leg mint) — the price of a real
/// leaf; the seam canaries above bypass it.
#[test]
fn conflict_leaves_mints_a_foldable_leg_c_leaf() {
    use dregg_multiway_tug::fold::fixture_rotated_roots;

    let start = board_with((10, 10), &[(0, 0)]);
    let turn =
        MultiRoundTurn::conflict_only(start, vec![[mv(0, (0, 0), (0, 2)), mv(1, (0, 0), (2, 0))]]);
    let leaves = turn.conflict_leaves().expect("the single fork round mints");
    assert_eq!(leaves.len(), 1, "one conflict round == one Leg C leaf");
    let leaf = &leaves[0];

    // The door carries the REAL rotated roots (nonce 0) — load-bearing, not cosmetic.
    let (old8, new8) = fixture_rotated_roots(0);
    assert_eq!(&leaf.public_inputs[..8], &old8[..], "leaf old8 door");
    assert_eq!(&leaf.public_inputs[8..16], &new8[..], "leaf new8 door");

    // It proves the Lean Leg C descriptor and declares the 32-lane RoundState window.
    let src = leaf
        .descriptor_state_leaf
        .as_ref()
        .expect("a conflict leaf carries a descriptor source");
    assert!(
        src.descriptor.name.contains("legc"),
        "proves the Leg C descriptor"
    );
    assert_eq!(
        src.board_window
            .as_ref()
            .expect("declares a window")
            .window_len(),
        32,
        "the conflict leaf declares the 32-lane RoundState window"
    );
    let (win_in, win_out) =
        extract_custom_pi_board_window(&leaf.public_inputs, &leg_c_roundstate_window_n11())
            .expect("the window is expressible");
    assert_eq!(win_in.len(), 32);
    assert_eq!(win_out.len(), 32);
}

/// **THE DEPLOYED CLEAN-ROUND PRODUCER.** `clean_leaves` mints the marks-aware Leg RM (20-lane
/// `[board ‖ marks ‖ auto]`, proving `automatafl-resolve-marks-n11`) then the marks-carrying Leg A
/// (also 20-lane `[board ‖ marks ‖ auto]`, proving `automatafl-step-marks-n11`). Its Leg RM IN
/// window's `board ‖ marks` prefix equals the conflict chain's `C_last.OUT` prefix — the deployed
/// producer wires the FULL handoff — and BOTH legs are 20-lane, so the clean sub-chain is now
/// UNIFORM-width (the mixed 20/11 residual is CLOSED). Both legs are `descriptor_backed` (no proving
/// here — the fill + bundle build).
#[test]
fn clean_leaves_mints_the_resolve_marks_leg_and_the_step_leg() {
    use dregg_automatafl::resolve_marks_witness::resolve_marks_board_window;

    let turn = three_conflict_turn();
    let leaves = turn.clean_leaves().expect("the clean round mints");
    assert_eq!(leaves.len(), 2, "clean round == Leg RM + Leg A");

    // Leg RM: proves the resolve-marks descriptor and declares the 20-lane window.
    let rm = &leaves[0];
    let rm_src = rm
        .descriptor_state_leaf
        .as_ref()
        .expect("Leg RM carries a descriptor source");
    assert!(
        rm_src.descriptor.name.contains("resolve-marks"),
        "Leg RM proves the marks-aware resolve descriptor, got {}",
        rm_src.descriptor.name
    );
    assert_eq!(
        rm_src
            .board_window
            .as_ref()
            .expect("RM declares a window")
            .window_len(),
        20,
        "Leg RM declares the 20-lane board ‖ marks ‖ auto window"
    );

    // Leg A: proves the marks-carrying step descriptor, now ALSO 20-lane (marks carried FROZEN) —
    // so the clean sub-chain RM(20) ∘ A(20) is uniform-width.
    let step_src = leaves[1]
        .descriptor_state_leaf
        .as_ref()
        .expect("Leg A carries a descriptor source");
    assert!(
        step_src.descriptor.name.contains("step-marks"),
        "Leg A proves the marks-carrying automaton step descriptor, got {}",
        step_src.descriptor.name
    );
    assert_eq!(
        step_src
            .board_window
            .as_ref()
            .expect("A declares a window")
            .window_len(),
        20,
        "Leg A is now the 20-lane board ‖ marks ‖ auto window (marks carried frozen) — uniform with RM"
    );

    // The minted Leg RM's board||marks prefix lines up with the conflict chain's C_last.OUT.
    let rmdesc = descriptor_by_name(
        dregg_automatafl::resolve_marks_witness::resolve_marks_descriptor_ident(N),
    )
    .unwrap();
    let rmwin = resolve_marks_board_window(N, &rmdesc).unwrap();
    let (rm_in, _) =
        extract_custom_pi_board_window(&rm.public_inputs, &rmwin).expect("20-lane window");
    let c_last_out = legc_window(conflict_traces(&turn).last().unwrap()).1;
    assert_eq!(
        c_last_out[0..18],
        rm_in[0..18],
        "the minted Leg RM IN board ‖ marks prefix == C_last.OUT board ‖ marks"
    );
}

// ============================================================================
// (c) THE DEPLOYED FOLD — a real conflict-chain fold. SLOW; `#[ignore]`d.
// ============================================================================

/// **THE HONEST CONFLICT-BRAID FOLD.** The uniform 32-lane Leg C chain folds through the DEPLOYED
/// recursive fold (`fold_match` → `aggregate_tree`, width auto-derived from the exposed 89-lane
/// shape — no M7-specific prover code), the light client ACCEPTS, and the attestation carries
/// `[first.IN ‖ last.OUT]` (the genesis RoundState and the accumulated-marks RoundState).
///
/// Welding the terminating clean round onto this root into ONE `WholeChainProof` is BLOCKED on two
/// residuals, both surfaced not faked (see the module + `MultiRoundTurn` docs): (1) the clean
/// sub-chain Leg RM(20) ∘ Leg A(11) is MIXED-width — the step descriptor has no marks PIs — so it
/// cannot fold through the uniform `aggregate_tree`, and a nested clean-handoff sub-root is not the
/// `SEG + 2W` shape the top merge reads; folding the step into the marks chain needs a marks-carrying
/// step descriptor (Lean). (2) No `WholeChainProof` assembler exists for the clean-handoff root
/// (`fold_clean_handoff_root` yields a bare `RecursionOutput`; the verifier's board-window tooth
/// ALREADY accepts a mixed-width `[first.IN(32) ‖ last.OUT(20)]` window, but the prover-side glue is
/// `dregg-circuit-prove` work). The `board ‖ marks` handoff and the terminating marks-legality are
/// closed at MINT level by the fast canaries above.
#[test]
#[ignore = "SLOW: a real n=11 conflict-chain fold (3 × 1208-col Leg C leaves, each recursion-wrapped, \
            plus the tree) is tens of minutes. It uses the DEPLOYED path unchanged (uniform 32-lane \
            window, width auto-derived) — no M7 prover code. Run on the build box with --ignored."]
fn the_honest_conflict_braid_folds_and_the_light_client_reads_the_roundstate_endpoints() {
    use dregg_lightclient::verify_history;
    use dregg_multiway_tug::fold::fold_match;

    let leaves = three_conflict_turn()
        .conflict_leaves()
        .expect("the honest braid lowers");
    let whole = fold_match(&leaves).expect("the uniform 32-lane Leg C chain must fold");
    let vk = whole.root_vk_fingerprint();
    let attested = verify_history(&whole, &vk).expect("the light client must ACCEPT");

    assert_eq!(
        attested.num_turns, 3,
        "three conflict rounds == three folded Leg C turns"
    );
    assert_eq!(
        attested.board_genesis.as_deref().map(<[BabyBear]>::len),
        Some(32),
        "the attested genesis RoundState is 32 lanes"
    );
    assert_eq!(
        attested.board_final.as_deref().map(<[BabyBear]>::len),
        Some(32),
        "the attested final RoundState is 32 lanes"
    );
}

// ============================================================================
// (d) THE CLEAN-HANDOFF ASSEMBLER — the whole turn (conflict braid ∘ clean round) as ONE artifact
// ============================================================================
//
// The prover-side glue (residual (2) of `MultiRoundTurn`): `fold_clean_handoff_match` /
// `prove_clean_handoff_chain_recursive` assemble the conflict sub-tree, the clean sub-tree, and the
// ONE mixed-width `C_last → R` node into ONE verifiable `WholeChainProof` whose root exposes the mixed
// `[C_first.IN(32) ‖ R_last.OUT(20)]` window.
//
// The FAST tests below drive the assembler's HOST CLAIM (the mixed board window it carries + the
// turn count) through `clean_handoff_root_board_window` — the pure window fold, no leg minting, no
// proving — so the seam the in-circuit `segment_combine_expose_with_clean_handoff` connects is
// exercised in milliseconds. The clean sub-chain is now UNIFORM-20 (Leg RM 20 ∘ the marks-carrying Leg
// A 20), so the mirror ACCEPTS it (exactly one C→R width change); the retired 11-lane plain step is
// kept only as a REGRESSION negative. The tier-3 end-to-end (the real fold) is `#[ignore]`-FREE — the
// residual it was blocked on is CLOSED.

/// The real 11-lane plain Leg A (automaton step, `automatafl-step-n11`) `(IN, OUT)` window for the
/// clean round — the LEGACY clean sub-chain's SECOND leg, kept ONLY as the regression negative below.
/// It is 11-lane `[board ‖ auto]` (no marks PIs); reintroducing it into the clean sub-chain makes it
/// mixed-width again (Leg RM 20 ∘ Leg A 11), which the assembler's host board-window mirror must
/// refuse. The DEPLOYED clean round no longer mints it — it mints the uniform-20 step-marks leg.
fn clean_plain_step_window_regression(
    start: &Board,
    subs: &[Move; 2],
    marks: &[Coord],
) -> (Vec<BabyBear>, Vec<BabyBear>) {
    use dregg_automatafl::resolve_marks_layout::ResolveMarksLayout;
    use dregg_automatafl::resolve_marks_witness::{
        automatafl_resolve_marks_trace, resolve_marks_descriptor_ident,
    };
    use dregg_automatafl::witness::{
        automatafl_step_trace, step_board_window, step_descriptor_name,
    };
    let rmdesc =
        descriptor_by_name(resolve_marks_descriptor_ident(N)).expect("resolve-marks descriptor");
    let rt = automatafl_resolve_marks_trace(start, subs, marks, &rmdesc)
        .expect("the clean resolve-marks fills");
    let mid = rt.mid_board(&ResolveMarksLayout::new(N));
    let sdesc = descriptor_by_name(&step_descriptor_name(N)).expect("the step descriptor");
    let st = automatafl_step_trace(&mid, &sdesc).expect("the clean step fills");
    let swin = step_board_window(N, &sdesc).expect("the 11-lane step window");
    extract_custom_pi_board_window(&st.public_inputs, &swin).expect("11-lane window")
}

/// The DEPLOYED 20-lane marks-carrying Leg A (`automatafl-step-marks-n11`) `(IN, OUT)` window for the
/// clean round — the clean sub-chain's SECOND leg AS MINTED. It is 20-lane `[board(9) ‖ marks(9) ‖
/// auto(2)]` with `marks` carried FROZEN (equal IN/OUT marks half), and its IN prefix == Leg RM's OUT
/// prefix (`RM.OUT == A.IN` lane-for-lane) — so the clean sub-chain RM(20) ∘ A(20) is UNIFORM.
fn clean_step_marks_window(
    start: &Board,
    subs: &[Move; 2],
    marks: &[Coord],
) -> (Vec<BabyBear>, Vec<BabyBear>) {
    use dregg_automatafl::resolve_marks_layout::ResolveMarksLayout;
    use dregg_automatafl::resolve_marks_witness::{
        automatafl_resolve_marks_trace, resolve_marks_descriptor_ident,
    };
    use dregg_automatafl::step_marks_witness::{
        automatafl_step_marks_trace, step_marks_board_window, step_marks_descriptor_ident,
    };
    let rmdesc =
        descriptor_by_name(resolve_marks_descriptor_ident(N)).expect("resolve-marks descriptor");
    let rt = automatafl_resolve_marks_trace(start, subs, marks, &rmdesc)
        .expect("the clean resolve-marks fills");
    let mid = rt.mid_board(&ResolveMarksLayout::new(N));
    let smdesc =
        descriptor_by_name(step_marks_descriptor_ident(N)).expect("the step-marks descriptor");
    let st = automatafl_step_marks_trace(&mid, marks, &smdesc).expect("the clean step-marks fills");
    let swin = step_marks_board_window(N, &smdesc).expect("the 20-lane step-marks window");
    extract_custom_pi_board_window(&st.public_inputs, &swin).expect("20-lane window")
}

/// **THE ASSEMBLER CARRIES THE MIXED WINDOW + THE RIGHT TURN COUNT (fast, no proving).** The conflict
/// braid's 32-lane RoundState windows fold with the clean round's 20-lane Leg RM window through the
/// SAME `fold_declared_windows` core the assembler's host claim uses, and the root window is the mixed
/// `[C_0.IN(32) ‖ R_last.OUT(20)]` — the genesis RoundState and the clean round's final state, the
/// exact `[first.IN ‖ last.OUT]` the verifier's board-window tooth (5) compares the root's exposure
/// against. The clean sub-chain is modeled by its ONE emitted 20-lane leaf (Leg RM); appending the
/// marks-carrying step (also 20-lane, once emitted) keeps this shape — see the uniform-20 case below.
#[test]
fn the_clean_handoff_assembler_carries_the_mixed_window_and_num_turns() {
    let turn = three_conflict_turn(); // 3 conflict rounds + a clean round
    let conflict_wins: Vec<(Vec<BabyBear>, Vec<BabyBear>)> =
        conflict_traces(&turn).iter().map(legc_window).collect();
    let marks = turn
        .accumulated_marks()
        .expect("the braid accumulates marks");
    let clean = turn.clean_subs.expect("the turn carries a clean round");
    let (rm_in, rm_out) = clean_rm_window(&turn.start, &clean, &marks);

    // The uniform-20 clean sub-chain interface, modeled by the ONE real 20-lane leaf (Leg RM).
    let mut windows = conflict_wins.clone();
    windows.push((rm_in.clone(), rm_out.clone()));

    let bw = clean_handoff_root_board_window(&windows, HANDOFF)
        .expect("the conflict∘clean windows fold to a mixed root window");

    // THE MIXED WINDOW: 32-lane genesis RoundState ‖ 20-lane clean final. The halves DIFFER in width
    // (this is the whole point of the clean-handoff node — a uniform merge refuses it).
    assert_eq!(bw.first_in.len(), 32, "genesis is the 32-lane RoundState");
    assert_eq!(
        bw.last_out.len(),
        20,
        "clean final is the 20-lane [board ‖ marks ‖ auto]"
    );
    assert_eq!(bw.first_in, conflict_wins[0].0, "genesis IS C_0.IN");
    assert_eq!(bw.last_out, rm_out, "final IS the clean round's OUT");

    // THE RIGHT TURN COUNT: the whole chain the assembler folds is k conflict Leg C turns + the clean
    // sub-chain's turns — the `num_turns` the root's segment tooth (4) carries. Here that is the
    // window count (one window per folded turn).
    assert_eq!(
        windows.len(),
        turn.conflict_subs.len() + 1,
        "the clean-handoff chain folds k conflict turns + the (modeled) clean turn"
    );

    // THE FULL UNIFORM-20 CLEAN SUB-CHAIN (Leg RM ∘ the marks-carrying step, both 20-lane): appending
    // a second uniform-20 leaf whose IN == RM.OUT (the clean→clean seam) keeps EXACTLY one width
    // change (C→clean) and the SAME mixed [32 ‖ 20] shape. This is the interface the emitted
    // step-marks descriptor will complete; the assembler is built against it.
    let step_marks_uniform20 = (rm_out.clone(), rm_out.clone());
    let mut windows_full = conflict_wins.clone();
    windows_full.push((rm_in.clone(), rm_out.clone()));
    windows_full.push(step_marks_uniform20);
    let bw_full = clean_handoff_root_board_window(&windows_full, HANDOFF)
        .expect("a uniform-20 clean sub-chain (RM ∘ step-marks) folds to the mixed root window");
    assert_eq!(bw_full.first_in.len(), 32, "genesis still 32-lane");
    assert_eq!(bw_full.last_out.len(), 20, "clean final still 20-lane");
    assert_eq!(bw_full.first_in, conflict_wins[0].0, "genesis unchanged");
}

/// **THE DEPLOYED CLEAN SUB-CHAIN IS UNIFORM-20 AND ACCEPTED — the step-marks residual is CLOSED.**
/// The clean round now mints Leg RM (20-lane) then the marks-carrying Leg A (also 20-lane, marks
/// FROZEN): both `[board ‖ marks ‖ auto]`, and `RM.OUT == A.IN` lane-for-lane. So the whole
/// conflict∘clean window chain has EXACTLY ONE width change (the C→R clean-handoff boundary), the
/// RM→A seam is a uniform intra-side seam, and the assembler's host board-window mirror ACCEPTS it,
/// yielding the mixed `[C_0.IN(32) ‖ A_last.OUT(20)]` root window.
///
/// The negative is now a REGRESSION guard: reintroducing the OLD 11-lane plain step (Leg A without
/// marks) makes the clean sub-chain mixed-width again (RM 20 ∘ A 11 = a SECOND width change), which
/// the mirror still refuses fail-closed. The deployed path is the accepted uniform-20; the plain-step
/// path is the refused one.
#[test]
fn the_deployed_clean_sub_chain_is_uniform_20_accepted_and_the_plain_step_regression_refused() {
    let turn = three_conflict_turn();
    let conflict_wins: Vec<(Vec<BabyBear>, Vec<BabyBear>)> =
        conflict_traces(&turn).iter().map(legc_window).collect();
    let marks = turn.accumulated_marks().expect("marks accumulate");
    let clean = turn.clean_subs.unwrap();
    let (rm_in, rm_out) = clean_rm_window(&turn.start, &clean, &marks);

    // ---- (a) THE DEPLOYED clean sub-chain: Leg RM (20) ∘ marks-carrying Leg A (20) — UNIFORM. ----
    let (a_in, a_out) = clean_step_marks_window(&turn.start, &clean, &marks);
    assert_eq!(
        a_in.len(),
        20,
        "the deployed Leg A window is 20-lane (marks carried)"
    );
    assert_eq!(a_out.len(), 20);
    // The uniform intra-side seam RM → A holds lane-for-lane (RM.OUT == step-marks.IN).
    assert_eq!(
        rm_out, a_in,
        "the clean sub-chain's RM → A seam is a uniform 20-lane seam (RM.OUT == A.IN)"
    );
    // Leg A carries the marks FROZEN (the step touches board + auto, never the marks half). (The
    // board half MAY be unchanged when the automaton has no attractor in range — the step is a
    // board no-op there — so only the marks-frozen invariant is asserted.)
    assert_eq!(a_in[MARKS], a_out[MARKS], "Leg A carries the marks frozen");

    let mut windows = conflict_wins.clone();
    windows.push((rm_in.clone(), rm_out.clone()));
    windows.push((a_in, a_out.clone()));
    let bw = clean_handoff_root_board_window(&windows, HANDOFF).expect(
        "the DEPLOYED uniform-20 clean sub-chain (RM 20 ∘ step-marks 20) folds to one root",
    );
    assert_eq!(bw.first_in.len(), 32, "genesis is the 32-lane RoundState");
    assert_eq!(
        bw.last_out.len(),
        20,
        "clean final is the 20-lane [board ‖ marks ‖ auto]"
    );
    assert_eq!(bw.first_in, conflict_wins[0].0, "genesis IS C_0.IN");
    assert_eq!(bw.last_out, a_out, "final IS the step-marks leg's OUT");

    // ---- (b) THE REGRESSION: the OLD 11-lane plain step reintroduces a mixed-width sub-chain. ----
    let (pa_in, pa_out) = clean_plain_step_window_regression(&turn.start, &clean, &marks);
    assert_eq!(
        pa_in.len(),
        11,
        "the legacy plain Leg A window is 11-lane (no marks PIs)"
    );
    assert_eq!(pa_out.len(), 11);
    let mut regressed = conflict_wins;
    regressed.push((rm_in, rm_out));
    regressed.push((pa_in, pa_out));
    let err = clean_handoff_root_board_window(&regressed, HANDOFF).expect_err(
        "a regression to the 11-lane plain step (RM 20 ∘ A 11) must be refused, not folded",
    );
    let msg = format!("{err}");
    assert!(
        msg.contains("more than one window-width change"),
        "the refusal names the second width change (the plain-step regression), got: {msg}"
    );
}

/// **A DROPPED CONFLICT ROUND BREAKS THE CLEAN-HANDOFF SEAM IN THE ASSEMBLER.** The clean round's Leg
/// RM enters with the FULL-braid accumulated marks; if the conflict chain handed off is SHORTENED (a
/// dropped round), the last conflict round's `C_last.OUT[board ‖ marks]` no longer equals the clean
/// RM's IN prefix. The assembler's window fold catches it at the C→R boundary — the in-circuit
/// `board_window_clean_handoff_connects` would be UNSAT (no root). Isolates the marks half: the board
/// stays frozen, only the marks prefix diverges.
#[test]
fn a_dropped_conflict_round_breaks_the_assemblers_clean_handoff_seam() {
    let turn = three_conflict_turn();
    let conflict_wins: Vec<(Vec<BabyBear>, Vec<BabyBear>)> =
        conflict_traces(&turn).iter().map(legc_window).collect();
    let clean = turn.clean_subs.unwrap();
    // The HONEST clean round consumes the FULL-braid marks — but the prover presents a SHORTENED
    // conflict chain (drop the last round C_2). Its C_last is now C_1, whose OUT marks lack C_2's clash.
    let full_marks = turn.accumulated_marks().expect("full braid marks");
    let (rm_in, rm_out) = clean_rm_window(&turn.start, &clean, &full_marks);

    // Control: against the FULL conflict chain the handoff holds and the mixed window folds.
    let mut honest = conflict_wins.clone();
    honest.push((rm_in.clone(), rm_out.clone()));
    clean_handoff_root_board_window(&honest, HANDOFF)
        .expect("control: the full conflict chain ∘ clean round folds");

    // DROP C_2 — the chain is [C_0, C_1, RM]; C_1.OUT.marks lacks C_2's clash the clean RM.IN expects.
    let mut dropped: Vec<(Vec<BabyBear>, Vec<BabyBear>)> = conflict_wins[..2].to_vec();
    dropped.push((rm_in, rm_out));
    let err = clean_handoff_root_board_window(&dropped, HANDOFF)
        .expect_err("a dropped last conflict round breaks the clean handoff — no root");
    let msg = format!("{err}");
    assert!(
        msg.contains("clean-handoff seam broken"),
        "the refusal names the broken board||marks handoff prefix, got: {msg}"
    );
}

/// An honest 2-conflict-round turn (two forks at disjoint coordinates, then a clean round moving
/// never-marked attractors) — the smaller turn the tier-3 end-to-end fold drives.
fn two_conflict_turn() -> MultiRoundTurn {
    let start = board_with((10, 10), &[(0, 0), (5, 5), (0, 7), (7, 0)]);
    let conflict_subs = vec![
        [mv(0, (0, 0), (0, 2)), mv(1, (0, 0), (2, 0))], // fork at (0,0)
        [mv(0, (5, 5), (5, 7)), mv(1, (5, 5), (7, 5))], // fork at (5,5)
    ];
    let clean = [mv(0, (0, 7), (2, 7)), mv(1, (7, 0), (7, 2))];
    MultiRoundTurn::new(start, conflict_subs, clean)
}

/// **TIER-3 END-TO-END — the whole multi-round turn assembles to ONE verifying `WholeChainProof`.**
/// `MultiRoundTurn::prove` lowers the conflict braid + the terminating clean round and assembles them
/// through the SHAPED clean-handoff fold; the light client ACCEPTS, and the root decodes to
/// `[genesis RoundState(32) ‖ clean final(20)]` (genesis board == pack(start), the clean final carries
/// the accumulated marks). A DROPPED conflict round FAILS to fold (the clean-handoff marks seam is
/// UNSAT ⇒ no root).
///
/// UN-IGNORED — the residual it was blocked on is CLOSED. The clean sub-chain is now UNIFORM-20 (Leg
/// RM 20 ∘ the marks-carrying Leg A 20, marks frozen), so the assembler's host board-window mirror
/// ACCEPTS it (exactly ONE C→R width change) — the "more than one window-width change" refusal is now
/// a REGRESSION guard on the retired 11-lane plain step
/// (`the_deployed_clean_sub_chain_is_uniform_20_accepted_and_the_plain_step_regression_refused`,
/// fast).
///
/// SLOW: this carries the deployed prover cost — 2 Leg C + Leg RM + the step-marks Leg A leaves, each
/// recursion-wrapped, plus the shaped tree — tens of minutes. It is a REAL STARK fold, kept
/// `#[ignore]`-FREE (the residual it was blocked on is closed) so CI / an on-demand run exercises the
/// whole weld; the FAST structural coherence (the uniform-20 sub-chain, the RM→A seam, the mixed
/// [32 ‖ 20] root window) is covered by the always-run tests above. The two other end-to-end
/// forgeries fail FAST at lowering and are covered genuinely by
/// `a_substituted_round_with_a_forged_marks_out_is_unsat` (the descriptor's OR gate) and
/// `a_clean_round_move_onto_an_accumulated_mark_is_unsat` (the M6 legality NOR pin) — the exact
/// fail-closed canaries `conflict_leaves` / `clean_leaves` gate on before a single leaf is proven.
#[test]
fn the_whole_multi_round_turn_folds_to_one_verifying_proof() {
    use dregg_lightclient::verify_history_bytes;
    use dreggnet_game_board::{CLEAN_HANDOFF_LANES, MultiRoundTurn, fold_clean_handoff_match};

    // ── POSITIVE: the honest turn welds to ONE verifying WholeChainProof. ──
    let turn = two_conflict_turn();
    let proof = turn
        .prove()
        .expect("the honest multi-round turn assembles to ONE WholeChainProof");

    // Self-attested already inside `prove`; re-verify the over-wire envelope against the fold's VK.
    let attested = verify_history_bytes(&proof.proof_bytes, &proof.vk)
        .expect("the light client ACCEPTS the clean-handoff artifact");

    // The whole turn folded: 2 conflict Leg C turns + the clean round's 2 (uniform-20) legs.
    assert_eq!(
        attested.num_turns,
        turn.conflict_subs.len() + 2,
        "num_turns == k conflict Leg C turns + Leg RM + the uniform-20 step-marks leg"
    );

    // The mixed endpoints decode in the clear (pack is injective): 32-lane genesis, 20-lane final.
    let genesis = attested
        .board_genesis
        .as_deref()
        .expect("attested genesis RoundState");
    let last = attested
        .board_final
        .as_deref()
        .expect("attested clean final state");
    assert_eq!(
        genesis.len(),
        32,
        "the attested genesis is the 32-lane RoundState"
    );
    assert_eq!(
        last.len(),
        20,
        "the attested final is the 20-lane clean [board ‖ marks ‖ auto]"
    );
    // Genesis decodes to the turn-start board with no marks (marksIn = ∅).
    assert_eq!(
        &genesis[BOARD],
        pack(&turn.start).as_slice(),
        "the root's genesis board IS pack(start)"
    );
    assert!(
        genesis[MARKS].iter().all(|m| *m == BabyBear::ZERO),
        "the genesis RoundState enters with marksIn = ∅"
    );
    // The clean final carries the accumulated conflict marks (frozen through the step).
    assert!(
        last[MARKS].iter().any(|m| *m != BabyBear::ZERO),
        "the clean final carries the accumulated conflict marks"
    );

    // ── NEGATIVE — a DROPPED conflict round leaves a broken clean handoff (no root). ──
    // The honest clean round consumed the FULL 2-fork braid's marks {(0,0),(5,5)}; a prover who folds
    // a SHORTENED (1-round) conflict chain hands off C_last.OUT.marks = {(0,0)} — which disagrees with
    // the clean Leg RM's IN marks on the handoff prefix. `board_window_clean_handoff_connects` is UNSAT
    // (caught at the assembler's fail-closed host claim, before the tree is proven) ⇒ no verifying root.
    let full_clean = turn.clean_leaves().expect("the full-braid clean leaves");
    let short = MultiRoundTurn::conflict_only(turn.start.clone(), turn.conflict_subs[..1].to_vec());
    let short_conflict = short
        .conflict_leaves()
        .expect("the shortened conflict braid lowers");
    assert!(
        fold_clean_handoff_match(&short_conflict, &full_clean, CLEAN_HANDOFF_LANES).is_err(),
        "a dropped conflict round leaves a broken clean handoff — no verifying root"
    );
}
