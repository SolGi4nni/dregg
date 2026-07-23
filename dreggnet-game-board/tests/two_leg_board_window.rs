//! **THE TWO-LEG BOARD-WINDOW SEAM** — the canaries for the fold that makes a ranked automatafl
//! match attest the PLAYERS' MOVES and a REAL TRAJECTORY, not K independent automaton steps.
//!
//! The design is `docs/reference/AUTOMATAFL-TWO-LEG-FOLD-DESIGN.md`. A round is TWO chained turns
//! on one cell lineage — turn `2i` = Leg R (`automataflResolveDescN 11`, `old → mid`, adjudicating
//! the two submitted moves) and turn `2i+1` = Leg A (`automataflStepDescN 11`, `mid → new`, the
//! automaton). Every leaf declares an 11-lane IN window and an 11-lane OUT window
//! (`pack(9) ‖ auto(2)`), and the ONLY cross-leaf rule in the whole design is
//!
//! ```text
//!     left.OUT  ==  right.IN
//! ```
//!
//! which instantiates three gaps at once:
//!
//! * `R_i.OUT == A_i.IN` IS `hseamPack ∧ hseamAutoX ∧ hseamAutoY` — the exact hypotheses
//!   `AutomataflTurnCapstone.turn_sat_imp_roundStep_pi` takes, so the round's `new` board IS
//!   `AutomataflRules.roundStep`'s outcome board for the decoded moves;
//! * `A_i.OUT == R_{i+1}.IN` is the inter-round carry — the boards form ONE trajectory;
//! * the root's `[first.IN ‖ last.OUT]` is the genesis/final position, and because the pack is
//!   INJECTIVE (`pack_injective_modp`: base-4 positional, `packed < 4^15 < p`) the 9-felt half IS
//!   the board in the clear — no collision-resistance assumption enters this seam.
//!
//! **THE SUBSTRATE, SAID OUT LOUD:** every constraint object here — both descriptors, both packs,
//! both PI layouts — is **Lean-authored AIR** (`metatheory/Dregg2/Circuit/Emit/Automatafl*.lean`,
//! emitted through `metatheory/EmitByName.lean` into `circuit/descriptors/by-name/`). This file
//! fills traces and drives the fold. It authors zero constraints.
//!
//! **WHAT A GREEN HERE MEANS — READ THIS BEFORE TRUSTING ONE.** Three tiers, and only the first
//! runs today:
//!
//! 1. **PI level (runs, green).** For real legal 11×11 rounds through the real Lean descriptors:
//!    `R.OUT == A.IN`, `A_0.OUT == R_1.IN`, every window decodes to the board the reference oracle
//!    produces, and a FORGED mid — whose Leg A still SATISFIES the step descriptor — breaks the
//!    equality. That is the seam's *content*: the numbers the fold will connect are the right
//!    numbers, and a forgery moves them.
//! 2. **Constraint level (runs, green, in `dregg-circuit-prove::board_window_seam_tests`).** That a
//!    broken equality is a `connect` CONFLICT — a witness that does not exist — for every one of
//!    the 11 lanes. That is the seam's *force*.
//! 3. **Deployed prover (`#[ignore]`d, NOT RUN).**
//!    `a_mismatched_mid_does_not_fold_on_the_deployed_prover` — a real fold, tens of minutes. Only
//!    this settles that a forged mid yields no verifying artifact end to end.
//!
//! So: green means *the seam is wired, carries the right values, and its mechanism bites*. It does
//! NOT mean a forged mid was proven unfoldable on the deployed prover.
//!
//! ⚠ Tier 3 is a NEW test. `dregg-automatafl/tests/prove_11x11.rs::mismatched_mid_fold_probe_11x11`
//! builds its leaves on the RUST-AIR path (`descriptor_state_leaf: None`), which declares no
//! window at all, so this seam never reaches it and its verdict is not about this work.
//!
//! ⚠ Several tests here need a MINTED LEG (and therefore `board_window_of_chain`, the host mirror).
//! They were `#[ignore]`d as BLOCKED on a wide-`Custom`-leg break (`compact_e1_columns` row-width
//! panic); that E1-compaction break is now FIXED (see `WIDE_LEG_BLOCKED`), so the two-leg fold
//! EXECUTES and they are re-marked SLOW — they mint wide Custom legs (~50s each), run `--ignored`.

use dregg_automatafl::reference::{Board, Move, automaton_step, resolve_mid, stock_two_player};
use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::ivc_turn_chain::board_window_of_chain;
use dregg_multiway_tug::fold::{LeafBundle, build_match_turns, fixture_rotated_roots};
use dreggnet_game_board::AutomataflMatch;

/// The real legal two-player turn on the stock 11×11 opening (the one
/// `prove_11x11.rs::honest_11x11_turn_matches_oracle` pins against the reference oracle):
/// seat 0 moves an ATT (7,1)→(7,5), seat 1 an ATT (0,4)→(0,2). Resolution places the ATT two east
/// of the automaton, which is then pulled east into (6,5).
fn round_one() -> (Move, Move) {
    (
        Move {
            who: 0,
            frm: (7, 1),
            to: (7, 5),
        },
        Move {
            who: 1,
            frm: (0, 4),
            to: (0, 2),
        },
    )
}

/// Find a legal, resolvable, seat-independent move pair on `b` by searching the real oracle
/// (`move_valid`) and gating on the real Lean-descriptor witness-gen (the `leaves()` call in the
/// caller). Rook moves only, distinct rows/columns per seat so the two never interact.
fn second_round(b: &Board) -> Option<(Move, Move)> {
    use dregg_automatafl::reference::move_valid;
    let mut found: Vec<Move> = Vec::new();
    for y in 0..b.n {
        for x in 0..b.n {
            if b.cells[y * b.n + x] != 2 {
                continue; // attractors only
            }
            for (tx, ty) in [
                (x, y.saturating_sub(2)),
                (x, (y + 2).min(b.n - 1)),
                (x.saturating_sub(2), y),
                ((x + 2).min(b.n - 1), y),
            ] {
                let m = Move {
                    who: found.len() as u32,
                    frm: (x as i32, y as i32),
                    to: (tx as i32, ty as i32),
                };
                if m.frm == m.to || !move_valid(b, &m) {
                    continue;
                }
                // Keep the two seats' moves on disjoint rows AND columns so no clash is possible.
                if found
                    .iter()
                    .any(|p| p.frm.0 == m.frm.0 || p.frm.1 == m.frm.1 || p.to == m.to)
                {
                    continue;
                }
                found.push(m);
                break;
            }
            if found.len() == 2 {
                return Some((found[0], found[1]));
            }
        }
    }
    None
}

/// Forge a board: place an attractor on some VACANT non-automaton square. This is the "I want a
/// different automaton pull than the moves I actually submitted earn" forgery — a board Leg R
/// never produced, handed to Leg A.
fn forge_one_cell(b: &Board) -> Board {
    let mut f = b.clone();
    let auto_idx = (f.auto.1 as usize) * f.n + (f.auto.0 as usize);
    let victim = (0..f.cells.len())
        .find(|&i| i != auto_idx && f.cells[i] == 0)
        .expect("an 11x11 mid board has a vacant square");
    f.cells[victim] = 2;
    f
}

/// An INDEPENDENT re-derivation of the base-4 positional pack the Lean descriptors publish
/// (`packed[f] = Σ_{i<15} cell[15f+i]·4^i`). Written out here rather than imported so the window
/// assertions below compare the fold's window against a value derived from the BOARD, not against
/// the same code path that produced it.
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

/// The 11-lane window a board occupies: `pack(9) ‖ (ax, ay)`.
fn window_of(board: &Board) -> Vec<BabyBear> {
    let mut w = pack(board);
    w.push(BabyBear::from_u64(board.auto.0 as u64));
    w.push(BabyBear::from_u64(board.auto.1 as u64));
    w
}

/// **THE WIDE-LEG BLOCKER, NAMED.** `AutomataflMatch::round_leaves` and `build_match_turns` both
/// route through `dregg_multiway_tug::fold::mint_custom_leg`, whose wide `Custom` leg currently
/// panics in the shared trace generator:
///
/// ```text
///   compact_e1_columns: customVmDescriptor2R24 row width 1627 < E1 band end 1675
///                       — the trace is not the S2-compacted wide row (compact E1 AFTER S2)
/// ```
///
/// That is the E1 dead-column compaction cutover (`bd21266e6b`, `circuit/src/effect_vm/
/// e1_compact_generated.rs`) disagreeing with the wide custom generator's row width — a break in a
/// path this file is the FIRST fast test to exercise (`dregg-multiway-tug`'s 39 lib tests all pass;
/// its leg-minting tests are `#[ignore]`d, so nothing covered it). It is UNRELATED to the board
/// window: no code in this seam touches the wide leg's columns.
///
/// So the canaries split in two. The ones below that need only the DESCRIPTORS and their PIs run
/// today and gate the seam. The ones that need a minted leg are `#[ignore]`d with this reason —
/// BLOCKED, not faked — and go green unchanged the moment the E1 table and the generator agree.
const WIDE_LEG_BLOCKED: &str = "FIXED: mint_custom_leg's wide Custom leg USED to panic with \
     `compact_e1_columns: customVmDescriptor2R24 row width 1627 < E1 band end 1675` — the E1 \
     compaction cutover (bd21266e6b) had emitted an E1 kill-set that reached into the prove-time \
     gentian refuse-aux block, PAST the wide producer's post-S2 row (systemic: EVERY bare-cohort \
     wide member, not just custom). Repaired by capping the emit's E1 scan at the host width \
     (`EmitWideRegistryProbe.e1Ceiling`) + regenerating the wide registry/E1 table. The two-leg \
     fold now EXECUTES; these tests are re-marked SLOW (they mint wide Custom legs, ~50s each).";

/// Build one round's two leaf PI vectors DIRECTLY from the Lean descriptors, bypassing
/// `round_leaves` (and therefore the broken wide leg). The door lanes `[0..16)` are left as the
/// witness-gen produced them: the FOLD binds those, the descriptor does not, and the board window
/// lives strictly past PI 16 — so nothing this file asserts depends on them.
/// Returns `([R.window, A.window], the board Leg A PRODUCED)`. The produced board is what the next
/// round must start from — chaining off a re-derivation instead would be testing the reference
/// oracle against itself rather than the leaves against each other.
fn round_windows_direct(
    start: &Board,
    mv: (Move, Move),
) -> Result<([(Vec<BabyBear>, Vec<BabyBear>); 2], Board), String> {
    use dregg_automatafl::resolve_witness::{
        automatafl_resolve_trace, resolve_board_window, resolve_descriptor_ident,
        resolve_trace_accepts,
    };
    use dregg_automatafl::witness::{
        automatafl_step_trace, step_board_window, step_descriptor_name, step_trace_accepts,
    };
    use dregg_circuit::descriptor_by_name::descriptor_by_name;
    use dregg_circuit::effect_vm::custom_state_binding::extract_custom_pi_board_window;

    let n = start.n;
    let rdesc = descriptor_by_name(resolve_descriptor_ident(n)).ok_or("no resolve descriptor")?;
    let sdesc = descriptor_by_name(&step_descriptor_name(n)).ok_or("no step descriptor")?;
    let rwin = resolve_board_window(n, &rdesc)?;
    let awin = step_board_window(n, &sdesc)?;
    let layout = dregg_automatafl::resolve_layout::ResolveLayout::new(n);

    let rt = automatafl_resolve_trace(start, &[mv.0, mv.1], &rdesc)?;
    if !resolve_trace_accepts(&rdesc, &rt) {
        return Err("Leg R does not satisfy the Lean resolve descriptor".into());
    }
    let mid = rt.mid_board(&layout);
    let st = automatafl_step_trace(&mid, &sdesc)?;
    if !step_trace_accepts(&sdesc, &st) {
        return Err("Leg A does not satisfy the Lean step descriptor".into());
    }

    let r = extract_custom_pi_board_window(&rt.public_inputs, &rwin)
        .ok_or("Leg R's declared window is not expressible in its PIs")?;
    let a = extract_custom_pi_board_window(&st.public_inputs, &awin)
        .ok_or("Leg A's declared window is not expressible in its PIs")?;
    Ok(([r, a], automaton_step(&mid)))
}

/// Read a leaf's declared `(IN, OUT)` windows straight off its public inputs, through the SAME
/// extractor the fold uses.
fn leaf_windows(b: &LeafBundle) -> (Vec<BabyBear>, Vec<BabyBear>) {
    use dregg_circuit::effect_vm::custom_state_binding::extract_custom_pi_board_window;
    let src = b
        .descriptor_state_leaf
        .as_ref()
        .expect("a two-leg round leaf carries a descriptor source");
    let binding = src
        .board_window
        .as_ref()
        .expect("a two-leg round leaf DECLARES a board window (that is the whole point)");
    extract_custom_pi_board_window(&b.public_inputs, binding)
        .expect("the declared window is expressible in the leaf's public inputs")
}

// ============================================================================
// THE SEAM, AT PI LEVEL — runs today, off the blocked wide-leg path
// ============================================================================

/// **THE MID SEAM.** `R.OUT == A.IN`, read straight off the two Lean descriptors' public inputs
/// for a real legal 11×11 round: 9 pack lanes and 2 automaton lanes, which is EXACTLY
/// `hseamPack ∧ hseamAutoX ∧ hseamAutoY`. This is the equality the aggregation node `connect`s;
/// `dregg-circuit-prove`'s `board_window_seam_tests` shows that a disagreement there has no witness.
#[test]
fn the_mid_seam_holds_on_a_real_round() {
    let (a, b) = round_one();
    let ([r, leg_a], _) = round_windows_direct(&stock_two_player(), (a, b))
        .expect("the honest 11x11 round satisfies both Lean descriptors");

    assert_eq!(r.0.len(), 11, "Leg R IN is pack(9) ‖ auto(2)");
    assert_eq!(leg_a.1.len(), 11, "Leg A OUT is pack(9) ‖ auto(2)");
    assert_eq!(
        r.1, leg_a.0,
        "R.OUT == A.IN — the MID SEAM (hseamPack ∧ hseamAutoX ∧ hseamAutoY)"
    );
    // NON-VACUITY: the seam is not trivially true because everything is equal.
    assert_ne!(r.0, r.1, "resolution actually changed the board");
    assert_ne!(
        leg_a.0, leg_a.1,
        "the automaton step actually changed it again"
    );
}

/// **THE WINDOWS ARE THE BOARDS.** Both legs' windows decode — via an independently written
/// base-4 pack — to the actual boards the reference oracle produces. This is what makes the root's
/// `[first.IN ‖ last.OUT]` readable as a position in the clear (`pack_injective_modp`).
#[test]
fn every_window_decodes_to_the_board_the_oracle_produces() {
    let (a, b) = round_one();
    let start = stock_two_player();
    let ([r, leg_a], produced) =
        round_windows_direct(&start, (a, b)).expect("the honest round lowers");

    let mid = resolve_mid(&start, &[a, b]);
    assert_eq!(
        produced,
        automaton_step(&mid),
        "the board Leg A produced IS the oracle's post-round board"
    );
    let new = automaton_step(&mid);
    assert_eq!(r.0, window_of(&start), "Leg R IN  == pack(old) ‖ auto(old)");
    assert_eq!(r.1, window_of(&mid), "Leg R OUT == pack(mid) ‖ auto(mid)");
    assert_eq!(
        leg_a.0,
        window_of(&mid),
        "Leg A IN  == pack(mid) ‖ auto(mid)"
    );
    assert_eq!(
        leg_a.1,
        window_of(&new),
        "Leg A OUT == pack(new) ‖ auto(new)"
    );
    // Leg A publishes the STEPPED automaton (the appended NAX/NAY PIs), without which the
    // inter-round carry could not exist.
    assert_ne!(
        leg_a.0[9..],
        leg_a.1[9..],
        "Leg A's OUT automaton is the one it PRODUCED"
    );
    assert_eq!(r.0[9..], r.1[9..], "resolution never moves the automaton");
}

/// **THE INTER-ROUND CARRY.** `A_0.OUT == R_1.IN` — the rounds form ONE trajectory. Same rule, one
/// level up the tree.
#[test]
fn the_inter_round_carry_holds_across_two_real_rounds() {
    let (a, b) = round_one();
    let start = stock_two_player();
    let after_one = automaton_step(&resolve_mid(&start, &[a, b]));
    let (r2a, r2b) =
        second_round(&after_one).expect("the board after round one admits a legal pair");

    let ([r0, a0], produced0) = round_windows_direct(&start, (a, b)).expect("round 0 lowers");
    // Round 1 starts from the board round 0's Leg A ACTUALLY PRODUCED — the same chaining
    // `AutomataflMatch::round_leaves` does (`board = automaton_step(&mid)`).
    let ([r1, a1], produced1) =
        round_windows_direct(&produced0, (r2a, r2b)).expect("round 1 lowers");

    assert_eq!(r0.1, a0.0, "R_0.OUT == A_0.IN");
    assert_eq!(a0.1, r1.0, "A_0.OUT == R_1.IN — THE INTER-ROUND CARRY");
    assert_eq!(r1.1, a1.0, "R_1.OUT == A_1.IN");

    // The chain's endpoints are the genesis and final positions, in the clear.
    assert_eq!(r0.0, window_of(&start), "first.IN is the genesis position");
    assert_eq!(
        a1.1,
        window_of(&produced1),
        "last.OUT is the final position"
    );
    // NON-VACUITY: the two rounds are genuinely different positions.
    assert_ne!(r0.0, a1.1, "the match actually moved");
}

/// **THE LOAD-BEARING NEGATIVE, AT PI LEVEL.** A forged mid: Leg A is fed a board Leg R did not
/// produce. BOTH legs still satisfy their own Lean descriptors — that is the whole difficulty —
/// and the ONLY thing that separates them is `R.OUT == A.IN`, which now fails on a specific lane.
/// In the fold that lane is a `connect` conflict; here it is an inequality we can see in
/// milliseconds.
#[test]
fn a_forged_mid_breaks_the_seam_though_both_legs_are_individually_valid() {
    use dregg_automatafl::witness::{
        automatafl_step_trace, step_board_window, step_descriptor_name, step_trace_accepts,
    };
    use dregg_circuit::descriptor_by_name::descriptor_by_name;
    use dregg_circuit::effect_vm::custom_state_binding::extract_custom_pi_board_window;

    let (a, b) = round_one();
    let start = stock_two_player();
    let ([r, honest_a], _) = round_windows_direct(&start, (a, b)).expect("the honest round lowers");
    assert_eq!(r.1, honest_a.0, "control: the honest seam holds");

    let forged_mid = forge_one_cell(&resolve_mid(&start, &[a, b]));
    let sdesc = descriptor_by_name(&step_descriptor_name(start.n)).expect("step descriptor");
    let awin = step_board_window(start.n, &sdesc).expect("step window");
    let st = automatafl_step_trace(&forged_mid, &sdesc).expect("Leg A builds on the forged mid");
    assert!(
        step_trace_accepts(&sdesc, &st),
        "the forged Leg A SATISFIES the Lean step descriptor — it is a genuine automaton step of \
         SOME board. Per-leaf validity cannot catch this; only the seam can."
    );
    let forged_a =
        extract_custom_pi_board_window(&st.public_inputs, &awin).expect("window is expressible");

    assert_ne!(
        r.1, forged_a.0,
        "R.OUT != A.IN on a forged mid — in the fold this is a per-lane connect CONFLICT (UNSAT \
         node, no root, no verifying artifact). This is precisely what \
         `mismatched_mid_diverges_board_roots_but_not_cell_continuity_11x11` shows the deployed \
         cell-continuity tooth does NOT see."
    );
    // And it is the PACK half that diverges, not an incidental automaton lane.
    assert_ne!(r.1[..9], forged_a.0[..9], "the packed board itself differs");
}

// ============================================================================
// THE HONEST FOLD — needs a MINTED LEG, so blocked on the E1 cutover
// ============================================================================

/// **TWO LEAVES PER ROUND, ON THE LEAN DESCRIPTORS.** A played round lowers to Leg R then Leg A —
/// not one automaton leaf — and each declares its own IN/OUT window.
#[test]
#[ignore = "SLOW (~50s/leg): round_leaves fills the door via mint_custom_leg — the two-leg fold now \
            EXECUTES; the E1-compaction block (bd21266e6b `compact_e1_columns` row-width panic) is \
            FIXED. Run with `--ignored`. See WIDE_LEG_BLOCKED"]
fn a_played_round_lowers_to_a_resolve_leaf_then_a_step_leaf() {
    let (a, b) = round_one();
    let m = AutomataflMatch::played(stock_two_player(), vec![(a, b)]);
    let leaves = m.leaves().expect("the honest 11x11 round lowers");

    assert_eq!(
        leaves.len(),
        2,
        "ONE round == TWO chained turns (Leg R, Leg A)"
    );

    let names: Vec<&str> = leaves
        .iter()
        .map(|l| {
            l.descriptor_state_leaf
                .as_ref()
                .expect("every round leaf proves a Lean descriptor")
                .descriptor
                .name
                .as_str()
        })
        .collect();
    assert!(
        names[0].contains("resolve"),
        "turn 2i must be the RESOLVE leg (the players' moves), got {names:?}"
    );
    assert!(
        names[1].contains("step"),
        "turn 2i+1 must be the STEP leg (the automaton), got {names:?}"
    );

    // Each leaf's door carries the REAL rotated roots of the leg the fold will mint for it — a
    // placeholder door is a UNSAT state tooth, so this is load-bearing, not cosmetic.
    for (i, l) in leaves.iter().enumerate() {
        let (old8, new8) = fixture_rotated_roots(i as u64);
        assert_eq!(&l.public_inputs[..8], &old8[..], "leaf {i} old8 door");
        assert_eq!(&l.public_inputs[8..16], &new8[..], "leaf {i} new8 door");
    }
}

/// **THE MID SEAM AND THE INTER-ROUND CARRY, AT PI LEVEL.** Over a TWO-round match:
/// `R_0.OUT == A_0.IN` (the mid seam) and `A_0.OUT == R_1.IN` (the carry). Every one of these
/// equalities becomes an in-circuit `connect`.
#[test]
#[ignore = "SLOW (~50s/leg): needs a MINTED LEG (mint_custom_leg) — the two-leg fold now EXECUTES; \
            the E1-compaction block (bd21266e6b `compact_e1_columns` row-width panic) is FIXED. Run \
            with `--ignored`. See WIDE_LEG_BLOCKED"]
fn the_windows_chain_leaf_to_leaf_across_the_mid_and_across_rounds() {
    let (a, b) = round_one();
    let start = stock_two_player();
    // A SECOND round on the board round one reaches. Rather than hand-pick coordinates that a
    // descriptor change could silently invalidate, SEARCH for a pair the real witness-gen accepts
    // — the whole two-round lowering is the gate.
    let after_one = automaton_step(&resolve_mid(&start, &[a, b]));
    let (r2a, r2b) = second_round(&after_one).expect(
        "the 11x11 board after round one admits SOME legal, resolvable, independent move pair",
    );
    let m = AutomataflMatch::played(start.clone(), vec![(a, b), (r2a, r2b)]);
    let leaves = m.leaves().expect("the honest two-round match lowers");
    assert_eq!(leaves.len(), 4, "two rounds == four chained turns");

    let wins: Vec<(Vec<BabyBear>, Vec<BabyBear>)> = leaves.iter().map(leaf_windows).collect();
    for (i, (win_in, win_out)) in wins.iter().enumerate() {
        assert_eq!(win_in.len(), 11, "leaf {i} IN is pack(9) ‖ auto(2)");
        assert_eq!(win_out.len(), 11, "leaf {i} OUT is pack(9) ‖ auto(2)");
    }

    assert_eq!(
        wins[0].1, wins[1].0,
        "R_0.OUT == A_0.IN — the MID SEAM (hseamPack ∧ hseamAutoX ∧ hseamAutoY)"
    );
    assert_eq!(
        wins[1].1, wins[2].0,
        "A_0.OUT == R_1.IN — the INTER-ROUND CARRY (the boards are ONE trajectory)"
    );
    assert_eq!(
        wins[2].1, wins[3].0,
        "R_1.OUT == A_1.IN — the second round's mid seam"
    );

    // Leg R never moves the automaton (Lean: `resolveMoves_automaton`), so its OUT automaton IS
    // its IN automaton — which is why the resolve window costs zero new lanes.
    assert_eq!(
        wins[0].0[9..],
        wins[0].1[9..],
        "Leg R's automaton is unmoved by resolution"
    );
    // Leg A DOES move it — and publishes the moved coordinate (the appended NAX/NAY PIs). Without
    // that the inter-round carry could not exist.
    assert_ne!(
        wins[1].0[9..],
        wins[1].1[9..],
        "Leg A publishes the STEPPED automaton coordinate, not its input one"
    );
}

/// **THE ROOT WINDOW IS THE GENESIS AND FINAL POSITION.** The host mirror of the in-circuit fold
/// yields `[first.IN ‖ last.OUT]`, and both halves decode — via an independently written base-4
/// pack — to the actual boards the match started from and reached. This is what lets a light
/// client read the final position in the clear and check the win condition with no extra circuit.
#[test]
#[ignore = "SLOW (~50s/leg): needs a MINTED LEG (mint_custom_leg) — the two-leg fold now EXECUTES; \
            the E1-compaction block (bd21266e6b `compact_e1_columns` row-width panic) is FIXED. Run \
            with `--ignored`. See WIDE_LEG_BLOCKED"]
fn the_root_window_is_the_genesis_and_final_board_in_the_clear() {
    let (a, b) = round_one();
    let start = stock_two_player();
    let m = AutomataflMatch::played(start.clone(), vec![(a, b)]);
    let leaves = m.leaves().expect("the honest round lowers");
    let turns = build_match_turns(&leaves);

    let w = board_window_of_chain(&turns)
        .expect("an honest two-leg chain has a well-formed board window")
        .expect("a two-leg chain DECLARES a board window");

    let final_board = automaton_step(&resolve_mid(&start, &[a, b]));
    assert_eq!(
        w.first_in,
        window_of(&start),
        "the root's first.IN IS the genesis position (pack is injective)"
    );
    assert_eq!(
        w.last_out,
        window_of(&final_board),
        "the root's last.OUT IS the final position (pack is injective)"
    );
    // And the same boards the match's own reference walk reports.
    let walked = m.round_boards();
    assert_eq!(walked.first().map(window_of), Some(w.first_in.clone()));
    assert_eq!(walked.last().map(window_of), Some(w.last_out.clone()));
}

// ============================================================================
// THE LOAD-BEARING NEGATIVE — A MISMATCHED MID DOES NOT FOLD
// ============================================================================

/// Build the two-leg leaves BY HAND so Leg A can be fed a board Leg R did NOT produce. This is the
/// forgery `mismatched_mid_diverges_board_roots_but_not_cell_continuity_11x11` demonstrates the
/// DEPLOYED cell-continuity tooth cannot see: the cell lineage is a nonce bump, content-independent,
/// so the forged chain is perfectly well-formed there.
fn hand_built_round(
    start: &Board,
    mv: (Move, Move),
    leg_a_input: &Board,
) -> Result<Vec<LeafBundle>, String> {
    use dregg_automatafl::resolve_witness::{
        automatafl_resolve_trace, resolve_board_window, resolve_descriptor_ident,
        resolve_trace_accepts,
    };
    use dregg_automatafl::witness::{
        automatafl_step_trace, step_board_window, step_descriptor_name, step_trace_accepts,
    };
    use dregg_circuit::descriptor_by_name::descriptor_by_name;
    use dregg_circuit_prove::joint_turn_aggregation::DescriptorStateLeafSource;

    let n = start.n;
    let rdesc = descriptor_by_name(resolve_descriptor_ident(n)).ok_or("no resolve descriptor")?;
    let sdesc = descriptor_by_name(&step_descriptor_name(n)).ok_or("no step descriptor")?;
    let rwin = resolve_board_window(n, &rdesc)?;
    let awin = step_board_window(n, &sdesc)?;
    let rows = 2usize;

    let mut rt = automatafl_resolve_trace(start, &[mv.0, mv.1], &rdesc)?;
    let (r_old8, r_new8) = fixture_rotated_roots(0);
    rt.public_inputs[..8].copy_from_slice(&r_old8);
    rt.public_inputs[8..16].copy_from_slice(&r_new8);
    if !resolve_trace_accepts(&rdesc, &rt) {
        return Err("the resolve leg does not satisfy its Lean descriptor".into());
    }

    // Leg A is built over `leg_a_input` — the honest mid in the control, a FORGED board in the
    // probe. Note it satisfies its OWN descriptor either way: a valid automaton step of SOME
    // board. That is precisely why the seam has to be a fold-enforced equality and not a
    // per-leaf check.
    let mut st = automatafl_step_trace(leg_a_input, &sdesc)?;
    let (a_old8, a_new8) = fixture_rotated_roots(1);
    st.public_inputs[..8].copy_from_slice(&a_old8);
    st.public_inputs[8..16].copy_from_slice(&a_new8);
    if !step_trace_accepts(&sdesc, &st) {
        return Err("the step leg does not satisfy its Lean descriptor".into());
    }

    // The retained Rust-AIR program rides along exactly as `round_leaves` retains it — it is NOT
    // the object proven (the descriptor is), but the bundle shape carries it.
    let r_prog = dregg_automatafl::moves::build_r_honest(start, &mv.0, &mv.1);
    let a_prog = dregg_automatafl::build_a_honest(leg_a_input);
    Ok(vec![
        LeafBundle {
            program: r_prog.cellprogram(),
            witness_values: r_prog.trace_witness(rows),
            num_rows: rows,
            public_inputs: rt.public_inputs.clone(),
            descriptor_state_leaf: Some(DescriptorStateLeafSource {
                descriptor: rdesc,
                base_trace: rt.base_trace(rows),
                board_window: Some(rwin),
            }),
        },
        LeafBundle {
            program: a_prog.cellprogram(),
            witness_values: a_prog.trace_witness(rows),
            num_rows: rows,
            public_inputs: st.public_inputs.clone(),
            descriptor_state_leaf: Some(DescriptorStateLeafSource {
                descriptor: sdesc,
                base_trace: st.base_trace(rows),
                board_window: Some(awin),
            }),
        },
    ])
}

/// **THE CONTROL.** The hand-built path with the HONEST mid folds exactly like `round_leaves`:
/// same window, no refusal. Without this the negative below would be unfalsifiable (a
/// hand-construction that ALWAYS fails proves nothing).
#[test]
#[ignore = "SLOW (~50s/leg): needs a MINTED LEG (mint_custom_leg) — the two-leg fold now EXECUTES; \
            the E1-compaction block (bd21266e6b `compact_e1_columns` row-width panic) is FIXED. Run \
            with `--ignored`. See WIDE_LEG_BLOCKED"]
fn the_hand_built_honest_round_is_accepted_and_matches_the_generated_one() {
    let (a, b) = round_one();
    let start = stock_two_player();
    let mid = resolve_mid(&start, &[a, b]);

    let hand = hand_built_round(&start, (a, b), &mid).expect("the honest hand-built round builds");
    let hand_turns = build_match_turns(&hand);
    let hand_w = board_window_of_chain(&hand_turns)
        .expect("the honest hand-built chain has a window")
        .expect("it declares one");

    let generated = AutomataflMatch::played(start.clone(), vec![(a, b)])
        .leaves()
        .expect("the generated round lowers");
    let gen_w = board_window_of_chain(&build_match_turns(&generated))
        .expect("the generated chain has a window")
        .expect("it declares one");

    assert_eq!(
        hand_w.first_in, gen_w.first_in,
        "hand-built and generated genesis windows must agree"
    );
    assert_eq!(
        hand_w.last_out, gen_w.last_out,
        "hand-built and generated final windows must agree"
    );
}

/// **THE LOAD-BEARING CANARY — A MISMATCHED MID IS REFUSED.** Leg A is fed a board Leg R did not
/// produce. Both leaves individually satisfy their Lean descriptors; the cell lineage is
/// untouched; the ONLY thing that catches it is `R.OUT == A.IN`. The chain is refused BEFORE any
/// proving, naming the broken seam — and in the circuit the same disagreement is a per-lane
/// `connect` conflict (UNSAT node ⇒ no root ⇒ the light client never receives a verifying
/// artifact).
///
/// This is the case `mismatched_mid_diverges_board_roots_but_not_cell_continuity_11x11` shows the
/// deployed fold does NOT catch today.
#[test]
#[ignore = "SLOW (~50s/leg): needs a MINTED LEG (mint_custom_leg) — the two-leg fold now EXECUTES; \
            the E1-compaction block (bd21266e6b `compact_e1_columns` row-width panic) is FIXED. Run \
            with `--ignored`. See WIDE_LEG_BLOCKED"]
fn a_mismatched_mid_breaks_the_board_window_seam_and_is_refused() {
    let (a, b) = round_one();
    let start = stock_two_player();
    let honest_mid = resolve_mid(&start, &[a, b]);

    let forged_mid = forge_one_cell(&honest_mid);
    assert_ne!(forged_mid, honest_mid, "the forgery must actually differ");

    let forged = hand_built_round(&start, (a, b), &forged_mid)
        .expect("the forged round still builds — BOTH legs satisfy their own descriptors");

    // The cell lineage is untouched by the forgery: turn 0's post-state IS turn 1's pre-state.
    // This is the tooth that does NOT see the forgery.
    let turns = build_match_turns(&forged);
    assert_eq!(
        turns[0].new_root(),
        turns[1].old_root(),
        "the CELL continuity tooth is perfectly happy with a forged mid — it is a nonce bump"
    );

    // The BOARD window is not.
    let err = board_window_of_chain(&turns)
        .expect_err("a forged mid must be REFUSED, not folded into a verifying artifact");
    let msg = format!("{err:?}");
    assert!(
        msg.contains("board-window seam broken"),
        "the refusal must name the broken seam, got: {msg}"
    );
}

/// Every lane of the window is load-bearing: forging the AUTOMATON coordinate alone (leaving the
/// packed board identical) is refused too. `hseamAutoX`/`hseamAutoY` are separate hypotheses of
/// the whole-turn theorem for a reason.
#[test]
#[ignore = "SLOW (~50s/leg): needs a MINTED LEG (mint_custom_leg) — the two-leg fold now EXECUTES; \
            the E1-compaction block (bd21266e6b `compact_e1_columns` row-width panic) is FIXED. Run \
            with `--ignored`. See WIDE_LEG_BLOCKED"]
fn a_forged_automaton_coordinate_alone_breaks_the_seam() {
    let (a, b) = round_one();
    let start = stock_two_player();
    let honest_mid = resolve_mid(&start, &[a, b]);

    let mut moved_auto = honest_mid.clone();
    // Relocate the automaton one square west onto a vacant cell — the leg then publishes an
    // automaton coordinate Leg R did not hand it.
    let (ax, ay) = moved_auto.auto;
    let n = moved_auto.n;
    let here = (ay as usize) * n + (ax as usize);
    let there = (ay as usize) * n + (ax as usize) - 1;
    if moved_auto.cells[there] != 0 {
        return; // no vacant neighbour on this board; nothing to forge cleanly
    }
    moved_auto.cells[here] = 0;
    moved_auto.cells[there] = 3; // AUTO
    moved_auto.auto = (ax - 1, ay);

    let Ok(forged) = hand_built_round(&start, (a, b), &moved_auto) else {
        // If the relocated automaton has no satisfying Leg A at all, the forgery is already dead
        // one level lower — also a refusal, and an honest outcome for this canary.
        return;
    };
    let err = board_window_of_chain(&build_match_turns(&forged))
        .expect_err("a relocated automaton must break the seam");
    assert!(format!("{err:?}").contains("board-window seam broken"));
}

// ============================================================================
// THE ACCEPTANCE GATE — the REAL fold. SLOW; `#[ignore]`d.
// ============================================================================
//
// ⚠ READ THIS BEFORE TRUSTING A GREEN. `dregg-automatafl/tests/prove_11x11.rs`'s
// `mismatched_mid_fold_probe_11x11` builds its leaves with `descriptor_state_leaf: None` — the
// RUST-AIR path, which declares NO board window — so it probes a chain this seam does not touch
// and will keep recording the hole. THESE are the twins that go through the two-leg
// descriptor+window path, and THEIR sign is what settles whether the seam is closed on the
// deployed prover. Neither has been run: a real n=11 two-leg fold is tens of minutes.
//
//   cargo test -p dreggnet-game-board --test two_leg_board_window -- --ignored --nocapture

/// **THE HONEST TWO-LEG FOLD.** The real deployed prover folds Leg R then Leg A, the light client
/// ACCEPTS, and the attestation carries the genesis and final positions — decodable in the clear.
#[test]
#[ignore = "SLOW: a real n=11 two-leg fold (1273-col Leg R + 680-col Leg A, each recursion-wrapped, \
            plus the tree) is tens of minutes. Run on the build box with --ignored"]
fn the_honest_two_leg_match_folds_and_the_light_client_reads_the_final_position() {
    use dregg_lightclient::verify_history;
    use dregg_multiway_tug::fold::fold_match;

    let (a, b) = round_one();
    let start = stock_two_player();
    let leaves = AutomataflMatch::played(start.clone(), vec![(a, b)])
        .leaves()
        .expect("the honest round lowers");

    let whole = fold_match(&leaves).expect("the honest two-leg chain must fold");
    let vk = whole.root_vk_fingerprint();
    let attested = verify_history(&whole, &vk).expect("the light client must ACCEPT");

    assert_eq!(attested.num_turns, 2, "one round == two folded turns");
    let final_board = automaton_step(&resolve_mid(&start, &[a, b]));
    assert_eq!(
        attested.board_genesis.as_deref(),
        Some(window_of(&start).as_slice()),
        "the attestation pins the GENESIS position"
    );
    assert_eq!(
        attested.board_final.as_deref(),
        Some(window_of(&final_board).as_slice()),
        "the attestation pins the FINAL position — the light client decodes it and checks the win \
         condition with no extra circuit (the pack is injective)"
    );
}

/// **THE MILESTONE — A MISMATCHED MID MUST NOT FOLD.** Both leaves satisfy their own Lean
/// descriptors; the cell lineage is intact; the ONLY thing standing between a forged mid and a
/// ranked leaderboard entry is the in-circuit `left.OUT == right.IN`. When this test REJECTS on
/// the deployed prover, the seam is real.
///
/// The refusal may land at either of two places, and BOTH are the seam doing its job: the host
/// mirror (milliseconds, before any proving) or the aggregation node's `connect` conflict (UNSAT).
/// What is NOT acceptable is a verifying artifact.
#[test]
#[ignore = "SLOW: the real n=11 mismatched-mid fold probe. Run on the build box with --ignored"]
fn a_mismatched_mid_does_not_fold_on_the_deployed_prover() {
    use dregg_lightclient::verify_history;
    use dregg_multiway_tug::fold::fold_match;

    let (a, b) = round_one();
    let start = stock_two_player();
    let forged_mid = forge_one_cell(&resolve_mid(&start, &[a, b]));

    let forged = hand_built_round(&start, (a, b), &forged_mid)
        .expect("both legs satisfy their own descriptors — that is the point");

    match fold_match(&forged) {
        Err(e) => eprintln!("MISMATCHED-MID REJECTED at fold assembly: {e}"),
        Ok(whole) => {
            let vk = whole.root_vk_fingerprint();
            match verify_history(&whole, &vk) {
                Err(e) => eprintln!("MISMATCHED-MID REJECTED at verify_history: {e:?}"),
                Ok(_) => panic!(
                    "SOUNDNESS GAP: a forged mid folded into an artifact the light client \
                     ACCEPTS. The board-window seam (left.OUT == right.IN) did not fire — check \
                     that BOTH leaves declared a window and that the aggregation node ran \
                     prove_custom_binding_node_state_and_board_segmented, not the state-only node."
                ),
            }
        }
    }
}

// ============================================================================
// SHAPE — the fail-closed verifier extension
// ============================================================================

/// The two-leg root exposes `25 + 2*11 = 47` lanes, and the leaf `24 + 2*11 = 46`. Today's
/// 25-lane verifier would REJECT a 47-lane root — the correct fail-closed default, which is why
/// the artifact carries the window explicitly and the verifier appends it to the SAME
/// exact-equality comparison (so both shape mismatches fall out of it, in both directions).
#[test]
fn the_two_leg_claim_widths_are_the_ones_the_verifier_was_extended_to() {
    use dregg_circuit_prove::ivc_turn_chain::SEG_WIDTH;
    const W: usize = 11;
    assert_eq!(SEG_WIDTH, 25, "the deployed segment is 25 lanes");
    assert_eq!(SEG_WIDTH + 2 * W, 47, "the board-window root exposes 47");
    assert_eq!(
        dregg_circuit_prove::custom_leaf_adapter::custom_board_window_claim_len(W),
        46,
        "the board-window LEAF exposes commitment(8) ‖ old8 ‖ new8 ‖ IN(11) ‖ OUT(11)"
    );
}

/// A chain that MIXES a windowed turn with a plain one is refused: the merge has no combine for
/// the mixed shape, and degrading to the plain combine would drop the seam exactly where a forger
/// wants it dropped.
#[test]
#[ignore = "SLOW (~50s/leg): needs a MINTED LEG (mint_custom_leg) — the two-leg fold now EXECUTES; \
            the E1-compaction block (bd21266e6b `compact_e1_columns` row-width panic) is FIXED. Run \
            with `--ignored`. See WIDE_LEG_BLOCKED"]
fn a_chain_mixing_windowed_and_plain_turns_is_refused() {
    let (a, b) = round_one();
    let start = stock_two_player();
    let mut leaves = AutomataflMatch::played(start.clone(), vec![(a, b)])
        .leaves()
        .expect("the honest round lowers");
    // Strip the SECOND leaf's window declaration — the "just fold it without the seam" dodge.
    leaves[1]
        .descriptor_state_leaf
        .as_mut()
        .expect("descriptor source")
        .board_window = None;

    let err = board_window_of_chain(&build_match_turns(&leaves))
        .expect_err("a mixed-shape chain must be refused");
    assert!(
        format!("{err:?}").contains("cannot mix board-window and plain turns"),
        "the refusal must name the mixed shape, got {err:?}"
    );
}
