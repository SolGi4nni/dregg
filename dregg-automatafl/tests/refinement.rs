//! FAST refinement battery (no proving): the AIR accepts the honest
//! `(old, moves, next)` IFF `next == apply_turn(old, moves)` (translation validation
//! shadowed by `Builder::air_accepts`), and is NON-VACUOUS — a wrong `next`, an
//! invalid move, or a forged resolution is REJECTED. Driven against the reference
//! oracle (which mirrors `Dregg2.Games.Automatafl` and its `#guard`s).

use dregg_automatafl::builder::Builder;
use dregg_automatafl::reference::{ATT, AUTO, Board, Move, REP, VAC, apply_turn, automaton_step};
use dregg_automatafl::{
    SealedMove, build_d1, build_d1_honest, build_d2, build_d3, build_sealed, build_sealed_honest,
};
use dregg_circuit::field::BabyBear;

fn mk(n: usize, placed: &[((i32, i32), u8)], auto: (i32, i32)) -> Board {
    let mut cells = vec![VAC; n * n];
    for &(c, p) in placed {
        cells[(c.1 as usize) * n + (c.0 as usize)] = p;
    }
    cells[(auto.1 as usize) * n + (auto.0 as usize)] = AUTO;
    Board {
        n,
        cells,
        auto,
        col_rule: true,
    }
}

/// Flip one non-automaton cell of `b` to produce a definitely-wrong board.
fn corrupt(b: &Board) -> Board {
    let mut c = b.clone();
    for i in 0..c.cells.len() {
        let coord = ((i % c.n) as i32, (i / c.n) as i32);
        if coord != c.auto {
            c.cells[i] = if c.cells[i] == VAC { ATT } else { VAC };
            return c;
        }
    }
    c
}

fn assert_failing(b: &Builder, ctx: &str) {
    let f = b.failing();
    assert!(
        !f.is_empty(),
        "{ctx}: expected the AIR to REJECT, but it accepted"
    );
}

// ============================================================================
// D1 — the automaton-step-only AIR.
// ============================================================================

fn d1_boards() -> Vec<(&'static str, Board)> {
    vec![
        (
            "demo: attractor north dist2 -> step north",
            mk(5, &[((2, 4), ATT)], (2, 2)),
        ),
        (
            "repulsor south dist1 -> flee north",
            mk(5, &[((2, 1), REP)], (2, 2)),
        ),
        ("empty -> no move", mk(5, &[], (2, 2))),
        (
            "attractor east dist2 -> step east",
            mk(5, &[((4, 2), ATT)], (2, 2)),
        ),
        (
            "attractor adjacent dist1 -> no room, no move",
            mk(5, &[((2, 3), ATT)], (2, 2)),
        ),
        (
            "unbalanced pair att north rep south -> north",
            mk(5, &[((2, 4), ATT), ((2, 0), REP)], (2, 2)),
        ),
        (
            "two attractors, closer wins (E dist2 vs W dist3)",
            mk(5, &[((4, 2), ATT), ((0, 2), ATT)], (3, 2)),
        ),
        (
            "repulsor pair both axes -> flee",
            mk(5, &[((2, 0), REP), ((0, 2), REP)], (2, 2)),
        ),
        (
            "auto at edge (0,0), attractor east",
            mk(5, &[((3, 0), ATT)], (0, 0)),
        ),
        (
            "column rule tie -> prefer Y",
            mk(5, &[((4, 2), ATT), ((2, 4), ATT)], (2, 2)),
        ),
    ]
}

#[test]
fn d1_accepts_honest_and_matches_reference() {
    for (name, old) in d1_boards() {
        let honest = automaton_step(&old);
        let b = build_d1(&old, &honest);
        let f = b.failing();
        assert!(
            f.is_empty(),
            "D1 [{name}]: honest transition must be ACCEPTED; failing constraints = {:?}",
            f
        );
    }
}

#[test]
fn d1_rejects_wrong_next() {
    for (name, old) in d1_boards() {
        let honest = automaton_step(&old);
        let wrong = corrupt(&honest);
        assert_ne!(wrong, honest);
        let b = build_d1(&old, &wrong);
        assert_failing(&b, &format!("D1 wrong-next [{name}]"));
    }
}

#[test]
fn d1_rejects_forged_offset() {
    // demoBoard steps north; forge the witnessed offset oy to 0 (claim it stayed).
    let old = mk(5, &[((2, 4), ATT)], (2, 2));
    let honest = automaton_step(&old);
    let mut b = build_d1(&old, &honest);
    let oy = b.col_by_name("oy").expect("oy column");
    b.tamper(oy, 0);
    assert_failing(&b, "D1 forged offset oy:=0");
}

#[test]
fn d1_rejects_forged_moved_bit() {
    // Empty board: automaton does not move. Forge `moved := 1` and a fake target.
    let old = mk(5, &[((2, 4), ATT)], (2, 2)); // this one DOES move
    let honest = automaton_step(&old);
    let mut b = build_d1(&old, &honest);
    let m = b.col_by_name("moved").expect("moved column");
    b.tamper(m, 0); // claim it didn't move
    assert_failing(&b, "D1 forged moved:=0 on a moving board");
}

// ============================================================================
// D2 — single move apply.
// ============================================================================

#[test]
fn d2_accepts_honest_and_rejects_wrong_next() {
    // Move attractor (0,0)->(0,3); automaton parked in corner (4,4) does not move.
    let old = mk(5, &[((0, 0), ATT)], (4, 4));
    let m = Move {
        who: 0,
        frm: (0, 0),
        to: (0, 3),
    };
    let honest = apply_turn(&old, &[m]);
    let b = build_d2(&old, &m, &honest);
    let f = b.failing();
    assert!(f.is_empty(), "D2 honest must accept; failing = {:?}", f);

    let wrong = corrupt(&honest);
    let b2 = build_d2(&old, &m, &wrong);
    assert_failing(&b2, "D2 wrong-next");
}

#[test]
fn d2_move_with_automaton_stepping() {
    // Move an attractor into the automaton's sight so the daemon also steps.
    // Board: auto (2,2); move attractor (2,0)->... actually place attractor far then
    // move it two-north-visible. Simpler: attractor at (4,2), auto (2,2): move a
    // repulsor (0,0)->(0,4) elsewhere; daemon steps east toward the attractor.
    let old = mk(5, &[((4, 2), ATT), ((0, 0), REP)], (2, 2));
    let m = Move {
        who: 0,
        frm: (0, 0),
        to: (0, 4),
    };
    let honest = apply_turn(&old, &[m]);
    let b = build_d2(&old, &m, &honest);
    let f = b.failing();
    assert!(
        f.is_empty(),
        "D2 move+step honest must accept; failing = {:?}",
        f
    );
}

#[test]
fn d2_rejects_invalid_move() {
    // An invalid move (not rook-aligned) must be rejected by the validity gates.
    let old = mk(5, &[((0, 0), ATT)], (4, 4));
    let bad = Move {
        who: 0,
        frm: (0, 0),
        to: (1, 3),
    }; // diagonal
    // apply_turn would DROP it (mid == old); but the AIR asserts submitted moves valid.
    let honest_next = automaton_step(&old); // since the move is dropped, next == step(old)
    let b = build_d2(&old, &bad, &honest_next);
    assert_failing(&b, "D2 invalid (diagonal) move");
}

#[test]
fn d2_occluded_move_piece_stays() {
    // (0,0)->(0,3) blocked by a repulsor at (0,2): the piece stays; next == step(old).
    let old = mk(5, &[((0, 0), ATT), ((0, 2), REP)], (4, 4));
    let m = Move {
        who: 0,
        frm: (0, 0),
        to: (0, 3),
    };
    let honest = apply_turn(&old, &[m]);
    // Reference: occluded => piece stays => (0,0) still ATT.
    assert_eq!(honest.cell_at((0, 0)), ATT);
    let b = build_d2(&old, &m, &honest);
    let f = b.failing();
    assert!(
        f.is_empty(),
        "D2 occluded honest must accept; failing = {:?}",
        f
    );
}

// ============================================================================
// D3 — the n=2 resolution truth table.
// ============================================================================

#[test]
fn d3_independent_moves() {
    // Two disjoint valid moves, both apply.
    let old = mk(7, &[((0, 0), ATT), ((6, 6), REP)], (3, 3));
    let a = Move {
        who: 0,
        frm: (0, 0),
        to: (0, 2),
    };
    let b = Move {
        who: 1,
        frm: (6, 6),
        to: (6, 4),
    };
    let honest = apply_turn(&old, &[a, b]);
    let prog = build_d3(&old, &a, &b, &honest);
    let f = prog.failing();
    assert!(
        f.is_empty(),
        "D3 independent honest must accept; failing = {:?}",
        f
    );
    let wrong = corrupt(&honest);
    assert_failing(&build_d3(&old, &a, &b, &wrong), "D3 independent wrong-next");
}

#[test]
fn d3_source_fork_both_dropped() {
    // Fork: one source, two distinct destinations -> both dropped, piece stays.
    let old = mk(5, &[((0, 0), ATT)], (4, 4));
    let a = Move {
        who: 0,
        frm: (0, 0),
        to: (0, 3),
    };
    let b = Move {
        who: 1,
        frm: (0, 0),
        to: (3, 0),
    };
    let honest = apply_turn(&old, &[a, b]);
    assert_eq!(honest.cell_at((0, 0)), ATT, "forked piece stays");
    let prog = build_d3(&old, &a, &b, &honest);
    let f = prog.failing();
    assert!(
        f.is_empty(),
        "D3 fork honest must accept; failing = {:?}",
        f
    );
    // Forged resolution: claim the piece moved to (0,3) anyway.
    let mut forged = old.clone();
    forged.cells[(0) * 5 + 0] = VAC;
    forged.cells[(3) * 5 + 0] = ATT;
    let forged_next = automaton_step(&forged);
    assert_failing(
        &build_d3(&old, &a, &b, &forged_next),
        "D3 forged fork survival",
    );
}

#[test]
fn d3_dest_collision_both_dropped() {
    // Two non-vacuum sources onto one destination -> both dropped.
    let old = mk(5, &[((0, 2), ATT), ((4, 2), REP)], (2, 4));
    let a = Move {
        who: 0,
        frm: (0, 2),
        to: (2, 2),
    };
    let b = Move {
        who: 1,
        frm: (4, 2),
        to: (2, 2),
    };
    let honest = apply_turn(&old, &[a, b]);
    assert_eq!(honest.cell_at((0, 2)), ATT, "collided A stays");
    assert_eq!(honest.cell_at((4, 2)), REP, "collided B stays");
    let prog = build_d3(&old, &a, &b, &honest);
    let f = prog.failing();
    assert!(
        f.is_empty(),
        "D3 collision honest must accept; failing = {:?}",
        f
    );
}

// ============================================================================
// D2/D3 SHARPENED non-vacuity: witnessed-bound reads + in-circuit selection.
// ============================================================================

#[test]
fn d2_rejects_forged_source_cell_read() {
    // The claimed source (0,0) is VACUUM. A prover forges the read source particle
    // fp := ATT to fake a carrying piece. The witnessed one-hot read pins
    // fp == old[n*fy+fx] == 0, so the forgery has no satisfying witness.
    let old = mk(5, &[((2, 2), ATT)], (4, 4));
    let m = Move {
        who: 0,
        frm: (0, 0),
        to: (0, 3),
    };
    let honest = apply_turn(&old, &[m]);
    let mut b = build_d2(&old, &m, &honest);
    assert!(b.failing().is_empty(), "sanity: honest D2 must accept");
    let fp = b.col_by_name("m0_fp_v").expect("m0_fp_v column");
    b.tamper(fp, 2); // claim the vacuum source holds an attractor
    assert_failing(&b, "D2 forged source-cell read (vacuum claimed non-vacuum)");
}

#[test]
fn d3_rejects_forged_selection_survive() {
    // Source-fork: a,b share source (0,0), distinct dests -> both dropped, piece stays.
    // A prover forges `surv := 1` to claim its move survived. The in-circuit truth
    // table derives fork = [frm_a==frm_b] & ![to_a==to_b] = 1 from the witnessed
    // coordinates, pinning surv = (1-fork)(1-collide) = 0 — the forgery is rejected.
    let old = mk(5, &[((0, 0), ATT)], (4, 4));
    let a = Move {
        who: 0,
        frm: (0, 0),
        to: (0, 3),
    };
    let b = Move {
        who: 1,
        frm: (0, 0),
        to: (3, 0),
    };
    let honest = apply_turn(&old, &[a, b]);
    let mut prog = build_d3(&old, &a, &b, &honest);
    assert!(prog.failing().is_empty(), "sanity: honest fork must accept");
    let surv = prog.col_by_name("surv").expect("surv column");
    prog.tamper(surv, 1); // claim the forked move survives
    assert_failing(&prog, "D3 forged selection (survive a fork)");
    // Also: forging the fork bit itself is rejected by its own derivation.
    let mut prog2 = build_d3(&old, &a, &b, &honest);
    let fork = prog2.col_by_name("fork").expect("fork column");
    prog2.tamper(fork, 0); // claim it is NOT a fork
    assert_failing(&prog2, "D3 forged fork:=0 on a genuine fork");
}

#[test]
fn d3_flow_through_vacuum_conduit_accepts() {
    // Vacuum flow-through: A's source (0,0) is VACUUM; a:(0,0)->(0,4), b:(0,2)->(0,0).
    // B (REP) targets A's vacuum source, then flows THROUGH A's resolved unoccluded
    // move to A's destination (0,4). The in-circuit dest derivation (ft_b) must place
    // REP at (0,4) — i.e. the chain endpoint is computed from the pattern bits, not
    // taken from the reference.
    let old = mk(5, &[((0, 2), REP)], (4, 4));
    let a = Move {
        who: 0,
        frm: (0, 0),
        to: (0, 4),
    };
    let b = Move {
        who: 1,
        frm: (0, 2),
        to: (0, 0),
    };
    let honest = apply_turn(&old, &[a, b]);
    assert_eq!(honest.cell_at((0, 4)), REP, "B flows through to A's dest");
    assert_eq!(honest.cell_at((0, 2)), VAC, "B's source cleared");
    let prog = build_d3(&old, &a, &b, &honest);
    let f = prog.failing();
    assert!(
        f.is_empty(),
        "D3 flow-through honest must accept (in-circuit chain endpoint); failing = {:?}",
        f
    );
    let wrong = corrupt(&honest);
    assert_failing(
        &build_d3(&old, &a, &b, &wrong),
        "D3 flow-through wrong-next",
    );
}

// ============================================================================
// THE IN-PROOF SEALED MOVE — the commit→reveal enforced inside the AIR.
// ============================================================================

fn sealed_board() -> Board {
    mk(5, &[((0, 0), ATT), ((4, 4), REP)], (2, 2))
}

fn sealed_a() -> SealedMove {
    SealedMove {
        seat: 0,
        mv: Move {
            who: 0,
            frm: (0, 0),
            to: (0, 3),
        },
        nonce: 0xABCD,
    }
}

fn sealed_b() -> SealedMove {
    SealedMove {
        seat: 1,
        mv: Move {
            who: 1,
            frm: (4, 4),
            to: (4, 1),
        },
        nonce: 0x1234,
    }
}

#[test]
fn sealed_honest_accepts_and_binds_commitment() {
    let old = sealed_board();
    let (a, b) = (sealed_a(), sealed_b());
    let prog = build_sealed_honest(&old, &a, &b);
    let f = prog.failing();
    assert!(f.is_empty(), "sealed honest must accept; failing = {:?}", f);
    // The in-AIR commit column byte-matches the host Poseidon2 commitment.
    let ca = prog.col_by_name("sa_commit").expect("sa_commit column");
    let cb = prog.col_by_name("sb_commit").expect("sb_commit column");
    assert_eq!(
        prog.value(ca),
        a.commit(old.n),
        "seat A in-circuit commit != host hash_4_to_1"
    );
    assert_eq!(
        prog.value(cb),
        b.commit(old.n),
        "seat B in-circuit commit != host hash_4_to_1"
    );
    // The committed hashes ride the descriptor PIs. The sealed leaf now publishes the door's
    // state-binding prefix (PI[0..16]) + the constrained old-board root (PI[16..24]) before the
    // two seat commitments (PI[24..26]) — the ABI the deployed state prover requires.
    assert_eq!(
        prog.pis.len(),
        26,
        "[old8 ‖ new8 ‖ board_old_root8 ‖ a_commit ‖ b_commit]"
    );
    assert!(prog.pis.contains(&a.commit(old.n)) && prog.pis.contains(&b.commit(old.n)));
}

#[test]
fn sealed_forged_reveal_rejected() {
    // Seat A committed (0,0)->(0,3) but tries to OPEN (0,0)->(0,4) after seeing the board.
    // Both are valid automatafl moves, so validity passes; the Hash4to1 commitment
    // (commit == hash(opened)) is the ONLY thing that bites — a post-reveal swap has no
    // satisfying leaf.
    let old = sealed_board();
    let (a, b) = (sealed_a(), sealed_b());
    let forged_open = Move {
        who: 0,
        frm: (0, 0),
        to: (0, 4),
    };
    assert_ne!(forged_open, a.mv, "the forged opening must differ");
    let prog = build_sealed(&old, &a, &forged_open, &b, &b.mv);
    assert_failing(
        &prog,
        "sealed forged reveal (A opens a move it did not commit)",
    );

    // And tampering the revealed nonce (opening with a different blinding) is rejected too.
    let mut prog2 = build_sealed_honest(&old, &a, &b);
    assert!(prog2.failing().is_empty(), "sanity: honest sealed accepts");
    let nonce_a = prog2.col_by_name("sa_nonce").expect("sa_nonce column");
    prog2.tamper(nonce_a, 0x9999);
    assert_failing(
        &prog2,
        "sealed forged nonce (A opens with a different blinding)",
    );
}

#[test]
fn d3_swap_stasis() {
    // 2-swap (to_a==frm_b AND to_b==frm_a) -> always stasis (both stay).
    let old = mk(5, &[((0, 0), ATT), ((0, 2), REP)], (4, 4));
    let a = Move {
        who: 0,
        frm: (0, 0),
        to: (0, 2),
    };
    let b = Move {
        who: 1,
        frm: (0, 2),
        to: (0, 0),
    };
    let honest = apply_turn(&old, &[a, b]);
    let prog = build_d3(&old, &a, &b, &honest);
    let f = prog.failing();
    assert!(
        f.is_empty(),
        "D3 swap-stasis honest must accept; failing = {:?}",
        f
    );
}

// ============================================================================
// THE BOARD-STATE ROOT: constrained, not merely published. The two board roots ride PI[16..32]
// via `bind_pi` (`ConstraintExpr::PiBinding`), and each is a `cap_node8` Merkle root the AIR
// FORCES over the board columns (`MerkleHash8` sites). So a published root is (a) BOUND — it must
// equal the trace column — and (b) DERIVED — that column must be the real node8 compression of
// the exact board the transition proves. This is the cure for "bound but constrained by nothing".
// ============================================================================

/// The two `MerkleHash8`-constrained board roots self-accept on the honest board, and every one of
/// their 16 published lanes rides a real PI (PI[16..32]) — the door prefix `[old8 ‖ new8]` sits
/// below at PI[0..16].
#[test]
fn board_roots_ride_the_app_public_inputs() {
    let old = mk(5, &[((2, 4), ATT)], (2, 2));
    let b = build_d1_honest(&old);
    assert!(
        b.air_accepts(),
        "honest D1 (with board roots) must self-accept"
    );
    // 16 door lanes + 8 old-board-root + 8 new-board-root = 32 PIs.
    assert_eq!(
        b.pis.len(),
        32,
        "D1 must publish [old8 ‖ new8 ‖ board_old_root8 ‖ board_new_root8]"
    );
}

/// **CANARY — the published root is BOUND.** Forging the published `board_new_root` PI while the
/// trace computes the real one is REFUSED by the `PiBinding`: the PI is constrained to its trace
/// column, not a free value. Revert → refused; restore → accepted (the standing falsifier).
#[test]
fn a_forged_published_board_root_is_refused() {
    let old = mk(5, &[((2, 4), ATT)], (2, 2));
    let mut b = build_d1_honest(&old);
    assert!(b.air_accepts(), "honest self-accepts");
    // PI[24] is board_new_root lane 0 (PI[0..16] door, PI[16..24] old root, PI[24..32] new root).
    let honest = b.pis[24];
    b.pis[24] = honest + BabyBear::ONE;
    assert!(
        !b.air_accepts(),
        "a forged published board-new-root PI must be refused — the PiBinding makes it CONSTRAINED"
    );
    b.pis[24] = honest;
    assert!(b.air_accepts(), "restored honest root re-accepts");
}

/// **CANARY — the root is DERIVED.** Forging the root's TRACE column (as a prover would, to
/// publish a lie the board did not produce) is REFUSED by the `MerkleHash8` site: the root column
/// must be `cap_node8` of its children, so a forged root has no satisfying witness. This is the
/// "constrained" half — a full 8-felt (~124-bit) node8 collision would be required to spoof it.
#[test]
fn a_forged_board_root_column_is_unsat() {
    let old = mk(5, &[((2, 4), ATT)], (2, 2));
    let mut b = build_d1_honest(&old);
    assert!(b.air_accepts(), "honest self-accepts");
    // The new-board root node (n=5: 25 cells → 4 leaves → r0 has 2 nodes → r1_n0 is the root).
    let root_lane0 = b
        .col_by_name("boardnew_r1_n0_l0")
        .expect("the new-board root node's lane-0 column exists");
    let honest = b.value(root_lane0);
    b.tamper(root_lane0, (honest + BabyBear::ONE).0 as i128);
    assert!(
        !b.air_accepts(),
        "a forged board-root column must be UNSAT — MerkleHash8 forces it to cap_node8(children)"
    );
    b.tamper(root_lane0, honest.0 as i128);
    assert!(b.air_accepts(), "restored honest root column re-accepts");
}
