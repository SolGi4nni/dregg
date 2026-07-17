//! **C.5 — the fold-leg split (Leg R ∘ Leg A).** FAST battery (no proving): the
//! monolithic turn is carved into two foldable custom leaves connected by the
//! intermediate board root `mid_root`.
//!
//!  - **Leg R** (`old → mid`): validity + m=2 conflict + chain-follow/flow-through +
//!    board rewrite, PUBLISHING `mid_root = board_root8(mid)` as its new-root app PI.
//!  - **Leg A** (`mid → new`): the automaton gadget on the resolved board, CONSUMING
//!    the byte-identical `board_root8(mid)` as its old-root app PI.
//!
//! Shadowed by `Builder::air_accepts`, this asserts: (1) each leg refines its half of
//! the oracle exactly and is non-vacuous (a forged `mid`/`new` is REJECTED); (2) the
//! composed `automaton_step ∘ resolve_mid == apply_turn` (the corrected reference);
//! (3) THE SEAM — Leg R's published `mid_root` byte-matches Leg A's consumed old-root
//! on the honest path, and DIVERGES when Leg A is fed a different `mid` than Leg R
//! produced (the per-lane connect conflict that makes a forged mid UNSAT in the fold).
//! The real prove + fold + light-client accept lives in `tests/prove_fold.rs`.

use dregg_automatafl::builder::Builder;
use dregg_automatafl::reference::{
    ATT, AUTO, Board, Move, REP, VAC, apply_turn, automaton_step, resolve_mid,
};
use dregg_automatafl::{build_a, build_a_honest, build_r, build_r_honest};
use dregg_circuit::dsl::circuit::MAX_TRACE_WIDTH;

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

/// Flip one non-automaton cell to produce a definitely-wrong board.
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
    assert!(
        !b.failing().is_empty(),
        "{ctx}: expected the AIR to REJECT, but it accepted"
    );
}

/// Board-state app PIs: `[16..24)` = old board root, `[24..32)` = new board root.
const ROOT_OLD: std::ops::Range<usize> = 16..24;
const ROOT_NEW: std::ops::Range<usize> = 24..32;

/// The two-player cases the split is exercised on. A collision (mid == old, at n=3)
/// and two independent survivors (mid != old, at n=5), so the seam is tested both when
/// the board is rewritten and when it is not.
fn cases() -> Vec<(&'static str, Board, Move, Move)> {
    vec![
        (
            "n3 dest-collision → both dropped (mid == old)",
            mk(3, &[((0, 0), ATT), ((2, 2), REP)], (2, 0)),
            Move {
                who: 0,
                frm: (0, 0),
                to: (0, 2),
            },
            Move {
                who: 1,
                frm: (2, 2),
                to: (0, 2),
            },
        ),
        (
            "n5 two independent survivors (mid != old)",
            mk(5, &[((0, 0), ATT), ((4, 4), REP)], (2, 2)),
            Move {
                who: 0,
                frm: (0, 0),
                to: (0, 3),
            },
            Move {
                who: 1,
                frm: (4, 4),
                to: (4, 1),
            },
        ),
    ]
}

// ============================================================================
// Leg R — the resolution leg (old → mid).
// ============================================================================

#[test]
fn leg_r_refines_resolve_mid() {
    for (tag, old, a, b) in cases() {
        let mid = resolve_mid(&old, &[a, b]);
        // honest accepts
        assert!(
            build_r_honest(&old, &a, &b).air_accepts(),
            "Leg R honest ({tag}) must self-accept"
        );
        // an equivalent explicit-mid build accepts
        assert!(
            build_r(&old, &a, &b, &mid).air_accepts(),
            "Leg R honest explicit-mid ({tag}) must self-accept"
        );
        // a forged mid is rejected by the per-cell rewrite equalities
        let bad = corrupt(&mid);
        assert_ne!(bad, mid, "corruption must differ ({tag})");
        assert_failing(
            &build_r(&old, &a, &b, &bad),
            &format!("Leg R forged mid ({tag})"),
        );
    }
}

#[test]
fn leg_r_rejects_invalid_move() {
    // A from==to move is invalid; Leg R's validate_move hard-gates it.
    let old = mk(5, &[((0, 0), ATT), ((4, 4), REP)], (2, 2));
    let bad_a = Move {
        who: 0,
        frm: (0, 0),
        to: (0, 0),
    };
    let b = Move {
        who: 1,
        frm: (4, 4),
        to: (4, 1),
    };
    // Drive the honest witness for the (filtered) resolution but hand Leg R the invalid move:
    // its coordinate/distinct gates cannot be satisfied by the witnessed columns.
    let mid = resolve_mid(&old, &[bad_a, b]);
    assert_failing(
        &build_r(&old, &bad_a, &b, &mid),
        "Leg R invalid move (from==to)",
    );
}

// ============================================================================
// Leg A — the automaton leg (mid → new).
// ============================================================================

#[test]
fn leg_a_refines_automaton_step() {
    for (tag, old, a, b) in cases() {
        let mid = resolve_mid(&old, &[a, b]);
        let new = automaton_step(&mid);
        // honest accepts
        assert!(
            build_a_honest(&mid).air_accepts(),
            "Leg A honest ({tag}) must self-accept"
        );
        assert!(
            build_a(&mid, &new).air_accepts(),
            "Leg A honest explicit-new ({tag}) must self-accept"
        );
        // a forged new board is rejected by the automaton output equalities
        let bad = corrupt(&new);
        assert_ne!(bad, new, "corruption must differ ({tag})");
        assert_failing(&build_a(&mid, &bad), &format!("Leg A forged new ({tag})"));
    }
}

// ============================================================================
// The composed refinement + the mid_root seam.
// ============================================================================

/// `automaton_step ∘ resolve_mid == apply_turn` — the composed legs refine the corrected
/// oracle exactly (the equation `build_r` proves `old→mid` and `build_a` proves `mid→new`).
#[test]
fn composed_legs_equal_apply_turn() {
    for (tag, old, a, b) in cases() {
        let mid = resolve_mid(&old, &[a, b]);
        let new = automaton_step(&mid);
        assert_eq!(
            new,
            apply_turn(&old, &[a, b]),
            "R∘A must equal apply_turn ({tag})"
        );
    }
}

/// THE SEAM: Leg R's PUBLISHED new-root PI (`mid_root = board_root8(mid)`, at PI[24..32])
/// byte-matches Leg A's CONSUMED old-root PI (`board_root8(mid)`, at PI[16..24]) — the
/// value the deployed continuity connect welds. Both legs compute a byte-identical `mid`
/// on the honest path.
#[test]
fn honest_mid_root_welds_the_two_legs() {
    for (tag, old, a, b) in cases() {
        let mid = resolve_mid(&old, &[a, b]);
        let leg_r = build_r_honest(&old, &a, &b);
        let leg_a = build_a_honest(&mid);
        assert!(
            leg_r.air_accepts() && leg_a.air_accepts(),
            "both legs accept ({tag})"
        );
        assert_eq!(leg_r.pis.len(), 32, "Leg R publishes 32 PIs ({tag})");
        assert_eq!(leg_a.pis.len(), 32, "Leg A publishes 32 PIs ({tag})");
        let r_mid_root = &leg_r.pis[ROOT_NEW];
        let a_old_root = &leg_a.pis[ROOT_OLD];
        assert_eq!(
            r_mid_root, a_old_root,
            "Leg R's published mid_root must byte-match Leg A's consumed old-root ({tag})"
        );
    }
}

/// THE SEAM IS LOAD-BEARING: feed Leg A a DIFFERENT `mid` than Leg R produced. Leg A
/// SELF-accepts (it is a genuine automaton step on that other board) — which is exactly
/// why the seam is needed — but its published old-root DIVERGES from Leg R's mid_root, so
/// the deployed continuity connect (`last_new8` R == `first_old8` A) is a per-lane conflict
/// ⇒ UNSAT ⇒ no folded proof. Here we witness the divergence at the PI level.
#[test]
fn forged_mid_breaks_the_seam() {
    for (tag, old, a, b) in cases() {
        let honest_mid = resolve_mid(&old, &[a, b]);
        let forged_mid = corrupt(&honest_mid);
        assert_ne!(forged_mid, honest_mid, "forged mid differs ({tag})");

        let leg_r = build_r_honest(&old, &a, &b);
        let leg_a_forged = build_a_honest(&forged_mid);
        // Leg A on the forged mid is itself a valid automaton step — it self-accepts.
        assert!(
            leg_a_forged.air_accepts(),
            "Leg A on the forged mid self-accepts (the seam, not Leg A, catches it) ({tag})"
        );
        // But its consumed old-root no longer matches Leg R's published mid_root.
        assert_ne!(
            &leg_r.pis[ROOT_NEW], &leg_a_forged.pis[ROOT_OLD],
            "a forged mid MUST diverge Leg A's old-root from Leg R's mid_root ({tag})"
        );
    }
}

// ============================================================================
// Width — each leg fits the deployed prover (< MAX_TRACE_WIDTH), and the split
// shrinks the widest leg below the monolith (the point of C.5).
// ============================================================================

#[test]
fn each_leg_fits_the_prover() {
    use dregg_automatafl::build_d3_honest;
    for (tag, old, a, b) in cases() {
        let mid = resolve_mid(&old, &[a, b]);
        let wr = build_r_honest(&old, &a, &b).descriptor().trace_width;
        let wa = build_a_honest(&mid).descriptor().trace_width;
        let wmono = build_d3_honest(&old, &a, &b).descriptor().trace_width;
        eprintln!("{tag:<44} legR={wr:<5} legA={wa:<5} monolith(D3)={wmono}");
        assert!(
            wr <= MAX_TRACE_WIDTH,
            "Leg R width {wr} exceeds {MAX_TRACE_WIDTH} ({tag})"
        );
        assert!(
            wa <= MAX_TRACE_WIDTH,
            "Leg A width {wa} exceeds {MAX_TRACE_WIDTH} ({tag})"
        );
        // The split's purpose: neither leg is wider than the monolith it was carved from.
        assert!(
            wr <= wmono && wa <= wmono,
            "a split leg is wider than the monolith ({tag}): R={wr} A={wa} mono={wmono}"
        );
    }
}
