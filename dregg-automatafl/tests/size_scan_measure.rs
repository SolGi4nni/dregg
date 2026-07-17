//! THROWAWAY MEASUREMENT (not a gate) — trace-width census across REAL tafl board sizes to
//! inform ember's board-size call. It reuses the exact honest-builder shapes from `size.rs`
//! but sweeps `n` over the standard tafl sizes: 5 (current), 7 (brandub), 9 (tablut),
//! 11 (hnefatafl standard). It does NOT change the game or any logic — it only builds the
//! staged AIRs at each `n` and prints their descriptor widths vs MAX_TRACE_WIDTH. Run with:
//!   cargo test -p dregg-automatafl --test size_scan_measure -- --ignored --nocapture

use dregg_automatafl::reference::{ATT, AUTO, Board, Move, REP, VAC};
use dregg_automatafl::{
    Builder, SealedMove, build_d1_honest, build_d2_honest, build_d3_honest, build_sealed_honest,
};
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

fn line(tag: &str, n: usize, b: &Builder) {
    let d = b.descriptor();
    let over = d.trace_width > MAX_TRACE_WIDTH;
    eprintln!(
        "{tag:<8} n={n:<3} width={:<6} constraints={:<5} max_degree={:<2} pis={:<3} {}",
        d.trace_width,
        d.constraints.len(),
        d.max_degree,
        d.public_input_count,
        if over { "OVER" } else { "fits" },
    );
    assert!(
        b.air_accepts(),
        "{tag} n={n}: honest witness must self-accept"
    );
}

/// Build the four staged AIRs at board edge `n` (same move shapes as size.rs; all coords <5 so
/// they are legal at every n>=5) and print each stage's width.
fn census_at(n: usize) {
    // D1 — automaton step alone.
    line("D1", n, &build_d1_honest(&mk(n, &[((2, 4), ATT)], (2, 2))));

    // D2 — single move + resolution, automaton on mid.
    let d2_old = mk(n, &[((0, 0), ATT)], (4, 4));
    let d2_m = Move {
        who: 0,
        frm: (0, 0),
        to: (0, 3),
    };
    line("D2", n, &build_d2_honest(&d2_old, &d2_m));

    // D3 — two-move simultaneous resolution.
    let d3_old = mk(n, &[((0, 0), ATT)], (4, 4));
    let d3_a = Move {
        who: 0,
        frm: (0, 0),
        to: (0, 3),
    };
    let d3_b = Move {
        who: 1,
        frm: (0, 0),
        to: (3, 0),
    };
    line("D3", n, &build_d3_honest(&d3_old, &d3_a, &d3_b));

    // SEALED — commit/reveal wrapper over the D3 resolution.
    let s_old = mk(n, &[((0, 0), ATT), ((4, 4), REP)], (2, 2));
    let s_a = SealedMove {
        seat: 0,
        mv: Move {
            who: 0,
            frm: (0, 0),
            to: (0, 3),
        },
        nonce: 0xABCD,
    };
    let s_b = SealedMove {
        seat: 1,
        mv: Move {
            who: 1,
            frm: (4, 4),
            to: (4, 1),
        },
        nonce: 0x1234,
    };
    line("SEALED", n, &build_sealed_honest(&s_old, &s_a, &s_b));

    eprintln!("  (MAX_TRACE_WIDTH = {MAX_TRACE_WIDTH})");
    eprintln!();
}

#[test]
#[ignore = "measurement, not a gate — run with --ignored --nocapture"]
fn width_scan_across_tafl_sizes() {
    for n in [5usize, 7, 9, 11] {
        eprintln!("==== n = {n} ====");
        census_at(n);
    }
    let _ = AUTO; // keep import if unused in a build variant
}
