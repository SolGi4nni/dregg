//! Width / constraint census across the staged AIRs. The automaton gadget runs on the
//! move-resolved `mid` in D2/D3, so each stage adds a second ~automaton-width block —
//! this test MEASURES whether the widened circuits fit under `MAX_TRACE_WIDTH = 1024` at
//! each board size, driving the prove/fold size decision (`prove_fold.rs`).

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

/// Measure one stage: PRINT its width census and (self-check) that the honest witness accepts,
/// then return `Some(tag width)` if it EXCEEDS `MAX_TRACE_WIDTH`. The caller collects the
/// over-budget stages and asserts NONE remain — so every stage's width still prints before the
/// gate fails. THE BUDGET IS A GATE, NOT A PRINTOUT: a leaf over `MAX_TRACE_WIDTH` cannot be
/// proven by the deployed prover, so this test is RED when any stage exceeds (D2/D3 at n=5 do
/// today; the ray-scan redesign is what closes it). Never weaken this to buy green.
#[must_use]
fn report(tag: &str, b: &Builder) -> Option<String> {
    let d = b.descriptor();
    let over = d.trace_width > MAX_TRACE_WIDTH;
    eprintln!(
        "{tag:<14} width={:<5} constraints={:<5} max_degree={:<2} pis={:<2} [{} {}]",
        d.trace_width,
        d.constraints.len(),
        d.max_degree,
        d.public_input_count,
        if over { "EXCEEDS" } else { "FITS" },
        MAX_TRACE_WIDTH,
    );
    assert!(b.air_accepts(), "{tag}: honest witness must self-accept");
    over.then(|| format!("{tag} (width {})", d.trace_width))
}

/// Fail the test iff any measured stage exceeds the width cap — listing every over-budget one.
fn assert_all_fit(over: Vec<Option<String>>) {
    let over: Vec<String> = over.into_iter().flatten().collect();
    assert!(
        over.is_empty(),
        "these stages EXCEED MAX_TRACE_WIDTH = {MAX_TRACE_WIDTH} and cannot be proven by the \
         deployed prover (the ray-scan redesign must land before they fit): {}",
        over.join(", "),
    );
}

#[test]
fn d1_size_report() {
    // D1 fits at both sizes (the automaton step alone); asserted, not just printed.
    let over = vec![
        report("D1 n5", &build_d1_honest(&mk(5, &[((2, 4), ATT)], (2, 2)))),
        report("D1 n3", &build_d1_honest(&mk(3, &[((1, 2), ATT)], (1, 0)))),
    ];
    assert_all_fit(over);
}

/// The n=3 staged census — every stage FITS at n=3 (asserted). This is the GREEN gate: the
/// board-root-bearing leaves at the playable-in-a-test size prove-fold today.
#[test]
fn staged_width_census_n3_fits() {
    let d2n3_old = mk(3, &[((0, 0), ATT)], (2, 2));
    let d2n3_m = Move {
        who: 0,
        frm: (0, 0),
        to: (0, 1),
    };
    let d3n3_old = mk(3, &[((0, 0), ATT), ((2, 2), REP)], (2, 0));
    let d3n3_a = Move {
        who: 0,
        frm: (0, 0),
        to: (0, 2),
    };
    let d3n3_b = Move {
        who: 1,
        frm: (2, 2),
        to: (0, 2),
    };
    let over = vec![
        report("D1 n3", &build_d1_honest(&mk(3, &[((1, 2), ATT)], (1, 0)))),
        report("D2 n3", &build_d2_honest(&d2n3_old, &d2n3_m)),
        report("D3 n3", &build_d3_honest(&d3n3_old, &d3n3_a, &d3n3_b)),
    ];
    assert_all_fit(over);
}

/// The n=5 (deployed board size) census. D2/D3 run the automaton gadget a SECOND time on the
/// move-resolved `mid`, and the 4n³ ray scan dominates — so they EXCEED `MAX_TRACE_WIDTH`
/// TODAY and this test is RED. That RED is the TRUE signal the ray-scan redesign is not yet
/// landed; it is NOT to be weakened into a print. (D1 n5 and the sealed reveal fit.)
#[test]
fn staged_width_census_n5() {
    let d2n5_old = mk(5, &[((0, 0), ATT)], (4, 4));
    let d2n5_m = Move {
        who: 0,
        frm: (0, 0),
        to: (0, 3),
    };
    let d3n5_old = mk(5, &[((0, 0), ATT)], (4, 4));
    let d3n5_a = Move {
        who: 0,
        frm: (0, 0),
        to: (0, 3),
    };
    let d3n5_b = Move {
        who: 1,
        frm: (0, 0),
        to: (3, 0),
    };
    let old = mk(5, &[((0, 0), ATT), ((4, 4), REP)], (2, 2));
    let a = SealedMove {
        seat: 0,
        mv: Move {
            who: 0,
            frm: (0, 0),
            to: (0, 3),
        },
        nonce: 0xABCD,
    };
    let b = SealedMove {
        seat: 1,
        mv: Move {
            who: 1,
            frm: (4, 4),
            to: (4, 1),
        },
        nonce: 0x1234,
    };
    let over = vec![
        report("D1 n5", &build_d1_honest(&mk(5, &[((2, 4), ATT)], (2, 2)))),
        report("D2 n5", &build_d2_honest(&d2n5_old, &d2n5_m)),
        report("D3 n5", &build_d3_honest(&d3n5_old, &d3n5_a, &d3n5_b)),
        report("SEALED n5", &build_sealed_honest(&old, &a, &b)),
    ];
    assert_all_fit(over);
}
