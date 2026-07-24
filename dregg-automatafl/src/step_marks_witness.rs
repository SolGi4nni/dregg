//! # The witness generator for the Lean-emitted STEP-MARKS descriptor — the AUTOMATON STEP of a
//! CLEAN ROUND carrying a FROZEN marks window (braid M6′).
//!
//! **The trusted, fail-closed trace generator that fills the PROVEN Lean descriptor
//! `automataflStepMarksDescN {n}` (`circuit/descriptors/by-name/automatafl-step-marks-n{n}.json`), so
//! the multi-round fold's CLEAN sub-chain `RM → A` folds UNIFORM-WIDTH (both legs 20-lane
//! `[board(9) ‖ marks(9) ‖ auto(2)]`).** House law #1: the AIR is authored in Lean; this Rust only
//! fills a trace and CALLS the general IR-v2 evaluator. It authors NO constraints.
//!
//! ## The method — the step witness-gen, plus a FROZEN marks window
//!
//! The marks-carrying step descriptor is `automataflStepDescN n`'s constraints VERBATIM plus a MARKS
//! WINDOW at fresh columns above `A_WIDTH_N n` (`AutomataflStepMarksCapstone` §1–§2): the accumulated
//! `marksIn` COMMITMENT — the `n²` `{0,1}` indicator cells, the `⌈n²/15⌉` base-4 packed felts, and
//! their PI bindings (`marksCommitFamilyAt`). There is NO legality re-check (that already happened at
//! the resolve-marks leg, M6): the step only CARRIES marks.
//!
//! Because `automatonStepCfg` is MARKS-INDEPENDENT (the capstone's KEY OBSERVATION), the step columns
//! `[0, A_WIDTH_N n)` fill EXACTLY as they do for the plain step leaf — so this reuses
//! [`crate::witness::seed_step`] on those columns verbatim, and adds only the marks window's free
//! inputs (the `marksIn` indicator cells). The packed marks felts are then solved by the SAME Rule-L
//! gate propagation over the descriptor's OWN gates. The load-bearing check is
//! [`step_marks_trace_accepts`]: the REAL `Ir2Air` row-local evaluator over two rows must accept
//! before any leaf is proven; a wrong fill fails a gate exactly as it would fail the STARK.

use dregg_circuit::descriptor_ir2::{EffectVmDescriptor2, VmConstraint2, ir2_eval_accepts_i64};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};

use crate::reference::{Board, Coord};
use crate::resolve_witness::rule_l_pass;
use crate::step_marks_layout::{StepMarksLayout, step_marks_descriptor_name};
use crate::witness::{
    STEP_PACK_IN_PI, bb, packed_felts, pi_binding_cols, placeholder_roots, seed_step, set_if_none,
    step_auto_in_pi, step_auto_out_pi, step_pack_out_pi,
};

/// The by-name loader identity of the Lean step-marks descriptor for board size `n`.
pub fn step_marks_descriptor_ident(n: usize) -> &'static str {
    step_marks_descriptor_name(n)
}

/// The canonical `i64` representative of a `BabyBear` (it stores its value reduced into `[0, p)`).
fn canon(f: BabyBear) -> i64 {
    f.0 as i64
}

/// **LEG A's BOARD-STATE WINDOW, marks-carrying** — the clean-round window the multi-round braid's
/// `RM → A` handoff and the `A → RM_next` inter-round carry connect.
/// `IN = pack(old) ‖ pack(marksIn) ‖ (ax, ay)`,
/// `OUT = pack(new) ‖ pack(marksIn) ‖ (nax, nay)` — 20 lanes at `n = 11`
/// (`board(9) ‖ marks(9) ‖ auto(2)`).
///
/// Its leading `board(9) ‖ marks(9)` prefix (18 lanes) is EXACTLY
/// [`roundstate_window_n11::HANDOFF_LANES`](dregg_circuit::effect_vm::custom_state_binding::roundstate_window_n11),
/// laid out in the SAME `board`-then-`marks` order as the conflict rounds' 32-lane RoundState window
/// and the resolve-marks leg's 20-lane window — so the clean sub-chain `RM(20) → A(20)` is UNIFORM,
/// and the nested sub-root `[RM.IN(20) ‖ A.OUT(20)]` the fold assembles is symmetric. `marks` is
/// FROZEN through the step (the step CARRIES marks, never touches them), so IN and OUT both point at
/// the single published `pack(marksIn)` PI window; `board` steps (`old → new`) and `auto` steps
/// (`(ax,ay) → (nax,nay)`).
///
/// `Err` (fail-closed) if the loaded descriptor's PI count is not the step-marks layout for `n`, if it
/// predates the `NAX`/`NAY` stepped-automaton append, or the window is not expressible in it.
pub fn step_marks_board_window(
    n: usize,
    desc: &EffectVmDescriptor2,
) -> Result<dregg_circuit::effect_vm::custom_state_binding::BoardWindowBinding, String> {
    use dregg_circuit::effect_vm::custom_state_binding::BoardWindowBinding;
    let l = StepMarksLayout::new(n);
    if l.pi_count() != desc.public_input_count {
        return Err(format!(
            "step-marks board window: layout PI count {} ≠ descriptor '{}' public_input_count {}",
            l.pi_count(),
            desc.name,
            desc.public_input_count
        ));
    }
    let f = packed_felts(n);
    let auto_out = step_auto_out_pi(n, desc).ok_or_else(|| {
        format!(
            "step-marks descriptor '{}' publishes {} PIs — it carries no STEPPED automaton \
             coordinate (NAX/NAY). Leg A cannot declare an OUT window whose automaton is the one it \
             PRODUCED, so the inter-round carry is blocked, not faked.",
            desc.name, desc.public_input_count
        )
    })?;
    let b = BoardWindowBinding {
        // board(pack_old) ‖ marks(pack_marksIn) ‖ auto (consumed).
        in_slices: vec![
            (STEP_PACK_IN_PI, f),
            (l.pi_marks_in(), f),
            (step_auto_in_pi(n), 2),
        ],
        // board(pack_new) ‖ marks(pack_marksIn, frozen) ‖ auto (stepped).
        out_slices: vec![
            (step_pack_out_pi(n), f),
            (l.pi_marks_out(), f),
            (auto_out, 2),
        ],
    };
    if !b.is_well_formed() || desc.public_input_count < b.pi_end() {
        return Err(format!(
            "step-marks board window {b:?} is not expressible in descriptor '{}' ({} PIs)",
            desc.name, desc.public_input_count
        ));
    }
    Ok(b)
}

/// The generated single-row trace + public inputs for the Lean step-marks descriptor.
#[derive(Clone, Debug)]
pub struct StepMarksTrace {
    /// One trace row of width `descriptor.trace_width` (the gates are row-local).
    pub row: Vec<BabyBear>,
    /// The descriptor public inputs
    /// (`door16 ‖ pack(old) ‖ pack(new) ‖ ax,ay ‖ nax,nay ‖ pack(marksIn)`).
    pub public_inputs: Vec<BabyBear>,
    /// The board size.
    pub n: usize,
}

impl StepMarksTrace {
    /// The base trace for the evaluator: the row replicated `num_rows` times. Use `≥ 2` rows to
    /// exercise the `when_transition` gates.
    pub fn base_trace(&self, num_rows: usize) -> Vec<Vec<BabyBear>> {
        vec![self.row.clone(); num_rows.max(2)]
    }

    /// The decoded NEW board cells (`NGen.new`) read back out of the filled trace — the automaton
    /// step's board. Marks-independent (the step columns are untouched by the marks carry), so this
    /// equals the plain step leaf's `new` board.
    pub fn new_cells(&self, l: &StepMarksLayout) -> Vec<u8> {
        (0..l.s.kk)
            .map(|c| canon(self.row[l.s.new_cell(c)]) as u8)
            .collect()
    }
}

// --------------------------------------------------------------------------------------------
// THE WITNESS GENERATOR.
// --------------------------------------------------------------------------------------------

/// **Fill the Lean step-marks descriptor's trace** for the honest automaton step `old → new` of a
/// clean round carrying the accumulated `marksIn` indicator `marks`, then assemble the public inputs.
///
/// `desc` is the decoded Lean descriptor for `old.n` (via
/// `dregg_circuit::descriptor_by_name(step_marks_descriptor_ident(old.n))`). The generator is checked
/// against it: on any layout disagreement (`trace_width` / `public_input_count`) it returns `Err`
/// (fail-closed). Every column is filled by SOLVING the descriptor's own gates; an unresolved column
/// is a named `Err`, never a silent mis-fill.
pub fn automatafl_step_marks_trace(
    old: &Board,
    marks: &[Coord],
    desc: &EffectVmDescriptor2,
) -> Result<StepMarksTrace, String> {
    let n = old.n;
    let l = StepMarksLayout::new(n);

    // Fail-closed layout guards: the descriptor must be the step-marks layout for this `n`.
    if l.width() != desc.trace_width {
        return Err(format!(
            "step-marks witness-gen: layout width {} ≠ descriptor '{}' trace_width {} — a descriptor \
             cutover the shape-independent mirror has not tracked",
            l.width(),
            desc.name,
            desc.trace_width
        ));
    }
    if l.pi_count() != desc.public_input_count {
        return Err(format!(
            "step-marks witness-gen: layout PI count {} ≠ descriptor '{}' public_input_count {}",
            l.pi_count(),
            desc.name,
            desc.public_input_count
        ));
    }
    if old.cells.len() != l.s.kk {
        return Err(format!(
            "step-marks witness-gen: board has {} cells, expected KK = {}",
            old.cells.len(),
            l.s.kk
        ));
    }

    let mut vals: Vec<Option<BabyBear>> = vec![None; l.width()];

    // -- SEED the step columns `[0, A_WIDTH_N)` — the marks carry does not touch them (the automaton
    // step is marks-independent, so this is the plain step leaf's fill verbatim). --
    seed_step(&l.s, old, &mut vals)?;

    // -- SEED the marks window's free inputs: the accumulated `marksIn` indicator cells. --
    seed_marks(&l, marks, &mut vals);

    // -- Fixpoint: Rule L over ALL gates (step body + marks window). `rule_l_pass(desc, …)` reads the
    // WHOLE descriptor, so it solves the step logic columns AND the marks packed felts in one sweep. --
    loop {
        if !rule_l_pass(desc, &mut vals)? {
            break;
        }
    }

    // -- Every column must now be resolved; an unresolved column is a real gap. --
    let unresolved: Vec<usize> = (0..l.width()).filter(|c| vals[*c].is_none()).collect();
    if !unresolved.is_empty() {
        return Err(format!(
            "step-marks witness-gen: {} column(s) unresolved after the gate solver reached fixpoint \
             — a genuine witness-gen gap: {:?}",
            unresolved.len(),
            &unresolved[..unresolved.len().min(24)]
        ));
    }
    let row: Vec<BabyBear> = vals.into_iter().map(|v| v.unwrap()).collect();

    // -- Assemble the PIs off the ABI: the state-binding prefix (placeholder cell roots, as the plain
    // step path — the fold driver overwrites them with the leg's real rotated roots), then EVERY bound
    // PI read off its own column (pack(old), pack(new), ax/ay, nax/nay, pack(marksIn)). Unbound lanes
    // exist only in the free 16-felt door. --
    let binds = pi_binding_cols(desc);
    let (old8, new8) = placeholder_roots();
    let door: Vec<BabyBear> = old8.iter().chain(new8.iter()).copied().collect();
    let mut public_inputs = Vec::with_capacity(desc.public_input_count);
    for pi in 0..desc.public_input_count {
        match binds.get(&pi) {
            Some(&c) => public_inputs.push(row[c]),
            None => {
                let v = door.get(pi).copied().ok_or_else(|| {
                    format!(
                        "step-marks witness-gen: PI {pi} is neither column-bound nor part of the \
                         16-felt free door — the descriptor publishes a lane the ABI cannot fill"
                    )
                })?;
                public_inputs.push(v);
            }
        }
    }
    if public_inputs.len() != desc.public_input_count {
        return Err(format!(
            "step-marks witness-gen: assembled {} PIs, descriptor wants {}",
            public_inputs.len(),
            desc.public_input_count
        ));
    }

    Ok(StepMarksTrace {
        row,
        public_inputs,
        n,
    })
}

/// Seed the marks window's genuinely-free columns: the accumulated `marksIn` indicator (`1` on the
/// marked coordinates, `0` elsewhere). The packed felts are left to Rule L (solved from the pack
/// gates), and their PI bindings are read off the descriptor.
fn seed_marks(l: &StepMarksLayout, marks: &[Coord], vals: &mut [Option<BabyBear>]) {
    let n = l.s.n;
    for c in 0..l.s.kk {
        let (x, y) = ((c % n) as i32, (c / n) as i32);
        let marked = marks.iter().any(|&(mx, my)| mx == x && my == y);
        set_if_none(vals, l.s_marks_in_cell(c), bb(i64::from(marked)));
    }
}

/// **THE LOAD-BEARING VERIFICATION.** Does the generated trace SATISFY the decoded Lean step-marks
/// descriptor under the REAL `Ir2Air` row-local evaluator (`ir2_eval_accepts_i64`)? Runs over two
/// replicated rows so the `when_transition` gates fire. This is the gate a folded clean-round
/// automaton-step leaf must pass BEFORE it is proven; a wrong fill fails here exactly as the STARK would.
pub fn step_marks_trace_accepts(desc: &EffectVmDescriptor2, tr: &StepMarksTrace) -> bool {
    let rows_i64: Vec<Vec<i64>> = tr
        .base_trace(2)
        .iter()
        .map(|r| r.iter().map(|f| canon(*f)).collect())
        .collect();
    let pis_i64: Vec<i64> = tr.public_inputs.iter().map(|f| canon(*f)).collect();
    ir2_eval_accepts_i64(desc, &rows_i64, &pis_i64)
}

/// A debugging reporter: the index and a short render of the FIRST row-local constraint the trace
/// violates, or `None` if it satisfies every one.
pub fn step_marks_trace_first_failure(
    desc: &EffectVmDescriptor2,
    tr: &StepMarksTrace,
) -> Option<(usize, String)> {
    let get = |i: usize| -> Option<BabyBear> { tr.row.get(i).copied() };
    for (ci, c) in desc.constraints.iter().enumerate() {
        match c {
            VmConstraint2::Base(VmConstraint::Gate(expr)) => {
                if let Some(v) = eval_expr(expr, &get)
                    && v != BabyBear::ZERO
                {
                    return Some((ci, format!("Gate body = {} (≠ 0)", canon(v))));
                }
            }
            VmConstraint2::Base(VmConstraint::PiBinding {
                row: VmRow::First,
                col,
                pi_index,
            }) => {
                let lhs = tr.row.get(*col).copied().map(canon).unwrap_or(-1);
                let rhs = tr
                    .public_inputs
                    .get(*pi_index)
                    .copied()
                    .map(canon)
                    .unwrap_or(-1);
                if lhs != rhs {
                    return Some((
                        ci,
                        format!("PiBinding col {col} = {lhs} ≠ pi[{pi_index}] = {rhs}"),
                    ));
                }
            }
            _ => {}
        }
    }
    None
}

/// A local `LeanExpr` evaluator over the fully-filled row.
fn eval_expr(e: &LeanExpr, get: &dyn Fn(usize) -> Option<BabyBear>) -> Option<BabyBear> {
    match e {
        LeanExpr::Var(i) => get(*i),
        LeanExpr::Const(c) => Some(bb(*c)),
        LeanExpr::Add(a, b) => Some(eval_expr(a, get)? + eval_expr(b, get)?),
        LeanExpr::Mul(a, b) => Some(eval_expr(a, get)? * eval_expr(b, get)?),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::reference::{ATT, AUTO, VAC, automaton_step, stock_two_player};
    use dregg_circuit::descriptor_by_name::descriptor_by_name;

    fn desc11() -> EffectVmDescriptor2 {
        descriptor_by_name(step_marks_descriptor_ident(11))
            .expect("the n=11 automatafl-step-marks descriptor dispatches by name")
    }

    /// The FRONT gate: the n=11 marks layout mirror matches the emitted descriptor shape.
    #[test]
    fn n11_descriptor_shape() {
        let desc = desc11();
        assert_eq!(desc.trace_width, 810);
        assert_eq!(desc.public_input_count, 47);
        let l = StepMarksLayout::new(11);
        assert_eq!(l.width(), desc.trace_width);
        assert_eq!(l.pi_count(), desc.public_input_count);
    }

    /// (1) THE STEP SATISFIES + new = automatonStepCfg(old): the honest automaton step of the stock
    /// board carrying accumulated marks SATISFIES the descriptor, and the decoded `new` board equals
    /// the reference `automaton_step(old)` (the step is marks-independent).
    #[test]
    fn step_with_marks_satisfies_and_new_is_automaton_step() {
        let desc = desc11();
        let l = StepMarksLayout::new(11);
        let old = stock_two_player();
        let marks: Vec<Coord> = vec![(5, 5), (9, 9), (0, 10)];
        let tr = automatafl_step_marks_trace(&old, &marks, &desc)
            .unwrap_or_else(|e| panic!("witness-gen: {e}"));
        assert_eq!(tr.row.len(), desc.trace_width);
        if let Some((ci, why)) = step_marks_trace_first_failure(&desc, &tr) {
            panic!("row-local constraint {ci} violated on the honest marked step: {why}");
        }
        assert!(
            step_marks_trace_accepts(&desc, &tr),
            "an honest automaton step carrying accumulated marks must satisfy the descriptor"
        );
        assert_eq!(
            tr.new_cells(&l),
            automaton_step(&old).cells,
            "the decoded new board IS automaton_step(old) (the step is marks-independent)"
        );
    }

    /// (1b) A stepped chain (a moving automaton) all satisfies with marks carried — not just the
    /// opening position.
    #[test]
    fn stepped_chain_all_satisfy_with_marks() {
        let desc = desc11();
        let marks: Vec<Coord> = vec![(5, 5), (2, 7)];
        let mut board = pulled_n11();
        for turn in 0..4 {
            let tr = automatafl_step_marks_trace(&board, &marks, &desc)
                .unwrap_or_else(|e| panic!("turn {turn} witness-gen: {e}"));
            assert!(
                step_marks_trace_accepts(&desc, &tr),
                "turn {turn}: the stepped board's marks trace must satisfy the Lean descriptor"
            );
            board = automaton_step(&board);
        }
    }

    /// (2) ⚑ marksOut = marksIn (FROZEN): the step carries the marks UNCHANGED. Two different
    /// accumulated-marks inputs yield the SAME `new` board (marks never touch the step), and the OUT
    /// window's marks slice reads the SAME published PIs as the IN window's.
    #[test]
    fn marks_are_frozen_through_the_step() {
        let desc = desc11();
        let l = StepMarksLayout::new(11);
        let old = stock_two_player();
        let tr_a = automatafl_step_marks_trace(&old, &[(5, 5)], &desc).expect("fill a");
        let tr_b = automatafl_step_marks_trace(&old, &[(9, 9), (0, 0)], &desc).expect("fill b");
        assert_eq!(
            tr_a.new_cells(&l),
            tr_b.new_cells(&l),
            "the new board is invariant under the accumulated-marks input (marks-independent step)"
        );
        // The window reads the SAME PIs for IN.marks and OUT.marks (structural freeze).
        assert_eq!(
            l.pi_marks_out(),
            l.pi_marks_in(),
            "marksOut and marksIn are the SAME published window (frozen by construction)"
        );
    }

    /// (3) A FORGED `marksIn`-pack PI is refused: leaving the trace honest but publishing a WRONG
    /// `pack(marksIn)` PI fails the marks pack PI binding — the seam the RM→A handoff welds to cannot
    /// be lied about.
    #[test]
    fn forged_marks_in_pi_is_rejected() {
        let desc = desc11();
        let l = StepMarksLayout::new(11);
        let old = stock_two_player();
        let mut tr = automatafl_step_marks_trace(&old, &[(5, 5)], &desc).expect("clean fill");
        let pi = l.pi_marks_in(); // the first published marksIn felt.
        tr.public_inputs[pi] = tr.public_inputs[pi] + BabyBear::ONE;
        assert!(
            !step_marks_trace_accepts(&desc, &tr),
            "a forged pack(marksIn) PI must fail the marks pack PI binding"
        );
    }

    /// (3b) A tampered `marksIn` CELL (breaking its base-4 pack gate) is refused.
    #[test]
    fn tampered_marks_cell_is_rejected() {
        let desc = desc11();
        let l = StepMarksLayout::new(11);
        let old = stock_two_player();
        let mut tr = automatafl_step_marks_trace(&old, &[(5, 5)], &desc).expect("clean fill");
        let cell = l.s_marks_in_cell(0);
        tr.row[cell] = tr.row[cell] + BabyBear::ONE;
        assert!(
            !step_marks_trace_accepts(&desc, &tr),
            "a tampered marksIn indicator cell must fail its base-4 pack gate"
        );
    }

    /// (3c) A tampered NEW board cell (the step's own output) is refused too — the marks carry does
    /// not weaken the step's board-update gates.
    #[test]
    fn tampered_new_cell_is_rejected() {
        let desc = desc11();
        let old = stock_two_player();
        let mut tr = automatafl_step_marks_trace(&old, &[(5, 5)], &desc).expect("clean fill");
        let front = *pi_binding_cols(&desc)
            .get(&16)
            .expect("pack_old[0] is PI-bound");
        tr.row[front] += BabyBear::ONE;
        assert!(
            !step_marks_trace_accepts(&desc, &tr),
            "a corrupted packed-felt column must fail the descriptor's pack gate"
        );
    }

    /// **THE 20-LANE CLEAN-ROUND WINDOW.** `step_marks_board_window` declares
    /// `board(9) ‖ marks(9) ‖ auto(2)` with the `board ‖ marks` prefix (18) matching the conflict
    /// rounds' and resolve-marks leg's handoff lanes, and the extracted window reads the REAL packed
    /// board / marks / auto values off an honest step trace. This is the window the WholeChainProof
    /// assembler folds for Leg A — now 20-lane, so `RM(20) → A(20)` is uniform.
    #[test]
    fn step_marks_window_is_the_20_lane_board_marks_auto() {
        use dregg_circuit::effect_vm::custom_state_binding::{
            extract_custom_pi_board_window, roundstate_window_n11,
        };
        let desc = desc11();
        let l = StepMarksLayout::new(11);
        let win = step_marks_board_window(11, &desc).expect("the n=11 clean-round step window");
        assert_eq!(win.window_len(), 20, "board(9) ‖ marks(9) ‖ auto(2)");
        assert_eq!(
            roundstate_window_n11::HANDOFF_LANES,
            18,
            "the handoff prefix is board(9) ‖ marks(9)"
        );

        let old = stock_two_player();
        let marks: Vec<Coord> = vec![(5, 5), (9, 9)];
        let tr = automatafl_step_marks_trace(&old, &marks, &desc).expect("clean fill");
        let (win_in, win_out) =
            extract_custom_pi_board_window(&tr.public_inputs, &win).expect("window expressible");
        assert_eq!(win_in.len(), 20);
        assert_eq!(win_out.len(), 20);
        // The IN board(9) is pack(old); OUT board(9) is pack(new) — the step CHANGES the board.
        assert_eq!(
            &win_in[0..9],
            &tr.public_inputs[STEP_PACK_IN_PI..STEP_PACK_IN_PI + 9]
        );
        assert_eq!(
            &win_out[0..9],
            &tr.public_inputs[step_pack_out_pi(11)..step_pack_out_pi(11) + 9]
        );
        // marks(9) equal both sides (FROZEN through the step).
        assert_eq!(
            win_in[9..18],
            win_out[9..18],
            "marks are frozen through the automaton step"
        );
    }

    /// n=2 minimal instance: the same solver fills the byte-golden 261w/23pi step-marks descriptor.
    #[test]
    fn n2_minimal_steps() {
        let desc = descriptor_by_name(step_marks_descriptor_ident(2))
            .expect("the n=2 automatafl-step-marks descriptor dispatches by name");
        assert_eq!(desc.trace_width, 261);
        assert_eq!(desc.public_input_count, 23);
        let n = 2usize;
        let mut cells = vec![VAC; n * n];
        cells[0] = AUTO; // (0,0)
        cells[3] = ATT; // (1,1)
        let board = Board {
            n,
            cells,
            auto: (0, 0),
            col_rule: true,
        };
        // Empty marks: a clean round at the minimal instance still satisfies.
        let tr = automatafl_step_marks_trace(&board, &[], &desc)
            .unwrap_or_else(|e| panic!("n=2 witness-gen: {e}"));
        assert!(
            step_marks_trace_accepts(&desc, &tr),
            "the n=2 trace must satisfy the step-marks descriptor"
        );
    }

    /// An n=11 position whose automaton IS pulled (an attractor three cells north), so the guard fires
    /// and the automaton actually moves across the chain.
    fn pulled_n11() -> Board {
        let n = 11usize;
        let mut cells = vec![VAC; n * n];
        cells[5 * n + 5] = AUTO;
        cells[8 * n + 5] = ATT;
        Board {
            n,
            cells,
            auto: (5, 5),
            col_rule: true,
        }
    }
}
