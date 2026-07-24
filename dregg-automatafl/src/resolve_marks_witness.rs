//! # The witness generator for the Lean-emitted RESOLVE-MARKS descriptor — the CLEAN ROUND of a
//! multi-round turn (braid M6).
//!
//! **The trusted, fail-closed trace generator that fills the PROVEN Lean descriptor
//! `automataflResolveMarksDescN {n}` (`circuit/descriptors/by-name/automatafl-resolve-marks-n{n}.json`),
//! so the multi-round fold's CLEAN round proves through the object REFINED in Lean
//! (`AutomataflResolveMarksCapstone`: `cMidV4` IS `AutomataflRules.roundStep`'s clean-round resolve
//! board at ACCUMULATED marks — `resolve_sat_imp_roundBoardMarksN` — and the moves are `MoveLegal`
//! against those marks — `resolveMarksMoveLegal`, a DESCRIPTOR THEOREM, not assumed).** House law #1:
//! the AIR is authored in Lean; this Rust only fills a trace and CALLS the general IR-v2 evaluator.
//! It authors NO constraints.
//!
//! ## The method — the resolve witness-gen, plus a marks tail
//!
//! The marks-carrying resolve descriptor is `automataflResolveDescN n`'s constraints VERBATIM plus a
//! MARKS TAIL at fresh columns above `R_WIDTH n` (`AutomataflResolveMarksCapstone` §1–§2):
//!
//!   * the accumulated `marksIn` COMMITMENT — the `n²` `{0,1}` indicator cells, the `⌈n²/15⌉` base-4
//!     packed felts, and their PI bindings (`marksCommitFamilyAt`);
//!   * the two moves' DESTINATION one-hots (`rTSelRow`/`rTSelCol`, pinned at `(tx, ty)`);
//!   * the two marks-legality NOR pins — `inMarksFrm[w]` / `inMarksTo[w]` are `marksIn` read at the
//!     move's two endpoints through the resolve descriptor's SOURCE one-hots and this tail's DEST
//!     one-hots, and `legal[w] = ¬inMarksFrm ∧ ¬inMarksTo` is PINNED to `1`: a submission naming a
//!     marked square makes the leaf UNSAT (exactly `roundStep`'s fresh filter refusing it).
//!
//! Because `resolveMoves` is MARKS-INDEPENDENT (the capstone's KEY OBSERVATION), the resolve columns
//! `[0, R_WIDTH)` fill EXACTLY as they do for the plain resolve leaf — so this reuses
//! [`crate::resolve_witness`]'s `seed` / `fire_fillers` / `rule_l_pass` on those columns verbatim, and
//! adds only the tail's free inputs (the `marksIn` indicator + the dest one-hots). The read/NOR/pin
//! columns are then solved by the SAME Rule-L gate propagation over the descriptor's OWN gates. The
//! load-bearing check is [`resolve_marks_trace_accepts`]: the REAL `Ir2Air` row-local evaluator over
//! two rows must accept before any leaf is proven; a wrong fill (or a marks-illegal move) fails a
//! gate exactly as it would fail the STARK.

use dregg_circuit::descriptor_ir2::{EffectVmDescriptor2, VmConstraint2, ir2_eval_accepts_i64};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};

use crate::reference::{Board, Coord, Move};
use crate::resolve_layout::AUTO_CODE;
use crate::resolve_marks_layout::{ResolveMarksLayout, resolve_marks_descriptor_name};
use crate::resolve_witness::{
    bb, canon, fill_one_hot, fire_fillers, rule_l_pass, seed, set_if_none,
};

/// The by-name loader identity of the Lean resolve-marks descriptor for board size `n`.
pub fn resolve_marks_descriptor_ident(n: usize) -> &'static str {
    resolve_marks_descriptor_name(n)
}

/// **LEG RM's BOARD-STATE WINDOW** — the marks-carrying clean-round window the multi-round braid's
/// `C_last → R` handoff connects. `IN = pack(old) ‖ pack(marksIn) ‖ (ax, ay)`,
/// `OUT = pack(cMidV4) ‖ pack(marksIn) ‖ (ax, ay)` — 20 lanes at `n = 11`
/// (`board(9) ‖ marks(9) ‖ auto(2)`).
///
/// Its leading `board(9) ‖ marks(9)` prefix (18 lanes) is EXACTLY
/// [`roundstate_window_n11::HANDOFF_LANES`](dregg_circuit::effect_vm::custom_state_binding::roundstate_window_n11),
/// laid out in the SAME `board`-then-`marks` order as the conflict rounds' 32-lane RoundState
/// window, so the deployed clean-handoff connect (`board_window_clean_handoff_connects`) welds
/// `C_last.OUT[board ‖ marks] == R.IN[board ‖ marks]`. `marks` is FROZEN through the resolution
/// (the marks carry gates legality, never the resolution board — see the module doc), so IN and OUT
/// both point at the single published `pack(marksIn)` PI window; `auto` likewise (resolution never
/// moves the automaton).
///
/// `Err` (fail-closed) if the loaded descriptor's PI count is not the resolve-marks layout for `n`,
/// or the window is not expressible in it — a size the marks descriptor is not emitted for is
/// BLOCKED, not faked.
pub fn resolve_marks_board_window(
    n: usize,
    desc: &EffectVmDescriptor2,
) -> Result<dregg_circuit::effect_vm::custom_state_binding::BoardWindowBinding, String> {
    use dregg_circuit::effect_vm::custom_state_binding::BoardWindowBinding;
    let l = ResolveMarksLayout::new(n);
    if l.pi_count() != desc.public_input_count {
        return Err(format!(
            "resolve-marks board window: layout PI count {} ≠ descriptor '{}' public_input_count {}",
            l.pi_count(),
            desc.name,
            desc.public_input_count
        ));
    }
    let rfc = l.r.rfc;
    let b = BoardWindowBinding {
        // board(pack_old) ‖ marks(pack_marksIn) ‖ auto.
        in_slices: vec![
            (l.r.pack_in_pi_base(), rfc),
            (l.pi_marks_in(), rfc),
            (l.r.auto_pi_base(), 2),
        ],
        // board(pack_cMidV4) ‖ marks(pack_marksIn, frozen) ‖ auto (unmoved).
        out_slices: vec![
            (l.r.pack_out_pi_base(), rfc),
            (l.pi_marks_in(), rfc),
            (l.r.auto_pi_base(), 2),
        ],
    };
    if !b.is_well_formed() || desc.public_input_count < b.pi_end() {
        return Err(format!(
            "resolve-marks board window {b:?} is not expressible in descriptor '{}' ({} PIs)",
            desc.name, desc.public_input_count
        ));
    }
    Ok(b)
}

/// The generated single-row trace + public inputs for the Lean resolve-marks descriptor.
#[derive(Clone, Debug)]
pub struct ResolveMarksTrace {
    /// One trace row of width `descriptor.trace_width` (the gates are row-local).
    pub row: Vec<BabyBear>,
    /// The descriptor public inputs
    /// (`door16 ‖ pack(old) ‖ pack(cMidV4) ‖ ax,ay ‖ pack(marksIn)`).
    pub public_inputs: Vec<BabyBear>,
    /// The board size.
    pub n: usize,
}

impl ResolveMarksTrace {
    /// The base trace for the evaluator: the row replicated `num_rows` times. Use `≥ 2` rows to
    /// exercise the `when_transition` gates.
    pub fn base_trace(&self, num_rows: usize) -> Vec<Vec<BabyBear>> {
        vec![self.row.clone(); num_rows.max(2)]
    }

    /// The decoded FINAL corrected mid board (`cMidV4`) read back out of the filled trace — the
    /// roundStep clean-round resolve board this leaf commits to. Marks-independent (the resolve
    /// columns are untouched by the marks carry), so this equals the plain resolve leaf's `cMidV4`.
    pub fn mid_board(&self, l: &ResolveMarksLayout) -> Board {
        let cells: Vec<u8> = (0..l.r.kk)
            .map(|c| canon(self.row[l.r.c_mid_v4(c)]) as u8)
            .collect();
        let auto = find_auto(&cells, self.n);
        Board {
            n: self.n,
            cells,
            auto,
            col_rule: true,
        }
    }
}

/// The scan of a board for the `AUTO` cell → its `(x, y)` (resolution never moves the automaton).
fn find_auto(cells: &[u8], n: usize) -> Coord {
    for (c, &v) in cells.iter().enumerate() {
        if i64::from(v) == AUTO_CODE {
            return ((c % n) as i32, (c / n) as i32);
        }
    }
    (0, 0)
}

// --------------------------------------------------------------------------------------------
// THE WITNESS GENERATOR.
// --------------------------------------------------------------------------------------------

/// **Fill the Lean resolve-marks descriptor's trace** for the honest clean-round resolution
/// `old → cMidV4` adjudicating the two moves `ms` against the accumulated `marksIn` indicator
/// `marks`, then assemble the public inputs.
///
/// `desc` is the decoded Lean descriptor for `old.n` (via
/// `dregg_circuit::descriptor_by_name(resolve_marks_descriptor_ident(old.n))`). The generator is
/// checked against it: on any layout disagreement (`trace_width` / `public_input_count`) it returns
/// `Err` (fail-closed). Every column is filled by SOLVING the descriptor's own gates; an unresolved
/// column is a named `Err`, never a silent mis-fill. A geometrically-valid move onto a `marks` square
/// fills fully but is rejected by [`resolve_marks_trace_accepts`] (the legality NOR pin bites) — the
/// M6 fail-closed property.
pub fn automatafl_resolve_marks_trace(
    old: &Board,
    ms: &[Move; 2],
    marks: &[Coord],
    desc: &EffectVmDescriptor2,
) -> Result<ResolveMarksTrace, String> {
    let n = old.n;
    let l = ResolveMarksLayout::new(n);

    // Fail-closed layout guards: the descriptor must be the resolve-marks layout for this `n`.
    if l.width() != desc.trace_width {
        return Err(format!(
            "resolve-marks witness-gen: layout width {} ≠ descriptor '{}' trace_width {} — a \
             descriptor cutover the shape-independent mirror has not tracked",
            l.width(),
            desc.name,
            desc.trace_width
        ));
    }
    if l.pi_count() != desc.public_input_count {
        return Err(format!(
            "resolve-marks witness-gen: layout PI count {} ≠ descriptor '{}' public_input_count {}",
            l.pi_count(),
            desc.name,
            desc.public_input_count
        ));
    }
    if old.cells.len() != l.r.kk {
        return Err(format!(
            "resolve-marks witness-gen: board has {} cells, expected KK = {}",
            old.cells.len(),
            l.r.kk
        ));
    }

    let mut vals: Vec<Option<BabyBear>> = vec![None; l.width()];

    // -- SEED the resolve free inputs (columns `[0, R_WIDTH)`) — the marks carry does not touch them. --
    seed(&l.r, old, ms, &mut vals)?;

    // -- SEED the marks tail's free inputs: the accumulated `marksIn` indicator + the dest one-hots. --
    seed_marks(&l, ms, marks, &mut vals)?;

    // -- Fixpoint: resolve gadget fillers, then Rule L over ALL gates (resolve body + marks tail).
    // `rule_l_pass(desc, …)` reads the WHOLE descriptor, so it solves the resolve logic columns AND
    // the marks felts / endpoint reads / NOR pins in one interleaved sweep. --
    loop {
        let mut progress = false;
        progress |= fire_fillers(&l.r, ms, &mut vals)?;
        progress |= rule_l_pass(desc, &mut vals)?;
        if !progress {
            break;
        }
    }

    // -- Every column must now be resolved; an unresolved column is a real gap. --
    let unresolved: Vec<usize> = (0..l.width()).filter(|c| vals[*c].is_none()).collect();
    if !unresolved.is_empty() {
        return Err(format!(
            "resolve-marks witness-gen: {} column(s) unresolved after the gate solver reached \
             fixpoint — a genuine witness-gen gap: {:?}",
            unresolved.len(),
            &unresolved[..unresolved.len().min(24)]
        ));
    }
    let row: Vec<BabyBear> = vals.into_iter().map(|v| v.unwrap()).collect();

    // -- Assemble the PIs off the ABI:
    //    door16 (free) ‖ pack(old) ‖ pack(cMidV4) ‖ ax, ay ‖ pack(marksIn). --
    let (old8, new8) = crate::witness::placeholder_roots();
    let mut public_inputs = Vec::with_capacity(desc.public_input_count);
    public_inputs.extend_from_slice(&old8);
    public_inputs.extend_from_slice(&new8);
    for j in 0..l.r.rfc {
        public_inputs.push(row[l.r.pack_old_felt(j)]);
    }
    for j in 0..l.r.rfc {
        public_inputs.push(row[l.r.pack_mid_felt(j)]);
    }
    public_inputs.push(row[l.r.ax_c()]);
    public_inputs.push(row[l.r.ay_c()]);
    for j in 0..l.r.rfc {
        public_inputs.push(row[l.r_marks_in_felt(j)]);
    }
    if public_inputs.len() != desc.public_input_count {
        return Err(format!(
            "resolve-marks witness-gen: assembled {} PIs, descriptor wants {}",
            public_inputs.len(),
            desc.public_input_count
        ));
    }

    Ok(ResolveMarksTrace {
        row,
        public_inputs,
        n,
    })
}

/// Seed the marks tail's genuinely-free columns: the accumulated `marksIn` indicator (`1` on the
/// marked coordinates), and the two moves' destination one-hots (the SOURCE one-hots come free from
/// the resolve `seed`). The read / NOR / pin columns are left to Rule L.
fn seed_marks(
    l: &ResolveMarksLayout,
    ms: &[Move; 2],
    marks: &[Coord],
    vals: &mut [Option<BabyBear>],
) -> Result<(), String> {
    let n = l.r.n;
    // `marksIn` indicator cells: `1` exactly on the (in-bounds) marked coordinates, `0` elsewhere.
    for c in 0..l.r.kk {
        let (x, y) = ((c % n) as i32, (c / n) as i32);
        let marked = marks.iter().any(|&(mx, my)| mx == x && my == y);
        set_if_none(vals, l.r_marks_in_cell(c), bb(i64::from(marked)));
    }
    // The destination one-hots @ `(ty, tx)` of each move (`rDestOneHot`, pinned at `cTy`/`cTx`).
    for w in 0..2 {
        let (tx, ty) = (i64::from(ms[w].to.0), i64::from(ms[w].to.1));
        fill_one_hot(vals, n, |j| l.r_tsel_row(w, j), ty)?;
        fill_one_hot(vals, n, |j| l.r_tsel_col(w, j), tx)?;
    }
    Ok(())
}

/// **THE LOAD-BEARING VERIFICATION.** Does the generated trace SATISFY the decoded Lean resolve-marks
/// descriptor under the REAL `Ir2Air` row-local evaluator (`ir2_eval_accepts_i64`)? Runs over two
/// replicated rows so the `when_transition` gates fire. This is the gate a folded clean-round leaf
/// must pass BEFORE it is proven; a wrong fill — or a marks-illegal move — fails here exactly as the
/// STARK would.
pub fn resolve_marks_trace_accepts(desc: &EffectVmDescriptor2, tr: &ResolveMarksTrace) -> bool {
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
pub fn resolve_marks_trace_first_failure(
    desc: &EffectVmDescriptor2,
    tr: &ResolveMarksTrace,
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

/// A local `LeanExpr` evaluator over the fully-filled row (mirrors `resolve_witness`'s private one).
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
    use crate::reference::{Move, resolve_mid, stock_two_player};
    use dregg_circuit::descriptor_by_name::descriptor_by_name;

    fn desc11() -> EffectVmDescriptor2 {
        descriptor_by_name(resolve_marks_descriptor_ident(11))
            .expect("the n=11 automatafl-resolve-marks descriptor dispatches by name")
    }

    fn mv(frm: Coord, to: Coord) -> Move {
        Move { who: 0, frm, to }
    }

    /// The FRONT gate: the n=11 marks layout mirror matches the emitted descriptor shape.
    #[test]
    fn n11_descriptor_shape() {
        let desc = desc11();
        assert_eq!(desc.trace_width, 1453);
        assert_eq!(desc.public_input_count, 45);
        let l = ResolveMarksLayout::new(11);
        assert_eq!(l.width(), desc.trace_width);
        assert_eq!(l.pi_count(), desc.public_input_count);
    }

    /// (1) A CLEAN round with ACCUMULATED marks that avoid both moves' endpoints ⇒ SATISFIES. Two
    /// independent clean moves, marks at squares neither move touches; every `legal[w] = 1` holds and
    /// the descriptor accepts — the marks-legal clean round mints.
    #[test]
    fn clean_round_with_marks_satisfies() {
        let desc = desc11();
        let l = ResolveMarksLayout::new(11);
        let old = stock_two_player();
        let ms = [mv((3, 1), (3, 3)), mv((7, 1), (7, 3))];
        // Accumulated marks well away from either move's source/destination.
        let marks: Vec<Coord> = vec![(5, 5), (9, 9), (0, 10)];
        let tr = automatafl_resolve_marks_trace(&old, &ms, &marks, &desc)
            .unwrap_or_else(|e| panic!("witness-gen: {e}"));
        assert_eq!(tr.row.len(), desc.trace_width);
        if let Some((ci, why)) = resolve_marks_trace_first_failure(&desc, &tr) {
            panic!("row-local constraint {ci} violated on the honest clean-marked round: {why}");
        }
        assert!(
            resolve_marks_trace_accepts(&desc, &tr),
            "a CLEAN round whose moves avoid the accumulated marks must satisfy the descriptor"
        );
        // Both legality bits are pinned to 1 (nothing marked at an endpoint).
        assert_eq!(canon(tr.row[l.r_legal(0)]), 1);
        assert_eq!(canon(tr.row[l.r_legal(1)]), 1);
    }

    /// (2) ⚑ THE LOAD-BEARING NEGATIVE (the M6 re-check, only reachable once this leaf mints): a CLEAN
    /// round whose move lands on a MARKED square is UNSAT. The move is geometrically valid (the
    /// resolve columns fill), but `marksIn[to] = 1` forces the `legal` NOR/pin into conflict, so the
    /// REAL evaluator rejects — exactly `roundStep`'s fresh filter refusing a move onto a mark.
    #[test]
    fn clean_round_marked_move_is_unsat() {
        let desc = desc11();
        let old = stock_two_player();
        let ms = [mv((3, 1), (3, 3)), mv((7, 1), (7, 3))];
        // Mark move 0's DESTINATION — a marks-illegal submission.
        let marks: Vec<Coord> = vec![(3, 3)];
        let tr = automatafl_resolve_marks_trace(&old, &ms, &marks, &desc).expect(
            "the trace still FILLS (geometry is valid); it is the legality gate that bites",
        );
        assert!(
            !resolve_marks_trace_accepts(&desc, &tr),
            "a clean-round move onto a MARKED square must be REJECTED by the legality NOR pin"
        );
        // And the failure is exactly the legality tail (not a resolve gate).
        let (_ci, why) = resolve_marks_trace_first_failure(&desc, &tr)
            .expect("a marked move must violate some row-local constraint");
        assert!(
            why.contains("Gate body"),
            "the violation is the marks-legality NOR/pin gate: {why}"
        );
    }

    /// (2b) A marked SOURCE square is equally refused (the other half of `moveLegalB`'s marks conjunct).
    #[test]
    fn clean_round_marked_source_is_unsat() {
        let desc = desc11();
        let old = stock_two_player();
        let ms = [mv((3, 1), (3, 3)), mv((7, 1), (7, 3))];
        let marks: Vec<Coord> = vec![(3, 1)]; // move 0's SOURCE.
        let tr = automatafl_resolve_marks_trace(&old, &ms, &marks, &desc).unwrap();
        assert!(
            !resolve_marks_trace_accepts(&desc, &tr),
            "a clean-round move OUT OF a marked square must be REJECTED too"
        );
    }

    /// (3) `cMidV4 == resolveMoves`: the marks carry is board-inert. The resolve-marks trace's decoded
    /// `cMidV4` equals the naive `resolve_mid` oracle for a clean move pair — the same board the plain
    /// resolve leaf commits (marks gate LEGALITY at proposal, never the resolution function).
    #[test]
    fn mid_board_is_marks_independent() {
        let desc = desc11();
        let l = ResolveMarksLayout::new(11);
        let old = stock_two_player();
        let ms = [mv((3, 1), (3, 3)), mv((7, 1), (7, 3))];
        let marks: Vec<Coord> = vec![(5, 5)];
        let tr = automatafl_resolve_marks_trace(&old, &ms, &marks, &desc).unwrap();
        let expect = resolve_mid(&old, &ms);
        assert_eq!(
            tr.mid_board(&l).cells,
            expect.cells,
            "cMidV4 must equal resolveMoves (the marks carry never touches the resolution board)"
        );
        // Re-filling with DIFFERENT (still legal) marks yields the SAME cMidV4.
        let marks2: Vec<Coord> = vec![(9, 9), (0, 0)];
        let tr2 = automatafl_resolve_marks_trace(&old, &ms, &marks2, &desc).unwrap();
        assert_eq!(
            tr.mid_board(&l).cells,
            tr2.mid_board(&l).cells,
            "cMidV4 is invariant under the accumulated-marks input"
        );
    }

    /// (4) A FORGED `marksIn`-pack PI is refused: leaving the trace honest but publishing a WRONG
    /// `pack(marksIn)` PI fails the marks pack PI binding — the seam the C→R handoff welds to cannot
    /// be lied about.
    #[test]
    fn forged_marks_in_pi_is_rejected() {
        let desc = desc11();
        let l = ResolveMarksLayout::new(11);
        let old = stock_two_player();
        let ms = [mv((3, 1), (3, 3)), mv((7, 1), (7, 3))];
        let marks: Vec<Coord> = vec![(5, 5)];
        let mut tr = automatafl_resolve_marks_trace(&old, &ms, &marks, &desc).unwrap();
        let pi = l.pi_marks_in(); // the first published marksIn felt.
        tr.public_inputs[pi] = tr.public_inputs[pi] + BabyBear::ONE;
        assert!(
            !resolve_marks_trace_accepts(&desc, &tr),
            "a forged pack(marksIn) PI must fail the marks pack PI binding"
        );
    }

    /// (4b) A tampered `marksIn` CELL (breaking its pack gate AND its published window) is refused.
    #[test]
    fn tampered_marks_cell_is_rejected() {
        let desc = desc11();
        let l = ResolveMarksLayout::new(11);
        let old = stock_two_player();
        let ms = [mv((3, 1), (3, 3)), mv((7, 1), (7, 3))];
        let marks: Vec<Coord> = vec![(5, 5)];
        let mut tr = automatafl_resolve_marks_trace(&old, &ms, &marks, &desc).unwrap();
        // Flip an unmarked cell to 1: the pack gate over that felt no longer vanishes.
        let cell = l.r_marks_in_cell(0);
        tr.row[cell] = tr.row[cell] + BabyBear::ONE;
        assert!(
            !resolve_marks_trace_accepts(&desc, &tr),
            "a tampered marksIn indicator cell must fail its base-4 pack gate"
        );
    }

    /// **THE 20-LANE CLEAN-ROUND WINDOW.** `resolve_marks_board_window` declares
    /// `board(9) ‖ marks(9) ‖ auto(2)` with the `board ‖ marks` prefix (18) matching the conflict
    /// rounds' RoundState handoff lanes, and the extracted window reads the REAL packed board / marks
    /// / auto values off an honest clean-round trace.
    #[test]
    fn resolve_marks_window_is_the_20_lane_board_marks_auto() {
        use dregg_circuit::effect_vm::custom_state_binding::{
            extract_custom_pi_board_window, roundstate_window_n11,
        };
        let desc = desc11();
        let l = ResolveMarksLayout::new(11);
        let win = resolve_marks_board_window(11, &desc).expect("the n=11 clean-round window");
        assert_eq!(win.window_len(), 20, "board(9) ‖ marks(9) ‖ auto(2)");
        assert_eq!(
            roundstate_window_n11::HANDOFF_LANES,
            18,
            "the handoff prefix is board(9) ‖ marks(9)"
        );

        let old = stock_two_player();
        let ms = [mv((3, 1), (3, 3)), mv((7, 1), (7, 3))];
        let marks: Vec<Coord> = vec![(5, 5), (9, 9)];
        let tr = automatafl_resolve_marks_trace(&old, &ms, &marks, &desc).expect("clean fill");
        let (win_in, win_out) =
            extract_custom_pi_board_window(&tr.public_inputs, &win).expect("window expressible");
        assert_eq!(win_in.len(), 20);
        assert_eq!(win_out.len(), 20);
        // The IN board(9) is pack(old); OUT board(9) is pack(cMidV4); marks(9) equal both sides
        // (frozen); auto(2) equal both sides (unmoved).
        assert_eq!(
            &win_in[0..9],
            &tr.public_inputs[l.r.pack_in_pi_base()..l.r.pack_in_pi_base() + 9]
        );
        assert_eq!(
            &win_out[0..9],
            &tr.public_inputs[l.r.pack_out_pi_base()..l.r.pack_out_pi_base() + 9]
        );
        assert_eq!(
            win_in[9..18],
            win_out[9..18],
            "marks are frozen through resolve"
        );
        assert_eq!(
            win_in[18..20],
            win_out[18..20],
            "auto is unmoved by resolve"
        );
    }

    /// n=2 minimal instance: the same solver fills the byte-golden 460w/21pi resolve-marks descriptor.
    #[test]
    fn n2_minimal_resolves() {
        let desc = descriptor_by_name(resolve_marks_descriptor_ident(2))
            .expect("the n=2 automatafl-resolve-marks descriptor dispatches by name");
        assert_eq!(desc.trace_width, 460);
        assert_eq!(desc.public_input_count, 21);
        let mut cells = vec![0u8; 4];
        cells[0] = 3; // AUTO @ (0,0)
        cells[3] = 1; // REP @ (1,1)
        let board = Board {
            n: 2,
            cells,
            auto: (0, 0),
            col_rule: true,
        };
        let ms = [mv((1, 1), (1, 0)), mv((1, 1), (0, 1))];
        // Empty marks: a clean round at the minimal instance.
        let tr = automatafl_resolve_marks_trace(&board, &ms, &[], &desc)
            .unwrap_or_else(|e| panic!("n=2 witness-gen: {e}"));
        assert!(
            resolve_marks_trace_accepts(&desc, &tr),
            "the n=2 trace must satisfy the resolve-marks descriptor"
        );
    }
}
