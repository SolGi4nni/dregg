//! # The witness generator for the Lean-emitted **Leg C** (conflict-round, `.again`) descriptor.
//!
//! **The trusted, fail-closed trace generator that fills the PROVEN Lean descriptor
//! `automataflLegCDescN {n}` (`circuit/descriptors/by-name/automatafl-legc-n{n}.json`), so a folded
//! conflict-round leaf proves through the object AUTHORED and (M2) REFINED in Lean
//! (`legC_sat_imp_roundAgainN`: the OUT window IS `AutomataflRules.roundStep`'s `.again` RoundState,
//! up to `List.Perm` on `marks`), not a hand-authored Rust AIR.** House law #1: the AIR is authored
//! in Lean; this Rust only fills a trace and CALLS the general IR-v2 evaluator. It authors NO
//! constraints.
//!
//! ## Leg C = Leg R's FRONT HALF + a state-transition TAIL, solved the same way
//!
//! Leg C is `roundStep`'s `.again` branch: a round that hits a fork/collide marks the conflicted
//! coordinate, freezes the board, drops every move touching the clash, and re-enters. Its front half
//! (`[0, CAR0)`) is Leg R's own families spliced in at Leg R's own columns (the `onePin`,
//! `autoRead`, `validateMove` ×2, `srcNonVac`, `patternBit`, `selection` gates), so the SAME
//! seed-then-solve method [`crate::resolve_witness`] uses fills it verbatim: SEED the non-affine
//! gadget columns (coordinate decompositions, the auto/source/dest one-hots, the `forced_ge0` range
//! blocks), then run [`crate::resolve_witness::rule_l_pass`] (the shared Rule-L gate propagation) to
//! fixpoint over the descriptor's OWN gates.
//!
//! What the tail adds — the frozen OUT board, the `cs` clash delta, `marksOut = marksIn ∨ cs`, the
//! per-move marks-legality / drop tests, and the seat-indexed `lockedOut`/`waitingOut` — is EVERY
//! one a degree-≤3 gate that is affine in its own defining column once the front-half verdict
//! (`cFork`/`cCollide`) and the seeds land, so Rule L computes each by evaluating the gate that
//! DEFINES it. Nothing here re-derives `roundStep`; the descriptor's gates do, and this generator
//! solves them. A column no gate determines is a hard `Err` (fail-closed), never a zero guess —
//! except the 250 documented DEAD lanes (`[NGen.occBase n 0, NGen.RES0 n)`, the two dropped
//! occlusion blocks Leg C keeps allocated but never constrains), which are filled with `0`.
//!
//! ## `cSurv` is PINNED to 0 (a clean round is UNSAT)
//!
//! The clash pin gates `cSurv = 0`; with `surv_iff_clash_empty_of_sat` that makes a clean round
//! (`cSurv = 1`) structurally UNSATISFIABLE as a Leg C — the prover cannot pad a turn with spurious
//! identity re-entry rounds. The generator does not special-case this: on a clean round the front
//! half's `selection` block forces `cSurv = 1`, [`legc_trace_accepts`] then fails the clash pin, and
//! the canary observes the reject exactly as the STARK would.
//!
//! The load-bearing check is [`legc_trace_accepts`]: the REAL `Ir2Air` row-local evaluator
//! (`ir2_eval_accepts_i64`) over TWO rows — a single replicated row exercises only the first/last-row
//! PI bindings, never the `when_transition` gates — must accept before any leaf is proven.

use std::collections::BTreeMap;

use dregg_circuit::descriptor_ir2::{EffectVmDescriptor2, VmConstraint2, ir2_eval_accepts_i64};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};

use crate::board::{Board, Coord, Move};
use crate::legc_layout::{LEGC_SEATS, LegCLayout, legc_descriptor_name};
use crate::resolve_layout::{AUTO_CODE, RBITS, SMALL_RBITS};
use crate::resolve_witness::rule_l_pass;

/// The by-name loader identity of the Lean Leg C descriptor for board size `n`.
pub fn legc_descriptor_ident(n: usize) -> String {
    legc_descriptor_name(n)
}

/// **The IN RoundState** the round is entered with: the turn-start board and the marks accumulated
/// so far. At `P = 2` (`LEGC_SEATS`) the IN `locked` is empty and `waiting = [0, 1]` — both PINNED
/// by the descriptor — so they are not carried here; the round is `(board, marks)` plus the fresh
/// submissions passed alongside.
#[derive(Clone, Debug)]
pub struct RoundStateIn {
    /// The turn-start board (never mutated across a clash braid).
    pub board: Board,
    /// The marks the round is entered with (`marksIn`), as a coordinate list (order-free).
    pub marks: Vec<Coord>,
}

/// The generated single-row trace + public inputs for the Lean Leg C descriptor at a resolution.
#[derive(Clone, Debug)]
pub struct LegCTrace {
    /// One trace row of width `descriptor.trace_width` (the gates are row-local).
    pub row: Vec<BabyBear>,
    /// The descriptor public inputs (the RoundState window at BOTH ends; see the module doc).
    pub public_inputs: Vec<BabyBear>,
    /// The board size.
    pub n: usize,
}

impl LegCTrace {
    /// The base trace for the evaluator: the row replicated `num_rows` times. Use `≥ 2` rows so the
    /// `when_transition` gates fire (a single row only fires the first/last-row PI bindings).
    pub fn base_trace(&self, num_rows: usize) -> Vec<Vec<BabyBear>> {
        vec![self.row.clone(); num_rows.max(2)]
    }
}

// --------------------------------------------------------------------------------------------
// Small field helpers (local mirrors of the resolve-witness helpers).
// --------------------------------------------------------------------------------------------

fn canon(b: BabyBear) -> i64 {
    b.0 as i64
}

fn bb(x: i64) -> BabyBear {
    if x >= 0 {
        BabyBear::from_u64(x as u64)
    } else {
        -BabyBear::from_u64((-x) as u64)
    }
}

fn set_if_none(vals: &mut [Option<BabyBear>], col: usize, v: BabyBear) -> bool {
    if vals[col].is_none() {
        vals[col] = Some(v);
        true
    } else {
        false
    }
}

/// A `forced_ge0` block over the head `source − 1`: the boolean `ib = [source ≥ 1]` at `ib_col`, and
/// `rbits` recomposition bits of `term = 2·ib·d + ib − d − 1` (`d = source − 1`). Fires once `source`
/// is resolved; a term outside `[0, 2^rbits)` is a fail-closed UNSAT.
fn fill_forced_ge0(
    vals: &mut [Option<BabyBear>],
    source_col: usize,
    ib_col: usize,
    bit0: impl Fn(usize) -> usize,
    rbits: usize,
) -> Result<bool, String> {
    let Some(sv) = vals[source_col] else {
        return Ok(false);
    };
    let x = canon(sv);
    let d = x - 1;
    let ib = i64::from(d >= 0);
    let term = 2 * ib * d + ib - d - 1;
    if term < 0 || term >= (1i64 << rbits) {
        return Err(format!(
            "legc witness-gen: forced_ge0 range term {term} ∉ [0, 2^{rbits}) for source col \
             {source_col} (value {x}): an out-of-range / invalid input (fail-closed)"
        ));
    }
    let mut prog = set_if_none(vals, ib_col, bb(ib));
    for k in 0..rbits {
        prog |= set_if_none(vals, bit0(k), bb((term >> k) & 1));
    }
    Ok(prog)
}

/// Set a one-hot selector vector to the indicator of `idx` (`sel[j] = [j == idx]`). Fails closed on
/// an out-of-board index.
fn fill_one_hot(
    vals: &mut [Option<BabyBear>],
    n: usize,
    sel: impl Fn(usize) -> usize,
    idx: i64,
) -> Result<bool, String> {
    if idx < 0 || idx >= n as i64 {
        return Err(format!(
            "legc witness-gen: one-hot index {idx} out of board [0, {n}) (fail-closed)"
        ));
    }
    let mut prog = false;
    for j in 0..n {
        prog |= set_if_none(
            vals,
            sel(j),
            if j as i64 == idx {
                BabyBear::ONE
            } else {
                BabyBear::ZERO
            },
        );
    }
    Ok(prog)
}

/// Place both edges of a coordinate's range decomposition: `lo = binary(coord)` and
/// `hi = binary((n−1) − coord)`.
fn seed_decompose(
    vals: &mut [Option<BabyBear>],
    cr: usize,
    coord: i64,
    n: usize,
    lo: impl Fn(usize) -> usize,
    hi: impl Fn(usize) -> usize,
) {
    let up = (n as i64 - 1) - coord;
    for k in 0..cr {
        set_if_none(vals, lo(k), bb((coord >> k) & 1));
        set_if_none(vals, hi(k), bb((up >> k) & 1));
    }
}

/// The scan of the board cells for the `AUTO` particle → its `(x, y)` (matches `autoPinHead`, which
/// reads the old cells).
fn find_auto(cells: &[u8], n: usize) -> (i64, i64) {
    for (c, &v) in cells.iter().enumerate() {
        if v as i64 == AUTO_CODE {
            return ((c % n) as i64, (c / n) as i64);
        }
    }
    (0, 0)
}

/// Render a sorted column list as contiguous `[lo..hi)` ranges (so an unresolved set reads as the
/// FAMILIES it belongs to).
fn contiguous_ranges(cols: &[usize]) -> String {
    let mut out: Vec<String> = Vec::new();
    let mut i = 0;
    while i < cols.len() {
        let lo = cols[i];
        let mut hi = lo;
        while i + 1 < cols.len() && cols[i + 1] == hi + 1 {
            i += 1;
            hi = cols[i];
        }
        out.push(if lo == hi {
            format!("[{lo}]")
        } else {
            format!("[{lo}..{})", hi + 1)
        });
        i += 1;
    }
    out.join(" ")
}

/// The descriptor's own first-row `PiBinding` map (`pi_index -> trace column`) — the ABI read that
/// keeps PI assembly shape-independent under append-only descriptor growth.
fn pi_binding_cols(desc: &EffectVmDescriptor2) -> BTreeMap<usize, usize> {
    let mut out = BTreeMap::new();
    for c in &desc.constraints {
        if let VmConstraint2::Base(VmConstraint::PiBinding {
            row: VmRow::First,
            col,
            pi_index,
        }) = c
        {
            out.insert(*pi_index, *col);
        }
    }
    out
}

// --------------------------------------------------------------------------------------------
// THE WITNESS GENERATOR.
// --------------------------------------------------------------------------------------------

/// **Fill the Lean Leg C descriptor's trace** for the conflict round `(rs, subs)` — the `.again`
/// branch of `roundStep`. `desc` is the decoded Lean descriptor for `rs.board.n` (via
/// `dregg_circuit::descriptor_by_name(&legc_descriptor_ident(n))`). The generator is checked against
/// it: on any layout disagreement (`trace_width` / `public_input_count`) it returns `Err`
/// (fail-closed). Every non-dead column is filled by SOLVING the descriptor's own gates; if any
/// cannot be resolved, the returned `Err` names it.
pub fn automatafl_legc_trace(
    rs: &RoundStateIn,
    subs: &[Move; 2],
    desc: &EffectVmDescriptor2,
) -> Result<LegCTrace, String> {
    let n = rs.board.n;
    let l = LegCLayout::new(n);

    // Fail-closed layout guards: the descriptor must be the Leg C layout for this `n`.
    if l.width() != desc.trace_width {
        return Err(format!(
            "legc witness-gen: layout width {} ≠ descriptor '{}' trace_width {}: a descriptor \
             cutover the shape-independent mirror has not tracked",
            l.width(),
            desc.name,
            desc.trace_width
        ));
    }
    if l.pi_count() != desc.public_input_count {
        return Err(format!(
            "legc witness-gen: layout PI count {} ≠ descriptor '{}' public_input_count {}",
            l.pi_count(),
            desc.name,
            desc.public_input_count
        ));
    }
    if rs.board.cells.len() != l.r.kk {
        return Err(format!(
            "legc witness-gen: board has {} cells, expected KK = {}",
            rs.board.cells.len(),
            l.r.kk
        ));
    }

    let mut vals: Vec<Option<BabyBear>> = vec![None; l.width()];

    // -- SEED the free inputs + the dead lanes. --
    seed(&l, rs, subs, &mut vals)?;

    // -- Fixpoint: fire the gadget fillers, then run Rule L, until nothing changes. --
    loop {
        let mut progress = false;
        progress |= fire_fillers(&l, &mut vals)?;
        progress |= rule_l_pass(desc, &mut vals)?;
        if !progress {
            break;
        }
    }

    // -- Every column must now be resolved (the dead lanes were seeded to 0); an unresolved column
    //    is a real gap. --
    let unresolved: Vec<usize> = (0..l.width()).filter(|c| vals[*c].is_none()).collect();
    if !unresolved.is_empty() {
        return Err(format!(
            "legc witness-gen: {} column(s) unresolved after the gate solver reached fixpoint. \
             A genuine witness-gen gap: no descriptor gate determines them, and no gadget filler \
             covers them. Contiguous ranges: {}",
            unresolved.len(),
            contiguous_ranges(&unresolved)
        ));
    }
    let row: Vec<BabyBear> = vals.into_iter().map(|v| v.unwrap()).collect();

    // -- Assemble the PIs off the descriptor's own PiBinding map: the free 16-felt door
    //    (placeholder cell roots) for the unbound prefix, every bound RoundState-window lane read off
    //    its own column. --
    let binds = pi_binding_cols(desc);
    let (old8, new8) = crate::witness::placeholder_roots();
    let door: Vec<BabyBear> = old8.iter().chain(new8.iter()).copied().collect();
    let mut public_inputs = Vec::with_capacity(desc.public_input_count);
    for pi in 0..desc.public_input_count {
        match binds.get(&pi) {
            Some(&c) => public_inputs.push(row[c]),
            None => {
                let v = door.get(pi).copied().ok_or_else(|| {
                    format!(
                        "legc witness-gen: PI {pi} is neither column-bound nor part of the 16-felt \
                         free door: the descriptor publishes a lane the ABI cannot fill"
                    )
                })?;
                public_inputs.push(v);
            }
        }
    }
    debug_assert_eq!(public_inputs.len(), desc.public_input_count);

    Ok(LegCTrace {
        row,
        public_inputs,
        n,
    })
}

/// Seed the genuinely-free trace columns + the dead lanes: `old` cells, `ONE`, the witnessed
/// automaton read, each move's coordinate + range bits + source one-hots + Leg C's destination
/// one-hots, the `marksIn` indicator, the `P = 2` seat pins, and `0` across the two dropped
/// occlusion blocks.
fn seed(
    l: &LegCLayout,
    rs: &RoundStateIn,
    subs: &[Move; 2],
    vals: &mut [Option<BabyBear>],
) -> Result<(), String> {
    let n = l.r.n;
    let old = &rs.board;

    // old board cells.
    for c in 0..l.r.kk {
        let code = old.cells[c] as i64;
        if !(0..=3).contains(&code) {
            return Err(format!(
                "legc witness-gen: cell {c} particle {code} ∉ {{0,1,2,3}}"
            ));
        }
        set_if_none(vals, l.r.old(c), bb(code));
    }
    // ONE.
    set_if_none(vals, l.r.one(), BabyBear::ONE);

    // Automaton position: scanned from `old` (matching `autoPinHead`).
    let (ax, ay) = find_auto(&old.cells, n);
    set_if_none(vals, l.r.ax_c(), bb(ax));
    set_if_none(vals, l.r.ay_c(), bb(ay));
    seed_decompose(vals, l.r.cr, ax, n, |k| l.r.ax_lo(k), |k| l.r.ax_hi(k));
    seed_decompose(vals, l.r.cr, ay, n, |k| l.r.ay_lo(k), |k| l.r.ay_hi(k));
    fill_one_hot(vals, n, |y| l.r.sel_auto_row(y), ay)?;
    fill_one_hot(vals, n, |x| l.r.sel_auto_col(x), ax)?;

    // Per-move validity front-end (Leg R's `validateMove`) + Leg C's own destination one-hots.
    for w in 0..2 {
        let b = l.r.mv_base(w);
        let (fx, fy) = (subs[w].frm.0 as i64, subs[w].frm.1 as i64);
        let (tx, ty) = (subs[w].to.0 as i64, subs[w].to.1 as i64);
        for (col, v) in [
            (l.r.c_fx(b), fx),
            (l.r.c_fy(b), fy),
            (l.r.c_tx(b), tx),
            (l.r.c_ty(b), ty),
        ] {
            if !(0..n as i64).contains(&v) {
                return Err(format!(
                    "legc witness-gen: move {w} coordinate {v} out of board [0, {n}) (fail-closed)"
                ));
            }
            set_if_none(vals, col, bb(v));
        }
        seed_decompose(
            vals,
            l.r.cr,
            fx,
            n,
            |k| l.r.c_fx_lo(b, k),
            |k| l.r.c_fx_hi(b, k),
        );
        seed_decompose(
            vals,
            l.r.cr,
            fy,
            n,
            |k| l.r.c_fy_lo(b, k),
            |k| l.r.c_fy_hi(b, k),
        );
        seed_decompose(
            vals,
            l.r.cr,
            tx,
            n,
            |k| l.r.c_tx_lo(b, k),
            |k| l.r.c_tx_hi(b, k),
        );
        seed_decompose(
            vals,
            l.r.cr,
            ty,
            n,
            |k| l.r.c_ty_lo(b, k),
            |k| l.r.c_ty_hi(b, k),
        );
        // `validateMove` SOURCE one-hots @ (fy, fx).
        fill_one_hot(vals, n, |j| l.r.c_sel_row(b, j), fy)?;
        fill_one_hot(vals, n, |j| l.r.c_sel_col(b, j), fx)?;
        // Leg C's DESTINATION one-hots @ (ty, tx).
        fill_one_hot(vals, n, |j| l.c_tsel_row(w, j), ty)?;
        fill_one_hot(vals, n, |j| l.c_tsel_col(w, j), tx)?;
    }

    // `marksIn` indicator: 1 exactly on the marked coordinates.
    for c in 0..l.r.kk {
        let (x, y) = ((c % n) as i32, (c / n) as i32);
        let marked = rs.marks.iter().any(|&(mx, my)| mx == x && my == y);
        set_if_none(vals, l.c_marks_in_cell(c), bb(i64::from(marked)));
    }

    // The `P = 2` seat pins: `lockedIn = 0` (all 5 lanes) and `waitingIn = 1`, per seat.
    for s in 0..LEGC_SEATS {
        for col in [
            l.c_locked_in_bit(s),
            l.c_locked_in_fx(s),
            l.c_locked_in_fy(s),
            l.c_locked_in_tx(s),
            l.c_locked_in_ty(s),
        ] {
            set_if_none(vals, col, BabyBear::ZERO);
        }
        set_if_none(vals, l.c_waiting_in_bit(s), BabyBear::ONE);
    }

    // THE DEAD LANES: the two dropped occlusion blocks `[occBase 0, RES0)` — read by nothing, bound
    // by nothing, so `0` satisfies every (nonexistent) constraint on them.
    for c in l.dead_lo()..l.dead_hi() {
        set_if_none(vals, c, BabyBear::ZERO);
    }
    Ok(())
}

/// Fire the front-half gadget fillers whose deps are resolved: the source-non-vacuum `forced_ge0`
/// bits (`anz`/`bnz`) and the four `patternBit` `eq_coords` `forced_ge0` blocks. Returns whether any
/// column was newly filled. (Leg C keeps NONE of Leg R's occlusion / resolvable-surface fillers.)
fn fire_fillers(l: &LegCLayout, vals: &mut [Option<BabyBear>]) -> Result<bool, String> {
    let mut prog = false;
    // Leg-3 source non-vacuum bits over each move's `cFp` (the solved source-cell particle).
    prog |= fill_forced_ge0(
        vals,
        l.r.c_fp(l.r.mv_base(0)),
        l.r.c_anz(),
        |k| l.r.anz_bit(k),
        SMALL_RBITS,
    )?;
    prog |= fill_forced_ge0(
        vals,
        l.r.c_fp(l.r.mv_base(1)),
        l.r.c_bnz(),
        |k| l.r.bnz_bit(k),
        SMALL_RBITS,
    )?;
    // Leg-4 pattern `eq_coords` neqs (the four `eqBase` blocks — eq_ff / eq_tt / eq_ab / eq_ba).
    for i in 0..4 {
        let e = l.r.eq_base(i);
        prog |= fill_forced_ge0(
            vals,
            l.r.c_eq_dsq(e),
            l.r.c_eq_neq(e),
            |k| l.r.eq_bit_at(e, k),
            RBITS,
        )?;
    }
    Ok(prog)
}

// --------------------------------------------------------------------------------------------
// The load-bearing verification + the RoundState-window ABI M7 connects.
// --------------------------------------------------------------------------------------------

/// **THE LOAD-BEARING VERIFICATION.** Does the generated trace SATISFY the decoded Lean descriptor
/// under the REAL `Ir2Air` row-local evaluator (`ir2_eval_accepts_i64`)? Runs over TWO replicated
/// rows so the `when_transition` gates fire. This is the gate a folded leaf must pass BEFORE it is
/// proven; a wrong fill fails here exactly as the STARK would (and a clean round fails the clash pin
/// here).
pub fn legc_trace_accepts(desc: &EffectVmDescriptor2, tr: &LegCTrace) -> bool {
    let rows_i64: Vec<Vec<i64>> = tr
        .base_trace(2)
        .iter()
        .map(|r| r.iter().map(|f| canon(*f)).collect())
        .collect();
    let pis_i64: Vec<i64> = tr.public_inputs.iter().map(|f| canon(*f)).collect();
    ir2_eval_accepts_i64(desc, &rows_i64, &pis_i64)
}

/// A debugging reporter: the index and a short render of the FIRST row-local `Gate`/first-row
/// `PiBinding` the trace violates, or `None` if it satisfies every one.
pub fn legc_trace_first_failure(
    desc: &EffectVmDescriptor2,
    tr: &LegCTrace,
) -> Option<(usize, String)> {
    fn eval(e: &LeanExpr, row: &[BabyBear]) -> BabyBear {
        match e {
            LeanExpr::Var(i) => row.get(*i).copied().unwrap_or(BabyBear::ZERO),
            LeanExpr::Const(c) => bb(*c),
            LeanExpr::Add(a, b) => eval(a, row) + eval(b, row),
            LeanExpr::Mul(a, b) => eval(a, row) * eval(b, row),
        }
    }
    for (ci, c) in desc.constraints.iter().enumerate() {
        match c {
            VmConstraint2::Base(VmConstraint::Gate(expr)) => {
                let v = eval(expr, &tr.row);
                if v != BabyBear::ZERO {
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

/// **LEG C's RoundState WINDOW** — the `IN`/`OUT` PI slice lists the multi-round fold (M7) connects.
///
/// ```text
///   IN  = pack(board) ‖ pack(marksIn)  ‖ lockedIn  ‖ waitingIn  ‖ (ax, ay)
///   OUT = pack(board) ‖ pack(marksOut) ‖ lockedOut ‖ waitingOut ‖ (ax, ay)
/// ```
///
/// The board is FROZEN (`boardFrozenConstraints`), so `pack(board) IN` and `pack(board) OUT` carry
/// equal values at distinct PI lanes; the automaton `(ax, ay)` is shared (a clash round never steps
/// it). Returned as `(in_slices, out_slices)`, each a list of `(pi_base, len)` — M7 welds
/// `prev.OUT == LegC.IN` and `LegC.OUT == next.IN`. `Err` on a descriptor whose PI count cannot
/// express the window (fail-closed).
pub fn legc_round_state_window(
    n: usize,
    desc: &EffectVmDescriptor2,
) -> Result<(Vec<(usize, usize)>, Vec<(usize, usize)>), String> {
    let l = LegCLayout::new(n);
    if l.pi_count() != desc.public_input_count {
        return Err(format!(
            "legc round-state window: layout PI count {} ≠ descriptor '{}' public_input_count {}",
            l.pi_count(),
            desc.name,
            desc.public_input_count
        ));
    }
    let f = l.r.rfc;
    let seats = LEGC_SEATS;
    let in_slices = vec![
        (l.pi_pack_in(), f),
        (l.pi_marks_in(), f),
        (l.pi_locked_in(), 5 * seats),
        (l.pi_waiting_in(), seats),
        (l.auto_pi_base(), 2),
    ];
    let out_slices = vec![
        (l.pi_pack_out(), f),
        (l.pi_marks_out(), f),
        (l.pi_locked_out(), 5 * seats),
        (l.pi_waiting_out(), seats),
        (l.auto_pi_base(), 2),
    ];
    let end = |sl: &[(usize, usize)]| sl.iter().map(|&(b, k)| b + k).max().unwrap_or(0);
    if end(&in_slices).max(end(&out_slices)) > desc.public_input_count {
        return Err(format!(
            "legc round-state window overruns descriptor '{}' ({} PIs)",
            desc.name, desc.public_input_count
        ));
    }
    Ok((in_slices, out_slices))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::board::{ATT, AUTO, VAC};
    use dregg_circuit::descriptor_by_name::descriptor_by_name;

    fn desc(n: usize) -> EffectVmDescriptor2 {
        descriptor_by_name(&legc_descriptor_ident(n))
            .unwrap_or_else(|| panic!("the n={n} automatafl-legc descriptor dispatches by name"))
    }

    fn mv(w: u32, frm: Coord, to: Coord) -> Move {
        Move { who: w, frm, to }
    }

    /// A blank `n×n` board with the automaton parked at `auto` and the listed non-vacuum pieces.
    fn board_with(n: usize, auto: Coord, placed: &[(Coord, u8)]) -> Board {
        let mut cells = vec![VAC; n * n];
        for &((x, y), p) in placed {
            cells[(y as usize) * n + (x as usize)] = p;
        }
        cells[(auto.1 as usize) * n + (auto.0 as usize)] = AUTO;
        Board {
            n,
            cells,
            auto,
            col_rule: true,
        }
    }

    /// **THE D4a COLLIDE**, ported to size `n`: two attractors drive rook-wise into a shared
    /// destination `(2, 0)` from distinct non-vacuum sources `(0, 0)` and `(4, 0)`. `clashCoords`
    /// collides at `(2, 0)`; round 1, so `marksIn = ∅`. Automaton parked out of the way.
    fn collide_round(n: usize) -> (RoundStateIn, [Move; 2]) {
        let c = n as i32 - 1;
        let board = board_with(n, (c, c), &[((0, 0), ATT), ((4, 0), ATT)]);
        let subs = [mv(0, (0, 0), (2, 0)), mv(1, (4, 0), (2, 0))];
        (
            RoundStateIn {
                board,
                marks: vec![],
            },
            subs,
        )
    }

    /// **THE D4b FORK**, ported to size `n`: one attractor at the shared source `(0, 0)`, two moves
    /// to distinct destinations `(0, 2)` and `(2, 0)`. `clashCoords` forks at `(0, 0)`.
    fn fork_round(n: usize) -> (RoundStateIn, [Move; 2]) {
        let c = n as i32 - 1;
        let board = board_with(n, (c, c), &[((0, 0), ATT)]);
        let subs = [mv(0, (0, 0), (0, 2)), mv(1, (0, 0), (2, 0))];
        (
            RoundStateIn {
                board,
                marks: vec![],
            },
            subs,
        )
    }

    /// A CLEAN round: distinct sources, distinct destinations, no fork/collide — `cSurv` would be 1.
    fn clean_round(n: usize) -> (RoundStateIn, [Move; 2]) {
        let c = n as i32 - 1;
        let board = board_with(n, (c, c), &[((0, 0), ATT), ((4, 0), ATT)]);
        let subs = [mv(0, (0, 0), (0, 2)), mv(1, (4, 0), (4, 2))];
        (
            RoundStateIn {
                board,
                marks: vec![],
            },
            subs,
        )
    }

    /// The n=11 layout mirror matches the emitted descriptor shape.
    #[test]
    fn n11_descriptor_shape() {
        let d = desc(11);
        assert_eq!(d.trace_width, 1208);
        assert_eq!(d.public_input_count, 78);
        assert_eq!(d.constraints.len(), 1425);
        let l = LegCLayout::new(11);
        assert_eq!(l.width(), d.trace_width);
        assert_eq!(l.pi_count(), d.public_input_count);
    }

    /// Fill a round's trace and assert the solver resolves every column and the REAL Ir2 evaluator
    /// accepts (or, for `expect_accept = false`, rejects). Returns the filled trace.
    fn check(n: usize, rs: &RoundStateIn, subs: &[Move; 2], expect_accept: bool) -> LegCTrace {
        let d = desc(n);
        let tr = automatafl_legc_trace(rs, subs, &d)
            .unwrap_or_else(|e| panic!("witness-gen (n={n}): {e}"));
        assert_eq!(tr.row.len(), d.trace_width);
        assert_eq!(tr.public_inputs.len(), d.public_input_count);
        let accepts = legc_trace_accepts(&d, &tr);
        if expect_accept {
            if let Some((ci, why)) = legc_trace_first_failure(&d, &tr) {
                panic!("n={n}: row-local constraint {ci} violated: {why}");
            }
            assert!(
                accepts,
                "n={n}: the trace must satisfy every gate of the PROVEN Leg C descriptor"
            );
        } else {
            assert!(!accepts, "n={n}: this round must be UNSAT as a Leg C");
        }
        tr
    }

    /// CANARY 1a: the D4a COLLIDE audit round (at n=11 and n=5) SATISFIES `automataflLegCDescN`.
    #[test]
    fn collide_round_satisfies() {
        for n in [11usize, 5] {
            let (rs, subs) = collide_round(n);
            check(n, &rs, &subs, true);
        }
    }

    /// CANARY 1b: the D4b FORK audit round (at n=11 and n=5) SATISFIES `automataflLegCDescN`.
    #[test]
    fn fork_round_satisfies() {
        for n in [11usize, 5] {
            let (rs, subs) = fork_round(n);
            check(n, &rs, &subs, true);
        }
    }

    /// CANARY 2: a CLEAN round is UNSATISFIABLE as a Leg C — `cSurv` would be 1, the clash pin gates
    /// it to 0. The generator still fills a trace; the accept-gate rejects it (no spurious round).
    #[test]
    fn clean_round_is_unsat() {
        for n in [11usize, 5] {
            let (rs, subs) = clean_round(n);
            check(n, &rs, &subs, false);
        }
    }

    /// CANARY 3: a FORGED `marksOut` that DROPS the new mark makes the descriptor UNSAT — the OR gate
    /// `marksOut = marksIn ∨ cs` bites at the conflicted cell (the "turn never terminates" forgery).
    #[test]
    fn forged_marks_out_drop_is_rejected() {
        let n = 11;
        let d = desc(n);
        let l = LegCLayout::new(n);
        let (rs, subs) = collide_round(n);
        let mut tr = automatafl_legc_trace(&rs, &subs, &d).unwrap();
        assert!(
            legc_trace_accepts(&d, &tr),
            "the honest collide trace accepts"
        );
        // The clash coordinate is (2, 0), linear index 2. Drop its OUT mark.
        let clash = 0 * n + 2;
        assert_eq!(
            canon(tr.row[l.c_marks_out_cell(clash)]),
            1,
            "the honest mark is set"
        );
        tr.row[l.c_marks_out_cell(clash)] = BabyBear::ZERO;
        assert!(
            !legc_trace_accepts(&d, &tr),
            "a forged marksOut that drops the new mark must fail the OR gate"
        );
    }

    /// CANARY 4: tampering a FROZEN-BOARD cell makes the descriptor UNSAT — the board-frozen gate
    /// (`mid = old`) and the OUT pack gate both break.
    #[test]
    fn tampered_frozen_board_cell_is_rejected() {
        let n = 11;
        let d = desc(n);
        let l = LegCLayout::new(n);
        let (rs, subs) = collide_round(n);
        let mut tr = automatafl_legc_trace(&rs, &subs, &d).unwrap();
        assert!(legc_trace_accepts(&d, &tr));
        // Corrupt a frozen OUT board cell (NGen.mid): boardFrozen `mid = old` no longer vanishes.
        tr.row[l.r.mid(0)] = tr.row[l.r.mid(0)] + BabyBear::ONE;
        assert!(
            !legc_trace_accepts(&d, &tr),
            "a tampered frozen-board cell must fail the board-frozen gate"
        );
    }

    /// The marks-legality gate is load-bearing: a `marksIn` that holds move 0's SOURCE square makes
    /// the submission illegal (`moveLegalB` refuses it), so the `legal = 1` pin fails — the ONLY
    /// place `marksIn` is consumed.
    #[test]
    fn marked_source_is_rejected() {
        let n = 11;
        let d = desc(n);
        let (_rs, subs) = collide_round(n);
        // Enter the round with move 0's source (0,0) already marked.
        let c = n as i32 - 1;
        let board = board_with(n, (c, c), &[((0, 0), ATT), ((4, 0), ATT)]);
        let rs = RoundStateIn {
            board,
            marks: vec![(0, 0)],
        };
        let tr = automatafl_legc_trace(&rs, &subs, &d).unwrap();
        assert!(
            !legc_trace_accepts(&d, &tr),
            "a submission naming a marked source must fail the legality pin"
        );
    }

    /// The OUT RoundState window IS `roundStep`'s `.again` state on the collide round: `marksOut`
    /// packs `{(2,0)}`, `lockedOut = ∅` (both seats conflicted), `waitingOut = [0,1]`. Read the
    /// published PI lanes back and check them against the reference outcome.
    #[test]
    fn out_window_is_round_again_state() {
        let n = 11;
        let d = desc(n);
        let l = LegCLayout::new(n);
        let (rs, subs) = collide_round(n);
        let tr = automatafl_legc_trace(&rs, &subs, &d).unwrap();
        assert!(legc_trace_accepts(&d, &tr));
        // waitingOut = [1, 1] (both seats re-enter); lockedOut bits = [0, 0] (nothing locks).
        for s in 0..LEGC_SEATS {
            assert_eq!(
                canon(tr.public_inputs[l.pi_waiting_out() + s]),
                1,
                "seat {s} re-enters (waitingOut)"
            );
            assert_eq!(
                canon(tr.public_inputs[l.pi_locked_out() + 5 * s]),
                0,
                "seat {s} does not lock (lockedOut bit)"
            );
        }
        // The frozen board: pack(board) IN == pack(board) OUT, lane for lane.
        for j in 0..l.r.rfc {
            assert_eq!(
                tr.public_inputs[l.pi_pack_in() + j],
                tr.public_inputs[l.pi_pack_out() + j],
                "the board is frozen across a clash round (felt {j})"
            );
        }
        // The window ABI is expressible in the descriptor.
        let (ins, outs) = legc_round_state_window(n, &d).expect("the window fits the descriptor");
        assert_eq!(ins.len(), 5);
        assert_eq!(outs.len(), 5);
    }

    /// The n=5 audit board is the minimal complete instance the same solver fills (the exact size
    /// `AutomataflRules`' D4a/D4b witnesses live on).
    #[test]
    fn n5_audit_size_resolves() {
        let d = desc(5);
        assert_eq!(d.trace_width, 536);
        assert_eq!(d.public_input_count, 50);
        let (rs, subs) = collide_round(5);
        check(5, &rs, &subs, true);
    }
}
