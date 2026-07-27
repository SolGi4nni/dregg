//! # The witness generator for the Lean-emitted RESOLVE (Leg R, `old → mid`) descriptor.
//!
//! **The trusted, fail-closed trace generator that fills the PROVEN Lean descriptor
//! `automataflResolveDescN {n}` (`circuit/descriptors/by-name/automatafl-resolve-n{n}.json`), so a
//! folded resolve leaf proves through the object REFINED in Lean
//! (`resolve_sat_imp_roundBoardN`: `cMidV4` IS `AutomataflRules.roundStep`'s resolve board), not a
//! hand-authored Rust AIR.** House law #1: the AIR is authored in Lean; this Rust only fills a
//! trace and CALLS the general IR-v2 evaluator. It authors NO constraints.
//!
//! ## Why resolve is harder than step (`witness.rs`), and the method
//!
//! The step witness-gen reused the Rust `Builder` fill byte-for-byte for its front-end. That does
//! NOT transfer: the Lean Leg R (`AutomataflResolveEmit.lean §2`) converts two compile-time bakes
//! into WITNESSED columns (the automaton row×column one-hot; the move-direction bit `iv`) AND
//! appends a whole STAGED-ADDITIVE correction chain (`INCL`/`NL`/`RESR`/`CV2`/`V3`/`V4`/`MIDV4`,
//! the occlusion / 2-cycle corrections that make `cMidV4` — not the leg-7 `mid` — the roundStep
//! board) with NO Rust counterpart.
//!
//! Rather than hand-transcribe ~500 gate right-hand-sides (fragile against the concurrent V2/V3
//! cutover), this fills the trace by SOLVING the descriptor's own gates. The Leg-R descriptor is a
//! deterministic feed-forward circuit over the free inputs `(old board, two move coordinates)`:
//! every witnessed column is pinned by a gate to a function of earlier columns. So the generator:
//!
//!   1. **SEEDS** the genuinely-free inputs — the `old` cells, the automaton one-hot (from a scan
//!      of `old` for the `AUTO` cell), and each move's coordinate + range-bit decomposition +
//!      source one-hots.
//!   2. Fires two families of **gadget fillers** the linear solver cannot derive — the
//!      `forced_ge0` boolean+range blocks (all of shape `[col − 1 ≥ 0]`) and the coordinate-pinned
//!      one-hots (`osrc`, the write-mid destination one-hots) — whose VALUES come from the game
//!      geometry, not a single linear gate.
//!   3. Runs a **linear gate-propagation solver** (Rule L) over the DESCRIPTOR'S OWN gates to
//!      fixpoint: any gate that is affine in its single remaining unknown column is solved for it.
//!      This computes every logic column (squared distances, inverses, line scans, the
//!      fork/collide/survive selection, the carries, the flow-through chain, the write-mid /
//!      corrected-board cells, the packed felts, the whole correction chain) by evaluating the
//!      gate that DEFINES it — so those columns satisfy their gates by construction, and the fill
//!      shrinks automatically as the descriptor shrinks (the solver reads whatever gates exist).
//!
//! Reading the descriptor's gates (never re-authoring them) is the shape-independence the design
//! demands. The load-bearing check is [`resolve_trace_accepts`]: the REAL `Ir2Air` row-local
//! evaluator (`ir2_eval_accepts_i64`, the STARK arithmetization) over TWO rows — a single
//! replicated row would exercise only the first/last-row PI bindings, never the `when_transition`
//! gates — must accept before any leaf is proven. A wrong fill fails a gate exactly as it would
//! fail the STARK.

use dregg_circuit::descriptor_ir2::{EffectVmDescriptor2, VmConstraint2, ir2_eval_accepts_i64};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};

use crate::board::{Board, Move};
use crate::resolve_layout::{
    AUTO_CODE, RBITS, ResolveLayout, SMALL_RBITS, resolve_descriptor_name,
};

/// The by-name loader identity of the Lean Leg-R resolve descriptor for board size `n`.
pub fn resolve_descriptor_ident(n: usize) -> &'static str {
    resolve_descriptor_name(n)
}

/// The generated single-row trace + public inputs for the Lean Leg-R descriptor at a resolution.
#[derive(Clone, Debug)]
pub struct ResolveTrace {
    /// One trace row of width `descriptor.trace_width` (the gates are row-local).
    pub row: Vec<BabyBear>,
    /// The descriptor public inputs (`door16 ‖ pack(old) ‖ pack(cMidV4) ‖ ax,ay`).
    pub public_inputs: Vec<BabyBear>,
    /// The board size.
    pub n: usize,
}

impl ResolveTrace {
    /// The base trace for the evaluator: the row replicated `num_rows` times. Use `≥ 2` rows to
    /// exercise the `when_transition` gates (a single row only fires the first/last-row PI
    /// bindings).
    pub fn base_trace(&self, num_rows: usize) -> Vec<Vec<BabyBear>> {
        vec![self.row.clone(); num_rows.max(2)]
    }

    /// The decoded FINAL corrected mid board (`cMidV4`) read back out of the filled trace — the
    /// roundStep resolve board this leaf commits to.
    pub fn mid_board(&self, l: &ResolveLayout) -> Board {
        let cells: Vec<u8> = (0..l.kk)
            .map(|c| canon(self.row[l.c_mid_v4(c)]) as u8)
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

// --------------------------------------------------------------------------------------------
// Small field helpers.
// --------------------------------------------------------------------------------------------

/// The canonical integer value of a felt (in `[0, p)`); small for every column a `forced_ge0`
/// head or the `i64` evaluator reads.
pub(crate) fn canon(b: BabyBear) -> i64 {
    b.0 as i64
}

/// A signed integer lifted into BabyBear.
pub(crate) fn bb(x: i64) -> BabyBear {
    if x >= 0 {
        BabyBear::from_u64(x as u64)
    } else {
        -BabyBear::from_u64((-x) as u64)
    }
}

/// Set a column iff it is currently unfilled; return `true` iff this call newly filled it.
pub(crate) fn set_if_none(vals: &mut [Option<BabyBear>], col: usize, v: BabyBear) -> bool {
    if vals[col].is_none() {
        vals[col] = Some(v);
        true
    } else {
        false
    }
}

// --------------------------------------------------------------------------------------------
// The IR-v2 expression evaluator (over a partial column assignment) — the engine of Rule L.
// --------------------------------------------------------------------------------------------

/// Evaluate a `LeanExpr` over a `get`-resolved assignment; `None` if any referenced column is
/// unresolved.
fn eval_expr(e: &LeanExpr, get: &dyn Fn(usize) -> Option<BabyBear>) -> Option<BabyBear> {
    match e {
        LeanExpr::Var(i) => get(*i),
        LeanExpr::Const(c) => Some(bb(*c)),
        LeanExpr::Add(a, b) => Some(eval_expr(a, get)? + eval_expr(b, get)?),
        LeanExpr::Mul(a, b) => Some(eval_expr(a, get)? * eval_expr(b, get)?),
    }
}

/// Collect the distinct column indices a `LeanExpr` reads.
fn collect_vars(e: &LeanExpr, out: &mut Vec<usize>) {
    match e {
        LeanExpr::Var(i) => {
            if !out.contains(i) {
                out.push(*i);
            }
        }
        LeanExpr::Const(_) => {}
        LeanExpr::Add(a, b) | LeanExpr::Mul(a, b) => {
            collect_vars(a, out);
            collect_vars(b, out);
        }
    }
}

/// **Rule L** for one gate `expr == 0`: if exactly one referenced column `u` is unresolved and the
/// gate is affine in `u`, solve `a·u + b == 0` for it. Returns `Ok(true)` iff it filled a column,
/// `Err` on a gate that forces `u` to no field value (a genuine UNSAT — the fail-closed signal).
fn try_solve_gate(expr: &LeanExpr, vals: &mut [Option<BabyBear>]) -> Result<bool, String> {
    let mut vars = Vec::new();
    collect_vars(expr, &mut vars);
    let unknown: Vec<usize> = vars
        .iter()
        .copied()
        .filter(|i| vals[*i].is_none())
        .collect();
    if unknown.len() != 1 {
        return Ok(false);
    }
    let u = unknown[0];
    let g = |t: BabyBear| -> BabyBear {
        eval_expr(expr, &|i| if i == u { Some(t) } else { vals[i] })
            .expect("all vars but the single unknown are resolved")
    };
    let zero = BabyBear::ZERO;
    let one = BabyBear::ONE;
    let two = one + one;
    let g0 = g(zero);
    let g1 = g(one);
    let g2 = g(two);
    // Affine in `u` iff the second finite difference vanishes: g0 − 2·g1 + g2 == 0.
    if g0 + g2 != g1 + g1 {
        return Ok(false); // higher-degree in u (a boolean/member gate) — not Rule L's to solve.
    }
    let a = g1 - g0; // coefficient of u
    let b = g0; // constant term
    if a == zero {
        if b == zero {
            return Ok(false); // 0 == 0 for any u — underdetermined here, solved by another gate.
        }
        return Err(format!(
            "resolve witness-gen: gate is UNSAT: column {u} forced to satisfy {}·u + {} = 0 with \
             a = 0, b ≠ 0",
            canon(a),
            canon(b)
        ));
    }
    let uval = -b * a.inverse().expect("a ≠ 0 has an inverse");
    vals[u] = Some(uval);
    Ok(true)
}

/// One Rule-L sweep over every `Base(Gate)` constraint.
pub(crate) fn rule_l_pass(
    desc: &EffectVmDescriptor2,
    vals: &mut [Option<BabyBear>],
) -> Result<bool, String> {
    let mut progress = false;
    for c in &desc.constraints {
        if let VmConstraint2::Base(VmConstraint::Gate(expr)) = c {
            progress |= try_solve_gate(expr, vals)?;
        }
    }
    Ok(progress)
}

// --------------------------------------------------------------------------------------------
// Gadget fillers the linear solver cannot derive: forced_ge0 blocks and coordinate one-hots.
// --------------------------------------------------------------------------------------------

/// A `forced_ge0` block over the head `source − 1` (every `forced_ge0` / `eq_scalar` / `eq_coords`
/// occlusion threshold in the descriptor has exactly this head): the boolean `ib = [source ≥ 1]`
/// at `ib_col`, and `rbits` recomposition bits of the range term `2·ib·d + ib − d − 1` (`d =
/// source − 1`) at `bit0(k)`. Fires once `source` is resolved; a term outside `[0, 2^rbits)` is a
/// fail-closed UNSAT (an invalid / out-of-range input).
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
    let ib = if d >= 0 { 1 } else { 0 };
    let term = 2 * ib * d + ib - d - 1;
    if term < 0 || term >= (1i64 << rbits) {
        return Err(format!(
            "resolve witness-gen: forced_ge0 range term {term} ∉ [0, 2^{rbits}) for source col \
             {source_col} (value {x}): an out-of-range / invalid input (fail-closed)"
        ));
    }
    let mut prog = set_if_none(vals, ib_col, bb(ib));
    for k in 0..rbits {
        prog |= set_if_none(vals, bit0(k), bb((term >> k) & 1));
    }
    Ok(prog)
}

/// Set a one-hot selector vector to the indicator of `idx` (`sel[j] = [j == idx]`). Fails closed
/// on an out-of-board index.
pub(crate) fn fill_one_hot(
    vals: &mut [Option<BabyBear>],
    n: usize,
    sel: impl Fn(usize) -> usize,
    idx: i64,
) -> Result<bool, String> {
    if idx < 0 || idx >= n as i64 {
        return Err(format!(
            "resolve witness-gen: one-hot index {idx} out of board [0, {n}) (fail-closed)"
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

/// Render a sorted column list as contiguous `[lo..hi)` ranges — so an unresolved set reads as
/// the FAMILIES it belongs to (`[121..242)` = the leg-7 `mid` board) rather than a wall of indices.
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

/// The scan of `old` for the `AUTO` cell → its `(x, y)`.
fn find_auto(cells: &[u8], n: usize) -> (i32, i32) {
    for (c, &v) in cells.iter().enumerate() {
        if v as i64 == AUTO_CODE {
            return ((c % n) as i32, (c / n) as i32);
        }
    }
    (0, 0)
}

/// Place both edges of a coordinate's range decomposition: `lo = binary(coord)` and
/// `hi = binary((n−1) − coord)`.
fn seed_decompose(
    vals: &mut [Option<BabyBear>],
    n: usize,
    cr: usize,
    coord: i64,
    lo: impl Fn(usize) -> usize,
    hi: impl Fn(usize) -> usize,
) {
    let up = (n as i64 - 1) - coord;
    for k in 0..cr {
        set_if_none(vals, lo(k), bb((coord >> k) & 1));
        set_if_none(vals, hi(k), bb((up >> k) & 1));
    }
}

// --------------------------------------------------------------------------------------------
// THE WITNESS GENERATOR.
// --------------------------------------------------------------------------------------------

/// **Fill the Lean Leg-R descriptor's trace** for the honest resolution `old → cMidV4` adjudicating
/// the two moves `ms`, then assemble the public inputs.
///
/// `desc` is the decoded Lean descriptor for `old.n` (via
/// `dregg_circuit::descriptor_by_name(resolve_descriptor_ident(old.n))`). The generator is checked
/// against it: on any layout disagreement (`trace_width` / `public_input_count`) it returns `Err`
/// (fail-closed). Every column is filled by SOLVING the descriptor's own gates; if any column
/// cannot be resolved, the returned `Err` names it — a genuine witness-gen gap, not a silent
/// mis-fill.
pub fn automatafl_resolve_trace(
    old: &Board,
    ms: &[Move; 2],
    desc: &EffectVmDescriptor2,
) -> Result<ResolveTrace, String> {
    let n = old.n;
    let l = ResolveLayout::new(n);

    // Fail-closed layout guards: the descriptor must be the Leg-R packed-felt layout for this `n`.
    if l.width() != desc.trace_width {
        return Err(format!(
            "resolve witness-gen: layout width {} ≠ descriptor '{}' trace_width {}: a descriptor \
             cutover the shape-independent mirror has not tracked",
            l.width(),
            desc.name,
            desc.trace_width
        ));
    }
    if l.pi_count() != desc.public_input_count {
        return Err(format!(
            "resolve witness-gen: layout PI count {} ≠ descriptor '{}' public_input_count {}",
            l.pi_count(),
            desc.name,
            desc.public_input_count
        ));
    }
    if old.cells.len() != l.kk {
        return Err(format!(
            "resolve witness-gen: board has {} cells, expected KK = {}",
            old.cells.len(),
            l.kk
        ));
    }

    let mut vals: Vec<Option<BabyBear>> = vec![None; l.width()];

    // -- SEED the free inputs. --
    seed(&l, old, ms, &mut vals)?;

    // -- Fixpoint: fire the gadget fillers, then run Rule L, until nothing changes. --
    loop {
        let mut progress = false;
        progress |= fire_fillers(&l, ms, &mut vals)?;
        progress |= rule_l_pass(desc, &mut vals)?;
        if !progress {
            break;
        }
    }

    // -- Every base column must now be resolved; an unresolved column is a real gap. --
    let unresolved: Vec<usize> = (0..l.width()).filter(|c| vals[*c].is_none()).collect();
    if !unresolved.is_empty() {
        return Err(format!(
            "resolve witness-gen: {} column(s) unresolved after the gate solver reached fixpoint. \
             A genuine witness-gen gap: no descriptor gate determines them, and no gadget filler \
             covers them. Contiguous ranges: {}",
            unresolved.len(),
            contiguous_ranges(&unresolved)
        ));
    }
    let row: Vec<BabyBear> = vals.into_iter().map(|v| v.unwrap()).collect();

    // -- Assemble the PIs off the ABI: door16 (free) ‖ pack(old) ‖ pack(cMidV4) ‖ ax, ay. --
    let (old8, new8) = crate::witness::placeholder_roots();
    let mut public_inputs = Vec::with_capacity(desc.public_input_count);
    public_inputs.extend_from_slice(&old8);
    public_inputs.extend_from_slice(&new8);
    for j in 0..l.rfc {
        public_inputs.push(row[l.pack_old_felt(j)]);
    }
    for j in 0..l.rfc {
        public_inputs.push(row[l.pack_mid_felt(j)]);
    }
    public_inputs.push(row[l.ax_c()]);
    public_inputs.push(row[l.ay_c()]);
    if public_inputs.len() != desc.public_input_count {
        return Err(format!(
            "resolve witness-gen: assembled {} PIs, descriptor wants {}",
            public_inputs.len(),
            desc.public_input_count
        ));
    }

    Ok(ResolveTrace {
        row,
        public_inputs,
        n,
    })
}

/// Seed the genuinely-free trace columns: `old` cells, `ONE`, the witnessed automaton position +
/// one-hots, and each move's coordinate + range bits + source one-hots + destination endpoint
/// one-hots.
pub(crate) fn seed(
    l: &ResolveLayout,
    old: &Board,
    ms: &[Move; 2],
    vals: &mut [Option<BabyBear>],
) -> Result<(), String> {
    let n = l.n;
    // old board cells.
    for c in 0..l.kk {
        let code = old.cells[c] as i64;
        if !(0..=3).contains(&code) {
            return Err(format!(
                "resolve witness-gen: cell {c} particle {code} ∉ {{0,1,2,3}}"
            ));
        }
        set_if_none(vals, l.old(c), bb(code));
    }
    // ONE.
    set_if_none(vals, l.one(), BabyBear::ONE);

    // Automaton position: scanned from `old` (matching `autoPinHead`, which reads the old cells).
    let (ax, ay) = find_auto(&old.cells, n);
    let (ax, ay) = (ax as i64, ay as i64);
    set_if_none(vals, l.ax_c(), bb(ax));
    set_if_none(vals, l.ay_c(), bb(ay));
    seed_decompose(vals, n, l.cr, ax, |k| l.ax_lo(k), |k| l.ax_hi(k));
    seed_decompose(vals, n, l.cr, ay, |k| l.ay_lo(k), |k| l.ay_hi(k));
    fill_one_hot(vals, n, |y| l.sel_auto_row(y), ay)?;
    fill_one_hot(vals, n, |x| l.sel_auto_col(x), ax)?;

    // Per-move validity front-end: coordinate + its range decomposition + the source one-hots +
    // the occlusion destination endpoint one-hots (all pinned to the move's own coordinates).
    for i in 0..2 {
        let b = l.mv_base(i);
        let (fx, fy) = (ms[i].frm.0 as i64, ms[i].frm.1 as i64);
        let (tx, ty) = (ms[i].to.0 as i64, ms[i].to.1 as i64);
        for (col, v) in [
            (l.c_fx(b), fx),
            (l.c_fy(b), fy),
            (l.c_tx(b), tx),
            (l.c_ty(b), ty),
        ] {
            if !(0..n as i64).contains(&v) {
                return Err(format!(
                    "resolve witness-gen: move {i} coordinate {v} out of board [0, {n}) \
                     (fail-closed)"
                ));
            }
            set_if_none(vals, col, bb(v));
        }
        seed_decompose(vals, n, l.cr, fx, |k| l.c_fx_lo(b, k), |k| l.c_fx_hi(b, k));
        seed_decompose(vals, n, l.cr, fy, |k| l.c_fy_lo(b, k), |k| l.c_fy_hi(b, k));
        seed_decompose(vals, n, l.cr, tx, |k| l.c_tx_lo(b, k), |k| l.c_tx_hi(b, k));
        seed_decompose(vals, n, l.cr, ty, |k| l.c_ty_lo(b, k), |k| l.c_ty_hi(b, k));
        // validate_move source one-hots @ (fy, fx).
        fill_one_hot(vals, n, |j| l.c_sel_row(b, j), fy)?;
        fill_one_hot(vals, n, |j| l.c_sel_col(b, j), fx)?;
        // write-mid SOURCE one-hots @ (fy, fx) (`writeEndpointConstraints`, piece `i`). These are
        // a distinct family from the validate_move pair above and must be seeded too: at n > 2 the
        // one-hot's weighted-sum gate has many unknowns and Rule L cannot crack it. (At n = 2 the
        // zero-coefficient term is dropped by `headToExpr`, leaving one unknown — which is exactly
        // why omitting these was invisible at n = 2 and fatal at n = 11.)
        fill_one_hot(vals, n, |j| l.w_src_row(i, j), fy)?;
        fill_one_hot(vals, n, |j| l.w_src_col(i, j), fx)?;
        // occlusion e_to endpoint one-hots @ (ty, tx) — occlusion block `o = occBase i`.
        let o = l.occ_base(i);
        fill_one_hot(vals, n, |j| l.c_ety(o, j), ty)?;
        fill_one_hot(vals, n, |j| l.c_etx(o, j), tx)?;
    }
    Ok(())
}

/// Fire the gadget fillers (forced_ge0 blocks + coordinate-pinned one-hots) whose deps are
/// resolved. Returns whether any column was newly filled.
pub(crate) fn fire_fillers(
    l: &ResolveLayout,
    ms: &[Move; 2],
    vals: &mut [Option<BabyBear>],
) -> Result<bool, String> {
    let n = l.n;
    let mut prog = false;

    // -- forced_ge0 blocks (uniform `source − 1` heads). --
    // Per occlusion block: the iv-scalar `neq`, the two passable `eq_scalar` `neq`s, and the
    // occlusion threshold `occ`.
    for i in 0..2 {
        let o = l.occ_base(i);
        prog |= fill_forced_ge0(
            vals,
            l.c_iv_dsq(o),
            l.c_iv_neq(o),
            |k| l.iv_neq_bit(o, k),
            RBITS,
        )?;
        prog |= fill_forced_ge0(
            vals,
            l.c_eqx_dsq(o),
            l.c_eqx_neq(o),
            |k| l.eqx_bit(o, k),
            RBITS,
        )?;
        prog |= fill_forced_ge0(
            vals,
            l.c_eqy_dsq(o),
            l.c_eqy_neq(o),
            |k| l.eqy_bit(o, k),
            RBITS,
        )?;
        prog |= fill_forced_ge0(vals, l.c_msum(o), l.c_occ(o), |k| l.occ_bit(o, k), RBITS)?;
    }
    // Leg-3 source non-vacuum bits.
    prog |= fill_forced_ge0(
        vals,
        l.c_fp(l.mv_base(0)),
        l.c_anz(),
        |k| l.anz_bit(k),
        SMALL_RBITS,
    )?;
    prog |= fill_forced_ge0(
        vals,
        l.c_fp(l.mv_base(1)),
        l.c_bnz(),
        |k| l.bnz_bit(k),
        SMALL_RBITS,
    )?;
    // Leg-4 pattern `eq_coords` neqs + the two resolvable-surface `eq_coords` neqs.
    for e in [
        l.eq_base(0),
        l.eq_base(1),
        l.eq_base(2),
        l.eq_base(3),
        l.res_eq_base,
        l.res_eq_v2_base,
    ] {
        prog |= fill_forced_ge0(
            vals,
            l.c_eq_dsq(e),
            l.c_eq_neq(e),
            |k| l.eq_bit_at(e, k),
            RBITS,
        )?;
    }
    // CHUNK-1 inclusive occlusion + non-leaver; CHUNK-5 corrected non-leaver.
    for w in 0..2 {
        prog |= fill_forced_ge0(
            vals,
            l.c_msum_incl(w),
            l.c_occ_incl(w),
            |k| l.occ_incl_bit(w, k),
            RBITS,
        )?;
    }
    for i in 0..2 {
        prog |= fill_forced_ge0(
            vals,
            l.c_land_old(i),
            l.c_land_nz(i),
            |k| l.land_nz_bit(i, k),
            SMALL_RBITS,
        )?;
        prog |= fill_forced_ge0(
            vals,
            l.c_land_old_v2(i),
            l.c_land_nz_v2(i),
            |k| l.land_nz_v2_bit(i, k),
            SMALL_RBITS,
        )?;
    }

    // -- coordinate-pinned one-hots the solver cannot derive. --
    for i in 0..2 {
        let o = l.occ_base(i);
        let ob = l.mv_base(1 - i);
        // osrc: the gated one-hot `Σ osrc = og`, hot at `iv ? fy_ob : fx_ob` when `og = 1`.
        if vals[l.c_osrc(o, 0)].is_none()
            && let Some(ogv) = vals[l.c_og(o)]
        {
            let og = canon(ogv);
            if og == 0 {
                for j in 0..n {
                    prog |= set_if_none(vals, l.c_osrc(o, j), BabyBear::ZERO);
                }
            } else if let (Some(ivv), Some(fxob), Some(fyob)) =
                (vals[l.c_iv(o)], vals[l.c_fx(ob)], vals[l.c_fy(ob)])
            {
                let idx = if canon(ivv) == 1 {
                    canon(fyob)
                } else {
                    canon(fxob)
                };
                prog |= fill_one_hot(vals, n, |j| l.c_osrc(o, j), idx)?;
            }
        }
    }
    // write-mid destination one-hots @ dest = to_i + ft_i·(to_other − to_i); corrected V2 twins.
    for i in 0..2 {
        let b = l.mv_base(i);
        let ob = l.mv_base(1 - i);
        prog |= fill_dest_one_hots(
            l,
            vals,
            l.ft_col(i),
            l.c_ty(b),
            l.c_ty(ob),
            l.c_tx(b),
            l.c_tx(ob),
            |j| l.w_dst_row(i, j),
            |j| l.w_dst_col(i, j),
        )?;
        prog |= fill_dest_one_hots(
            l,
            vals,
            l.ft_v2_col(i),
            l.c_ty(b),
            l.c_ty(ob),
            l.c_tx(b),
            l.c_tx(ob),
            |j| l.w_dst_v2_row(i, j),
            |j| l.w_dst_v2_col(i, j),
        )?;
    }
    let _ = ms;
    Ok(prog)
}

/// Fill a piece's destination row+column one-hots at the flow-through-interpolated destination
/// `own + ft·(other − own)`. Fires once the `ft` bit and the four destination coordinates resolve.
#[allow(clippy::too_many_arguments)]
fn fill_dest_one_hots(
    l: &ResolveLayout,
    vals: &mut [Option<BabyBear>],
    ft_col: usize,
    ty_own: usize,
    ty_other: usize,
    tx_own: usize,
    tx_other: usize,
    row_sel: impl Fn(usize) -> usize,
    col_sel: impl Fn(usize) -> usize,
) -> Result<bool, String> {
    if vals[row_sel(0)].is_some() {
        return Ok(false);
    }
    let (Some(ftv), Some(tyo), Some(tyx), Some(txo), Some(txx)) = (
        vals[ft_col],
        vals[ty_own],
        vals[ty_other],
        vals[tx_own],
        vals[tx_other],
    ) else {
        return Ok(false);
    };
    let ft = canon(ftv);
    let dest_y = canon(tyo) + ft * (canon(tyx) - canon(tyo));
    let dest_x = canon(txo) + ft * (canon(txx) - canon(txo));
    let mut prog = fill_one_hot(vals, l.n, &row_sel, dest_y)?;
    prog |= fill_one_hot(vals, l.n, &col_sel, dest_x)?;
    Ok(prog)
}

/// **LEG R's BOARD WINDOW** — `IN = pack(old) ‖ (ax, ay)`, `OUT = pack(cMidV4) ‖ (ax, ay)`.
///
/// Resolution never moves the automaton (Lean: `resolveMoves_automaton`), so Leg R's OUT automaton
/// IS its IN automaton and costs zero new lanes. Connected to Leg A's IN window in the fold, this
/// window is exactly `hseamPack ∧ hseamAutoX ∧ hseamAutoY` — the three seam hypotheses
/// `AutomataflTurnCapstone.turn_sat_imp_roundStep_pi` takes.
pub fn resolve_board_window(
    n: usize,
    desc: &EffectVmDescriptor2,
) -> Result<dregg_circuit::effect_vm::custom_state_binding::BoardWindowBinding, String> {
    use dregg_circuit::effect_vm::custom_state_binding::BoardWindowBinding;
    let l = ResolveLayout::new(n);
    if l.pi_count() != desc.public_input_count {
        return Err(format!(
            "resolve board window: layout PI count {} ≠ descriptor '{}' public_input_count {}",
            l.pi_count(),
            desc.name,
            desc.public_input_count
        ));
    }
    let b = BoardWindowBinding {
        in_slices: vec![(l.pack_in_pi_base(), l.rfc), (l.auto_pi_base(), 2)],
        out_slices: vec![(l.pack_out_pi_base(), l.rfc), (l.auto_pi_base(), 2)],
    };
    if !b.is_well_formed() || desc.public_input_count < b.pi_end() {
        return Err(format!(
            "resolve board window {b:?} is not expressible in descriptor '{}' ({} PIs)",
            desc.name, desc.public_input_count
        ));
    }
    Ok(b)
}

// --------------------------------------------------------------------------------------------
// The load-bearing check + a per-gate failure reporter (the design's `ir2_first_failing_constraint`
// kept local to this lane to avoid touching the shared circuit crate mid-cutover).
// --------------------------------------------------------------------------------------------

/// **THE LOAD-BEARING VERIFICATION.** Does the generated trace SATISFY the decoded Lean descriptor
/// under the REAL `Ir2Air` row-local evaluator (`ir2_eval_accepts_i64`)? Runs over TWO replicated
/// rows so the `when_transition` gates fire (not only the first/last-row PI bindings). This is the
/// gate a folded leaf must pass BEFORE it is proven; a wrong fill fails here exactly as the STARK
/// would.
pub fn resolve_trace_accepts(desc: &EffectVmDescriptor2, tr: &ResolveTrace) -> bool {
    let rows_i64: Vec<Vec<i64>> = tr
        .base_trace(2)
        .iter()
        .map(|r| r.iter().map(|f| canon(*f)).collect())
        .collect();
    let pis_i64: Vec<i64> = tr.public_inputs.iter().map(|f| canon(*f)).collect();
    ir2_eval_accepts_i64(desc, &rows_i64, &pis_i64)
}

/// A debugging reporter (the design's Step-0 `ir2_first_failing_constraint`, local): the index and
/// a short render of the FIRST row-local constraint the trace violates, or `None` if it satisfies
/// every one. Row-local scope: `Gate` bodies + first-row `PiBinding`s (the resolve descriptor has
/// no `Transition`/`Boundary`/lookup forms).
pub fn resolve_trace_first_failure(
    desc: &EffectVmDescriptor2,
    tr: &ResolveTrace,
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::board::Move;
    use crate::rules::{resolve_mid, stock_two_player};
    use dregg_circuit::descriptor_by_name::descriptor_by_name;

    fn desc11() -> EffectVmDescriptor2 {
        descriptor_by_name(resolve_descriptor_ident(11))
            .expect("the n=11 automatafl-resolve descriptor dispatches by name")
    }

    fn mv(frm: (i32, i32), to: (i32, i32)) -> Move {
        Move { who: 0, frm, to }
    }

    /// The FRONT gate: the n=11 layout mirror matches the emitted descriptor shape.
    #[test]
    fn n11_descriptor_shape() {
        let desc = desc11();
        assert_eq!(desc.trace_width, 1273);
        assert_eq!(desc.public_input_count, 36);
        let l = ResolveLayout::new(11);
        assert_eq!(l.width(), desc.trace_width);
        assert_eq!(l.pi_count(), desc.public_input_count);
    }

    /// Fill the trace for a move pair and assert (a) the solver resolves every column and (b) the
    /// REAL Ir2 evaluator accepts. When `expect_mid` is `Some`, additionally assert the trace's
    /// decoded `cMidV4` equals it; when `None`, print how `cMidV4` relates to `old` / the spec's
    /// `resolveMoves` (they are the SAME object now — the descriptor is refined against
    /// `roundStep`'s resolve board and the oracle IS `roundStep`, so a difference is a
    /// witness-generator fault, not a known divergence). Returns the filled trace.
    fn check(ms: [Move; 2], expect_mid: Option<Board>) -> ResolveTrace {
        let desc = desc11();
        let l = ResolveLayout::new(11);
        let old =
            stock_two_player().expect("the Lean game oracle (`dregg_automatafl_rules`) answers");
        let tr = automatafl_resolve_trace(&old, &ms, &desc)
            .unwrap_or_else(|e| panic!("witness-gen: {e}"));
        assert_eq!(tr.row.len(), desc.trace_width);
        if let Some((ci, why)) = resolve_trace_first_failure(&desc, &tr) {
            panic!("row-local constraint {ci} violated: {why}");
        }
        assert!(
            resolve_trace_accepts(&desc, &tr),
            "the generated trace must satisfy every gate of the PROVEN Lean descriptor"
        );
        let mid = tr.mid_board(&l);
        match expect_mid {
            Some(want) => assert_eq!(
                mid.cells, want.cells,
                "the descriptor's cMidV4 must equal the expected resolution"
            ),
            None => {
                let om = resolve_mid(&old, &[], &ms)
                    .expect("the Lean game oracle (`dregg_automatafl_rules`) answers");
                println!(
                    "  cMidV4 == old? {}   cMidV4 == resolve_mid(oracle)? {}",
                    mid.cells == old.cells,
                    mid.cells == om.cells
                );
            }
        }
        tr
    }

    /// (1) A CLEAN resolve: two independent, unoccluded, non-conflicting moves of the stock
    /// attractors — the descriptor's cMidV4 equals `resolve_mid`.
    #[test]
    fn clean_resolve_satisfies() {
        let old =
            stock_two_player().expect("the Lean game oracle (`dregg_automatafl_rules`) answers");
        let ms = [mv((3, 1), (3, 3)), mv((7, 1), (7, 3))];
        let expect = resolve_mid(&old, &[], &ms)
            .expect("the Lean game oracle (`dregg_automatafl_rules`) answers");
        check(ms, Some(expect));
    }

    /// (2) An OCCLUDED-STAYER: a move whose interior is blocked (by the flank attractor at (0,4))
    /// leaves its source piece in place; paired with a clean move. cMidV4 == `resolve_mid`.
    #[test]
    fn occluded_stayer_satisfies() {
        let old =
            stock_two_player().expect("the Lean game oracle (`dregg_automatafl_rules`) answers");
        let ms = [mv((0, 0), (0, 6)), mv((7, 1), (7, 3))];
        let expect = resolve_mid(&old, &[], &ms)
            .expect("the Lean game oracle (`dregg_automatafl_rules`) answers");
        assert_ne!(
            expect.cells, old.cells,
            "the clean partner move does change the board"
        );
        check(ms, Some(expect));
    }

    /// (3) A 2-CYCLE: the two flank pieces on column 0 name each other's squares (`to_a == frm_b`,
    /// `to_b == frm_a`). The ruleset says both pieces STAY PUT — `PHILOSOPHY.md`: *"2-cycles (A→B,
    /// B→A): **Always** stay in place — unambiguous composition"* (`AutomataflRules.twoCyc`) — and the
    /// descriptor's CHUNK-6 2-cycle detector zeroes both `carryV4`s, so `cMidV4 == old`.
    ///
    /// ⚑ **THIS TEST USED TO ASSERT A DIVERGENCE.** The Rust oracle it compared against
    /// (`reference::resolve_mid`, a transcription of `~/dev/automatafl/logic`) performed the SWAP, so
    /// the descriptor and the very oracle its witness generator consulted disagreed on this input —
    /// and the test pinned the disagreement "as a stated property of the descriptor rather than a
    /// silent surprise". There is nothing left to state: the oracle IS now the ruleset the descriptor
    /// was refined against, so the two AGREE, and the agreement is the tooth.
    #[test]
    fn two_cycle_satisfies_and_both_pieces_stay_put() {
        let old =
            stock_two_player().expect("the Lean game oracle (`dregg_automatafl_rules`) answers");
        let ms = [mv((0, 0), (0, 4)), mv((0, 4), (0, 0))];
        let oracle = resolve_mid(&old, &[], &ms)
            .expect("the Lean game oracle (`dregg_automatafl_rules`) answers");
        assert_eq!(
            oracle.cells, old.cells,
            "the ruleset keeps BOTH pieces put on a 2-cycle (the old Rust twin swapped them)"
        );
        let tr = check(ms, Some(old.clone()));
        let l = ResolveLayout::new(11);
        assert_eq!(
            tr.mid_board(&l).cells,
            oracle.cells,
            "the descriptor's 2-cycle detector and the ruleset oracle now agree"
        );
    }

    /// (4) A FORK clash: two moves from the SAME source to distinct destinations ⇒ both dropped ⇒
    /// clash ⇒ roundStep re-entry ⇒ cMidV4 == old, STILL satisfying the descriptor.
    #[test]
    fn fork_clash_reenters_with_mid_equals_old() {
        let old =
            stock_two_player().expect("the Lean game oracle (`dregg_automatafl_rules`) answers");
        let ms = [mv((0, 0), (0, 4)), mv((0, 0), (4, 0))];
        // Fork ⇒ both moves dropped by conflict-resolution ⇒ the oracle's resolve_mid IS `old`;
        // assert the descriptor's cMidV4 equals that clash re-entry board.
        let expect = resolve_mid(&old, &[], &ms)
            .expect("the Lean game oracle (`dregg_automatafl_rules`) answers");
        assert_eq!(
            expect.cells, old.cells,
            "a fork drops both moves ⇒ resolve_mid == old"
        );
        check(ms, Some(expect));
    }

    /// TAMPER REJECTS: corrupting a packed `cMidV4` felt (breaking its pack gate AND its PI
    /// binding) makes the descriptor UNSAT — the fail-closed property.
    #[test]
    fn tampered_mid_felt_is_rejected() {
        let desc = desc11();
        let l = ResolveLayout::new(11);
        let old =
            stock_two_player().expect("the Lean game oracle (`dregg_automatafl_rules`) answers");
        let ms = [mv((3, 1), (3, 3)), mv((7, 1), (7, 3))];
        let mut tr = automatafl_resolve_trace(&old, &ms, &desc).unwrap();
        // Corrupt the first packed mid felt's trace column: the pack gate no longer vanishes and
        // the felt no longer equals its bound PI.
        tr.row[l.pack_mid_felt(0)] = tr.row[l.pack_mid_felt(0)] + BabyBear::ONE;
        assert!(
            !resolve_trace_accepts(&desc, &tr),
            "a corrupted packed cMidV4 felt must fail the descriptor"
        );
    }

    /// FORGED MID PI REJECTS: leaving the trace honest but publishing a WRONG `pack(mid)` PI
    /// (a forged mid board) fails the mid pack PI binding — the seam the fold welds to cannot be
    /// lied about.
    #[test]
    fn forged_mid_pi_is_rejected() {
        let desc = desc11();
        let l = ResolveLayout::new(11);
        let old =
            stock_two_player().expect("the Lean game oracle (`dregg_automatafl_rules`) answers");
        let ms = [mv((3, 1), (3, 3)), mv((7, 1), (7, 3))];
        let mut tr = automatafl_resolve_trace(&old, &ms, &desc).unwrap();
        let pi = l.pack_out_pi_base();
        tr.public_inputs[pi] = tr.public_inputs[pi] + BabyBear::ONE;
        assert!(
            !resolve_trace_accepts(&desc, &tr),
            "a forged pack(mid) PI must fail the mid pack PI binding"
        );
    }

    /// n=2 minimal instance: the same solver fills the byte-golden 441w/20pi descriptor.
    #[test]
    fn n2_minimal_resolves() {
        let desc = descriptor_by_name(resolve_descriptor_ident(2))
            .expect("the n=2 automatafl-resolve descriptor dispatches by name");
        assert_eq!(desc.trace_width, 441);
        assert_eq!(desc.public_input_count, 20);
        // A 2x2 board: automaton at (0,0), a repulsor at (1,1); move (1,0)->... there is little
        // room, so use two vacuum no-op-ish valid moves of the single non-auto occupant.
        let mut cells = vec![0u8; 4];
        cells[0] = 3; // AUTO @ (0,0)
        cells[3] = 1; // REP @ (1,1)
        let board = Board {
            n: 2,
            cells,
            auto: (0, 0),
            col_rule: true,
        };
        // Move the repulsor (1,1)->(1,0) [rook, distinct, not auto], and a second identical-source
        // partner is a fork; instead give move b a distinct valid source-less line (1,1)->(0,1).
        let ms = [mv((1, 1), (1, 0)), mv((1, 1), (0, 1))];
        let tr = automatafl_resolve_trace(&board, &ms, &desc)
            .unwrap_or_else(|e| panic!("n=2 witness-gen: {e}"));
        assert!(
            resolve_trace_accepts(&desc, &tr),
            "the n=2 trace must satisfy the descriptor"
        );
    }
}
