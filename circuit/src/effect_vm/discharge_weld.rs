//! # `discharge_weld` — the IN-AIR DISCHARGE-OBLIGATION (tag 18) capacity-satisfaction gates with a
//! DUE-NESS RANGE CHECK (PIECE 2 of the VK epoch for tag 18, STAGED).
//!
//! This is the tag-18 sibling of [`super::satisfaction_weld`] (sealed escrow, tag 17) +
//! [`super::carrier_floor_weld`] (the selector-forcing floor decode). The Lean soundness rung is
//! `Dregg2.Deos.CapacitySatisfaction` §8 (`DischargeFieldGate`,
//! `discharge_satisfaction_witnessed`, and the teeth `discharge_early_field_rejected` /
//! `discharge_cursor_not_advanced_field_rejected` / `discharge_wrong_amount_field_rejected`); the
//! deployed off-AIR reference is `verify.rs`'s `DISCHARGE_OBLIGATION` arm.
//!
//! ## What is different from the escrow weld (why a NEW primitive)
//!
//! The sealed-escrow gate is pure status-code EQUALITY (`satisfaction_weld`'s four selector-gated
//! equalities). The standing-obligation discharge gate (the Lean `DischargeFieldGate`) is:
//!
//!  1. a per-period CURSOR ADVANCE   `after[cur] = before[cur] + period`  (additive equality)
//!  2. a schedule-amount TOTAL ADVANCE `after[tot] = before[tot] + amount` (additive equality)
//!  3. a DUE-NESS INEQUALITY          `before[due] ≤ clock`                (range check)
//!
//! The two additive equalities are mirror-able as selector-gated `(after − before − k) == 0` gates
//! (degree 1 inside the selector). The DUE-NESS leg is the genuinely-new gadget: an in-field
//! "`clock − due_block ≥ 0`" assertion, realized as a RANGE CHECK over an auxiliary difference
//! column `DUE_DIFF = clock − due_block` decomposed into `DUE_BITS` boolean bits — a forger paying
//! EARLY (`clock < due_block`) makes the difference WRAP to a large field element (`≈ p`), which has
//! NO `DUE_BITS`-wide bit decomposition, so the range-assembly gate cannot vanish (UNSAT). The
//! committed `due_block` is itself range-checked to `DUE_BITS` so a forger cannot pick a near-`p`
//! due block whose underflow wraps back DOWN into `[0, 2^DUE_BITS)` (the wrap-to-small dodge).
//!
//! ### Why `DUE_BITS = 28` is the sound width
//!
//! BabyBear's prime is `p = 2^31 − 2^27 + 1 ≈ 2^30.9`. For the range check to REJECT every underflow
//! we need the wrapped value `p − (due − clock)` to land ABOVE `2^DUE_BITS` (so it is un-representable
//! in `DUE_BITS` bits). With `due, clock < 2^DUE_BITS` the underflow magnitude `due − clock < 2^DUE_BITS`,
//! so the wrap lands in `(p − 2^DUE_BITS, p)`; this is disjoint from `[0, 2^DUE_BITS)` exactly when
//! `p − 2^DUE_BITS ≥ 2^DUE_BITS`, i.e. `2^{DUE_BITS+1} ≤ p`, i.e. `DUE_BITS ≤ 29`. `28` is taken
//! (a ~268M-block honest window) for comfortable margin (`p − 2^28 ≈ 1.74e9 ≫ 2^28`).
//!
//! ## STAGED — descriptor EMITTED (Lean) + producer EXPORTED; the registry row rides the big-bang
//!
//! The welded descriptor IS now emitted from Lean (`Dregg2.Deos.DischargeSatDescriptor.
//! dischargeSatVmDescriptor2R24`, v12 offsets through the canonical constants; exercise fixture
//! `circuit/tests/fixtures/discharge-sat-v3-staged.json`) and the producer aux-fill is EXPORTED
//! below ([`fill_discharge_aux`]); `gentian_discharge_vault_prove.rs` proves real STARKs against it
//! (honest settle proves+verifies; early / cursor-not-advanced / wrong-amount REFUSED). What still
//! rides the ONE big-bang descriptor regen: the `rotation-v3-staged-registry.tsv` row + the
//! drift-gate FP pin, the declared-tag-18 routing tie, the PI/manifest-param binding of
//! `PERIOD_COL`/`AMOUNT_COL`/`CLOCK_COL`, and the welded VK commit + live admission.

use super::carrier_floor_weld::caveat_tag_col;
use super::columns::rotation::caveat as cav;
use super::pi::SLOT_CAVEAT_TAG_DISCHARGE_OBLIGATION;
use super::satisfaction_weld::{after_field_col, before_field_col};
use super::trace_rotated::GRAD_ROT_WIDTH;
use crate::descriptor_ir2::{VmConstraint2, WindowExpr, WindowGateSpec};
use crate::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};

/// **THE DISCHARGE CAPACITY-SELECTOR COLUMN** — `param2` (`PARAM_BASE + 2`), the same free param slot
/// the escrow weld uses for its selector (this is a SEPARATE descriptor, so the slot is reused).
/// `1` on the settle row, `0` on padding; the emitted descriptor pins it to PI 46.
pub const DISCHARGE_SEL_COL: usize = super::columns::PARAM_BASE + 2;

/// The PI slot the emitted descriptor pins the selector to.
pub const DISCHARGE_SEL_PI: usize = 46;

/// **THE DECODED DISCHARGE-FLOOR COLUMN** — `param4` (`PARAM_BASE + 4`), the boolean "this cell
/// declares the discharge-obligation capacity (some bound caveat type-tag == 18)". The OR-fold writes
/// it; the first-row selector-force reads it. Mirror of `FLOOR_ESCROW_COL`.
pub const FLOOR_DISCHARGE_COL: usize = super::columns::PARAM_BASE + 4;

/// The carrier-bound `period` scalar column (the per-period cursor step). PI/manifest-param bound.
pub const PERIOD_COL: usize = super::columns::PARAM_BASE + 5;
/// The carrier-bound `amount` scalar column (the per-period schedule amount). PI/manifest-param bound.
pub const AMOUNT_COL: usize = super::columns::PARAM_BASE + 6;
/// The batch-height `clock` scalar column (the schedule clock). PI-bound (the deployed `block_height`).
pub const CLOCK_COL: usize = super::columns::PARAM_BASE + 7;

/// The discharge tag as a signed felt constant (`= 18`). Lean
/// `Dregg2.Deos.ConstraintBinding.tagDischargeObligation`.
const TAG_DISCHARGE: i64 = SLOT_CAVEAT_TAG_DISCHARGE_OBLIGATION as i64;

/// is-zero boolean aux column for declared-caveat slot `k` (free headroom past the rotated lane,
/// shared layout with `carrier_floor_weld` — distinct descriptor).
pub const fn bit_col(k: usize) -> usize {
    GRAD_ROT_WIDTH + k
}
/// is-zero inverse-witness aux column for slot `k`.
pub const fn inv_col(k: usize) -> usize {
    GRAD_ROT_WIDTH + cav::MAX_CAVEATS + k
}
/// running-OR carrier aux column `j`.
pub const fn or_col(j: usize) -> usize {
    GRAD_ROT_WIDTH + 2 * cav::MAX_CAVEATS + j
}

/// The bit-width of the due-ness range check (see the module header for why ≤ 29 is sound; 28 is the
/// honest window taken).
pub const DUE_BITS: usize = 28;

/// The range-check aux block base (past the decode aux `GRAD_ROT_WIDTH + 0..10`).
const RC_BASE: usize = GRAD_ROT_WIDTH + 16;

/// **THE DUE-NESS DIFFERENCE COLUMN** `DUE_DIFF = clock − due_block`, range-checked to `[0, 2^DUE_BITS)`.
/// The producer fills it with `clock − before[due]`; the link gate ties it to the field columns and
/// the bit decomposition forces it non-negative (small) — so `clock < due_block` (an early discharge)
/// has no satisfying assignment.
pub const DUE_DIFF_COL: usize = RC_BASE;
/// Bit `i` of the `DUE_DIFF` decomposition.
pub const fn diff_bit_col(i: usize) -> usize {
    RC_BASE + 1 + i
}
/// Bit `i` of the committed-`due_block` decomposition (closes the wrap-to-small dodge).
pub const fn due_bit_col(i: usize) -> usize {
    RC_BASE + 1 + DUE_BITS + i
}

// ---------------------------------------------------------------------------
// gate-body builders
// ---------------------------------------------------------------------------

fn var(c: usize) -> LeanExpr {
    LeanExpr::var(c)
}
fn neg(e: LeanExpr) -> LeanExpr {
    LeanExpr::mul(LeanExpr::constant(-1), e)
}
fn gate(body: LeanExpr) -> VmConstraint2 {
    VmConstraint2::Base(VmConstraint::Gate(body))
}
/// `sel · body` as an every-row `Gate` (inert on padding / non-capacity rows where `sel = 0`).
fn sel_gate(sel: usize, body: LeanExpr) -> VmConstraint2 {
    gate(LeanExpr::mul(var(sel), body))
}

/// `Σ_{i<nbits} 2^i · var(bit(i))` as a `LeanExpr`.
fn bit_sum(bit: impl Fn(usize) -> usize, nbits: usize) -> LeanExpr {
    let mut acc = LeanExpr::constant(0);
    for i in 0..nbits {
        acc = LeanExpr::add(
            acc,
            LeanExpr::mul(LeanExpr::constant(1i64 << i), var(bit(i))),
        );
    }
    acc
}

/// A selector-gated boolean gate `sel · (b · (b − 1)) == 0`.
fn sel_bool_gate(sel: usize, b: usize) -> VmConstraint2 {
    sel_gate(
        sel,
        LeanExpr::mul(var(b), LeanExpr::add(var(b), LeanExpr::constant(-1))),
    )
}

/// A selector-gated range-assembly gate `sel · (value − Σ 2^i bit_i) == 0`.
fn sel_assembly_gate(
    sel: usize,
    value: LeanExpr,
    bit: impl Fn(usize) -> usize,
    nbits: usize,
) -> VmConstraint2 {
    sel_gate(sel, LeanExpr::add(value, neg(bit_sum(bit, nbits))))
}

// --- the carrier floor decode (mirror of `carrier_floor_weld`, tag 18) ---

fn is_zero_def_gate(tag_col: usize, b: usize, inv: usize) -> VmConstraint2 {
    gate(LeanExpr::add(
        LeanExpr::add(
            var(b),
            LeanExpr::mul(
                LeanExpr::add(var(tag_col), LeanExpr::constant(-TAG_DISCHARGE)),
                var(inv),
            ),
        ),
        LeanExpr::constant(-1),
    ))
}
fn is_zero_force_gate(tag_col: usize, b: usize) -> VmConstraint2 {
    gate(LeanExpr::mul(
        LeanExpr::add(var(tag_col), LeanExpr::constant(-TAG_DISCHARGE)),
        var(b),
    ))
}
fn or_seed_gate(out: usize, b: usize) -> VmConstraint2 {
    gate(LeanExpr::add(var(out), neg(var(b))))
}
fn or_fold_gate(out: usize, in_or: usize, b: usize) -> VmConstraint2 {
    let or = LeanExpr::add(
        LeanExpr::add(var(in_or), var(b)),
        neg(LeanExpr::mul(var(in_or), var(b))),
    );
    gate(LeanExpr::add(var(out), neg(or)))
}
fn selector_force_first_gate(floor: usize, sel: usize) -> VmConstraint2 {
    VmConstraint2::Base(VmConstraint::Boundary {
        row: VmRow::First,
        body: LeanExpr::mul(var(floor), LeanExpr::add(var(sel), LeanExpr::constant(-1))),
    })
}
fn caveat_uniform_gate(tag_col: usize) -> VmConstraint2 {
    VmConstraint2::WindowGate(WindowGateSpec {
        body: WindowExpr::Add(
            Box::new(WindowExpr::Nxt(tag_col)),
            Box::new(WindowExpr::Mul(
                Box::new(WindowExpr::Const(-1)),
                Box::new(WindowExpr::Loc(tag_col)),
            )),
        ),
        on_transition: true,
    })
}

/// **THE DISCHARGE FLOOR DECODE + FIRST-ROW SELECTOR-FORCE + CAVEAT-UNIFORMITY GATES (STAGED).**
/// Decode "this cell declares discharge (some bound caveat type-tag == 18)" from the caveat-commit
/// bound type-tag columns, force the capacity selector ON on the settle (first) row, and force the
/// caveat manifest uniform across rows — the tag-18 mirror of `carrier_floor_weld::carrier_floor_gates`.
pub fn discharge_floor_gates() -> Vec<VmConstraint2> {
    let mut g = Vec::new();
    for k in 0..cav::MAX_CAVEATS {
        g.push(is_zero_def_gate(caveat_tag_col(k), bit_col(k), inv_col(k)));
        g.push(is_zero_force_gate(caveat_tag_col(k), bit_col(k)));
    }
    g.push(or_seed_gate(or_col(0), bit_col(0)));
    g.push(or_fold_gate(or_col(1), or_col(0), bit_col(1)));
    g.push(or_fold_gate(or_col(2), or_col(1), bit_col(2)));
    g.push(or_fold_gate(FLOOR_DISCHARGE_COL, or_col(2), bit_col(3)));
    g.push(selector_force_first_gate(
        FLOOR_DISCHARGE_COL,
        DISCHARGE_SEL_COL,
    ));
    for k in 0..cav::MAX_CAVEATS {
        g.push(caveat_uniform_gate(caveat_tag_col(k)));
    }
    g
}

/// **THE DISCHARGE SATISFACTION GATES (STAGED).** The two additive equalities + the due-ness range
/// check, all selector-gated (inert when `DISCHARGE_SEL_COL = 0`):
///
///  1. cursor advance `sel · (after[cur] − before[cur] − period) == 0`
///  2. total advance  `sel · (after[tot] − before[tot] − amount) == 0`
///  3. due-ness:
///     - link    `sel · (clock − before[due] − DUE_DIFF) == 0`
///     - `DUE_DIFF` boolean bits + assembly (forces `DUE_DIFF ∈ [0, 2^DUE_BITS)`)
///     - `before[due]` boolean bits + assembly (forces it `< 2^DUE_BITS` — the wrap-to-small dodge)
///
/// Read over the rotated BEFORE/AFTER field columns the wide commit binds (the Rust shadow of the Lean
/// `DischargeFieldGate`). A satisfying proof FORCES `before[due] ≤ clock`, the cursor advanced by one
/// period, and the total by exactly the amount — an EARLY / NON-ADVANCED / WRONG-AMOUNT discharge is
/// UNSAT.
pub fn discharge_satisfaction_gates(
    cur_slot: usize,
    tot_slot: usize,
    due_slot: usize,
) -> Vec<VmConstraint2> {
    let sel = DISCHARGE_SEL_COL;
    let mut g = Vec::new();

    // (1) cursor advance.
    let cur = LeanExpr::add(
        LeanExpr::add(
            var(after_field_col(cur_slot)),
            neg(var(before_field_col(cur_slot))),
        ),
        neg(var(PERIOD_COL)),
    );
    g.push(sel_gate(sel, cur));

    // (2) total advance.
    let tot = LeanExpr::add(
        LeanExpr::add(
            var(after_field_col(tot_slot)),
            neg(var(before_field_col(tot_slot))),
        ),
        neg(var(AMOUNT_COL)),
    );
    g.push(sel_gate(sel, tot));

    // (3a) due-ness link: DUE_DIFF = clock − before[due].
    let link = LeanExpr::add(
        LeanExpr::add(var(CLOCK_COL), neg(var(before_field_col(due_slot)))),
        neg(var(DUE_DIFF_COL)),
    );
    g.push(sel_gate(sel, link));

    // (3b) DUE_DIFF range check (boolean bits + assembly).
    for i in 0..DUE_BITS {
        g.push(sel_bool_gate(sel, diff_bit_col(i)));
    }
    g.push(sel_assembly_gate(
        sel,
        var(DUE_DIFF_COL),
        diff_bit_col,
        DUE_BITS,
    ));

    // (3c) committed due_block range check (closes the wrap-to-small dodge).
    for i in 0..DUE_BITS {
        g.push(sel_bool_gate(sel, due_bit_col(i)));
    }
    g.push(sel_assembly_gate(
        sel,
        var(before_field_col(due_slot)),
        due_bit_col,
        DUE_BITS,
    ));

    g
}

/// **THE FULL IN-AIR DISCHARGE GADGET (STAGED).** The floor decode / selector-force / uniformity gates
/// followed by the satisfaction gates. A satisfying proof on a declared-discharge cell forces the
/// per-period discipline over the committed state for a PURE light client — the tag-18 face of the
/// sealed-escrow weld.
pub fn discharge_gates(cur_slot: usize, tot_slot: usize, due_slot: usize) -> Vec<VmConstraint2> {
    let mut g = discharge_floor_gates();
    g.extend(discharge_satisfaction_gates(cur_slot, tot_slot, due_slot));
    g
}

// ---------------------------------------------------------------------------
// THE EXPORTED PRODUCER AUX-FILL (the graduation of the in-test `make_row` witness logic).
// ---------------------------------------------------------------------------

/// **THE PRODUCTION DISCHARGE AUX-FILL (one row).** Fill every auxiliary column the discharge
/// gadget's gates read, from the row's OWN bound columns — the producer arm the rotated trace
/// generator (and the gentian-style prove exercise) calls after the settle-carrier trace is
/// generated:
///
///  * the floor decode witness (`bit`/`inv`/`or` + `FLOOR_DISCHARGE_COL`), read from the four
///    caveat-commit-bound type-tag columns already on the row;
///  * the schedule scalars (`PERIOD_COL`/`AMOUNT_COL`/`CLOCK_COL`);
///  * the due-ness range witness: `DUE_DIFF = clock − before[due]` (field), its `DUE_BITS`
///    decomposition, and the committed `before[due]` decomposition.
///
/// The row is grown to `width` first. Does NOT touch the capacity selector (`DISCHARGE_SEL_COL`),
/// the field columns, or the PI vector — the trace generator owns those. TOTAL: a non-witnessable
/// row (e.g. an EARLY discharge, whose difference wraps past `2^DUE_BITS`) still fills, producing a
/// REFUSING witness (the range-assembly gate cannot vanish) — fail-closed by construction.
pub fn fill_discharge_aux_row(
    row: &mut Vec<crate::field::BabyBear>,
    width: usize,
    due_slot: usize,
    period: u32,
    amount: u32,
    clock: u32,
) {
    use crate::field::BabyBear;
    if row.len() < width {
        row.resize(width, BabyBear::ZERO);
    }
    // The floor decode witness over the bound type-tag columns.
    let mut running = 0u32;
    for k in 0..cav::MAX_CAVEATS {
        let tag = row[caveat_tag_col(k)].as_u32();
        let is_disc = tag == SLOT_CAVEAT_TAG_DISCHARGE_OBLIGATION;
        let b = u32::from(is_disc);
        row[bit_col(k)] = BabyBear::new(b);
        row[inv_col(k)] = if is_disc {
            BabyBear::ZERO
        } else {
            (BabyBear::new(tag) - BabyBear::new(SLOT_CAVEAT_TAG_DISCHARGE_OBLIGATION))
                .inverse()
                .expect("nonzero tag−18 invertible")
        };
        running |= b;
        if k == 0 {
            row[or_col(0)] = BabyBear::new(running);
        } else if k < cav::MAX_CAVEATS - 1 {
            row[or_col(k)] = BabyBear::new(running);
        } else {
            row[FLOOR_DISCHARGE_COL] = BabyBear::new(running);
        }
    }
    // The schedule scalars.
    row[PERIOD_COL] = BabyBear::new(period);
    row[AMOUNT_COL] = BabyBear::new(amount);
    row[CLOCK_COL] = BabyBear::new(clock);
    // The due-ness range witness (read `before[due]` from the row's own rotated field column).
    let due = row[before_field_col(due_slot)];
    let diff = BabyBear::new(clock) - due;
    row[DUE_DIFF_COL] = diff;
    for i in 0..DUE_BITS {
        row[diff_bit_col(i)] = BabyBear::new((diff.as_u32() >> i) & 1);
        row[due_bit_col(i)] = BabyBear::new((due.as_u32() >> i) & 1);
    }
}

/// **THE PRODUCTION DISCHARGE AUX-FILL (whole trace).** [`fill_discharge_aux_row`] on every row —
/// the decode gates are EVERY-ROW (the satisfaction gates are selector-gated, inert on padding),
/// so the aux columns are filled uniformly. The rotated settle-carrier trace + this fill is a
/// complete witness for the staged `dischargeSatVmDescriptor2R24` + `discharge_floor_gates` weld.
pub fn fill_discharge_aux(
    trace: &mut [Vec<crate::field::BabyBear>],
    width: usize,
    due_slot: usize,
    period: u32,
    amount: u32,
    clock: u32,
) {
    for row in trace.iter_mut() {
        fill_discharge_aux_row(row, width, due_slot, period, amount, clock);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::descriptor_ir2::eval_lean_expr;
    use crate::field::BabyBear;

    const CUR: usize = 0;
    const TOT: usize = 1;
    const DUE: usize = 2;

    /// Row-aware evaluation of one constraint over a `(local, next, is_first)` window — replays the
    /// deployed firing domains (every-row `Gate`, `Boundary{First}`, `on_transition` `WindowGate`).
    fn violation(
        c: &VmConstraint2,
        local: &[BabyBear],
        next: &[BabyBear],
        is_first: bool,
    ) -> BabyBear {
        match c {
            VmConstraint2::Base(VmConstraint::Gate(body)) => eval_lean_expr(body, local),
            VmConstraint2::Base(VmConstraint::Boundary {
                row: VmRow::First,
                body,
            }) => {
                if is_first {
                    eval_lean_expr(body, local)
                } else {
                    BabyBear::ZERO
                }
            }
            VmConstraint2::WindowGate(g) => eval_window(&g.body, local, next),
            other => panic!("unexpected discharge constraint kind: {other:?}"),
        }
    }

    fn eval_window(e: &WindowExpr, local: &[BabyBear], next: &[BabyBear]) -> BabyBear {
        match e {
            WindowExpr::Loc(i) => local[*i],
            WindowExpr::Nxt(i) => next[*i],
            WindowExpr::Const(c) => {
                if *c < 0 {
                    -BabyBear::new((-*c) as u32)
                } else {
                    BabyBear::new(*c as u32)
                }
            }
            WindowExpr::Add(a, b) => eval_window(a, local, next) + eval_window(b, local, next),
            WindowExpr::Mul(a, b) => eval_window(a, local, next) * eval_window(b, local, next),
        }
    }

    /// Build a row by setting the generator-owned columns (tags, selector, field columns), then
    /// running the EXPORTED production aux-fill [`fill_discharge_aux_row`] — the tests exercise the
    /// same producer arm the prove exercise / rotated trace generator calls.
    #[allow(clippy::too_many_arguments)]
    fn make_row(
        tags: [u32; cav::MAX_CAVEATS],
        sel: u32,
        before_cur: u32,
        before_tot: u32,
        before_due: u32,
        after_cur: u32,
        after_tot: u32,
        after_due: u32,
        period: u32,
        amount: u32,
        clock: u32,
    ) -> Vec<BabyBear> {
        let width = (due_bit_col(DUE_BITS - 1) + 1)
            .max(after_field_col(7) + 1)
            .max(CLOCK_COL + 1);
        let mut row = vec![BabyBear::ZERO; width];

        for k in 0..cav::MAX_CAVEATS {
            row[caveat_tag_col(k)] = BabyBear::new(tags[k]);
        }
        row[DISCHARGE_SEL_COL] = BabyBear::new(sel);
        row[before_field_col(CUR)] = BabyBear::new(before_cur);
        row[before_field_col(TOT)] = BabyBear::new(before_tot);
        row[before_field_col(DUE)] = BabyBear::new(before_due);
        row[after_field_col(CUR)] = BabyBear::new(after_cur);
        row[after_field_col(TOT)] = BabyBear::new(after_tot);
        row[after_field_col(DUE)] = BabyBear::new(after_due);

        fill_discharge_aux_row(&mut row, width, DUE, period, amount, clock);
        row
    }

    fn all_zero_settle(gates: &[VmConstraint2], row: &[BabyBear]) -> bool {
        gates
            .iter()
            .all(|g| violation(g, row, row, /*is_first*/ true) == BabyBear::ZERO)
    }

    #[test]
    fn columns_are_distinct() {
        let mut cols: Vec<usize> = (0..cav::MAX_CAVEATS)
            .flat_map(|k| [caveat_tag_col(k), bit_col(k), inv_col(k)])
            .collect();
        cols.extend([
            or_col(0),
            or_col(1),
            or_col(2),
            FLOOR_DISCHARGE_COL,
            DISCHARGE_SEL_COL,
        ]);
        cols.extend([PERIOD_COL, AMOUNT_COL, CLOCK_COL, DUE_DIFF_COL]);
        cols.extend((0..DUE_BITS).map(diff_bit_col));
        cols.extend((0..DUE_BITS).map(due_bit_col));
        let n = cols.len();
        cols.sort_unstable();
        cols.dedup();
        assert_eq!(cols.len(), n, "no two discharge-gadget columns alias");
    }

    #[test]
    fn honest_discharge_satisfies_every_gate() {
        // The Lean §10 witness: cursor 1000→1100 (+period 100), total 0→50 (+amount 50), due 1000 ≤
        // clock 1000. A declared-discharge manifest with the selector on.
        let gates = discharge_gates(CUR, TOT, DUE);
        let row = make_row(
            [TAG_DISCHARGE as u32, 19, 0, 0],
            /*sel*/ 1,
            /*before*/ 1000,
            0,
            1000,
            /*after*/ 1100,
            50,
            1000,
            /*period*/ 100,
            /*amount*/ 50,
            /*clock*/ 1000,
        );
        assert_eq!(
            row[FLOOR_DISCHARGE_COL],
            BabyBear::ONE,
            "discharge declared ⟹ floor 1"
        );
        assert!(
            all_zero_settle(&gates, &row),
            "the honest discharge must satisfy every in-AIR gate"
        );
    }

    #[test]
    fn early_discharge_is_unsat() {
        // clock 999 BELOW the committed due block 1000 — the difference wraps to ≈ p and has no
        // DUE_BITS decomposition, so the range-assembly gate bites.
        let gates = discharge_gates(CUR, TOT, DUE);
        let row = make_row(
            [TAG_DISCHARGE as u32, 19, 0, 0],
            1,
            1000,
            0,
            1000,
            1100,
            50,
            1000,
            100,
            50,
            /*clock*/ 999,
        );
        assert!(
            !all_zero_settle(&gates, &row),
            "an early discharge (clock < due) must violate a gate"
        );
    }

    #[test]
    fn cursor_not_advanced_is_unsat() {
        // A replay leaving the one-shot cursor where it was (after_cur = before_cur, no +period).
        let gates = discharge_gates(CUR, TOT, DUE);
        let row = make_row(
            [TAG_DISCHARGE as u32, 19, 0, 0],
            1,
            1000,
            0,
            1000,
            /*after_cur*/ 1000,
            50,
            1000,
            100,
            50,
            1000,
        );
        assert!(
            !all_zero_settle(&gates, &row),
            "a non-advanced cursor must violate the cursor gate"
        );
    }

    #[test]
    fn wrong_amount_is_unsat() {
        // The discharged total advances by an amount ≠ the schedule amount.
        let gates = discharge_gates(CUR, TOT, DUE);
        let row = make_row(
            [TAG_DISCHARGE as u32, 19, 0, 0],
            1,
            1000,
            0,
            1000,
            1100,
            /*after_tot*/ 9999,
            1000,
            100,
            50,
            1000,
        );
        assert!(
            !all_zero_settle(&gates, &row),
            "a wrong-amount discharge must violate the total gate"
        );
    }

    #[test]
    fn declared_discharge_with_selector_off_is_unsat() {
        // The forger dodges by SEL = 0 on the settle row — the first-row selector-force bites.
        let gates = discharge_gates(CUR, TOT, DUE);
        let row = make_row(
            [TAG_DISCHARGE as u32, 19, 0, 0],
            /*sel*/ 0,
            1000,
            0,
            1000,
            1100,
            50,
            1000,
            100,
            50,
            1000,
        );
        assert!(
            !all_zero_settle(&gates, &row),
            "a declared-discharge cell cannot dodge the satisfaction discipline by SEL = 0"
        );
    }

    #[test]
    fn first_row_force_inert_on_padding() {
        // THE ROW-LOCALITY discipline: a carry-forward padding row (is_first = false) with discharge
        // declared (FLOOR 1) and the selector 0 satisfies every gate (the force is settle-row scoped).
        let gates = discharge_gates(CUR, TOT, DUE);
        let row = make_row(
            [TAG_DISCHARGE as u32, 19, 0, 0],
            /*sel*/ 0,
            1000,
            0,
            1000,
            1100,
            50,
            1000,
            100,
            50,
            1000,
        );
        assert_eq!(row[FLOOR_DISCHARGE_COL], BabyBear::ONE);
        let all_inert = gates
            .iter()
            .all(|g| violation(g, &row, &row, /*is_first*/ false) == BabyBear::ZERO);
        assert!(
            all_inert,
            "with sel 0 every gate must be inert on a padding row (first-row scoping)"
        );
    }

    #[test]
    fn no_discharge_declared_leaves_selector_free() {
        // No tag-18 in the manifest ⟹ floor 0 ⟹ the selector-force is inert (no false demand).
        let gates = discharge_gates(CUR, TOT, DUE);
        let row = make_row(
            [6, 19, 0, 0],
            /*sel*/ 0,
            1000,
            0,
            1000,
            1100,
            50,
            1000,
            100,
            50,
            1000,
        );
        assert_eq!(row[FLOOR_DISCHARGE_COL], BabyBear::ZERO);
        assert!(
            all_zero_settle(&gates, &row),
            "no discharge declared ⟹ no false reject"
        );
    }

    #[test]
    fn caveat_uniformity_bites_on_non_uniform_manifest() {
        // A forger lighting a no-discharge manifest on the settle row (local) while committing the
        // discharge manifest on the next/last row (next) trips a uniformity window gate.
        let gates = discharge_gates(CUR, TOT, DUE);
        let local = make_row(
            [6, 19, 0, 0],
            0,
            1000,
            0,
            1000,
            1100,
            50,
            1000,
            100,
            50,
            1000,
        );
        let next = make_row(
            [TAG_DISCHARGE as u32, 19, 0, 0],
            0,
            1000,
            0,
            1000,
            1100,
            50,
            1000,
            100,
            50,
            1000,
        );
        let bites = gates
            .iter()
            .any(|g| violation(g, &local, &next, /*is_first*/ true) != BabyBear::ZERO);
        assert!(
            bites,
            "a non-uniform caveat manifest must trip a uniformity gate"
        );
    }
}
