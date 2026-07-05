//! # `carrier_floor_weld` — the GENTIAN floor BINDING discharged (PATH b, STAGED).
//!
//! `docs/deos/VK-EPOCH-CONSTRAINT-BINDING-DESIGN.md` §6 item 2 / `IN-AIR-AUTHORITY-DIGEST-GADGET.md`
//! named the last soundness gap before the sealed-escrow weld can flip to a deployed PURE-LIGHT-CLIENT
//! truth: the selector-forcing gadget ([`authority_digest_weld`]) decoded the required-tag floor from a
//! separately-hashed `B_AUTHORITY_DIGEST` limb, and its soundness was conditional on the Lean
//! `hcommitLimb` hypothesis — that the FREE rotated limb carries `hash(the real declared floor)`.
//! Nothing FORCED it: a forger settling a half-open escrow on a declared-escrow cell could write
//! `hash([])` into the limb, decode an empty floor, and leave the selector free.
//!
//! This module is the Rust shadow of the FIX: decode the escrow bit DIRECTLY from the caveat-manifest
//! TYPE-TAG columns — the deployed, caveat-commit-bound columns the COVERAGE carrier already pins
//! (`trace_rotated::CAVEAT_BASE`, the type tags at cols 291/298/305/312, chained by `caveatCommit` to
//! PI 45). The floor the gadget reads is then the cell's REAL declared required-tag floor, bound by the
//! EXISTING caveat-commit chain — no separate digest limb, no recompute chip lookup, no new floor
//! collision-resistance hypothesis. The Lean soundness rung proving the selector forcing holds with the
//! `hcommitLimb` DISCHARGED (under only the deployed carrier `Poseidon2SpongeCR` floor) is
//! `Dregg2.Deos.CarrierBoundFloorGadget` (`gentian_selector_forced_carrier` /
//! `gentian_forged_floor_unsat_carrier`).
//!
//! ## What is and is NOT a VK change
//!
//! The floor BINDING needs NO new VK: the caveat manifest + its `caveatCommit` chain are already in the
//! deployed AIR (the COVERAGE carrier — `CapacityCarrier`'s "NOT VK-affecting" finding). The only new
//! constraint polynomials are the in-AIR DECODE + selector-force ARITHMETIC gates below (the irreducible
//! in-AIR selector forcing). This path DROPS the recompute chip lookup, the separate digest limb, and
//! the `FloorDigestBinds` floor the digest path carried.
//!
//! ## STAGED — built BESIDE the deployed, NOT flipped, NOT yet in a committed VK
//!
//! These gates are NOT emitted into a committed welded descriptor / VK and NOT routed onto any live
//! path; the deployed descriptors / VK are byte-identical. What remains to the FLIP: EMIT the carrier
//! gadget descriptor into a staged registry + a satisfying STARK PRODUCER (fill the bit/inv/OR aux
//! columns over the bound type-tag columns) + commit the (decode-only) VK delta + live admission.
//!
//! ## The constraint shape (with the ROW-LOCALITY FIX)
//!
//! Per declared-caveat slot `k` (`MAX_CAVEATS = 4`): an is-zero gadget against the escrow tag (a
//! defining gate `b_k + (tag_k − 17)·inv_k − 1 == 0` and a forcing gate `(tag_k − 17)·b_k == 0`, sound
//! over the integral domain), then a running-OR fold (`O0 = b0`, `O_{j} = O_{j-1} + b_j − O_{j-1}·b_j`)
//! into `FLOOR_ESCROW_COL`, then the FIRST-ROW-SCOPED selector-force gate
//! `FLOOR_ESCROW_COL · (ESCROW_SEL_COL − 1) == 0` (a `Boundary{First}`, fired only on the settle row),
//! then four caveat-uniformity `windowGate`s `nxt(tag_k) − loc(tag_k) == 0` (on-transition).
//!
//! A cell DECLARING escrow (some bound type-tag column == 17) forces `FLOOR_ESCROW_COL = 1` and hence,
//! on the settle row, `ESCROW_SEL_COL = 1`; a cell declaring no escrow leaves both inert.
//!
//! ### Why first-row scoping (the empirical `10ac36c54` row-locality defect, FIXED)
//!
//! The deployed satisfaction selector is producer-controlled: `1` on the settle row (row 0), `0` on the
//! carry-forward padding rows (which carry the post-settle `Consumed` status in their BEFORE block). An
//! EVERY-ROW force, over the uniformly-`fill_caveat`'d escrow manifest (`FLOOR = 1` every row), forced
//! `sel = 1` on every row — but `sel = 1` on a padding row makes the base satisfaction gate
//! `sel · (before_leg − Deposited)` bite (`before_leg = Consumed ≠ Deposited`), so the honest
//! escrow-declared settle had NO satisfying multi-row assignment (`OodEvaluationMismatch`). Scoping the
//! force to the FIRST row (where the settle, and the satisfaction discipline, live) makes it inert on
//! padding ⟹ the honest settle is SATISFIABLE again, while the `sel = 0` dodge on the settle row stays
//! closed. The uniformity `windowGate`s close the secondary decode/commit decoupling: PI 45 (the caveat
//! commit) is pinned to the LAST row, the decode reads the type-tag columns on the settle row, and
//! without a cross-row gate a forger could light a no-escrow manifest on the settle row while committing
//! the real escrow manifest to PI 45 — uniformity forces the two equal.

use super::authority_digest_weld::FLOOR_ESCROW_COL;
use super::pi::SLOT_CAVEAT_TAG_SETTLE_ESCROW;
use super::satisfaction_weld::ESCROW_SEL_COL;
use super::trace_rotated::{CAVEAT_BASE, GRAD_ROT_WIDTH};
use crate::descriptor_ir2::{VmConstraint2, WindowExpr, WindowGateSpec};
use crate::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};

use super::columns::rotation::caveat as cav;

/// The escrow tag as a signed felt constant (`SLOT_CAVEAT_TAG_SETTLE_ESCROW = 17`). Lean
/// `Dregg2.Deos.InAirAuthorityDigestGadget.tagEscrowZ`.
const TAG_ESCROW: i64 = SLOT_CAVEAT_TAG_SETTLE_ESCROW as i64;

/// **THE BOUND CAVEAT-MANIFEST TYPE-TAG COLUMN** for declared-caveat slot `k` — the deployed,
/// caveat-commit-bound column the COVERAGE carrier already pins (`CAVEAT_BASE + 1 + k·ENTRY_SIZE`, cols
/// 291/298/305/312). The decode reads the floor from HERE, NOT from a forgeable separate digest limb —
/// this is the discharge of the Lean `hcommitLimb`. Lean twin
/// `Dregg2.Deos.CarrierBoundFloorGadget.cavTagCol`.
pub const fn caveat_tag_col(k: usize) -> usize {
    CAVEAT_BASE + 1 + k * cav::ENTRY_SIZE
}

/// The per-slot is-zero boolean aux column (free headroom past the graduated rotated lane). Lean twin
/// `Dregg2.Deos.CarrierBoundFloorGadget.bitCol`.
pub const fn bit_col(k: usize) -> usize {
    GRAD_ROT_WIDTH + k
}

/// The per-slot inverse-witness aux column (free headroom). Lean twin
/// `Dregg2.Deos.CarrierBoundFloorGadget.invCol`.
pub const fn inv_col(k: usize) -> usize {
    GRAD_ROT_WIDTH + cav::MAX_CAVEATS + k
}

/// The running-OR carrier aux column `j` (`O0 = b0`, `O1 = O0∨b1`, `O2 = O1∨b2`; the final OR rides
/// `FLOOR_ESCROW_COL`). Lean twin `Dregg2.Deos.CarrierBoundFloorGadget.orCol`.
pub const fn or_col(j: usize) -> usize {
    GRAD_ROT_WIDTH + 2 * cav::MAX_CAVEATS + j
}

/// (def_k) **is-zero defining gate**: `b_k + (tag_k − 17)·inv_k − 1 == 0`. Lean
/// `Dregg2.Deos.InAirAuthorityDigestGadget.isZeroDefGate`.
fn is_zero_def_gate(tag_col: usize, bool_col: usize, inv_c: usize) -> VmConstraint2 {
    let body = LeanExpr::add(
        LeanExpr::add(
            LeanExpr::var(bool_col),
            LeanExpr::mul(
                LeanExpr::add(LeanExpr::var(tag_col), LeanExpr::constant(-TAG_ESCROW)),
                LeanExpr::var(inv_c),
            ),
        ),
        LeanExpr::constant(-1),
    );
    VmConstraint2::Base(VmConstraint::Gate(body))
}

/// (force_k) **is-zero forcing gate**: `(tag_k − 17)·b_k == 0`. Lean
/// `Dregg2.Deos.InAirAuthorityDigestGadget.isZeroForceGate`.
fn is_zero_force_gate(tag_col: usize, bool_col: usize) -> VmConstraint2 {
    let body = LeanExpr::mul(
        LeanExpr::add(LeanExpr::var(tag_col), LeanExpr::constant(-TAG_ESCROW)),
        LeanExpr::var(bool_col),
    );
    VmConstraint2::Base(VmConstraint::Gate(body))
}

/// (seed) **OR seed**: `O0 − b0 == 0`. Lean `Dregg2.Deos.CarrierBoundFloorGadget.orSeedGate`.
fn or_seed_gate(out_col: usize, bit_c: usize) -> VmConstraint2 {
    let body = LeanExpr::add(
        LeanExpr::var(out_col),
        LeanExpr::mul(LeanExpr::constant(-1), LeanExpr::var(bit_c)),
    );
    VmConstraint2::Base(VmConstraint::Gate(body))
}

/// (fold) **OR fold**: `out − (inOr + b − inOr·b) == 0`. Lean
/// `Dregg2.Deos.CarrierBoundFloorGadget.orFoldGate`.
fn or_fold_gate(out_col: usize, in_or_col: usize, bit_c: usize) -> VmConstraint2 {
    let or = LeanExpr::add(
        LeanExpr::add(LeanExpr::var(in_or_col), LeanExpr::var(bit_c)),
        LeanExpr::mul(
            LeanExpr::constant(-1),
            LeanExpr::mul(LeanExpr::var(in_or_col), LeanExpr::var(bit_c)),
        ),
    );
    let body = LeanExpr::add(
        LeanExpr::var(out_col),
        LeanExpr::mul(LeanExpr::constant(-1), or),
    );
    VmConstraint2::Base(VmConstraint::Gate(body))
}

/// (selector-force, FIRST-ROW SCOPED) `FLOOR_ESCROW_COL · (ESCROW_SEL_COL − 1) == 0`, fired ONLY on
/// the FIRST (settle) row (`Boundary{First}`, the `when_first_row` AIR domain) — the ROW-LOCALITY FIX.
/// The deployed producer pins the selector to PI 46 on the first row and sets `sel = 1` there (the
/// settle row) and `0` on the carry-forward padding rows. The previous EVERY-ROW force over a uniform
/// escrow manifest forced `sel = 1` on padding rows too, which the base satisfaction gates
/// (`sel · (before_leg − Deposited)`, with `before_leg = Consumed` on carry-forward rows) then BIT —
/// rendering the honest escrow-declared settle UNSATISFIABLE. Scoping the force to the first row makes
/// it INERT on padding (so the honest settle is satisfiable) while still closing the `sel = 0` dodge on
/// the settle row, where the satisfaction discipline must hold. Lean
/// `Dregg2.Deos.CarrierBoundFloorGadget.selectorForceFirstGate`.
fn selector_force_first_gate(floor_col: usize, sel_col: usize) -> VmConstraint2 {
    let body = LeanExpr::mul(
        LeanExpr::var(floor_col),
        LeanExpr::add(LeanExpr::var(sel_col), LeanExpr::constant(-1)),
    );
    VmConstraint2::Base(VmConstraint::Boundary {
        row: VmRow::First,
        body,
    })
}

/// (caveat-uniformity) `nxt(tag_k) − loc(tag_k) == 0`, asserted on the transition (`when_transition`,
/// rows `0..n-2`) — a two-row `windowGate` forcing the caveat type-tag column UNIFORM across adjacent
/// rows. Couples the row-0 floor DECODE to the LAST-row-pinned committed caveat (PI 45,
/// `last[CAVEAT_BASE + C_SPAN − 1]`): a forger cannot light a no-escrow manifest on the settle row
/// (decoding `floor = 0` to free the selector) while committing the cell's real escrow manifest to PI
/// 45 — uniformity forces the settle-row tags to equal the committed (last-row) tags. Lean
/// `Dregg2.Deos.CarrierBoundFloorGadget.caveatUniformGate`.
fn caveat_uniform_gate(tag_col: usize) -> VmConstraint2 {
    let body = WindowExpr::Add(
        Box::new(WindowExpr::Nxt(tag_col)),
        Box::new(WindowExpr::Mul(
            Box::new(WindowExpr::Const(-1)),
            Box::new(WindowExpr::Loc(tag_col)),
        )),
    );
    VmConstraint2::WindowGate(WindowGateSpec {
        body,
        on_transition: true,
    })
}

/// **THE CARRIER-BOUND FLOOR-DECODE + SELECTOR-FORCE + CAVEAT-UNIFORMITY GATES (STAGED).** Decode the
/// escrow bit from the four caveat-commit-bound type-tag columns, force the capacity selector ON the
/// SETTLE (first) row when escrow is declared, and force the caveat manifest UNIFORM across rows — the
/// `hcommitLimb`-discharged GENTIAN forcing (no recompute lookup, no separate digest limb) with the
/// ROW-LOCALITY FIX. The floor read is the cell's REAL declared floor, bound by the EXISTING
/// caveat-commit chain; the first-row scoping of the force makes the honest escrow-declared settle
/// SATISFIABLE (the every-row force false-rejected it on carry-forward rows); the uniformity gates
/// couple the row-0 decode to the last-row PI-45 commit. STAGED: not in a committed VK, no live routing.
/// Lean `Dregg2.Deos.CarrierBoundFloorGadget.carrierGates`.
pub fn carrier_floor_gates() -> Vec<VmConstraint2> {
    let mut gates = Vec::with_capacity(17);
    for k in 0..cav::MAX_CAVEATS {
        gates.push(is_zero_def_gate(caveat_tag_col(k), bit_col(k), inv_col(k)));
        gates.push(is_zero_force_gate(caveat_tag_col(k), bit_col(k)));
    }
    gates.push(or_seed_gate(or_col(0), bit_col(0)));
    gates.push(or_fold_gate(or_col(1), or_col(0), bit_col(1)));
    gates.push(or_fold_gate(or_col(2), or_col(1), bit_col(2)));
    gates.push(or_fold_gate(FLOOR_ESCROW_COL, or_col(2), bit_col(3)));
    // The selector-force, scoped to the settle (first) row — the row-locality fix.
    gates.push(selector_force_first_gate(FLOOR_ESCROW_COL, ESCROW_SEL_COL));
    // The cross-row caveat-uniformity gates coupling the row-0 decode to the last-row PI-45 commit.
    for k in 0..cav::MAX_CAVEATS {
        gates.push(caveat_uniform_gate(caveat_tag_col(k)));
    }
    gates
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::descriptor_ir2::eval_lean_expr;
    use crate::field::BabyBear;

    /// Row-aware violation of one carrier constraint against a `(local, next)` window with an
    /// `is_first` tag — replaying the deployed `Ir2Air::Main` firing domains: an every-row `Gate` and
    /// an `on_transition` `WindowGate` fire on the transition (here: always, the window over
    /// `local`/`next`); a `Boundary{First}` body fires only when `is_first`. Returns `0` iff satisfied.
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
            VmConstraint2::WindowGate(g) => eval_window_expr(&g.body, local, next),
            other => panic!("unexpected carrier constraint kind: {other:?}"),
        }
    }

    /// A felt evaluator for `WindowExpr` over a `(local, next)` row window (the test twin of the AIR's
    /// `eval_expr`).
    fn eval_window_expr(e: &WindowExpr, local: &[BabyBear], next: &[BabyBear]) -> BabyBear {
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
            WindowExpr::Add(a, b) => {
                eval_window_expr(a, local, next) + eval_window_expr(b, local, next)
            }
            WindowExpr::Mul(a, b) => {
                eval_window_expr(a, local, next) * eval_window_expr(b, local, next)
            }
        }
    }

    /// Build a wide-enough zero row, fill the four bound type-tag columns + the bit/inv/OR aux columns
    /// for a witnessed decode of `tags`, set the floor + selector.
    fn make_row(tags: [u32; cav::MAX_CAVEATS], sel: u32) -> Vec<BabyBear> {
        let width = (or_col(2) + 1)
            .max(FLOOR_ESCROW_COL + 1)
            .max(ESCROW_SEL_COL + 1)
            .max(caveat_tag_col(cav::MAX_CAVEATS - 1) + 1);
        let mut row = vec![BabyBear::ZERO; width];
        // the producer's decode witness: bits = (tag == escrow), inv = 1/(tag-17) when nonzero, OR fold.
        let mut running_or = 0u32;
        for k in 0..cav::MAX_CAVEATS {
            row[caveat_tag_col(k)] = BabyBear::new(tags[k]);
            let is_escrow = tags[k] == SLOT_CAVEAT_TAG_SETTLE_ESCROW;
            let b = if is_escrow { 1 } else { 0 };
            row[bit_col(k)] = BabyBear::new(b);
            // inverse witness: any value when tag == escrow (b forced 1 by the def gate's d=0 branch);
            // 1/(tag-17) when tag != escrow so the def gate `b + (tag-17)*inv - 1 = 0` holds with b=0.
            if !is_escrow {
                let d = BabyBear::new(tags[k]) - BabyBear::new(SLOT_CAVEAT_TAG_SETTLE_ESCROW);
                row[inv_col(k)] = d.inverse().expect("nonzero tag−escrow has a field inverse");
            }
            let next_or = running_or | b;
            if k == 0 {
                row[or_col(0)] = BabyBear::new(next_or);
            } else if k < cav::MAX_CAVEATS - 1 {
                row[or_col(k)] = BabyBear::new(next_or);
            } else {
                row[FLOOR_ESCROW_COL] = BabyBear::new(next_or);
            }
            running_or = next_or;
        }
        row[ESCROW_SEL_COL] = BabyBear::new(sel);
        row
    }

    /// Every carrier gate satisfied on the SETTLE row (`is_first = true`) with a self-`next` (a uniform
    /// manifest, so the uniformity window gates vanish) — the row-0 acceptance check.
    fn all_gates_zero_settle(gates: &[VmConstraint2], row: &[BabyBear]) -> bool {
        gates
            .iter()
            .all(|g| violation(g, row, row, /*is_first*/ true) == BabyBear::ZERO)
    }

    #[test]
    fn columns_are_distinct() {
        let mut cols: Vec<usize> = (0..cav::MAX_CAVEATS)
            .flat_map(|k| [caveat_tag_col(k), bit_col(k), inv_col(k)])
            .collect();
        cols.push(or_col(0));
        cols.push(or_col(1));
        cols.push(or_col(2));
        cols.push(FLOOR_ESCROW_COL);
        cols.push(ESCROW_SEL_COL);
        let n = cols.len();
        cols.sort_unstable();
        cols.dedup();
        assert_eq!(cols.len(), n, "no two carrier-decode columns alias");
    }

    #[test]
    fn tag_cols_are_the_deployed_bound_columns() {
        // The decode reads the EXACT deployed caveat-manifest type-tag columns the COVERAGE carrier
        // already binds via the caveat-commit chain — NOT a free digest limb. Each is the carrier's
        // own `CAVEAT_BASE + 1 + k·ENTRY_SIZE` (definitional alignment to the bound manifest).
        for k in 0..cav::MAX_CAVEATS {
            assert_eq!(caveat_tag_col(k), CAVEAT_BASE + 1 + k * cav::ENTRY_SIZE);
        }
        // The concrete bound columns (drift pin at v13 geometry: CAVEAT_BASE = V1_WIDTH(188) +
        // 2*B_SPAN(227) = 642; ENTRY_SIZE = 7; so caveat_tag_col(0) = 643).
        assert_eq!(caveat_tag_col(0), 643);
        assert_eq!(caveat_tag_col(1), 650);
        assert_eq!(caveat_tag_col(2), 657);
        assert_eq!(caveat_tag_col(3), 664);
    }

    #[test]
    fn declared_escrow_decodes_and_forces_selector() {
        let gates = carrier_floor_gates();
        // a cell declaring escrow (tag 17 in slot 0, a vault tag elsewhere) with the selector ON.
        let row = make_row([SLOT_CAVEAT_TAG_SETTLE_ESCROW, 19, 0, 0], /*sel*/ 1);
        assert!(
            all_gates_zero_settle(&gates, &row),
            "a declared-escrow manifest must decode floor=1 and the selector-forced settle row satisfies"
        );
        // FLOOR_ESCROW_COL is forced 1 by the decode.
        assert_eq!(row[FLOOR_ESCROW_COL], BabyBear::new(1));
    }

    #[test]
    fn declared_escrow_with_selector_off_on_settle_row_is_unsat() {
        let gates = carrier_floor_gates();
        // escrow declared (floor decodes 1) but the forger sets the selector 0 on the SETTLE row — the
        // first-row selector-force gate bites: the half-open dodge by `sel = 0` is closed.
        let row = make_row([SLOT_CAVEAT_TAG_SETTLE_ESCROW, 19, 0, 0], /*sel*/ 0);
        assert!(
            !all_gates_zero_settle(&gates, &row),
            "a declared-escrow cell cannot set the selector 0 on the settle row — the force must bite"
        );
    }

    #[test]
    fn first_row_force_is_inert_on_padding_rows() {
        // THE ROW-LOCALITY FIX: a carry-forward padding row (is_first = false) with escrow declared
        // (FLOOR = 1) and the selector 0 MUST satisfy the first-row-scoped force — this is exactly the
        // case the previous EVERY-ROW force false-rejected, rendering the honest settle unsatisfiable.
        let gates = carrier_floor_gates();
        let row = make_row([SLOT_CAVEAT_TAG_SETTLE_ESCROW, 19, 0, 0], /*sel*/ 0);
        assert_eq!(row[FLOOR_ESCROW_COL], BabyBear::new(1), "escrow ⟹ FLOOR 1");
        let all_inert = gates
            .iter()
            .all(|g| violation(g, &row, &row, /*is_first*/ false) == BabyBear::ZERO);
        assert!(
            all_inert,
            "with escrow declared + selector 0, every carrier gate must be inert on a PADDING row \
             (is_first=false) — the first-row scoping is what restores honest-settle satisfiability"
        );
    }

    #[test]
    fn no_escrow_declared_leaves_selector_inert() {
        let gates = carrier_floor_gates();
        // no escrow tag in the manifest (monotonic/vault only) → floor decodes 0 → selector inert
        // (whatever the selector value). The decode is fail-open ONLY where the cell declares no escrow.
        let row0 = make_row([6, 19, 0, 0], /*sel*/ 0);
        assert!(
            all_gates_zero_settle(&gates, &row0),
            "no declared escrow ⟹ floor 0 ⟹ selector inert (no false reject)"
        );
        assert_eq!(row0[FLOOR_ESCROW_COL], BabyBear::ZERO);
    }

    #[test]
    fn escrow_in_a_later_slot_still_forces() {
        let gates = carrier_floor_gates();
        // escrow declared in slot 2 (not slot 0) — the OR fold still lights the floor.
        let row = make_row([6, 19, SLOT_CAVEAT_TAG_SETTLE_ESCROW, 0], /*sel*/ 1);
        assert!(
            all_gates_zero_settle(&gates, &row),
            "escrow declared in any slot must light the floor through the OR fold"
        );
        assert_eq!(row[FLOOR_ESCROW_COL], BabyBear::new(1));
        // ...and the selector-off variant bites on the settle row.
        let row_off = make_row([6, 19, SLOT_CAVEAT_TAG_SETTLE_ESCROW, 0], /*sel*/ 0);
        assert!(!all_gates_zero_settle(&gates, &row_off));
    }

    #[test]
    fn caveat_uniformity_gate_bites_on_a_non_uniform_manifest() {
        // THE (ii) COUPLING: the four uniformity window gates force the caveat type-tag columns equal
        // across adjacent rows. A forger lighting a no-escrow manifest on the settle row (local) while
        // committing the escrow manifest on the next/last row (next) trips a uniformity gate.
        let gates = carrier_floor_gates();
        let local = make_row([6, 19, 0, 0], /*sel*/ 0); // settle row: no escrow tag
        let next = make_row([SLOT_CAVEAT_TAG_SETTLE_ESCROW, 19, 0, 0], /*sel*/ 0); // committed: escrow
        let some_bites = gates
            .iter()
            .any(|g| violation(g, &local, &next, /*is_first*/ true) != BabyBear::ZERO);
        assert!(
            some_bites,
            "a non-uniform caveat manifest (settle-row tags ≠ next-row tags) must trip a uniformity gate"
        );
        // ...and a uniform escrow manifest with the selector ON (the honest settle row) passes every
        // carrier gate.
        let honest = make_row([SLOT_CAVEAT_TAG_SETTLE_ESCROW, 19, 0, 0], /*sel*/ 1);
        let all_uniform_ok = gates
            .iter()
            .all(|g| violation(g, &honest, &honest, /*is_first*/ true) == BabyBear::ZERO);
        assert!(
            all_uniform_ok,
            "a uniform escrow manifest with the selector on satisfies every carrier gate on the settle row"
        );
    }

    #[test]
    fn gate_count_matches_lean() {
        // 4 × (def + force) + seed + 2 folds + final fold + first-row selector-force + 4 caveat
        // uniformity gates = 17, matching the Lean `carrierGates.length == 17`.
        assert_eq!(carrier_floor_gates().len(), 17);
    }
}
