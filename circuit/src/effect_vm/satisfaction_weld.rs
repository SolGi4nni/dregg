//! # `satisfaction_weld` — the IN-AIR capacity-gate satisfaction constraints (PIECE 2 of the VK
//! epoch, STAGED).
//!
//! `docs/deos/VK-EPOCH-CONSTRAINT-BINDING-DESIGN.md` §6 names two halves of the house-capacity
//! light-client weld:
//!
//!  * **COVERAGE** (PIECE 1) — the capacity manifest entry cannot be OMITTED. Done + deployed: the
//!    rotated caveat carrier (`caveatCommit` → PI 45) binds the manifest into the ~124-bit wide
//!    commit, so a pure light client witnesses presence (`trace_rotated::slot_caveats_to_rotated_manifest`
//!    + `verify::verify_rotated_caveat_coverage`; Lean `Dregg2.Deos.CapacityCarrier`).
//!
//!  * **SATISFACTION** (PIECE 2, THIS module) — the gate must have HELD over the COMMITTED state.
//!    Today the deployed off-AIR re-evaluation (`verify::verify_slot_caveat_manifest`, the
//!    `SETTLE_ESCROW` arm) reads CALLER-supplied `initial_fields`/`final_fields` 8-felt slot views; a
//!    pure light client does not bind those. This module is the genuinely-VK-affecting fix: the
//!    gate's slot reads are expressed as IN-AIR `VmConstraint::Gate` constraints over the rotated
//!    BEFORE/AFTER state-block FIELD columns (`r3..r10`, the `trace_rotated::fill_block` welds), which
//!    the chained `wireCommitR` → state-commit absorbs into the wide commit. A satisfying proof then
//!    FORCES the gate over the committed state.
//!
//! ## STAGED — built BESIDE the deployed, NOT flipped, NOT yet in a committed VK
//!
//! These constraints are NOT yet emitted into a committed welded descriptor / VK and NOT routed onto
//! any live path. They are the constraint polynomials a staged `settleEscrowSatVmDescriptor2R24` would
//! carry; assembling that descriptor (its Lean emit keystone), committing its VK, and flipping the
//! live path through it is the remaining gated VK epoch (the design doc §6 remaining + flip plan).
//! Until that flip, satisfaction is NOT light-client-witnessed — only a verifier holding the
//! committed-state opening witnesses it (the cap-membership posture). The Lean rung proving these
//! constraints carry pure-light-client satisfaction is `Dregg2.Deos.CapacitySatisfaction`
//! (`satisfaction_witnessed` + the composed `capacity_witnessed_pure_lightclient`).
//!
//! ## The constraint shape
//!
//! Each gate is a selector-gated row-local equality `sel · (col − const) == 0` (degree 2), inert when
//! the capacity selector `sel` is 0 (padding / non-capacity rows), and forcing the field equality when
//! `sel = 1`. The sealed-escrow gate (the Lean `SettleFieldGate`) is FOUR such gates: both legs
//! `Deposited` in the BEFORE block, both `Consumed` in the AFTER block.

use super::pi;
use super::trace_rotated::{AFTER_BASE, BEFORE_BASE};
use crate::descriptor_ir2::VmConstraint2;
use crate::lean_descriptor_air::{LeanExpr, VmConstraint};

/// **THE REAL CAPACITY-SELECTOR COLUMN** — the free PARAM slot `param2` (`PARAM_BASE + 2 = 70`) the
/// emitted `settleEscrowSatVmDescriptor2R24` gates the four satisfaction constraints on, and that the
/// producer fills (`1` on the settle row, `0` on padding). This REPLACES the prior placeholder
/// `SEL = 320` (a column no producer filled): the emitted descriptor pins this column to PI 46 on the
/// first row (`pi_binding first col 70 pi 46`), so a verifier that knows the cell declares the escrow
/// capacity (the deployed COVERAGE carrier) can FORCE the selector on. The Lean twin is
/// `Dregg2.Deos.SettleEscrowSatDescriptor.ESCROW_SEL_COL`.
pub const ESCROW_SEL_COL: usize = super::columns::PARAM_BASE + 2;

/// The PI slot the emitted descriptor pins the selector to (the fifth appended PI, `pi_base + 4`).
/// Lean `Dregg2.Deos.SettleEscrowSatDescriptor.ESCROW_SEL_PI`.
pub const ESCROW_SEL_PI: usize = 46;

/// The rotated state-block in-block offset of field-slot `k`: the `r3..r10 ↔ fields[0..8]` weld
/// (`r3` is pre-limb index 4, so `fields[k]` rides limb `4 + k` — `trace_rotated::fill_block`). The
/// Rust twin of the Lean `Dregg2.Deos.CapacitySatisfaction.fieldOffset`.
pub const fn rotated_field_offset(k: usize) -> usize {
    4 + k
}

/// The absolute trace column carrying field-slot `k` of the rotated BEFORE block.
pub const fn before_field_col(k: usize) -> usize {
    BEFORE_BASE + rotated_field_offset(k)
}

/// The absolute trace column carrying field-slot `k` of the rotated AFTER block.
pub const fn after_field_col(k: usize) -> usize {
    AFTER_BASE + rotated_field_offset(k)
}

/// One selector-gated equality gate `sel · (col − value) == 0` as a `VmConstraint::Gate` body. The
/// selector multiplier is baked into the body (the deployed `VmConstraint::Gate` convention: the body
/// must also vanish on padding rows, here via `sel = 0`).
fn selector_eq_gate(sel_col: usize, col: usize, value: u32) -> VmConstraint2 {
    let body = LeanExpr::mul(
        LeanExpr::var(sel_col),
        LeanExpr::add(LeanExpr::var(col), LeanExpr::constant(-(value as i64))),
    );
    VmConstraint2::Base(VmConstraint::Gate(body))
}

/// **THE SEALED-ESCROW IN-AIR SATISFACTION GATES (STAGED).** The four `VmConstraint::Gate`
/// constraints welding the `SETTLE_ESCROW` gate to the rotated BEFORE/AFTER state-block field columns,
/// gated by the capacity selector `sel_col` (active on a settle row, 0 elsewhere):
///
///  1. `sel · (before[legA] − Deposited) == 0`
///  2. `sel · (before[legB] − Deposited) == 0`
///  3. `sel · (after[legA]  − Consumed)  == 0`
///  4. `sel · (after[legB]  − Consumed)  == 0`
///
/// where `before[k] = before_field_col(k)` and `after[k] = after_field_col(k)` read the rotated
/// `r{3+k}` columns the wide commit absorbs. This is the Rust shadow of the Lean `SettleFieldGate`
/// (`Dregg2.Deos.CapacitySatisfaction`): a satisfying proof FORCES both legs `Deposited` before and
/// `Consumed` after — a forged PARTIAL or PHANTOM settle is UNSAT. STAGED: not yet in a committed VK.
pub fn settle_escrow_satisfaction_gates(
    sel_col: usize,
    leg_a_slot: usize,
    leg_b_slot: usize,
) -> Vec<VmConstraint2> {
    let dep = pi::SETTLE_ESCROW_STATUS_DEPOSITED;
    let con = pi::SETTLE_ESCROW_STATUS_CONSUMED;
    vec![
        selector_eq_gate(sel_col, before_field_col(leg_a_slot), dep),
        selector_eq_gate(sel_col, before_field_col(leg_b_slot), dep),
        selector_eq_gate(sel_col, after_field_col(leg_a_slot), con),
        selector_eq_gate(sel_col, after_field_col(leg_b_slot), con),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::descriptor_ir2::eval_lean_expr;
    use crate::field::BabyBear;

    /// Pull the `LeanExpr` body out of a `VmConstraint::Gate` for evaluation.
    fn gate_body(c: &VmConstraint2) -> &LeanExpr {
        match c {
            VmConstraint2::Base(VmConstraint::Gate(body)) => body,
            _ => panic!("expected a Gate constraint"),
        }
    }

    /// Build a wide-enough zero row, then set the selector + the four leg field columns.
    fn make_row(
        sel_col: usize,
        sel: u32,
        leg_a_slot: usize,
        leg_b_slot: usize,
        before_a: u32,
        before_b: u32,
        after_a: u32,
        after_b: u32,
    ) -> Vec<BabyBear> {
        let width = (after_field_col(7) + 1).max(sel_col + 1);
        let mut row = vec![BabyBear::ZERO; width];
        row[sel_col] = BabyBear::new(sel);
        row[before_field_col(leg_a_slot)] = BabyBear::new(before_a);
        row[before_field_col(leg_b_slot)] = BabyBear::new(before_b);
        row[after_field_col(leg_a_slot)] = BabyBear::new(after_a);
        row[after_field_col(leg_b_slot)] = BabyBear::new(after_b);
        row
    }

    fn all_gates_zero(gates: &[VmConstraint2], row: &[BabyBear]) -> bool {
        gates
            .iter()
            .all(|g| eval_lean_expr(gate_body(g), row) == BabyBear::ZERO)
    }

    // The legs ride field slots 0 and 1; the capacity selector is the REAL `ESCROW_SEL_COL` (param2,
    // col 70) the emitted `settleEscrowSatVmDescriptor2R24` gates on and the producer fills — NOT the
    // prior `SEL = 320` placeholder. A settle row sets it to 1.
    const SEL: usize = ESCROW_SEL_COL;
    const LEG_A: usize = 0;
    const LEG_B: usize = 1;
    const DEP: u32 = pi::SETTLE_ESCROW_STATUS_DEPOSITED;
    const CON: u32 = pi::SETTLE_ESCROW_STATUS_CONSUMED;

    #[test]
    fn honest_settle_satisfies_the_in_air_gates() {
        let gates = settle_escrow_satisfaction_gates(SEL, LEG_A, LEG_B);
        // both legs Deposited before, both Consumed after, selector active.
        let row = make_row(SEL, 1, LEG_A, LEG_B, DEP, DEP, CON, CON);
        assert!(
            all_gates_zero(&gates, &row),
            "the honest settle transition must satisfy every in-AIR gate"
        );
    }

    #[test]
    fn partial_settle_is_unsat() {
        let gates = settle_escrow_satisfaction_gates(SEL, LEG_A, LEG_B);
        // leg A Consumed, leg B still Deposited after — the half-open trade.
        let row = make_row(SEL, 1, LEG_A, LEG_B, DEP, DEP, CON, DEP);
        assert!(
            !all_gates_zero(&gates, &row),
            "a partial settle (leg B left Deposited) must violate an in-AIR gate"
        );
    }

    #[test]
    fn phantom_settle_is_unsat() {
        let gates = settle_escrow_satisfaction_gates(SEL, LEG_A, LEG_B);
        // leg A never Deposited before (Empty = 0) — no genuine lock.
        let row = make_row(SEL, 1, LEG_A, LEG_B, 0, DEP, CON, CON);
        assert!(
            !all_gates_zero(&gates, &row),
            "a phantom settle (leg A not Deposited before) must violate an in-AIR gate"
        );
    }

    /// **THE EMITTED DESCRIPTOR CARRIES THESE GATES AND THEY BITE.** Parse the staged
    /// `settleEscrowSatVmDescriptor2R24` straight from the committed registry TSV, pull out its
    /// FOUR welded satisfaction gates (the `.gate` constraints whose body is
    /// `mul(var ESCROW_SEL_COL, …)`), and confirm: (a) the Rust builder
    /// [`settle_escrow_satisfaction_gates`] reproduces EXACTLY those four gate bodies; (b) an honest
    /// settle row makes every emitted gate body vanish; (c) a forged partial / phantom settle makes
    /// an emitted gate body NON-zero — the teeth bite against the DEPLOYED-staged descriptor's own
    /// constraints, not a hand-built shadow. The selector is the real col 70 (param2), pinned to PI
    /// 46 by the descriptor.
    #[test]
    fn emitted_descriptor_carries_the_welded_gates_and_they_bite() {
        use crate::descriptor_ir2::parse_vm_descriptor2;
        use crate::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;

        let json = V3_STAGED_REGISTRY_TSV
            .lines()
            .find_map(|l| {
                let mut it = l.splitn(3, '\t');
                if it.next() == Some("settleEscrowSatVmDescriptor2R24") {
                    let _name = it.next();
                    it.next()
                } else {
                    None
                }
            })
            .expect("settleEscrowSatVmDescriptor2R24 in the staged registry");
        let desc = parse_vm_descriptor2(json).expect("welded escrow descriptor parses");
        assert_eq!(
            desc.public_input_count, 47,
            "rotated 46-PI + the selector slot"
        );

        // The emitted welded gates: row-local bodies of the form `mul(var ESCROW_SEL_COL, _)`.
        // Read through `row_local_body` rather than by matching `VmConstraint::Gate`: the last-row
        // hardening flag day carries every row-local body as a whole-domain `windowGate`, and a
        // kind-match here silently collected zero — taking this Rust-builder-vs-Lean-emitter
        // byte-equality tie with it.
        let emitted: Vec<LeanExpr> = desc
            .constraints
            .iter()
            .filter_map(|c| {
                let body = crate::descriptor_ir2::row_local_body(c)?;
                match body.as_ref() {
                    LeanExpr::Mul(l, _) if **l == LeanExpr::Var(ESCROW_SEL_COL) => {
                        Some(body.into_owned())
                    }
                    _ => None,
                }
            })
            .collect();
        assert_eq!(
            emitted.len(),
            4,
            "the emitted descriptor carries EXACTLY the four selector-gated satisfaction gates"
        );

        // (a) the Rust builder reproduces the emitted gate bodies byte-for-byte.
        let built = settle_escrow_satisfaction_gates(ESCROW_SEL_COL, LEG_A, LEG_B);
        let built_bodies: Vec<LeanExpr> = built.iter().map(|c| gate_body(c).clone()).collect();
        assert_eq!(
            built_bodies, emitted,
            "the Rust builder reproduces the emitted descriptor's welded gate bodies"
        );

        // (b) honest settle: every emitted gate body vanishes.
        let honest = make_row(ESCROW_SEL_COL, 1, LEG_A, LEG_B, DEP, DEP, CON, CON);
        assert!(
            emitted
                .iter()
                .all(|b| eval_lean_expr(b, &honest) == BabyBear::ZERO),
            "the honest settle satisfies every EMITTED welded gate"
        );
        // (c) forged partial (leg B left Deposited) + phantom (leg A never Deposited): a gate bites.
        let partial = make_row(ESCROW_SEL_COL, 1, LEG_A, LEG_B, DEP, DEP, CON, DEP);
        assert!(
            emitted
                .iter()
                .any(|b| eval_lean_expr(b, &partial) != BabyBear::ZERO),
            "a partial settle violates an EMITTED welded gate"
        );
        let phantom = make_row(ESCROW_SEL_COL, 1, LEG_A, LEG_B, 0, DEP, CON, CON);
        assert!(
            emitted
                .iter()
                .any(|b| eval_lean_expr(b, &phantom) != BabyBear::ZERO),
            "a phantom settle violates an EMITTED welded gate"
        );
    }

    #[test]
    fn selector_off_makes_the_gates_inert() {
        let gates = settle_escrow_satisfaction_gates(SEL, LEG_A, LEG_B);
        // A NON-capacity / padding row (selector 0) with arbitrary field values: the gates vanish, so
        // the weld is inert exactly where the cell declares no escrow caveat (fail-OPEN only off the
        // selector — coverage is what forces the selector on a declared capacity turn).
        let row = make_row(SEL, 0, LEG_A, LEG_B, 7, 9, 3, 4);
        assert!(
            all_gates_zero(&gates, &row),
            "with the capacity selector 0 the satisfaction gates must be inert (no false reject)"
        );
    }
}
